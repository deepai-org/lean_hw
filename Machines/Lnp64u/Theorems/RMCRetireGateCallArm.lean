-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCallPrimary

/-!
# R-MC retirement: full gate_call arm

Top-level decode and specification reduction for the `gate_call` retirement
square.  The semantic, transfer, status-memory, and Mover bridges live in
`RMCRetireGateCall`; this file assembles them against the core cycle.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- The system table's opcode-22 entry is the named gate-call semantics used
by the proof-side bridge library. -/
theorem gateCall_system_exec :
    (Machines.Lnp64u.Isa.system.get ⟨6, by decide⟩).sem.exec =
      Machines.Lnp64u.Isa.Wip.gateCallExec := by
  rfl

/-- Exact retirement reduction for a decoded gate call: architectural PC
advance followed by the named gate-call body and the standard outcome
triage. -/
theorem retire_gateCall_exec (τ : MachineState) (E : DomainId)
    (W : Loom.Word32)
    (hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6))) :
    retire τ E W =
      let c : Ctx := { d := E, pc := (τ.doms E).pc, op := operandsOf W }
      let τ0 := τ.setDom E fun ds => { ds with pc := ds.pc + 1 }
      match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err e τ' =>
          τ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
      | .fault f => haltWith τ E f := by
  have hfind : isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) =
      some (Machines.Lnp64u.Isa.system.get ⟨6, by decide⟩) := by
    rfl
  rw [retire_of_decode_some _ E W _ (hdec.trans hfind)]
  rw [gateCall_system_exec]
  rfl

/-- Opcode 22 selects the gate-call circuit's complete memory-port triple
from the domain and opcode folds. -/
theorem retireMem_gateCall_sel (σ : Loom.Hw.St) (E : DomainId)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6) :
    ((((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))).1).eval σ
      = (Hw.callCirc E).memEn.eval σ)
    ∧ ((Hw.callCirc E).memEn.eval σ = 1#1 →
        ((((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
            (.lit 0 : Expr 32))).2.1).eval σ = (Hw.callCirc E).memAddr.eval σ)
        ∧ ((((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
            (.lit 0 : Expr 32))).2.2).eval σ = (Hw.callCirc E).memData.eval σ)) := by
  have hmn : (Hw.isMn "gate_call").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_call" = 22#6).symm
  have hmem : ("gate_call", Hw.callCirc E) ∈ Hw.opCircs E := by
    simp [Hw.opCircs]
  have hnd : ((Hw.opCircs E).map Prod.fst).Nodup := by
    rw [opCircs_fst_all E]
    exact allMns_nodup
  have hq : ∀ p ∈ Hw.opCircs E, p.1 ≠ "gate_call" →
      (Hw.isMn p.1).eval σ = 0#1 ∨ isLit0 p.2.memEn = true := by
    intro p hp hne
    left
    exact bv1_ne_one.mp (isMn_ne_of_opc σ p.1 22#6 hopc
      ((by decide +kernel : ∀ mn' ∈ allMns, mn' ≠ "gate_call" →
        (22#6 : BitVec 6) ≠ Hw.opcodeOf mn') p.1
        (by rw [← opCircs_fst_all E]; exact List.mem_map_of_mem hp) hne))
  exact retireMem_op_sel σ E "gate_call" (Hw.callCirc E) hifsel hifexcl
    hmn hmem hnd hq

/-- If the combined call predicate is false, opcode 22 leaves the core
memory port disabled. -/
theorem coreAct_mem_gateCall_failed (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hok0 : (Hw.callOkE E).eval σ = 0#1) (b : Addr) :
    ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
      b.toNat 32 = σ.mems "mem" b.toNat 32 := by
  have hport := retireMem_gateCall_sel σ E hifsel hifexcl hopc
  rw [coreAct_run_retire_eq m σ _ hifv hcl,
    retireAct_run_mems σ _ b.toNat 32]
  show (if (((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1,
          .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
        (.lit 0 : Expr 32))).1).eval σ = 1#1 then _
    else ((Hw.refillAct m).run σ σ)).mems "mem" b.toNat 32 = _
  rw [if_neg (by
    rw [hport.1]
    show ¬((Hw.callCirc E).memEn.eval σ = 1#1)
    unfold Hw.callCirc Hw.sweepMem Hw.andAll
    change ¬((Hw.callOkE E).eval σ &&& _ = 1#1)
    rw [hok0]
    exact (by decide : ∀ x : BitVec 1, ¬(0#1 &&& x = 1#1)) _)]
  rw [refill_pres_mem m σ "mem" b.toNat 32]

/-- Common full-cycle square for every gate-call errno branch. The caller
supplies only the selected response action and its matching specification
state; Mover and memory quiescence follow from `callOkE = 0`. -/
theorem square_retire_gateCall_error (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (E : DomainId)
    (hEval : E.val = (σ.regs "if_dom" 2).toNat)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hok0 : (Hw.callOkE E).eval σ = 0#1)
    (errw : Loom.Word32)
    (hcoreX : ∀ acc, (Hw.retireFor E).run σ acc =
      (Act.seq (Hw.pcAdvA E)
        (Hw.writeReg E Hw.rdE (.lit errw))).run σ acc)
    (hspecE : corePhase m (refillPhase m (Hw.abs σ)) =
      (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).setDom E
          (fun ds => ds.setReg
            (operandsOf (σ.regs "if_word" 32)).rd errw)) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hret := retiringE_one σ hifv hcl
  have hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1 := by
    intro d
    by_cases hd : d = E
    · subst d
      rw [if_pos rfl]
      exact hifsel
    · rw [if_neg hd, bv1_ne_one.mp (hifexcl d hd)]
  have hmn : (Hw.isMn "gate_call").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_call" = 22#6).symm
  have hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_drop" 22#6 hopc (by decide +kernel)
  have hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_revoke" 22#6 hopc (by decide +kernel)
  have hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_return" 22#6 hopc (by decide +kernel)
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1 := by
    intro d
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 22#6 hopc (by decide +kernel)
  have hbad : ∀ d : DomainId, d = E → (Hw.callOkE d).eval σ = 0#1 := by
    intro d hd
    simpa [hd] using hok0
  have hin : Inert σ := Inert.of_failed_call σ E hret hif hdrop hrev hmn
    hreturn hbad hnew
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 22#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 22#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d
          (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 22#6 hopc (by decide +kernel))
  have hcoremem : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = σ.mems "mem" b.toNat 32 :=
    coreAct_mem_gateCall_failed m σ E hifv hcl hifsel hifexcl hopc hok0
  exact retire_err_common_mem m hwf hfit σ hsync hifv hcl hin hmapz
    hunmapz hswz hcoremem E hEval errw hcoreX hspecE

/-- Turn a first failing gate-call check and its matching specification
equation into the full-cycle retirement square.  This packages the repeated
`callOkE = 0`, errno-ladder selection, memory quiescence, and common error
assembly needed by all ten call checks. -/
theorem square_retire_gateCall_firstError (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (E : DomainId)
    (hEval : E.val = (σ.regs "if_dom" 2).toNat)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (pre post : List Hw.Check) (cond : Expr 1) (er : Errno)
    (hchecks : Hw.callChecks E = pre ++ (cond, .err er) :: post)
    (hpre : ∀ x ∈ pre, x.1.eval σ ≠ 1#1)
    (hfail : cond.eval σ = 1#1)
    (hspecE : corePhase m (refillPhase m (Hw.abs σ)) =
      (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).setDom E
          (fun ds => ds.setReg
            (operandsOf (σ.regs "if_word" 32)).rd er.toWord)) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hok0 : (Hw.callOkE E).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro hok
    have hall := (okOf_eval_iff σ (Hw.callChecks E)).mp hok
    have hmem : (cond, .err er) ∈ Hw.callChecks E := by
      rw [hchecks]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    exact hall (cond, .err er) hmem hfail
  have hcoreX : ∀ acc, (Hw.retireFor E).run σ acc =
      (Act.seq (Hw.pcAdvA E)
        (Hw.writeReg E Hw.rdE (.lit er.toWord))).run σ acc := by
    intro acc
    exact retireFor_gateCall_first_error σ acc E pre post cond er hopc
      hchecks hpre hfail
  exact square_retire_gateCall_error m hwf hfit σ hsync hifv hcl E hEval
    hifsel hifexcl hopc hok0 er.toWord hcoreX hspecE

/-- Complete first ladder arm: a stale primary gate handle retires with
`-ESTALE`, with no architectural effect beyond PC and `rd`. -/
theorem square_retire_gateCall_stale (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hstale : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ ≠ 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  set HWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hHWv
  have hSval : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (HWv.extractLsb' 0 4)).val =
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := by
    rw [hR1]
    rfl
  have hlivE := capSel_live_eval σ E (Hw.readReg E Hw.rs1E) _ hSval
  rw [hR1] at hlivE
  have hraw : ¬(σ.regs (Hw.dcapV E
        (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1 ∧
      σ.regs (Hw.dgen E (finOfBv (by decide)
        (HWv.extractLsb' 0 4))) 8 = HWv.extractLsb' 4 8 ∧
      HWv.extractLsb' 4 8 ≠ 0) := by
    intro h
    exact hstale (hlivE.mpr h)
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 = HWv := by
    exact specReg_bridge m σ E _
  have hnone : (τ0.doms E).liveCap (Handle.decode HWv).slot
      (Handle.decode HWv).gen = none := by
    unfold τ0
    rw [specLiveCap_bridge, abs_liveCap]
    exact if_neg hraw
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.staleHandle.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec
      { d := E
        pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
        op := operandsOf W } τ0 with
      | .ok _ τ' => τ'
      | .err e τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd e.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [gateCallExec_stale]
    change (τ0.doms E).liveCap
      (Handle.decode ((τ0.doms E).reg (operandsOf W).rs1)).slot
      (Handle.decode ((τ0.doms E).reg (operandsOf W).rs1)).gen = none
    rw [hreg]
    exact hnone
  have hfail : (Expr.not (Hw.callSel E).live).eval σ = 1#1 := by
    show ~~~((Hw.callSel E).live.eval σ) = 1#1
    rw [bv1_ne_one.mp hstale]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc [] (Hw.callChecks E).tail
    (Expr.not (Hw.callSel E).live) .staleHandle
  · rfl
  · intro x hx
    simp at hx
  · exact hfail
  simpa [τ0, W] using hspec

/-- Complete second ladder arm.  Once the primary handle is live, the
combined gate-capability check fails exactly when its class disagrees with
the selected entry or that entry is a memory capability. -/
theorem square_retire_gateCall_badPrimary (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hbad : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  set HWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hHWv
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 = HWv := by
    exact specReg_bridge m σ E _
  have hword : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg, hR1]
  have hslot : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4)).val =
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := rfl
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  obtain ⟨e, hliveτ, hcap⟩ := capSel_entry_of_live σ τ0 E
    (Hw.readReg E Hw.rs1E) hbridge (by simpa [E] using hlive)
  have hclsIff := capSel_clsOk_iff_some σ E (Hw.readReg E Hw.rs1E)
    (finOfBv (by decide) (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4))
    e hkc hslot hcap
  have hmemIff := capSel_isMem_iff_some σ E (Hw.readReg E Hw.rs1E)
    (finOfBv (by decide) (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4))
    e hkc hslot hcap
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .badCap τ0 := by
    by_cases hcls : (Hw.callSel E).clsOk.eval σ = 1#1
    · have hmem : (Hw.kIsMem (Hw.callSel E).kindW).eval σ = 1#1 := by
        have hb : ~~~((Hw.callSel E).clsOk.eval σ &&&
            ~~~((Hw.kIsMem (Hw.callSel E).kindW).eval σ)) = 1#1 := by
          simpa [E] using hbad
        rw [hcls] at hb
        by_contra hm
        rw [bv1_ne_one.mp hm] at hb
        simp at hb
      obtain ⟨base, len, perms, hkind⟩ := hmemIff.mp hmem
      apply gateCallExec_memCap c τ0 e
      · simpa [c, hreg, hR1] using hliveτ
      · rw [hword]
        exact hclsIff.mp hcls
      · exact hkind
    · apply gateCallExec_badClass c τ0 e
      · simpa [c, hreg, hR1] using hliveτ
      · intro heq
        apply hcls
        apply hclsIff.mpr
        rwa [hword] at heq
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.badCap.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle)]
    (List.drop 2 (Hw.callChecks E))
    (Expr.not (Expr.and (Hw.callSel E).clsOk
      (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))) .badCap
  · rfl
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact hpassLive
  · simpa [E] using hbad
  · simpa [τ0, W] using hspec

/-- Complete third ladder arm.  A live, class-correct gate capability whose
selected gate already has an activation retires with `gateBusy`. -/
theorem square_retire_gateCall_active (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hactive : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  set HWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hHWv
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 = HWv := by
    exact specReg_bridge m σ E _
  have hword : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg, hR1]
  have hslot : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4)).val =
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := rfl
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  obtain ⟨e, hliveτ, hcap⟩ := capSel_entry_of_live σ τ0 E
    (Hw.readReg E Hw.rs1E) hbridge (by simpa [E] using hlive)
  have hclsIff := capSel_clsOk_iff_some σ E (Hw.readReg E Hw.rs1E)
    (finOfBv (by decide) (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4))
    e hkc hslot hcap
  have hmemIff := capSel_isMem_iff_some σ E (Hw.readReg E Hw.rs1E)
    (finOfBv (by decide) (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4))
    e hkc hslot hcap
  have hlogic : (Hw.callSel E).clsOk.eval σ = 1#1 ∧
      (Hw.kIsMem (Hw.callSel E).kindW).eval σ = 0#1 := by
    apply (by decide : ∀ a b : BitVec 1,
      ~~~(a &&& ~~~b) ≠ 1#1 → a = 1#1 ∧ b = 0#1)
    simpa [E] using hprimary
  have hcls := hclsIff.mp hlogic.1
  obtain ⟨g, hkind⟩ : ∃ g : GateId, e.kind = .gate g := by
    cases hk : e.kind with
    | mem base len perms =>
        exfalso
        have hm := hmemIff.mpr ⟨base, len, perms, hk⟩
        have hm0 : (Hw.kIsMem
            (Hw.capSel E (Hw.readReg E Hw.rs1E)).kindW).eval σ = 0#1 := by
          simpa [Hw.callSel] using hlogic.2
        rw [hm0] at hm
        contradiction
    | gate g => exact ⟨g, rfl⟩
  have hkw : (Hw.callSel E).kindW.eval σ = Hw.encKind (.gate g) := by
    have hk := capSel_kind_of_some σ E (Hw.readReg E Hw.rs1E)
      (finOfBv (by decide)
        (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4)) e
      hkc hslot hcap
    simpa [Hw.callSel, hkind] using hk
  have hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid E).eval σ) = g :=
    kGid_encGate_eval σ (Hw.callSel E).kindW g hkw
  have hcapLive : Machines.Lnp64u.Isa.capLive c.d
      ((τ0.doms c.d).reg c.op.rs1) τ0 =
      .ok ((Handle.decode ((Hw.readReg E Hw.rs1E).eval σ)).slot,
        (Handle.decode ((Hw.readReg E Hw.rs1E).eval σ)).gen, e) τ0 := by
    apply capLive_eq_selected
    · rw [hword]
      cases hd : Handle.decode ((Hw.readReg E Hw.rs1E).eval σ) with
      | mk S G cls =>
          simp only [hd] at hcls ⊢
          rw [hcls]
    · simpa [c, hword] using hliveτ
  have hactSome := (callGateActive_eval σ E g hgid).mp
    (by simpa [E] using hactive)
  obtain ⟨a, hact⟩ := Option.isSome_iff_exists.mp hactSome
  have hactτ : (τ0.gates g).act = some a := by
    simpa [τ0] using hact
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .gateBusy τ0 := by
    apply gateCallExec_active c τ0
      (Handle.decode ((Hw.readReg E Hw.rs1E).eval σ)).slot
      (Handle.decode ((Hw.readReg E Hw.rs1E).eval σ)).gen e g a
    · exact hcapLive
    · exact hkind
    · exact hactτ
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.gateBusy.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle),
      ((Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))), .err .badCap)]
    (List.drop 3 (Hw.callChecks E))
    (Hw.muxFin (fun g => .reg 1 (Hw.gactV g)) (Hw.callGid E)) .gateBusy
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hpassLive
    · simpa [E] using hprimary
  · simpa [E] using hactive
  · simpa [τ0, W] using hspec

/-- Complete fourth ladder arm.  After selecting an idle gate, a call back
into the issuing domain retires with `gateBusy`. -/
theorem square_retire_gateCall_self (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hself : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 := by
    exact specReg_bridge m σ E _
  have hword : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg, hR1]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  obtain ⟨S, G, e, g, hcapLive, hkind, hgid⟩ :=
    callPrimary_of_pass σ τ0 E c rfl hword hbridge hkc
      (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hact : ((Hw.abs σ).gates g).act = none := by
    cases ha : ((Hw.abs σ).gates g).act with
    | none => rfl
    | some a =>
        exfalso
        apply hidle
        apply (callGateActive_eval σ E g hgid).mpr
        simp [ha]
  have hactτ : (τ0.gates g).act = none := by
    simpa [τ0] using hact
  let cal : DomainId := ((Hw.abs σ).gates g).config.callee
  have hcalSel : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal E).eval σ) = cal :=
    callCal_eval_selected σ E g hgid
  have hcalE : cal = E :=
    (callSameCallee_eval σ E cal hcalSel).mp (by simpa [E] using hself)
  have hcalτ : (τ0.gates g).config.callee = c.d := by
    simpa [τ0, c, cal] using hcalE
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .gateBusy τ0 :=
    gateCallExec_self c τ0 S G e g hcapLive hkind hactτ hcalτ
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.gateBusy.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle),
      ((Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))), .err .badCap),
      ((Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.callGid E)), .err .gateBusy)]
    (List.drop 4 (Hw.callChecks E))
    (Expr.eq (Hw.callCal E) (Hw.dLit E)) .gateBusy
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hpassLive
    · simpa [E] using hprimary
    · simpa [E] using hidle
  · simpa [E] using hself
  · simpa [τ0, W] using hspec

/-- Complete fifth ladder arm.  An idle, non-self gate whose callee is not
running retires with `gateBusy`. -/
theorem square_retire_gateCall_notRunning (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotRunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hword : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg, hR1]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal,
      hne, hgid, hcalSel⟩ :=
    callCallee_of_pass σ τ0 E c rfl hgates hp
      (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunAbs : ((Hw.abs σ).doms cal).run ≠ .running :=
    (callCalleeNotRunning_eval σ E cal (hrc cal) hcalSel).mp
      (by simpa [E] using hnotRunning)
  have hcalNE : cal ≠ E := by simpa [c] using hne
  have hrunEq : (τ0.doms cal).run = ((Hw.abs σ).doms cal).run := by
    simp [τ0, MachineState.setDom, Loom.Fun.update, hcalNE]
  have hrun : (τ0.doms cal).run ≠ .running := by
    rw [hrunEq]
    exact hrunAbs
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .gateBusy τ0 :=
    gateCallExec_calleeNotRunning c τ0 S G e g cal hcapLive hkind
      hact hcal hne hrun
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.gateBusy.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle),
      ((Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))), .err .badCap),
      ((Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.callGid E)), .err .gateBusy),
      ((Expr.eq (Hw.callCal E) (Hw.dLit E)), .err .gateBusy)]
    (List.drop 5 (Hw.callChecks E))
    (Hw.neqE (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
      (Hw.callCal E)) (.lit 0)) .gateBusy
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hpassLive
    · simpa [E] using hprimary
    · simpa [E] using hidle
    · simpa [E] using hnotSelf
  · simpa [E] using hnotRunning
  · simpa [τ0, W] using hspec

/-- Complete sixth ladder arm.  A running callee that is already serving an
activation retires with `gateBusy`. -/
theorem square_retire_gateCall_serving (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ ≠ 1#1)
    (hserving : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hword : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg, hR1]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal,
      hne, hgid, hcalSel⟩ :=
    callCallee_of_pass σ τ0 E c rfl hgates hp
      (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunAbs : ((Hw.abs σ).doms cal).run = .running := by
    by_contra hn
    exact hrunning ((callCalleeNotRunning_eval σ E cal (hrc cal)
      hcalSel).mpr hn)
  have hcalNE : cal ≠ E := by simpa [c] using hne
  have hrunEq : (τ0.doms cal).run = ((Hw.abs σ).doms cal).run := by
    simp [τ0, MachineState.setDom, Loom.Fun.update, hcalNE]
  have hrun : (τ0.doms cal).run = .running := hrunEq.trans hrunAbs
  have hservSome := (callCalleeServing_eval σ E cal hcalSel).mp
    (by simpa [E] using hserving)
  obtain ⟨served, hservAbs⟩ := Option.isSome_iff_exists.mp hservSome
  have hservEq : (τ0.doms cal).serving =
      ((Hw.abs σ).doms cal).serving := by
    simp [τ0, MachineState.setDom, Loom.Fun.update, hcalNE]
  have hserv : (τ0.doms cal).serving = some served :=
    hservEq.trans hservAbs
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .gateBusy τ0 :=
    gateCallExec_calleeServing c τ0 S G e g cal served hcapLive hkind
      hact hcal hne hrun hserv
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.gateBusy.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle),
      ((Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))), .err .badCap),
      ((Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.callGid E)), .err .gateBusy),
      ((Expr.eq (Hw.callCal E) (Hw.dLit E)), .err .gateBusy),
      ((Hw.neqE (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal E)) (.lit 0)), .err .gateBusy)]
    (List.drop 6 (Hw.callChecks E))
    (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal E)) .gateBusy
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hpassLive
    · simpa [E] using hprimary
    · simpa [E] using hidle
    · simpa [E] using hnotSelf
    · simpa [E] using hrunning
  · simpa [E] using hserving
  · simpa [τ0, W] using hspec

/-- Complete seventh ladder arm.  A call whose activation chain would exceed
the global depth bound retires with `gateBusy`. -/
theorem square_retire_gateCall_depthOverflow (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ ≠ 1#1)
    (hnotServing : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hoverflow : (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hword : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg, hR1]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal,
      hne, hgid, hcalSel⟩ :=
    callCallee_of_pass σ τ0 E c rfl hgates hp
      (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunAbs : ((Hw.abs σ).doms cal).run = .running := by
    by_contra hn
    exact hrunning ((callCalleeNotRunning_eval σ E cal (hrc cal)
      hcalSel).mpr hn)
  have hcalNE : cal ≠ E := by simpa [c] using hne
  have hrunEq : (τ0.doms cal).run = ((Hw.abs σ).doms cal).run := by
    simp [τ0, MachineState.setDom, Loom.Fun.update, hcalNE]
  have hrun : (τ0.doms cal).run = .running := hrunEq.trans hrunAbs
  have hservAbs : ((Hw.abs σ).doms cal).serving = none := by
    cases hs : ((Hw.abs σ).doms cal).serving with
    | none => rfl
    | some served =>
        exfalso
        apply hnotServing
        apply (callCalleeServing_eval σ E cal hcalSel).mpr
        simp [hs]
  have hservEq : (τ0.doms cal).serving =
      ((Hw.abs σ).doms cal).serving := by
    simp [τ0, MachineState.setDom, Loom.Fun.update, hcalNE]
  have hserv : (τ0.doms cal).serving = none := hservEq.trans hservAbs
  have hwfAbs : Wf (Hw.abs σ) :=
    (Machines.Lnp64u.wfa_invariant m hwf (Hw.abs σ) hsr).1
  have hdepthAbs : ¬Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) ≤
      maxChainDepth :=
    (callDepthOverflow_eval σ c hwfAbs).mp (by simpa [c, E] using hoverflow)
  have hservCaller : (τ0.doms c.d).serving =
      ((Hw.abs σ).doms c.d).serving := by
    simp [τ0, c, MachineState.setDom, Loom.Fun.update]
  have hdepthEq : Machines.Lnp64u.Isa.Wip.gateDepth c τ0 =
      Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) := by
    unfold Machines.Lnp64u.Isa.Wip.gateDepth
    rw [hservCaller, hgates]
  have hdepth : ¬Machines.Lnp64u.Isa.Wip.gateDepth c τ0 ≤
      maxChainDepth := by
    rw [hdepthEq]
    exact hdepthAbs
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .gateBusy τ0 :=
    gateCallExec_depthOverflow c τ0 S G e g cal hcapLive hkind hact
      hcal hne hrun hserv hdepth
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.gateBusy.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle),
      ((Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))), .err .badCap),
      ((Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.callGid E)), .err .gateBusy),
      ((Expr.eq (Hw.callCal E) (Hw.dLit E)), .err .gateBusy),
      ((Hw.neqE (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal E)) (.lit 0)), .err .gateBusy),
      ((Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
        (Hw.callCal E)), .err .gateBusy)]
    (List.drop 7 (Hw.callChecks E))
    (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth E)) .gateBusy
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpassLive
    · simpa [E] using hprimary
    · simpa [E] using hidle
    · simpa [E] using hnotSelf
    · simpa [E] using hrunning
    · simpa [E] using hnotServing
  · simpa [E] using hoverflow
  · simpa [τ0, W] using hspec

/-- Complete eighth ladder arm.  Once the gate and callee are ready, a
non-null stale argument handle is returned unchanged as `staleHandle`. -/
theorem square_retire_gateCall_argStale (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ ≠ 1#1)
    (hnotServing : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hdepthPass : (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hargStale : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.argSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).live)).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  have hreg1 : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hreg2 : (τ0.doms E).reg (operandsOf W).rs2 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    specReg_bridge m σ E _
  have hword1 : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg1, hR1]
  have hword2 : (τ0.doms c.d).reg c.op.rs2 =
      (Hw.argW E).eval σ := by
    simp only [c, Hw.argW]
    rw [hreg2, hR2]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword1 hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  have hcallee := callCallee_of_pass σ τ0 E c rfl hgates hp
    (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunBridge : ∀ x : DomainId,
      (τ0.doms x).run = ((Hw.abs σ).doms x).run := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, MachineState.setDom, Loom.Fun.update, hx]
  have hservBridge : ∀ x : DomainId,
      (τ0.doms x).serving = ((Hw.abs σ).doms x).serving := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, MachineState.setDom, Loom.Fun.update, hx]
  have hwfAbs : Wf (Hw.abs σ) :=
    (Machines.Lnp64u.wfa_invariant m hwf (Hw.abs σ) hsr).1
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal, hne,
      hrun, hserv, hdepth, hgid, hcalSel⟩ :=
    callReady_of_pass σ τ0 E c rfl hwfAbs hrc hrunBridge hservBridge
      hgates hcallee (by simpa [E] using hrunning)
      (by simpa [E] using hnotServing) (by simpa [E] using hdepthPass)
  have hargLogic : (Hw.argNZ E).eval σ = 1#1 ∧
      (Hw.argSel E).live.eval σ = 0#1 := by
    apply (by decide : ∀ a b : BitVec 1,
      a &&& ~~~b = 1#1 → a = 1#1 ∧ b = 0#1)
    simpa [E] using hargStale
  have hnz : (Hw.argW E).eval σ ≠ 0#32 :=
    (argNZ_eval_iff σ E).mp hargLogic.1
  let AS : Slot := finOfBv (by decide)
    (((Hw.argW E).eval σ).extractLsb' 0 4)
  have hraw : ¬(σ.regs (Hw.dcapV E AS) 1 = 1#1 ∧
      σ.regs (Hw.dgen E AS) 8 = ((Hw.argW E).eval σ).extractLsb' 4 8 ∧
      ((Hw.argW E).eval σ).extractLsb' 4 8 ≠ 0) := by
    intro hr
    have hsel := (capSel_live_eval σ E (Hw.argW E) AS rfl).mpr hr
    have : (Hw.argSel E).live.eval σ = 1#1 := by
      simpa [Hw.argSel] using hsel
    rw [hargLogic.2] at this
    exact absurd this (by decide)
  have hnone : (τ0.doms E).liveCap
      (Handle.decode ((Hw.argW E).eval σ)).slot
      (Handle.decode ((Hw.argW E).eval σ)).gen = none := by
    rw [hbridge, abs_liveCap]
    exact if_neg hraw
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ0.doms c.d).reg c.op.rs2) τ0 = .err .staleHandle τ0 := by
    rw [hword2]
    exact transferByHandle_stale τ0 E cal ((Hw.argW E).eval σ) hnz hnone
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .staleHandle τ0 :=
    gateCallExec_transferErr c τ0 S G e g cal .staleHandle hcapLive
      hkind hact hcal hne hrun hserv hdepth htransfer
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.staleHandle.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle),
      ((Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))), .err .badCap),
      ((Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.callGid E)), .err .gateBusy),
      ((Expr.eq (Hw.callCal E) (Hw.dLit E)), .err .gateBusy),
      ((Hw.neqE (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal E)) (.lit 0)), .err .gateBusy),
      ((Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
        (Hw.callCal E)), .err .gateBusy),
      ((Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
        (Hw.callDepth E)), .err .gateBusy)]
    (List.drop 8 (Hw.callChecks E))
    (Expr.and (Hw.argNZ E) (Expr.not (Hw.argSel E).live)) .staleHandle
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpassLive
    · simpa [E] using hprimary
    · simpa [E] using hidle
    · simpa [E] using hnotSelf
    · simpa [E] using hrunning
    · simpa [E] using hnotServing
    · simpa [E] using hdepthPass
  · simpa [E] using hargStale
  · simpa [τ0, W] using hspec

/-- Complete ninth ladder arm.  A live non-null argument handle whose class
bit disagrees with its capability entry retires with `badCap`. -/
theorem square_retire_gateCall_argBadClass (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ ≠ 1#1)
    (hnotServing : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hdepthPass : (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hargLive : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.argSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).live)).eval σ ≠ 1#1)
    (hargBad : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.argSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk)).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  have hreg1 : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hreg2 : (τ0.doms E).reg (operandsOf W).rs2 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    specReg_bridge m σ E _
  have hword1 : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg1, hR1]
  have hword2 : (τ0.doms c.d).reg c.op.rs2 =
      (Hw.argW E).eval σ := by
    simp only [c, Hw.argW]
    rw [hreg2, hR2]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword1 hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  have hcallee := callCallee_of_pass σ τ0 E c rfl hgates hp
    (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunBridge : ∀ x : DomainId,
      (τ0.doms x).run = ((Hw.abs σ).doms x).run := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, MachineState.setDom, Loom.Fun.update, hx]
  have hservBridge : ∀ x : DomainId,
      (τ0.doms x).serving = ((Hw.abs σ).doms x).serving := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, MachineState.setDom, Loom.Fun.update, hx]
  have hwfAbs : Wf (Hw.abs σ) :=
    (Machines.Lnp64u.wfa_invariant m hwf (Hw.abs σ) hsr).1
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal, hne,
      hrun, hserv, hdepth, hgid, hcalSel⟩ :=
    callReady_of_pass σ τ0 E c rfl hwfAbs hrc hrunBridge hservBridge
      hgates hcallee (by simpa [E] using hrunning)
      (by simpa [E] using hnotServing) (by simpa [E] using hdepthPass)
  have hargLogic : (Hw.argNZ E).eval σ = 1#1 ∧
      (Hw.argSel E).clsOk.eval σ = 0#1 := by
    apply (by decide : ∀ a b : BitVec 1,
      a &&& ~~~b = 1#1 → a = 1#1 ∧ b = 0#1)
    simpa [E] using hargBad
  have hargLive1 : (Hw.argSel E).live.eval σ = 1#1 := by
    exact (by decide : ∀ a b : BitVec 1,
      a = 1#1 → a &&& ~~~b ≠ 1#1 → b = 1#1)
      ((Hw.argNZ E).eval σ) ((Hw.argSel E).live.eval σ) hargLogic.1
      (by simpa [E] using hargLive)
  have hnz : (Hw.argW E).eval σ ≠ 0#32 :=
    (argNZ_eval_iff σ E).mp hargLogic.1
  obtain ⟨ae, alive, acap⟩ := capSel_entry_of_live σ τ0 E
    (Hw.argW E) hbridge (by simpa [Hw.argSel] using hargLive1)
  have aslot : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.argW E).eval σ).extractLsb' 0 4)).val =
      (((Hw.argW E).eval σ).extractLsb' 0 4).toNat := rfl
  have aclsIff := capSel_clsOk_iff_some σ E (Hw.argW E)
    (finOfBv (by decide) (((Hw.argW E).eval σ).extractLsb' 0 4))
    ae hkc aslot acap
  have aclsNe : (Handle.decode ((Hw.argW E).eval σ)).cls ≠ ae.kind.cls := by
    intro heq
    have hone := aclsIff.mpr heq
    have hzero : (Hw.capSel E (Hw.argW E)).clsOk.eval σ = 0#1 := by
      simpa [Hw.argSel] using hargLogic.2
    rw [hzero] at hone
    exact absurd hone (by decide)
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ0.doms c.d).reg c.op.rs2) τ0 = .err .badCap τ0 := by
    rw [hword2]
    exact transferByHandle_badClass τ0 E cal ((Hw.argW E).eval σ)
      (Handle.decode ((Hw.argW E).eval σ)).slot
      (Handle.decode ((Hw.argW E).eval σ)).gen ae hnz rfl alive aclsNe
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .badCap τ0 :=
    gateCallExec_transferErr c τ0 S G e g cal .badCap hcapLive hkind
      hact hcal hne hrun hserv hdepth htransfer
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.badCap.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle),
      ((Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))), .err .badCap),
      ((Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.callGid E)), .err .gateBusy),
      ((Expr.eq (Hw.callCal E) (Hw.dLit E)), .err .gateBusy),
      ((Hw.neqE (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal E)) (.lit 0)), .err .gateBusy),
      ((Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
        (Hw.callCal E)), .err .gateBusy),
      ((Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
        (Hw.callDepth E)), .err .gateBusy),
      ((Expr.and (Hw.argNZ E)
        (Expr.not (Hw.argSel E).live)), .err .staleHandle)]
    (List.drop 9 (Hw.callChecks E))
    (Expr.and (Hw.argNZ E) (Expr.not (Hw.argSel E).clsOk)) .badCap
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpassLive
    · simpa [E] using hprimary
    · simpa [E] using hidle
    · simpa [E] using hnotSelf
    · simpa [E] using hrunning
    · simpa [E] using hnotServing
    · simpa [E] using hdepthPass
    · simpa [E] using hargLive
  · simpa [E] using hargBad
  · simpa [τ0, W] using hspec

/-- Complete tenth ladder arm.  A live, class-correct non-null argument that
cannot be placed in the callee retires with `slotOccupied`. -/
theorem square_retire_gateCall_argBlocked (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ ≠ 1#1)
    (hnotServing : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hdepthPass : (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hargLive : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.argSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).live)).eval σ ≠ 1#1)
    (hargClass : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.argSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk)).eval σ ≠ 1#1)
    (hblocked : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.transferBlocked
        (finOfBv (by decide) (σ.regs "if_dom" 2))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
        (Hw.argSel
          (finOfBv (by decide) (σ.regs "if_dom" 2))))).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let c : Ctx :=
    { d := E
      pc := (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      op := operandsOf W }
  let τ0 : MachineState :=
    ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  have hreg1 : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hreg2 : (τ0.doms E).reg (operandsOf W).rs2 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    specReg_bridge m σ E _
  have hword1 : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg1, hR1]
  have hword2 : (τ0.doms c.d).reg c.op.rs2 =
      (Hw.argW E).eval σ := by
    simp only [c, Hw.argW]
    rw [hreg2, hR2]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword1 hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  have hcallee := callCallee_of_pass σ τ0 E c rfl hgates hp
    (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunBridge : ∀ x : DomainId,
      (τ0.doms x).run = ((Hw.abs σ).doms x).run := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, MachineState.setDom, Loom.Fun.update, hx]
  have hservBridge : ∀ x : DomainId,
      (τ0.doms x).serving = ((Hw.abs σ).doms x).serving := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, MachineState.setDom, Loom.Fun.update, hx]
  have hwfAbs : Wf (Hw.abs σ) :=
    (Machines.Lnp64u.wfa_invariant m hwf (Hw.abs σ) hsr).1
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal, hne,
      hrun, hserv, hdepth, hgid, hcalSel⟩ :=
    callReady_of_pass σ τ0 E c rfl hwfAbs hrc hrunBridge hservBridge
      hgates hcallee (by simpa [E] using hrunning)
      (by simpa [E] using hnotServing) (by simpa [E] using hdepthPass)
  have hargLogic : (Hw.argNZ E).eval σ = 1#1 ∧
      (Hw.transferBlocked E (Hw.callCal E) (Hw.argSel E)).eval σ = 1#1 := by
    apply (by decide : ∀ a b : BitVec 1,
      a &&& b = 1#1 → a = 1#1 ∧ b = 1#1)
    simpa [E] using hblocked
  have hargLive1 : (Hw.argSel E).live.eval σ = 1#1 := by
    exact (by decide : ∀ a b : BitVec 1,
      a = 1#1 → a &&& ~~~b ≠ 1#1 → b = 1#1)
      ((Hw.argNZ E).eval σ) ((Hw.argSel E).live.eval σ) hargLogic.1
      (by simpa [E] using hargLive)
  have hargCls1 : (Hw.argSel E).clsOk.eval σ = 1#1 := by
    exact (by decide : ∀ a b : BitVec 1,
      a = 1#1 → a &&& ~~~b ≠ 1#1 → b = 1#1)
      ((Hw.argNZ E).eval σ) ((Hw.argSel E).clsOk.eval σ) hargLogic.1
      (by simpa [E] using hargClass)
  have hnz : (Hw.argW E).eval σ ≠ 0#32 :=
    (argNZ_eval_iff σ E).mp hargLogic.1
  obtain ⟨ae, alive, acap⟩ := capSel_entry_of_live σ τ0 E
    (Hw.argW E) hbridge (by simpa [Hw.argSel] using hargLive1)
  let AS : Slot := (Handle.decode ((Hw.argW E).eval σ)).slot
  let AG : Gen := (Handle.decode ((Hw.argW E).eval σ)).gen
  have aslotNat : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.argW E).eval σ).extractLsb' 0 4)).val =
      (((Hw.argW E).eval σ).extractLsb' 0 4).toNat := rfl
  have aclsIff := capSel_clsOk_iff_some σ E (Hw.argW E)
    (finOfBv (by decide) (((Hw.argW E).eval σ).extractLsb' 0 4))
    ae hkc aslotNat acap
  have acls : (Handle.decode ((Hw.argW E).eval σ)).cls = ae.kind.cls :=
    aclsIff.mp (by simpa [Hw.argSel] using hargCls1)
  have aslotE : (Hw.capSel E (Hw.argW E)).slot.eval σ =
      BitVec.ofNat 4 AS.val := by
    exact (bv4_slot_iff _ AS).mpr rfl
  have hsource : (τ0.doms E).caps AS = some ae := by
    change (τ0.doms E).liveCap AS AG = some ae at alive
    unfold DomainState.liveCap at alive
    cases hc : (τ0.doms E).caps AS with
    | none => simp [hc] at alive
    | some ae' =>
        rw [hc] at alive
        change (if (decide ((τ0.doms E).slotGen AS = AG) && AG != 0) = true
          then some ae' else none) = some ae at alive
        by_cases hg : (decide ((τ0.doms E).slotGen AS = AG) && AG != 0) = true
        · rw [if_pos hg] at alive
          have heq : ae' = ae := Option.some.inj alive
          rw [← heq]
        · rw [if_neg hg] at alive
          exact nomatch alive
  have hlineage : ∀ L : LineageId,
      (τ0.doms E).lineage L = ((Hw.abs σ).doms E).lineage L := by
    intro L
    simp [τ0, MachineState.setDom, Loom.Fun.update]
  have hcalNE : cal ≠ E := by simpa [c] using hne
  have hfreeSlot : τ0.freeSlot cal = (Hw.abs σ).freeSlot cal := by
    unfold MachineState.freeSlot
    simp [τ0, MachineState.setDom, Loom.Fun.update, hcalNE]
  have hfreeCell : τ0.freeCell cal = (Hw.abs σ).freeCell cal := by
    unfold MachineState.freeCell
    simp [τ0, MachineState.setDom, Loom.Fun.update, hcalNE]
  have htransferNone : τ0.transferCap E AS cal = none :=
    transferCap_none_of_blocked σ τ0 E cal (Hw.callCal E) (Hw.argW E)
      AS ae hcalSel aslotE acap hsource hlineage hfreeSlot hfreeCell
      hwfAbs (by simpa [Hw.argSel] using hargLogic.2)
  have hargCapLive : Machines.Lnp64u.Isa.capLive E
      ((Hw.argW E).eval σ) τ0 = .ok (AS, AG, ae) τ0 := by
    apply capLive_eq_selected
    · cases hd : Handle.decode ((Hw.argW E).eval σ) with
      | mk S' G' cls =>
          simp only [AS, AG, hd] at acls ⊢
          rw [acls]
    · simpa [AS, AG] using alive
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ0.doms c.d).reg c.op.rs2) τ0 = .err .slotOccupied τ0 := by
    rw [hword2]
    exact transferByHandle_slotOccupied τ0 E cal ((Hw.argW E).eval σ)
      AS AG ae hnz hargCapLive htransferNone
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .err .slotOccupied τ0 :=
    gateCallExec_transferErr c τ0 S G e g cal .slotOccupied hcapLive
      hkind hact hcal hne hrun hserv hdepth htransfer
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E (fun ds =>
        ds.setReg (operandsOf W).rd Errno.slotOccupied.toWord) := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith
          { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
    rw [hexec]
  have hpassLive : (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 := by
    show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
    rw [show (Hw.callSel E).live.eval σ = 1#1 from by simpa [E] using hlive]
    decide
  apply square_retire_gateCall_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc
    [((Expr.not (Hw.callSel E).live), .err .staleHandle),
      ((Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))), .err .badCap),
      ((Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.callGid E)), .err .gateBusy),
      ((Expr.eq (Hw.callCal E) (Hw.dLit E)), .err .gateBusy),
      ((Hw.neqE (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal E)) (.lit 0)), .err .gateBusy),
      ((Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
        (Hw.callCal E)), .err .gateBusy),
      ((Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
        (Hw.callDepth E)), .err .gateBusy),
      ((Expr.and (Hw.argNZ E)
        (Expr.not (Hw.argSel E).live)), .err .staleHandle),
      ((Expr.and (Hw.argNZ E)
        (Expr.not (Hw.argSel E).clsOk)), .err .badCap)]
    []
    (Expr.and (Hw.argNZ E)
      (Hw.transferBlocked E (Hw.callCal E) (Hw.argSel E))) .slotOccupied
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpassLive
    · simpa [E] using hprimary
    · simpa [E] using hidle
    · simpa [E] using hnotSelf
    · simpa [E] using hrunning
    · simpa [E] using hnotServing
    · simpa [E] using hdepthPass
    · simpa [E] using hargLive
    · simpa [E] using hargClass
  · simpa [E] using hblocked
  · simpa [τ0, W] using hspec

end Machines.Lnp64u.Theorems.RMC
