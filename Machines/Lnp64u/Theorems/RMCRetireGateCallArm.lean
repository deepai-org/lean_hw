-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCall

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
  have hok0 : (Hw.callOkE E).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro hok
    have hp := (okOf_eval_iff σ (Hw.callChecks E)).mp hok
      ((Expr.not (Hw.callSel E).live), .err .staleHandle)
      (by simp [Hw.callChecks])
    exact hp hfail
  have hcoreX : ∀ acc, (Hw.retireFor E).run σ acc =
      (Act.seq (Hw.pcAdvA E)
        (Hw.writeReg E Hw.rdE (.lit Errno.staleHandle.toWord))).run σ acc := by
    intro acc
    apply retireFor_gateCall_first_error σ acc E []
      (Hw.callChecks E).tail (Expr.not (Hw.callSel E).live)
      .staleHandle hopc
    · rfl
    · intro x hx
      simp at hx
    · exact hfail
  apply square_retire_gateCall_error m hwf hfit σ hsync hifv hcl E rfl
    hifsel hifexcl hopc hok0 Errno.staleHandle.toWord hcoreX
  simpa [τ0, W] using hspec

end Machines.Lnp64u.Theorems.RMC
