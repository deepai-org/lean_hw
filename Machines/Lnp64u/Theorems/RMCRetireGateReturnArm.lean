-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateReturn

/-!
# R-MC retirement: gate_return failure arms

Full-cycle assembly for the protocol-fault and reply-transfer errno branches
of `gate_return`.  Successful return assembly remains in
`RMCRetireGateReturnSuccess`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- Opcode 23 selects the return circuit's complete memory-port triple. -/
theorem retireMem_gateReturn_sel (σ : Loom.Hw.St) (E : DomainId)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6) :
    ((((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))).1).eval σ
      = (Hw.retCirc E).memEn.eval σ)
    ∧ ((Hw.retCirc E).memEn.eval σ = 1#1 →
        ((((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
            (.lit 0 : Expr 32))).2.1).eval σ = (Hw.retCirc E).memAddr.eval σ)
        ∧ ((((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
            (.lit 0 : Expr 32))).2.2).eval σ = (Hw.retCirc E).memData.eval σ)) := by
  have hmn : (Hw.isMn "gate_return").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_return" = 23#6).symm
  have hmem : ("gate_return", Hw.retCirc E) ∈ Hw.opCircs E := by
    simp [Hw.opCircs]
  have hnd : ((Hw.opCircs E).map Prod.fst).Nodup := by
    rw [opCircs_fst_all E]
    exact allMns_nodup
  have hq : ∀ p ∈ Hw.opCircs E, p.1 ≠ "gate_return" →
      (Hw.isMn p.1).eval σ = 0#1 ∨ isLit0 p.2.memEn = true := by
    intro p hp hne
    left
    exact bv1_ne_one.mp (isMn_ne_of_opc σ p.1 23#6 hopc
      ((by decide +kernel : ∀ mn' ∈ allMns, mn' ≠ "gate_return" →
        (23#6 : BitVec 6) ≠ Hw.opcodeOf mn') p.1
        (by rw [← opCircs_fst_all E]; exact List.mem_map_of_mem hp) hne))
  exact retireMem_op_sel σ E "gate_return" (Hw.retCirc E) hifsel hifexcl
    hmn hmem hnd hq

/-- A failed return disables its sweep-memory port, so core retirement leaves
the memory array unchanged. -/
theorem coreAct_mem_gateReturn_failed (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hok0 : (Hw.retOkE E).eval σ = 0#1) (ad : Nat) :
    ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
      ad 32 = σ.mems "mem" ad 32 := by
  have hport := retireMem_gateReturn_sel σ E hifsel hifexcl hopc
  rw [coreAct_run_retire_eq m σ _ hifv hcl,
    retireAct_run_mems σ _ ad 32]
  show (if (((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1,
          .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
        (.lit 0 : Expr 32))).1).eval σ = 1#1 then _
    else ((Hw.refillAct m).run σ σ)).mems "mem" ad 32 = _
  rw [if_neg (by
    rw [hport.1]
    show ¬((Hw.retCirc E).memEn.eval σ = 1#1)
    unfold Hw.retCirc Hw.sweepMem Hw.andAll
    change ¬((Hw.retOkE E).eval σ &&& _ = 1#1)
    rw [hok0]
    exact (by decide : ∀ x : BitVec 1, ¬(0#1 &&& x = 1#1)) _)]
  rw [refill_pres_mem m σ "mem" ad 32]

/-- Common full-cycle square for every return errno branch. -/
theorem square_retire_gateReturn_error (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (E : DomainId)
    (hEval : E.val = (σ.regs "if_dom" 2).toNat)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hok0 : (Hw.retOkE E).eval σ = 0#1)
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
  have hmn : (Hw.isMn "gate_return").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_return" = 23#6).symm
  have hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_drop" 23#6 hopc (by decide +kernel)
  have hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_revoke" 23#6 hopc (by decide +kernel)
  have hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_call" 23#6 hopc (by decide +kernel)
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1 := by
    intro d
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 23#6 hopc (by decide +kernel)
  have hbad : ∀ d : DomainId, d = E → (Hw.retOkE d).eval σ = 0#1 := by
    intro d hd
    simpa [hd] using hok0
  have hin : Inert σ := Inert.of_failed_gateReturn σ E hret hif hdrop hrev
    hcall hmn hbad hnew
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 23#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 23#6 hopc (by decide +kernel))
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
      (isMn_ne_of_opc σ "sw" 23#6 hopc (by decide +kernel))
  have hcoremem : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = σ.mems "mem" b.toNat 32 :=
    fun b => coreAct_mem_gateReturn_failed m σ E hifv hcl hifsel hifexcl
      hopc hok0 b.toNat
  exact retire_err_common_mem m hwf hfit σ hsync hifv hcl hin hmapz
    hunmapz hswz hcoremem E hEval errw hcoreX hspecE

/-- Turn the first failing return errno check into the full-cycle square. -/
theorem square_retire_gateReturn_firstError (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (E : DomainId)
    (hEval : E.val = (σ.regs "if_dom" 2).toNat)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (pre post : List Hw.Check) (cond : Expr 1) (er : Errno)
    (hchecks : Hw.retChecks E = pre ++ (cond, .err er) :: post)
    (hpre : ∀ x ∈ pre, x.1.eval σ ≠ 1#1)
    (hfail : cond.eval σ = 1#1)
    (hspecE : corePhase m (refillPhase m (Hw.abs σ)) =
      (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).setDom E
          (fun ds => ds.setReg
            (operandsOf (σ.regs "if_word" 32)).rd er.toWord)) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hok0 : (Hw.retOkE E).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro hok
    have hall := (okOf_eval_iff σ (Hw.retChecks E)).mp hok
    have hmem : (cond, .err er) ∈ Hw.retChecks E := by
      rw [hchecks]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    exact hall (cond, .err er) hmem hfail
  have hcoreX : ∀ acc, (Hw.retireFor E).run σ acc =
      (Act.seq (Hw.pcAdvA E)
        (Hw.writeReg E Hw.rdE (.lit er.toWord))).run σ acc := by
    intro acc
    exact retireFor_gateReturn_first_failure σ acc E pre post cond (.err er)
      hopc hchecks hpre hfail
  exact square_retire_gateReturn_error m hwf hfit σ hsync hifv hcl E hEval
    hifsel hifexcl hopc hok0 er.toWord hcoreX hspecE

/-- Turn the first failing return fault check into the full-cycle square. -/
theorem square_retire_gateReturn_firstFault (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (E : DomainId)
    (hEval : E.val = (σ.regs "if_dom" 2).toNat)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (pre post : List Hw.Check) (cond : Expr 1) (f : Fault)
    (hchecks : Hw.retChecks E = pre ++ (cond, .fault f) :: post)
    (hpre : ∀ x ∈ pre, x.1.eval σ ≠ 1#1)
    (hfail : cond.eval σ = 1#1)
    (hspecF : retire { refillPhase m (Hw.abs σ) with inflight := none } E
      (σ.regs "if_word" 32) =
        haltWith { refillPhase m (Hw.abs σ) with inflight := none } E f) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hok0 : (Hw.retOkE E).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro hok
    have hall := (okOf_eval_iff σ (Hw.retChecks E)).mp hok
    have hmem : (cond, .fault f) ∈ Hw.retChecks E := by
      rw [hchecks]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    exact hall (cond, .fault f) hmem hfail
  have hret := retiringE_one σ hifv hcl
  have hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1 := by
    intro d
    by_cases hd : d = E
    · subst d
      rw [if_pos rfl]
      exact hifsel
    · rw [if_neg hd, bv1_ne_one.mp (hifexcl d hd)]
  have hmn : (Hw.isMn "gate_return").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_return" = 23#6).symm
  have hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_drop" 23#6 hopc (by decide +kernel)
  have hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_revoke" 23#6 hopc (by decide +kernel)
  have hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_call" 23#6 hopc (by decide +kernel)
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1 := by
    intro d
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 23#6 hopc (by decide +kernel)
  have hbad : ∀ d : DomainId, d = E → (Hw.retOkE d).eval σ = 0#1 := by
    intro d hd
    simpa [hd] using hok0
  have hin : Inert σ := Inert.of_failed_gateReturn σ E hret hif hdrop hrev
    hcall hmn hbad hnew
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 23#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 23#6 hopc (by decide +kernel))
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
      (isMn_ne_of_opc σ "sw" 23#6 hopc (by decide +kernel))
  have hcoremem : ∀ ad : Nat,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        ad 32 = σ.mems "mem" ad 32 :=
    coreAct_mem_gateReturn_failed m σ E hifv hcl hifsel hifexcl hopc hok0
  have hcoreF : ∀ acc, (Hw.retireFor E).run σ acc =
      (Hw.haltFault E f).run σ acc := by
    intro acc
    have h := retireFor_gateReturn_first_failure σ acc E pre post cond
      (.fault f) hopc hchecks hpre hfail
    simpa [Hw.respA] using h
  exact square_retire_fault_of m hwf hfit σ hsync hifv hcl hin hswz hmapz
    hunmapz hcoremem E hEval f hcoreF hspecF

/-- Complete first ladder arm: a return outside any serving activation
retires as a protocol fault. -/
theorem square_retire_gateReturn_notServing (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hnotServing : σ.regs (Hw.dsrvV
      (finOfBv (by decide) (σ.regs "if_dom" 2))) 1 ≠ 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (23#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (23#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  have hservAbs : ((Hw.abs σ).doms E).serving = none := by
    change (if σ.regs (Hw.dsrvV E) 1 = 1#1 then some _ else none) = none
    rw [if_neg (by simpa [E] using hnotServing)]
  have hservBase : (base.doms E).serving = none := by
    simp [base, refillPhase_serving, hservAbs]
  have hspecF : retire base E W = haltWith base E .protocol := by
    rw [retire_gateReturn_exec base E W hdec]
    dsimp only
    rw [gateReturnExec_notServing]
    simp [MachineState.setDom, Loom.Fun.update, hservBase]
  have hfail : (Expr.not (.reg 1 (Hw.dsrvV E))).eval σ = 1#1 := by
    exact (notE_eval _ σ).mpr
      (bv1_ne_one.mp (by simpa [E] using hnotServing))
  apply square_retire_gateReturn_firstFault m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc [] (Hw.retChecks E).tail
    (.not (.reg 1 (Hw.dsrvV E))) .protocol
  · rfl
  · intro x hx
    contradiction
  · exact hfail
  · exact hspecF

end Machines.Lnp64u.Theorems.RMC
