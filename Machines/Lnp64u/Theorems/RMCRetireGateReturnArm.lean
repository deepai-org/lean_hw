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

/-- Complete second ladder arm: a serving tag that selects an inactive gate
retires as a protocol fault. -/
theorem square_retire_gateReturn_inactive (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hserving : σ.regs (Hw.dsrvV
      (finOfBv (by decide) (σ.regs "if_dom" 2))) 1 = 1#1)
    (hinactive : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.retGid (finOfBv (by decide) (σ.regs "if_dom" 2)))).eval σ ≠ 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  set gid : GateId := finOfBv (by decide) ((Hw.retGid E).eval σ) with hgid
  have hop : Machines.Lnp64u.sig.opcodeOf W = (23#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (23#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hservingE : σ.regs (Hw.dsrvV E) 1 = 1#1 := by
    simpa [E] using hserving
  have hservAbs : ((Hw.abs σ).doms E).serving = some gid := by
    change (if σ.regs (Hw.dsrvV E) 1 = 1#1 then
      some (finOfBv (by decide) (σ.regs (Hw.dsrv E) 2)) else none) = some gid
    rw [if_pos hservingE]
    rfl
  have hinactiveE : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.retGid E)).eval σ ≠ 1#1 := by
    simpa [E] using hinactive
  have hgateV : σ.regs (Hw.gactV gid) 1 ≠ 1#1 := by
    rw [muxFin_eval (by decide : 2 ^ 2 = numGates), ← hgid] at hinactiveE
    exact hinactiveE
  have hactAbs : ((Hw.abs σ).gates gid).act = none := by
    change (if σ.regs (Hw.gactV gid) 1 = 1#1 then some _ else none) = none
    rw [if_neg hgateV]
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  have hservBase : (base.doms E).serving = some gid := by
    simp [base, refillPhase_serving, hservAbs]
  have hactBase : (base.gates gid).act = none := by
    simp [base, refillPhase_gates, hactAbs]
  have hspecF : retire base E W = haltWith base E .protocol := by
    rw [retire_gateReturn_exec base E W hdec]
    dsimp only
    let c : Ctx := { d := E, pc := (base.doms E).pc, op := operandsOf W }
    let τ0 := base.setDom E fun ds => { ds with pc := ds.pc + 1 }
    have hserv0 : (τ0.doms c.d).serving = some gid := by
      simp [τ0, c, MachineState.setDom, Loom.Fun.update, hservBase]
    have hact0 : (τ0.gates gid).act = none := by
      simp [τ0, MachineState.setDom, hactBase]
    rw [gateReturnExec_inactive c τ0 gid hserv0 hact0]
  let first : Hw.Check :=
    (.not (.reg 1 (Hw.dsrvV E)), .fault .protocol)
  have hpre : ∀ x ∈ [first], x.1.eval σ ≠ 1#1 := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    change (Expr.not (.reg 1 (Hw.dsrvV E))).eval σ ≠ 1#1
    simp [Expr.eval, hservingE]
  have hfail : (Expr.not (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.retGid E))).eval σ = 1#1 := by
    exact (notE_eval _ σ).mpr (bv1_ne_one.mp hinactiveE)
  apply square_retire_gateReturn_firstFault m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc [first] (List.drop 2 (Hw.retChecks E))
    (.not (Hw.muxFin (fun g => .reg 1 (Hw.gactV g)) (Hw.retGid E)))
    .protocol
  · rfl
  · exact hpre
  · exact hfail
  · exact hspecF

/-- Complete third ladder arm: a non-null stale reply handle returns
`staleHandle` without applying the restoration tail. -/
theorem square_retire_gateReturn_stale (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (gid : GateId) (act : Activation)
    (hserv : ((Hw.abs σ).doms
      (finOfBv (by decide) (σ.regs "if_dom" 2))).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hstale : (Expr.and
      (Hw.retNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.retSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).live)).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let c : Ctx := { d := E, pc := (base.doms E).pc, op := operandsOf W }
  let τ0 := base.setDom E fun ds => { ds with pc := ds.pc + 1 }
  have hop : Machines.Lnp64u.sig.opcodeOf W = (23#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (23#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) = retire base E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR : (Hw.retW E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    retW_eval σ hz E (operandsOf W).rs1 rfl
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hword : (τ0.doms c.d).reg c.op.rs1 = (Hw.retW E).eval σ := by
    simp only [c]
    rw [hreg, hR]
  have hlogic : (Hw.retNZ E).eval σ = 1#1 ∧
      (Hw.retSel E).live.eval σ = 0#1 := by
    apply (by decide : ∀ a b : BitVec 1,
      a &&& ~~~b = 1#1 → a = 1#1 ∧ b = 0#1)
    simpa [E] using hstale
  have hnz : (Hw.retW E).eval σ ≠ 0#32 :=
    (retNZ_eval_iff σ E).mp hlogic.1
  let S : Slot := finOfBv (by decide)
    (((Hw.retW E).eval σ).extractLsb' 0 4)
  have hraw : ¬(σ.regs (Hw.dcapV E S) 1 = 1#1 ∧
      σ.regs (Hw.dgen E S) 8 = ((Hw.retW E).eval σ).extractLsb' 4 8 ∧
      ((Hw.retW E).eval σ).extractLsb' 4 8 ≠ 0) := by
    intro hr
    have hsel := (capSel_live_eval σ E (Hw.retW E) S rfl).mpr hr
    have : (Hw.retSel E).live.eval σ = 1#1 := by
      simpa [Hw.retSel] using hsel
    rw [hlogic.2] at this
    contradiction
  have hnone : (τ0.doms E).liveCap
      (Handle.decode ((Hw.retW E).eval σ)).slot
      (Handle.decode ((Hw.retW E).eval σ)).gen = none := by
    rw [specLiveCap_bridge m σ E, abs_liveCap]
    exact if_neg hraw
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d act.caller
      ((τ0.doms c.d).reg c.op.rs1) τ0 = .err .staleHandle τ0 := by
    rw [hword]
    exact transferByHandle_stale τ0 E act.caller ((Hw.retW E).eval σ)
      hnz hnone
  have hserv0 : (τ0.doms c.d).serving = some gid := by
    simp [τ0, c, base, MachineState.setDom, Loom.Fun.update,
      refillPhase_serving, hserv]
  have hact0 : (τ0.gates gid).act = some act := by
    simp [τ0, base, MachineState.setDom, refillPhase_gates, hact]
  have hexec : Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 =
      .err .staleHandle τ0 :=
    gateReturnExec_transferErr c τ0 gid act .staleHandle hserv0 hact0 htransfer
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E fun ds =>
        ds.setReg (operandsOf W).rd Errno.staleHandle.toWord := by
    rw [hcore0, retire_gateReturn_exec base E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith base E f) = _
    rw [hexec]
  have hgid := retGid_eval_selected σ E gid (by simpa [E] using hserv)
  have hservV : σ.regs (Hw.dsrvV E) 1 = 1#1 := by
    change (if σ.regs (Hw.dsrvV E) 1 = 1#1 then some _ else none) =
      some gid at hserv
    by_contra hv
    rw [if_neg hv] at hserv
    contradiction
  have hactV : σ.regs (Hw.gactV gid) 1 = 1#1 := by
    change (if σ.regs (Hw.gactV gid) 1 = 1#1 then some _ else none) =
      some act at hact
    by_contra hv
    rw [if_neg hv] at hact
    contradiction
  let p0 : Hw.Check :=
    (.not (.reg 1 (Hw.dsrvV E)), .fault .protocol)
  let p1 : Hw.Check :=
    (.not (Hw.muxFin (fun g => .reg 1 (Hw.gactV g)) (Hw.retGid E)),
      .fault .protocol)
  have hpre : ∀ x ∈ [p0, p1], x.1.eval σ ≠ 1#1 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · subst x
      simp [p0, Expr.eval, hservV]
    · subst x
      have hactive : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
          (Hw.retGid E)).eval σ = 1#1 := by
        rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
        exact hactV
      simp [p1, Expr.eval, hactive]
  apply square_retire_gateReturn_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc [p0, p1] (List.drop 3 (Hw.retChecks E))
    (.and (Hw.retNZ E) (.not (Hw.retSel E).live)) .staleHandle
  · rfl
  · exact hpre
  · simpa [E] using hstale
  · simpa [τ0, W, base] using hspec

/-- Complete fourth ladder arm: a live non-null reply handle with a class
mismatch returns `badCap`. -/
theorem square_retire_gateReturn_badClass (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (gid : GateId) (act : Activation)
    (hserv : ((Hw.abs σ).doms
      (finOfBv (by decide) (σ.regs "if_dom" 2))).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hstalePass : (Expr.and
      (Hw.retNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.retSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).live)).eval σ ≠ 1#1)
    (hbad : (Expr.and
      (Hw.retNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.retSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk)).eval σ = 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let c : Ctx := { d := E, pc := (base.doms E).pc, op := operandsOf W }
  let τ0 := base.setDom E fun ds => { ds with pc := ds.pc + 1 }
  have hop : Machines.Lnp64u.sig.opcodeOf W = (23#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (23#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) = retire base E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR : (Hw.retW E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    retW_eval σ hz E (operandsOf W).rs1 rfl
  have hreg : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hword : (τ0.doms c.d).reg c.op.rs1 = (Hw.retW E).eval σ := by
    simp only [c]
    rw [hreg, hR]
  have hlogic : (Hw.retNZ E).eval σ = 1#1 ∧
      (Hw.retSel E).clsOk.eval σ = 0#1 := by
    apply (by decide : ∀ a b : BitVec 1,
      a &&& ~~~b = 1#1 → a = 1#1 ∧ b = 0#1)
    simpa [E] using hbad
  have hlive : (Hw.retSel E).live.eval σ = 1#1 := by
    exact (by decide : ∀ a b : BitVec 1,
      a = 1#1 → a &&& ~~~b ≠ 1#1 → b = 1#1)
      ((Hw.retNZ E).eval σ) ((Hw.retSel E).live.eval σ) hlogic.1
      (by simpa [E] using hstalePass)
  have hnz : (Hw.retW E).eval σ ≠ 0#32 :=
    (retNZ_eval_iff σ E).mp hlogic.1
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  obtain ⟨e, alive, acap⟩ := capSel_entry_of_live σ τ0 E
    (Hw.retW E) hbridge (by simpa [Hw.retSel] using hlive)
  have slotNat : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.retW E).eval σ).extractLsb' 0 4)).val =
      (((Hw.retW E).eval σ).extractLsb' 0 4).toNat := rfl
  have hclsIff := capSel_clsOk_iff_some σ E (Hw.retW E)
    (finOfBv (by decide) (((Hw.retW E).eval σ).extractLsb' 0 4))
    e hkc slotNat acap
  have hcls : (Handle.decode ((Hw.retW E).eval σ)).cls ≠ e.kind.cls := by
    intro heq
    have hone := hclsIff.mpr heq
    have hzero : (Hw.capSel E (Hw.retW E)).clsOk.eval σ = 0#1 := by
      simpa [Hw.retSel] using hlogic.2
    rw [hzero] at hone
    contradiction
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d act.caller
      ((τ0.doms c.d).reg c.op.rs1) τ0 = .err .badCap τ0 := by
    rw [hword]
    exact transferByHandle_badClass τ0 E act.caller ((Hw.retW E).eval σ)
      (Handle.decode ((Hw.retW E).eval σ)).slot
      (Handle.decode ((Hw.retW E).eval σ)).gen e hnz rfl alive hcls
  have hserv0 : (τ0.doms c.d).serving = some gid := by
    simp [τ0, c, base, MachineState.setDom, Loom.Fun.update,
      refillPhase_serving, hserv]
  have hact0 : (τ0.gates gid).act = some act := by
    simp [τ0, base, MachineState.setDom, refillPhase_gates, hact]
  have hexec : Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 =
      .err .badCap τ0 :=
    gateReturnExec_transferErr c τ0 gid act .badCap hserv0 hact0 htransfer
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) =
      τ0.setDom E fun ds => ds.setReg (operandsOf W).rd Errno.badCap.toWord := by
    rw [hcore0, retire_gateReturn_exec base E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith base E f) = _
    rw [hexec]
  have hgid := retGid_eval_selected σ E gid (by simpa [E] using hserv)
  have hservV : σ.regs (Hw.dsrvV E) 1 = 1#1 := by
    change (if σ.regs (Hw.dsrvV E) 1 = 1#1 then some _ else none) =
      some gid at hserv
    by_contra hv
    rw [if_neg hv] at hserv
    contradiction
  have hactV : σ.regs (Hw.gactV gid) 1 = 1#1 := by
    change (if σ.regs (Hw.gactV gid) 1 = 1#1 then some _ else none) =
      some act at hact
    by_contra hv
    rw [if_neg hv] at hact
    contradiction
  let p0 : Hw.Check :=
    (.not (.reg 1 (Hw.dsrvV E)), .fault .protocol)
  let p1 : Hw.Check :=
    (.not (Hw.muxFin (fun g => .reg 1 (Hw.gactV g)) (Hw.retGid E)),
      .fault .protocol)
  let p2 : Hw.Check :=
    (.and (Hw.retNZ E) (.not (Hw.retSel E).live), .err .staleHandle)
  have hpre : ∀ x ∈ [p0, p1, p2], x.1.eval σ ≠ 1#1 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx
    · subst x
      simp [p0, Expr.eval, hservV]
    · subst x
      have hactive : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
          (Hw.retGid E)).eval σ = 1#1 := by
        rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
        exact hactV
      simp [p1, Expr.eval, hactive]
    · subst x
      simpa [p2, E] using hstalePass
  apply square_retire_gateReturn_firstError m hwf hfit σ hsync hifv hcl E
    rfl hifsel hifexcl hopc [p0, p1, p2] (List.drop 4 (Hw.retChecks E))
    (.and (Hw.retNZ E) (.not (Hw.retSel E).clsOk)) .badCap
  · rfl
  · exact hpre
  · simpa [E] using hbad
  · simpa [τ0, W, base] using hspec

end Machines.Lnp64u.Theorems.RMC
