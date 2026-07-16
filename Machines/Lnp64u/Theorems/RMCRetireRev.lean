-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRv
import Machines.Lnp64u.Theorems.RMCRetireGateAbs

/-!
# R-MC retirement: `cap_revoke`

This file connects the converged hidden mark vector proved in `RMCRv` to
the `revCirc` kill predicate and then to the kernel's `destroyMarked` state
transformation.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- At revoke retirement, the dynamic circuit kill lookup is exactly the
kernel mark bit at the decoded domain and slot. -/
theorem revKilled_eval (σ : Loom.Hw.St) (hrv : RvSync σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (dm : Expr 2) (sl : Expr 4) :
    ((Hw.revKilled dm sl).eval σ = 1#1) ↔
      (Hw.abs σ).marks (rvRoot σ)
        (finOfBv (by decide) (dm.eval σ))
        (finOfBv (by decide) (sl.eval σ)) = true := by
  let c : DomainId := finOfBv (by decide) (dm.eval σ)
  let s : Slot := finOfBv (by decide) (sl.eval σ)
  have hc : dm.eval σ = BitVec.ofNat 2 c.val :=
    (bv2_lit_iff _ c).mpr rfl
  have hs : sl.eval σ = BitVec.ofNat 4 s.val :=
    (bv4_slot_iff _ s).mpr rfl
  have hr := rvR_eq_marks_of_sync σ hrv hifv hopc hcl c s
  unfold Hw.revKilled Hw.marksAt
  rw [nodeAt_eval]
  have hn := nDom_pack (dm.eval σ).toNat (sl.eval σ).toNat
    (dm.eval σ).isLt (sl.eval σ).isLt
  have hnode :
      (⟨(dm.eval σ).toNat * 16 + (sl.eval σ).toNat, by
        show _ < numDomains * numSlots
        simp only [numDomains, numSlots]
        have := (dm.eval σ).isLt
        have := (sl.eval σ).isLt
        omega⟩ : Hw.NodeId) = Hw.nodeOf c s := by
    apply Fin.ext
    change (dm.eval σ).toNat * 16 + (sl.eval σ).toNat =
      c.val * numSlots + s.val
    simp [c, s, finOfBv, numSlots]
  rw [hnode]
  show (σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 = 1#1) ↔ _
  rw [hr]
  by_cases hm : (Hw.abs σ).marks (rvRoot σ) c s = true <;> simp [hm, c, s]

/-- Boolean-value form of `revKilled_eval`. -/
theorem revKilled_value (σ : Loom.Hw.St) (hrv : RvSync σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.revKilled dm sl).eval σ =
      if (Hw.abs σ).marks (rvRoot σ)
          (finOfBv (by decide) (dm.eval σ))
          (finOfBv (by decide) (sl.eval σ))
        then 1#1 else 0#1 := by
  by_cases hm : (Hw.abs σ).marks (rvRoot σ)
      (finOfBv (by decide) (dm.eval σ))
      (finOfBv (by decide) (sl.eval σ)) = true
  · rw [if_pos hm]
    exact (revKilled_eval σ hrv hifv hopc hcl dm sl).mpr hm
  · rw [if_neg hm]
    apply bv1_ne_one.mp
    exact fun hk => hm ((revKilled_eval σ hrv hifv hopc hcl dm sl).mp hk)

private def revNodeIx : List (DomainId × Slot) :=
  (List.finRange numDomains).flatMap fun c =>
    (List.finRange numSlots).map fun s => (c, s)

private def revCellIx : List (DomainId × LineageId) :=
  (List.finRange numDomains).flatMap fun c =>
    (List.finRange numLineage).map fun l => (c, l)

private def revNodeA (x : DomainId × Slot) : Act :=
  let c := x.1
  let s := x.2
  .ite (.and (.reg 1 (Hw.rvR (Hw.nodeOf c s))) (.reg 1 (Hw.dcapV c s)))
    (.seq (.write 1 (Hw.dcapV c s) (.lit 0))
      (.write 8 (Hw.dgen c s) (Hw.bumpE (.reg 8 (Hw.dgen c s)))))
    .skip

private def revCellA (x : DomainId × LineageId) : Act :=
  let c := x.1
  let l := x.2
  .ite (Hw.orAll ((List.finRange numSlots).map fun s =>
      Hw.andAll [.reg 1 (Hw.rvR (Hw.nodeOf c s)), .reg 1 (Hw.dcapV c s),
        .reg 1 (Hw.dcapLinV c s), .eq (.reg 4 (Hw.dcapLin c s)) (Hw.lLit l)]))
    (.write 1 (Hw.dcellV c l) (.lit 0)) .skip

private def revStructuralA : Act :=
  Hw.seqAll (revNodeIx.map revNodeA ++ revCellIx.map revCellA)

private def revSuccessA (E : DomainId) : Act :=
  Hw.seqAll
    (revNodeIx.map revNodeA ++ revCellIx.map revCellA ++
      [Hw.sweepRegionsA Hw.revKilled, Hw.writeReg E Hw.rdE (.lit 0),
        Hw.pcAdvA E])

/-- Public arm-level name for the successful revoke payload. -/
def revSuccessArmA (E : DomainId) : Act := revSuccessA E

/-- The selected `cap_revoke` dispatch reduces to its two checks and the
named successful payload. -/
theorem retireFor_rev_ladder (σ : Loom.Hw.St) (E : DomainId)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6) :
    ∀ acc, (Hw.retireFor E).run σ acc =
      if (Expr.not (Hw.revSel E).live).eval σ = 1#1 then
        (Hw.respA E (.err .staleHandle)).run σ acc
      else if (Expr.not
          (Expr.and (Hw.revSel E).clsOk (Hw.kIsMem (Hw.revSel E).kindW))).eval σ = 1#1 then
        (Hw.respA E (.err .badCap)).run σ acc
      else (revSuccessA E).run σ acc := by
  intro acc
  have hsel := retireFor_sel_of_opc σ E "cap_revoke" 18#6 hopc
    (by decide +kernel +revert) (by decide +kernel +revert) (Hw.revCirc E)
    (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  rw [hsel acc]
  rfl

private theorem seqAll_actions_at_update {I : Type} {w : Nat}
    (σ acc : Loom.Hw.St) (a : I → Act) (l : List I) (i : I)
    (hi : i ∈ l) (hnd : l.Nodup) (rn : String) (f : BitVec w → BitVec w)
    (hat : ∀ acc', ((a i).run σ acc').regs rn w = f (acc'.regs rn w))
    (hframe : ∀ j ∈ l, j ≠ i → ∀ acc',
      ((a j).run σ acc').regs rn w = acc'.regs rn w) :
    ((Hw.seqAll (l.map a)).run σ acc).regs rn w = f (acc.regs rn w) := by
  induction l generalizing acc with
  | nil => exact absurd hi List.not_mem_nil
  | cons j t ih =>
      have hnd' := List.nodup_cons.mp hnd
      by_cases hji : j = i
      · subst j
        change ((Hw.seqAll (t.map a)).run σ ((a i).run σ acc)).regs rn w = _
        rw [seqAll_actions_frame σ _ a t rn]
        · exact hat acc
        · intro k hk
          exact hframe k (List.mem_cons_of_mem i hk)
            (fun h => hnd'.1 (h ▸ hk))
      · have hit : i ∈ t := (List.mem_cons.mp hi).resolve_left
          (fun h => hji h.symm)
        change ((Hw.seqAll (t.map a)).run σ ((a j).run σ acc)).regs rn w = _
        rw [ih _ hit hnd'.2 (fun k hk hki acc' =>
          hframe k (List.mem_cons_of_mem j hk) hki acc')]
        exact congrArg f (hframe j (List.mem_cons_self ..) hji acc)

private theorem revNodeIx_mem (x : DomainId × Slot) : x ∈ revNodeIx := by
  rcases x with ⟨c, s⟩
  simp [revNodeIx]

private theorem revNodeIx_nodup : revNodeIx.Nodup := by
  decide +kernel

private theorem dcapV_node_ne (x y : DomainId × Slot) (hxy : x ≠ y) :
    Hw.dcapV x.1 x.2 ≠ Hw.dcapV y.1 y.2 := by
  revert x y
  decide +kernel

private theorem dgen_node_ne (x y : DomainId × Slot) (hxy : x ≠ y) :
    Hw.dgen x.1 x.2 ≠ Hw.dgen y.1 y.2 := by
  revert x y
  decide +kernel

private theorem rev_dcapV_ne_dgen (x y : DomainId × Slot) :
    Hw.dcapV x.1 x.2 ≠ Hw.dgen y.1 y.2 := by
  revert x y
  decide +kernel

private theorem revNodeA_run_v_same (σ acc : Loom.Hw.St)
    (x : DomainId × Slot) :
    ((revNodeA x).run σ acc).regs (Hw.dcapV x.1 x.2) 1 =
      if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf x.1 x.2)))
          (.reg 1 (Hw.dcapV x.1 x.2))).eval σ = 1#1
      then 0#1 else acc.regs (Hw.dcapV x.1 x.2) 1 := by
  have hcross := rev_dcapV_ne_dgen x x
  simp [revNodeA, Act.run, RegEnv.set, Expr.eval, hcross]

private theorem revNodeA_run_gen_same (σ acc : Loom.Hw.St)
    (x : DomainId × Slot) :
    ((revNodeA x).run σ acc).regs (Hw.dgen x.1 x.2) 8 =
      if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf x.1 x.2)))
          (.reg 1 (Hw.dcapV x.1 x.2))).eval σ = 1#1
      then bumpGen (σ.regs (Hw.dgen x.1 x.2) 8)
      else acc.regs (Hw.dgen x.1 x.2) 8 := by
  simp [revNodeA, Act.run, RegEnv.set, Expr.eval, bumpE_eval]

private theorem revNodeA_run_v_frame (σ acc : Loom.Hw.St)
    (x y : DomainId × Slot) (hxy : x ≠ y) :
    ((revNodeA x).run σ acc).regs (Hw.dcapV y.1 y.2) 1 =
      acc.regs (Hw.dcapV y.1 y.2) 1 := by
  have hv := dcapV_node_ne x y hxy
  have hg := rev_dcapV_ne_dgen y x
  simp [revNodeA, Act.run, RegEnv.set, hv, Ne.symm hv, hg]

private theorem revNodeA_run_gen_frame (σ acc : Loom.Hw.St)
    (x y : DomainId × Slot) (hxy : x ≠ y) :
    ((revNodeA x).run σ acc).regs (Hw.dgen y.1 y.2) 8 =
      acc.regs (Hw.dgen y.1 y.2) 8 := by
  have hg := dgen_node_ne x y hxy
  have hv := rev_dcapV_ne_dgen x y
  simp [revNodeA, Act.run, RegEnv.set, hg, Ne.symm hg, hv]

/-- The node-destruction sweep clears exactly a fired node's valid bit. -/
theorem revNodes_run_v (σ acc : Loom.Hw.St) (c : DomainId) (s : Slot) :
    ((Hw.seqAll (revNodeIx.map revNodeA)).run σ acc).regs
        (Hw.dcapV c s) 1 =
      if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf c s)))
          (.reg 1 (Hw.dcapV c s))).eval σ = 1#1
      then 0#1 else acc.regs (Hw.dcapV c s) 1 := by
  let x : DomainId × Slot := (c, s)
  apply seqAll_actions_at_update σ acc revNodeA revNodeIx x
    (revNodeIx_mem x) revNodeIx_nodup (Hw.dcapV c s)
    (fun b => if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf c s)))
      (.reg 1 (Hw.dcapV c s))).eval σ = 1#1 then 0#1 else b
    )
  · intro acc'
    exact revNodeA_run_v_same σ acc' x
  · intro y _ hy acc'
    exact revNodeA_run_v_frame σ acc' y x hy

/-- The node-destruction sweep bumps exactly a fired live node's generation. -/
theorem revNodes_run_gen (σ acc : Loom.Hw.St) (c : DomainId) (s : Slot) :
    ((Hw.seqAll (revNodeIx.map revNodeA)).run σ acc).regs
        (Hw.dgen c s) 8 =
      if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf c s)))
          (.reg 1 (Hw.dcapV c s))).eval σ = 1#1
      then bumpGen (σ.regs (Hw.dgen c s) 8)
      else acc.regs (Hw.dgen c s) 8 := by
  let x : DomainId × Slot := (c, s)
  apply seqAll_actions_at_update σ acc revNodeA revNodeIx x
    (revNodeIx_mem x) revNodeIx_nodup (Hw.dgen c s)
    (fun b => if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf c s)))
      (.reg 1 (Hw.dcapV c s))).eval σ = 1#1
      then bumpGen (σ.regs (Hw.dgen c s) 8) else b)
  · intro acc'
    exact revNodeA_run_gen_same σ acc' x
  · intro y _ hy acc'
    exact revNodeA_run_gen_frame σ acc' y x hy

private theorem revCellIx_mem (x : DomainId × LineageId) : x ∈ revCellIx := by
  rcases x with ⟨c, l⟩
  simp [revCellIx]

private theorem revCellIx_nodup : revCellIx.Nodup := by
  decide +kernel

private theorem dcellV_cell_ne (x y : DomainId × LineageId) (hxy : x ≠ y) :
    Hw.dcellV x.1 x.2 ≠ Hw.dcellV y.1 y.2 := by
  revert x y
  decide +kernel

private theorem revCellA_run_same (σ acc : Loom.Hw.St)
    (x : DomainId × LineageId) :
    ((revCellA x).run σ acc).regs (Hw.dcellV x.1 x.2) 1 =
      if (Hw.orAll ((List.finRange numSlots).map fun s =>
          Hw.andAll [.reg 1 (Hw.rvR (Hw.nodeOf x.1 s)),
            .reg 1 (Hw.dcapV x.1 s), .reg 1 (Hw.dcapLinV x.1 s),
            .eq (.reg 4 (Hw.dcapLin x.1 s)) (Hw.lLit x.2)])).eval σ = 1#1
      then 0#1 else acc.regs (Hw.dcellV x.1 x.2) 1 := by
  simp [revCellA, Act.run, RegEnv.set, Expr.eval]

private theorem revCellA_run_frame (σ acc : Loom.Hw.St)
    (x y : DomainId × LineageId) (hxy : x ≠ y) :
    ((revCellA x).run σ acc).regs (Hw.dcellV y.1 y.2) 1 =
      acc.regs (Hw.dcellV y.1 y.2) 1 := by
  have hn := dcellV_cell_ne x y hxy
  simp [revCellA, Act.run, RegEnv.set, Expr.eval, hn, Ne.symm hn]

/-- The cell sweep clears precisely the lineage cells selected by its
marked-live-slot disjunction. -/
theorem revCells_run_v (σ acc : Loom.Hw.St)
    (c : DomainId) (l : LineageId) :
    ((Hw.seqAll (revCellIx.map revCellA)).run σ acc).regs
        (Hw.dcellV c l) 1 =
      if (Hw.orAll ((List.finRange numSlots).map fun s =>
          Hw.andAll [.reg 1 (Hw.rvR (Hw.nodeOf c s)),
            .reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
            .eq (.reg 4 (Hw.dcapLin c s)) (Hw.lLit l)])).eval σ = 1#1
      then 0#1 else acc.regs (Hw.dcellV c l) 1 := by
  let x : DomainId × LineageId := (c, l)
  apply seqAll_actions_at_update σ acc revCellA revCellIx x
    (revCellIx_mem x) revCellIx_nodup (Hw.dcellV c l)
    (fun b => if (Hw.orAll ((List.finRange numSlots).map fun s =>
      Hw.andAll [.reg 1 (Hw.rvR (Hw.nodeOf c s)),
        .reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
        .eq (.reg 4 (Hw.dcapLin c s)) (Hw.lLit l)])).eval σ = 1#1
      then 0#1 else b)
  · intro acc'
    exact revCellA_run_same σ acc' x
  · intro y _ hy acc'
    exact revCellA_run_frame σ acc' y x hy

private theorem revCellA_frame_dcapV (σ acc : Loom.Hw.St)
    (x : DomainId × LineageId) (c : DomainId) (s : Slot) :
    ((revCellA x).run σ acc).regs (Hw.dcapV c s) 1 =
      acc.regs (Hw.dcapV c s) 1 := by
  have hn : Hw.dcellV x.1 x.2 ≠ Hw.dcapV c s := by
    revert x c s
    decide +kernel
  simp [revCellA, Act.run, RegEnv.set, Expr.eval, hn, Ne.symm hn]

private theorem revCellA_frame_dgen (σ acc : Loom.Hw.St)
    (x : DomainId × LineageId) (c : DomainId) (s : Slot) :
    ((revCellA x).run σ acc).regs (Hw.dgen c s) 8 =
      acc.regs (Hw.dgen c s) 8 := by
  have hn : Hw.dcellV x.1 x.2 ≠ Hw.dgen c s := by
    revert x c s
    decide +kernel
  simp [revCellA, Act.run, RegEnv.set, hn]

private theorem revNodeA_frame_dcellV (σ acc : Loom.Hw.St)
    (x : DomainId × Slot) (c : DomainId) (l : LineageId) :
    ((revNodeA x).run σ acc).regs (Hw.dcellV c l) 1 =
      acc.regs (Hw.dcellV c l) 1 := by
  have hv : Hw.dcapV x.1 x.2 ≠ Hw.dcellV c l := by
    revert x c l
    decide +kernel
  have hg : Hw.dgen x.1 x.2 ≠ Hw.dcellV c l := by
    revert x c l
    decide +kernel
  simp [revNodeA, Act.run, RegEnv.set, Expr.eval,
    hv, Ne.symm hv, hg, Ne.symm hg]

private theorem revCells_frame_dcapV (σ acc : Loom.Hw.St)
    (c : DomainId) (s : Slot) :
    ((Hw.seqAll (revCellIx.map revCellA)).run σ acc).regs (Hw.dcapV c s) 1 =
      acc.regs (Hw.dcapV c s) 1 := by
  apply seqAll_actions_frame σ acc revCellA revCellIx (Hw.dcapV c s)
  intro x _ acc'
  exact revCellA_frame_dcapV σ acc' x c s

private theorem revCells_frame_dgen (σ acc : Loom.Hw.St)
    (c : DomainId) (s : Slot) :
    ((Hw.seqAll (revCellIx.map revCellA)).run σ acc).regs (Hw.dgen c s) 8 =
      acc.regs (Hw.dgen c s) 8 := by
  apply seqAll_actions_frame σ acc revCellA revCellIx (Hw.dgen c s)
  intro x _ acc'
  exact revCellA_frame_dgen σ acc' x c s

private theorem revNodes_frame_dcellV (σ acc : Loom.Hw.St)
    (c : DomainId) (l : LineageId) :
    ((Hw.seqAll (revNodeIx.map revNodeA)).run σ acc).regs (Hw.dcellV c l) 1 =
      acc.regs (Hw.dcellV c l) 1 := by
  apply seqAll_actions_frame σ acc revNodeA revNodeIx (Hw.dcellV c l)
  intro x _ acc'
  exact revNodeA_frame_dcellV σ acc' x c l

private theorem revTail_frame_dcapV (σ acc : Loom.Hw.St) (E c : DomainId)
    (s : Slot) :
    ((Hw.seqAll [Hw.sweepRegionsA Hw.revKilled,
      Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E]).run σ acc).regs
        (Hw.dcapV c s) 1 = acc.regs (Hw.dcapV c s) 1 := by
  apply frame
  fin_cases E <;> fin_cases c <;> fin_cases s <;> decide +kernel

private theorem revTail_frame_dgen (σ acc : Loom.Hw.St) (E c : DomainId)
    (s : Slot) :
    ((Hw.seqAll [Hw.sweepRegionsA Hw.revKilled,
      Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E]).run σ acc).regs
        (Hw.dgen c s) 8 = acc.regs (Hw.dgen c s) 8 := by
  apply frame
  fin_cases E <;> fin_cases c <;> fin_cases s <;> decide +kernel

private theorem revTail_frame_dcellV (σ acc : Loom.Hw.St) (E c : DomainId)
    (l : LineageId) :
    ((Hw.seqAll [Hw.sweepRegionsA Hw.revKilled,
      Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E]).run σ acc).regs
        (Hw.dcellV c l) 1 = acc.regs (Hw.dcellV c l) 1 := by
  apply frame
  fin_cases E <;> fin_cases c <;> fin_cases l <;> decide +kernel

/-- Full successful revoke payload: capability validity. -/
theorem revSuccessA_run_v (σ acc : Loom.Hw.St) (E c : DomainId) (s : Slot) :
    ((revSuccessA E).run σ acc).regs (Hw.dcapV c s) 1 =
      if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf c s)))
          (.reg 1 (Hw.dcapV c s))).eval σ = 1#1
      then 0#1 else acc.regs (Hw.dcapV c s) 1 := by
  unfold revSuccessA
  rw [seqAll_append_run σ (revNodeIx.map revNodeA ++ revCellIx.map revCellA)
      [Hw.sweepRegionsA Hw.revKilled, Hw.writeReg E Hw.rdE (.lit 0),
        Hw.pcAdvA E] acc,
    seqAll_append_run σ (revNodeIx.map revNodeA)
      (revCellIx.map revCellA) acc]
  rw [revTail_frame_dcapV, revCells_frame_dcapV, revNodes_run_v]

/-- Full successful revoke payload: slot generation. -/
theorem revSuccessA_run_gen (σ acc : Loom.Hw.St) (E c : DomainId) (s : Slot) :
    ((revSuccessA E).run σ acc).regs (Hw.dgen c s) 8 =
      if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf c s)))
          (.reg 1 (Hw.dcapV c s))).eval σ = 1#1
      then bumpGen (σ.regs (Hw.dgen c s) 8)
      else acc.regs (Hw.dgen c s) 8 := by
  unfold revSuccessA
  rw [seqAll_append_run σ (revNodeIx.map revNodeA ++ revCellIx.map revCellA)
      [Hw.sweepRegionsA Hw.revKilled, Hw.writeReg E Hw.rdE (.lit 0),
        Hw.pcAdvA E] acc,
    seqAll_append_run σ (revNodeIx.map revNodeA)
      (revCellIx.map revCellA) acc]
  rw [revTail_frame_dgen, revCells_frame_dgen, revNodes_run_gen]

/-- Full successful revoke payload: lineage-cell validity. -/
theorem revSuccessA_run_cellV (σ acc : Loom.Hw.St) (E c : DomainId)
    (l : LineageId) :
    ((revSuccessA E).run σ acc).regs (Hw.dcellV c l) 1 =
      if (Hw.orAll ((List.finRange numSlots).map fun s =>
          Hw.andAll [.reg 1 (Hw.rvR (Hw.nodeOf c s)),
            .reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
            .eq (.reg 4 (Hw.dcapLin c s)) (Hw.lLit l)])).eval σ = 1#1
      then 0#1 else acc.regs (Hw.dcellV c l) 1 := by
  unfold revSuccessA
  rw [seqAll_append_run σ (revNodeIx.map revNodeA ++ revCellIx.map revCellA)
      [Hw.sweepRegionsA Hw.revKilled, Hw.writeReg E Hw.rdE (.lit 0),
        Hw.pcAdvA E] acc,
    seqAll_append_run σ (revNodeIx.map revNodeA)
      (revCellIx.map revCellA) acc]
  rw [revTail_frame_dcellV, revCells_run_v, revNodes_frame_dcellV]

/-- Structural revoke sweep: validity bit before the region/register tail. -/
theorem revStructuralA_run_v (σ acc : Loom.Hw.St) (c : DomainId) (s : Slot) :
    (revStructuralA.run σ acc).regs (Hw.dcapV c s) 1 =
      if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf c s)))
          (.reg 1 (Hw.dcapV c s))).eval σ = 1#1
      then 0#1 else acc.regs (Hw.dcapV c s) 1 := by
  unfold revStructuralA
  rw [seqAll_append_run, revCells_frame_dcapV, revNodes_run_v]

/-- Structural revoke sweep: generation before the region/register tail. -/
theorem revStructuralA_run_gen (σ acc : Loom.Hw.St) (c : DomainId) (s : Slot) :
    (revStructuralA.run σ acc).regs (Hw.dgen c s) 8 =
      if (Expr.and (.reg 1 (Hw.rvR (Hw.nodeOf c s)))
          (.reg 1 (Hw.dcapV c s))).eval σ = 1#1
      then bumpGen (σ.regs (Hw.dgen c s) 8)
      else acc.regs (Hw.dgen c s) 8 := by
  unfold revStructuralA
  rw [seqAll_append_run, revCells_frame_dgen, revNodes_run_gen]

/-- Structural revoke sweep: lineage-cell validity before the tail. -/
theorem revStructuralA_run_cellV (σ acc : Loom.Hw.St)
    (c : DomainId) (l : LineageId) :
    (revStructuralA.run σ acc).regs (Hw.dcellV c l) 1 =
      if (Hw.orAll ((List.finRange numSlots).map fun s =>
          Hw.andAll [.reg 1 (Hw.rvR (Hw.nodeOf c s)),
            .reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
            .eq (.reg 4 (Hw.dcapLin c s)) (Hw.lLit l)])).eval σ = 1#1
      then 0#1 else acc.regs (Hw.dcellV c l) 1 := by
  unfold revStructuralA
  rw [seqAll_append_run, revCells_run_v, revNodes_frame_dcellV]

private theorem abs_cap_lineage_some_iff (σ : Loom.Hw.St)
    (c : DomainId) (s : Slot) (l : LineageId) :
    (∃ e, ((Hw.abs σ).doms c).caps s = some e ∧ e.lineage = some l) ↔
      σ.regs (Hw.dcapV c s) 1 = 1#1 ∧
      σ.regs (Hw.dcapLinV c s) 1 = 1#1 ∧
      finOfBv (by decide) (σ.regs (Hw.dcapLin c s) 4) = l := by
  unfold Hw.abs Hw.absDom
  by_cases hv : σ.regs (Hw.dcapV c s) 1 = 1#1
  · by_cases hl : σ.regs (Hw.dcapLinV c s) 1 = 1#1
    · simp [hv, hl]
    · have hl0 := bv1_ne_one.mp hl
      simp [hv, hl0, hl]
  · have hv0 := bv1_ne_one.mp hv
    simp [hv0, hv]

/-- The cell-sweep disjunction fires exactly when a marked live capability
belongs to the lineage cell. -/
theorem revCellCond_eval (σ : Loom.Hw.St) (hrv : RvSync σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (c : DomainId) (l : LineageId) :
    ((Hw.orAll ((List.finRange numSlots).map fun s =>
        Hw.andAll [.reg 1 (Hw.rvR (Hw.nodeOf c s)),
          .reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
          .eq (.reg 4 (Hw.dcapLin c s)) (Hw.lLit l)])).eval σ = 1#1) ↔
      ∃ s e, (Hw.abs σ).marks (rvRoot σ) c s = true ∧
        ((Hw.abs σ).doms c).caps s = some e ∧ e.lineage = some l := by
  rw [orAll_eval]
  constructor
  · rintro ⟨e, he, hone⟩
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp he
    have hr := rvR_eq_marks_of_sync σ hrv hifv hopc hcl c s
    change (σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 &&&
      (σ.regs (Hw.dcapV c s) 1 &&&
        (σ.regs (Hw.dcapLinV c s) 1 &&&
          (if σ.regs (Hw.dcapLin c s) 4 = (Hw.lLit l).eval σ
            then 1#1 else 0#1)))) = 1#1 at hone
    rw [bv1_and_eq_one, bv1_and_eq_one, bv1_and_eq_one] at hone
    have hm : (Hw.abs σ).marks (rvRoot σ) c s = true := by
      by_cases hmark : (Hw.abs σ).marks (rvRoot σ) c s = true
      · exact hmark
      · have hmark0 : (Hw.abs σ).marks (rvRoot σ) c s = false :=
          Bool.eq_false_of_not_eq_true hmark
        have hzero : σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 = 0#1 := by
          simp [hr, hmark0]
        rw [hzero] at hone
        exact absurd hone.1 (by decide)
    have hlin : finOfBv (by decide)
        (σ.regs (Hw.dcapLin c s) 4) = l := by
      have heq : σ.regs (Hw.dcapLin c s) 4 = (Hw.lLit l).eval σ := by
        by_contra hne
        simp [hne] at hone
      apply (bv4_slot_iff (σ.regs (Hw.dcapLin c s) 4) l).mp
      simpa [Hw.lLit, Expr.eval] using heq
    obtain ⟨entry, hcap, hentry⟩ :=
      (abs_cap_lineage_some_iff σ c s l).mpr
        ⟨hone.2.1, hone.2.2.1, hlin⟩
    exact ⟨s, entry, hm, hcap, hentry⟩
  · rintro ⟨s, e, hm, hcap, hlin⟩
    refine ⟨Hw.andAll [.reg 1 (Hw.rvR (Hw.nodeOf c s)),
      .reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
      .eq (.reg 4 (Hw.dcapLin c s)) (Hw.lLit l)], ?_, ?_⟩
    · exact List.mem_map_of_mem (List.mem_finRange s)
    · have hr := rvR_eq_marks_of_sync σ hrv hifv hopc hcl c s
      have hc := (abs_cap_lineage_some_iff σ c s l).mp ⟨e, hcap, hlin⟩
      change (σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 &&&
        (σ.regs (Hw.dcapV c s) 1 &&&
          (σ.regs (Hw.dcapLinV c s) 1 &&&
            (if σ.regs (Hw.dcapLin c s) 4 = (Hw.lLit l).eval σ
              then 1#1 else 0#1)))) = 1#1
      rw [hr, hm, hc.1, hc.2.1]
      have hbits : σ.regs (Hw.dcapLin c s) 4 = (Hw.lLit l).eval σ := by
        simpa [Hw.lLit, Expr.eval] using
          (bv4_slot_iff (σ.regs (Hw.dcapLin c s) 4) l).mpr hc.2.2
      simp [hbits]

/-- Structural validity writes implement the `destroyMarked` caps mask. -/
theorem revStructuralA_run_v_semantic (σ acc : Loom.Hw.St) (hrv : RvSync σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hacc : ∀ c s, acc.regs (Hw.dcapV c s) 1 =
      σ.regs (Hw.dcapV c s) 1)
    (c : DomainId) (s : Slot) :
    (revStructuralA.run σ acc).regs (Hw.dcapV c s) 1 =
      if (Hw.abs σ).marks (rvRoot σ) c s then 0#1
      else acc.regs (Hw.dcapV c s) 1 := by
  rw [revStructuralA_run_v]
  have hr := rvR_eq_marks_of_sync σ hrv hifv hopc hcl c s
  change (if (σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 &&&
      σ.regs (Hw.dcapV c s) 1) = 1#1 then 0#1
    else acc.regs (Hw.dcapV c s) 1) = _
  rw [hr]
  by_cases hm : (Hw.abs σ).marks (rvRoot σ) c s = true
  · rw [hm]
    by_cases hv : σ.regs (Hw.dcapV c s) 1 = 1#1
    · simp [hv]
    · have hv0 := bv1_ne_one.mp hv
      rw [hacc c s, hv0]
      decide
  · have hm0 := Bool.eq_false_of_not_eq_true hm
    simp [hm0]

/-- Structural generation writes implement the live-entry bump in
`destroyMarked`. -/
theorem revStructuralA_run_gen_semantic (σ acc : Loom.Hw.St)
    (hrv : RvSync σ) (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (haccV : ∀ c s, acc.regs (Hw.dcapV c s) 1 =
      σ.regs (Hw.dcapV c s) 1)
    (haccG : ∀ c s, acc.regs (Hw.dgen c s) 8 =
      σ.regs (Hw.dgen c s) 8)
    (c : DomainId) (s : Slot) :
    (revStructuralA.run σ acc).regs (Hw.dgen c s) 8 =
      if (Hw.abs σ).marks (rvRoot σ) c s &&
          (((Hw.abs σ).doms c).caps s).isSome
      then bumpGen (acc.regs (Hw.dgen c s) 8)
      else acc.regs (Hw.dgen c s) 8 := by
  rw [revStructuralA_run_gen]
  have hr := rvR_eq_marks_of_sync σ hrv hifv hopc hcl c s
  change (if (σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 &&&
      σ.regs (Hw.dcapV c s) 1) = 1#1
    then bumpGen (σ.regs (Hw.dgen c s) 8)
    else acc.regs (Hw.dgen c s) 8) = _
  rw [hr, haccG c s]
  by_cases hm : (Hw.abs σ).marks (rvRoot σ) c s = true
  · rw [hm]
    by_cases hv : σ.regs (Hw.dcapV c s) 1 = 1#1
    · have his : (((Hw.abs σ).doms c).caps s).isSome = true := by
        unfold Hw.abs Hw.absDom
        simp [hv]
      simp [hv, his]
    · have hv0 := bv1_ne_one.mp hv
      have his : (((Hw.abs σ).doms c).caps s).isSome = false := by
        unfold Hw.abs Hw.absDom
        simp [hv0]
      simp [hv0, his]
  · have hm0 := Bool.eq_false_of_not_eq_true hm
    simp [hm0]

/-- Structural cell writes implement `destroyMarked`'s `cellDead` mask. -/
theorem revStructuralA_run_cellV_semantic (σ acc : Loom.Hw.St)
    (hrv : RvSync σ) (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (c : DomainId) (l : LineageId) :
    (revStructuralA.run σ acc).regs (Hw.dcellV c l) 1 =
      if (List.finRange numSlots).any (fun s =>
          (Hw.abs σ).marks (rvRoot σ) c s &&
          match ((Hw.abs σ).doms c).caps s with
          | some e => e.lineage == some l
          | none => false)
      then 0#1 else acc.regs (Hw.dcellV c l) 1 := by
  rw [revStructuralA_run_cellV]
  have hc := revCellCond_eval σ hrv hifv hopc hcl c l
  by_cases hd : (List.finRange numSlots).any (fun s =>
      (Hw.abs σ).marks (rvRoot σ) c s &&
      match ((Hw.abs σ).doms c).caps s with
      | some e => e.lineage == some l
      | none => false) = true
  · rw [if_pos hd, if_pos]
    · apply hc.mpr
      rw [List.any_eq_true] at hd
      obtain ⟨s, _, hs⟩ := hd
      rw [Bool.and_eq_true_iff] at hs
      cases hcap : ((Hw.abs σ).doms c).caps s with
      | none => simp [hcap] at hs
      | some e =>
          have hlin : e.lineage = some l := by
            simpa [hcap] using hs.2
          exact ⟨s, e, hs.1, hcap, hlin⟩
  · rw [if_neg hd, if_neg]
    intro hcond
    have hex := hc.mp hcond
    obtain ⟨s, e, hm, hcap, hlin⟩ := hex
    apply hd
    rw [List.any_eq_true]
    refine ⟨s, List.mem_finRange s, ?_⟩
    simp [hm, hcap, hlin]

/-- The complete structural revoke walk decodes to `destroyMarked` on every
domain.  The accumulator may differ from the sampled state in unrelated
fields (notably refill bookkeeping); only the capability-table view and the
two sampled write banks must still agree. -/
theorem absDom_revStructuralA (σ acc : Loom.Hw.St)
    (hrv : RvSync σ) (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (haccV : ∀ c s, acc.regs (Hw.dcapV c s) 1 =
      σ.regs (Hw.dcapV c s) 1)
    (haccG : ∀ c s, acc.regs (Hw.dgen c s) 8 =
      σ.regs (Hw.dgen c s) 8)
    (hcaps : ∀ c, ((Hw.abs acc).doms c).caps =
      ((Hw.abs σ).doms c).caps)
    (c : DomainId) :
    Hw.absDom (revStructuralA.run σ acc) c =
      (((Hw.abs acc).destroyMarked
        ((Hw.abs σ).marks (rvRoot σ))).doms c) := by
  let out := revStructuralA.run σ acc
  apply domainState_ext
  · funext r
    change out.regs (Hw.dreg c r) 32 = acc.regs (Hw.dreg c r) 32
    apply frame
    fin_cases c <;> fin_cases r <;> decide +kernel
  · change out.regs (Hw.dpc c) 12 = acc.regs (Hw.dpc c) 12
    apply frame
    fin_cases c <;> decide +kernel
  · funext s
    rw [destroyMarked_caps]
    change (if out.regs (Hw.dcapV c s) 1 = 1#1 then
        some (⟨Hw.decKind (out.regs (Hw.dcapKind c s) 32),
          if out.regs (Hw.dcapLinV c s) 1 = 1#1 then
            some (finOfBv (by decide) (out.regs (Hw.dcapLin c s) 4))
          else none⟩ : CapEntry)
      else none) = _
    have hkind : out.regs (Hw.dcapKind c s) 32 =
        acc.regs (Hw.dcapKind c s) 32 := by
      apply frame
      fin_cases c <;> fin_cases s <;> decide +kernel
    have hlinV : out.regs (Hw.dcapLinV c s) 1 =
        acc.regs (Hw.dcapLinV c s) 1 := by
      apply frame
      fin_cases c <;> fin_cases s <;> decide +kernel
    have hlin : out.regs (Hw.dcapLin c s) 4 =
        acc.regs (Hw.dcapLin c s) 4 := by
      apply frame
      fin_cases c <;> fin_cases s <;> decide +kernel
    rw [revStructuralA_run_v_semantic σ acc hrv hifv hopc hcl
      haccV c s, hkind, hlinV, hlin]
    by_cases hm : (Hw.abs σ).marks (rvRoot σ) c s = true
    · simp [hm]
    · have hm0 := Bool.eq_false_of_not_eq_true hm
      simp [hm0]
      rfl
  · funext s
    rw [destroyMarked_slotGen]
    change out.regs (Hw.dgen c s) 8 = _
    rw [revStructuralA_run_gen_semantic σ acc hrv hifv hopc hcl
      haccV haccG c s, ← hcaps c]
    change (if (Hw.abs σ).marks (rvRoot σ) c s &&
          (((Hw.abs acc).doms c).caps s).isSome
        then bumpGen (acc.regs (Hw.dgen c s) 8)
        else acc.regs (Hw.dgen c s) 8) =
      if (Hw.abs σ).marks (rvRoot σ) c s &&
          (((Hw.abs acc).doms c).caps s).isSome
        then bumpGen (acc.regs (Hw.dgen c s) 8)
        else acc.regs (Hw.dgen c s) 8
    rfl
  · funext l
    change (if out.regs (Hw.dcellV c l) 1 = 1#1 then
        some (LineageCell.mk (Hw.decRef (out.regs (Hw.dcellPar c l) 14)))
      else none) = _
    have hpar : out.regs (Hw.dcellPar c l) 14 =
        acc.regs (Hw.dcellPar c l) 14 := by
      apply frame
      fin_cases c <;> fin_cases l <;> decide +kernel
    have hdead :
        (List.finRange numSlots).any (fun s =>
          (Hw.abs σ).marks (rvRoot σ) c s &&
          match ((Hw.abs σ).doms c).caps s with
          | some e => e.lineage == some l
          | none => false) =
        (List.finRange numSlots).any (fun s =>
          (Hw.abs σ).marks (rvRoot σ) c s &&
          match ((Hw.abs acc).doms c).caps s with
          | some e => e.lineage == some l
          | none => false) := by
      rw [hcaps c]
    rw [revStructuralA_run_cellV_semantic σ acc hrv hifv hopc hcl c l,
      hpar, hdead]
    change (if (if (List.finRange numSlots).any (fun s =>
          (Hw.abs σ).marks (rvRoot σ) c s &&
          match ((Hw.abs acc).doms c).caps s with
          | some e => e.lineage == some l
          | none => false) then 0#1 else acc.regs (Hw.dcellV c l) 1) = 1#1
        then some (LineageCell.mk (Hw.decRef (acc.regs (Hw.dcellPar c l) 14)))
        else none) =
      if (List.finRange numSlots).any (fun s =>
          (Hw.abs σ).marks (rvRoot σ) c s &&
          match ((Hw.abs acc).doms c).caps s with
          | some e => e.lineage == some l
          | none => false)
        then none else ((Hw.abs acc).doms c).lineage l
    by_cases hd : (List.finRange numSlots).any (fun s =>
        (Hw.abs σ).marks (rvRoot σ) c s &&
        match ((Hw.abs acc).doms c).caps s with
        | some e => e.lineage == some l
        | none => false) = true
    · simp [hd]
    · have hd0 := Bool.eq_false_of_not_eq_true hd
      simp [hd0]
      rfl
  · funext r
    change (if out.regs (Hw.drgnV c r) 1 = 1#1 then
        some (Hw.decRegion (out.regs (Hw.drgn c r) 42)) else none) = _
    have hv : out.regs (Hw.drgnV c r) 1 = acc.regs (Hw.drgnV c r) 1 := by
      apply frame
      fin_cases c <;> fin_cases r <;> decide +kernel
    have hr : out.regs (Hw.drgn c r) 42 = acc.regs (Hw.drgn c r) 42 := by
      apply frame
      fin_cases c <;> fin_cases r <;> decide +kernel
    rw [hv, hr]
    rfl
  · rw [destroyMarked_run]
    change Hw.decRun (out.regs (Hw.drun c) 2)
      (out.regs (Hw.drunG c) 2) = _
    have hrun : out.regs (Hw.drun c) 2 = acc.regs (Hw.drun c) 2 := by
      apply frame
      fin_cases c <;> decide +kernel
    have hrunG : out.regs (Hw.drunG c) 2 = acc.regs (Hw.drunG c) 2 := by
      apply frame
      fin_cases c <;> decide +kernel
    rw [hrun, hrunG]
    change Hw.decRun (acc.regs (Hw.drun c) 2)
      (acc.regs (Hw.drunG c) 2) =
      Hw.decRun (acc.regs (Hw.drun c) 2) (acc.regs (Hw.drunG c) 2)
    rfl
  · change (if out.regs (Hw.dsrvV c) 1 = 1#1 then
        some (finOfBv (by decide) (out.regs (Hw.dsrv c) 2)) else none) = _
    have hv : out.regs (Hw.dsrvV c) 1 = acc.regs (Hw.dsrvV c) 1 := by
      apply frame
      fin_cases c <;> decide +kernel
    have hs : out.regs (Hw.dsrv c) 2 = acc.regs (Hw.dsrv c) 2 := by
      apply frame
      fin_cases c <;> decide +kernel
    rw [hv, hs]
    rfl
  · change out.regs (Hw.dcause c) 32 = acc.regs (Hw.dcause c) 32
    apply frame
    fin_cases c <;> decide +kernel
  · change (out.regs (Hw.dbudget c) 32).toNat =
      (acc.regs (Hw.dbudget c) 32).toNat
    congr 1
    apply frame
    fin_cases c <;> decide +kernel
  · change (out.regs (Hw.dmaxdon c) 32).toNat =
      (acc.regs (Hw.dmaxdon c) 32).toNat
    congr 1
    apply frame
    fin_cases c <;> decide +kernel

/-- Destroying a reference known to be live makes it dead exactly when its
slot is selected by the mark set. -/
theorem destroyMarked_liveRef_false_iff_of_live (tau : MachineState)
    (marked : DomainId → Slot → Bool) (r : CapRef)
    (hlive : tau.liveRef r = true) :
    (tau.destroyMarked marked).liveRef r = false ↔
      marked r.dom r.slot = true := by
  by_cases hm : marked r.dom r.slot = true
  · unfold MachineState.liveRef DomainState.liveCap
    rw [destroyMarked_caps, destroyMarked_slotGen]
    simp [hm]
  · have hm0 := Bool.eq_false_of_not_eq_true hm
    have heq : (tau.destroyMarked marked).liveRef r = tau.liveRef r := by
      unfold MachineState.liveRef DomainState.liveCap
      rw [destroyMarked_caps, destroyMarked_slotGen]
      simp [hm0]
    rw [heq, hlive, hm0]
    decide

/-- The dynamic region-backing lookup used by the revoke sweep decodes to
the corresponding abstract backing domain and slot. -/
theorem revKilled_region_eval (σ acc : Loom.Hw.St) (hrv : RvSync σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (c : DomainId) (r : RegionId)
    (hword : acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42) :
    ((Hw.revKilled
      (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
      (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval σ = 1#1) ↔
      (Hw.abs σ).marks (rvRoot σ)
        (Hw.decRegion (acc.regs (Hw.drgn c r) 42)).backing.dom
        (Hw.decRegion (acc.regs (Hw.drgn c r) 42)).backing.slot = true := by
  rw [revKilled_eval σ hrv hifv hopc hcl]
  have hdom : finOfBv (by decide)
      ((Hw.field (.reg 42 (Hw.drgn c r)) 40 2).eval σ) =
      (Hw.decRegion (acc.regs (Hw.drgn c r) 42)).backing.dom := by
    rw [hword]
    unfold Hw.field Hw.decRegion Hw.decRef finOfBv
    simp only [Expr.eval]
    rw [extractLsb'_extractLsb' _ 28 12 (by omega)]
  have hslot : finOfBv (by decide)
      ((Hw.field (.reg 42 (Hw.drgn c r)) 36 4).eval σ) =
      (Hw.decRegion (acc.regs (Hw.drgn c r) 42)).backing.slot := by
    rw [hword]
    unfold Hw.field Hw.decRegion Hw.decRef finOfBv
    simp only [Expr.eval]
    rw [extractLsb'_extractLsb' _ 28 8 (by omega)]
  rw [hdom, hslot]

/-- Composing the structural revoke walk with the region sweep implements
`destroyMarked` followed by the kernel region-authority sweep. -/
theorem absDom_revStructuralRegionsA (σ acc : Loom.Hw.St)
    (hrv : RvSync σ) (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (haccV : ∀ c s, acc.regs (Hw.dcapV c s) 1 =
      σ.regs (Hw.dcapV c s) 1)
    (haccG : ∀ c s, acc.regs (Hw.dgen c s) 8 =
      σ.regs (Hw.dgen c s) 8)
    (hcaps : ∀ c, ((Hw.abs acc).doms c).caps =
      ((Hw.abs σ).doms c).caps)
    (hrgnV : ∀ c r, acc.regs (Hw.drgnV c r) 1 =
      σ.regs (Hw.drgnV c r) 1)
    (hrgn : ∀ c r, acc.regs (Hw.drgn c r) 42 =
      σ.regs (Hw.drgn c r) 42)
    (hwf : Wf (Hw.abs acc)) (c : DomainId) :
    Hw.absDom ((Hw.sweepRegionsA Hw.revKilled).run σ
      (revStructuralA.run σ acc)) c =
      (((((Hw.abs acc).destroyMarked
        ((Hw.abs σ).marks (rvRoot σ))).sweepRegions).doms c)) := by
  let str := revStructuralA.run σ acc
  apply absDom_sweepRegionsA_of_doms σ str Hw.revKilled
    ((Hw.abs acc).destroyMarked ((Hw.abs σ).marks (rvRoot σ)))
  · funext d
    exact absDom_revStructuralA σ acc hrv hifv hopc hcl haccV haccG hcaps d
  · intro d r
    change str.regs (Hw.drgnV d r) 1 = σ.regs (Hw.drgnV d r) 1
    rw [frame (by
      fin_cases d <;> fin_cases r <;> decide +kernel) σ acc]
    exact hrgnV d r
  · intro d r hv
    have hvframe : str.regs (Hw.drgnV d r) 1 =
        acc.regs (Hw.drgnV d r) 1 := by
      apply frame
      fin_cases d <;> fin_cases r <;> decide +kernel
    have hvacc : acc.regs (Hw.drgnV d r) 1 = 1#1 := by
      rw [← hvframe]
      exact hv
    have hwframe : str.regs (Hw.drgn d r) 42 =
        acc.regs (Hw.drgn d r) 42 := by
      apply frame
      fin_cases d <;> fin_cases r <;> decide +kernel
    have hregion : ((Hw.abs acc).doms d).regions r =
        some (Hw.decRegion (acc.regs (Hw.drgn d r) 42)) := by
      unfold Hw.abs Hw.absDom
      simp [hvacc]
    have hlive : (Hw.abs acc).liveRef
        (Hw.decRegion (acc.regs (Hw.drgn d r) 42)).backing = true :=
      regionBacking_live hwf hregion
    rw [hwframe, revKilled_region_eval σ acc hrv hifv hopc hcl d r
      (hrgn d r)]
    exact (destroyMarked_liveRef_false_iff_of_live (Hw.abs acc)
      ((Hw.abs σ).marks (rvRoot σ))
      (Hw.decRegion (acc.regs (Hw.drgn d r) 42)).backing hlive).symm

/-- The full successful revoke payload, up to the separate Mover phase,
decodes to structural destruction, region sweeping, result-register zero,
and retirement PC advance. -/
theorem absDom_revSuccessA (σ acc : Loom.Hw.St)
    (hrv : RvSync σ) (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (haccV : ∀ c s, acc.regs (Hw.dcapV c s) 1 =
      σ.regs (Hw.dcapV c s) 1)
    (haccG : ∀ c s, acc.regs (Hw.dgen c s) 8 =
      σ.regs (Hw.dgen c s) 8)
    (hcaps : ∀ c, ((Hw.abs acc).doms c).caps =
      ((Hw.abs σ).doms c).caps)
    (hrgnV : ∀ c r, acc.regs (Hw.drgnV c r) 1 =
      σ.regs (Hw.drgnV c r) 1)
    (hrgn : ∀ c r, acc.regs (Hw.drgn c r) 42 =
      σ.regs (Hw.drgn c r) 42)
    (hpc : ∀ c, acc.regs (Hw.dpc c) 12 = σ.regs (Hw.dpc c) 12)
    (hwf : Wf (Hw.abs acc)) (E : DomainId) (RD : RegId)
    (hrd : (Hw.rdE.eval σ).toNat = RD.val) (c : DomainId) :
    Hw.absDom ((revSuccessA E).run σ acc) c =
      let tau := ((Hw.abs acc).destroyMarked
        ((Hw.abs σ).marks (rvRoot σ))).sweepRegions
      if c = E then
        ({ tau.doms E with pc := (tau.doms E).pc + 1 }).setReg RD 0
      else tau.doms c := by
  let str := revStructuralA.run σ acc
  let swept := (Hw.sweepRegionsA Hw.revKilled).run σ str
  let tau := ((Hw.abs acc).destroyMarked
    ((Hw.abs σ).marks (rvRoot σ))).sweepRegions
  have habs : ∀ d, Hw.absDom swept d = tau.doms d := by
    intro d
    exact absDom_revStructuralRegionsA σ acc hrv hifv hopc hcl
      haccV haccG hcaps hrgnV hrgn hwf d
  have hpcStr : str.regs (Hw.dpc E) 12 = acc.regs (Hw.dpc E) 12 := by
    apply frame
    fin_cases E <;> decide +kernel
  have hpcSwept : swept.regs (Hw.dpc E) 12 = σ.regs (Hw.dpc E) 12 := by
    change ((Hw.sweepRegionsA Hw.revKilled).run σ str).regs
      (Hw.dpc E) 12 = _
    rw [sweepRegionsA_frame_width σ str Hw.revKilled (Hw.dpc E) 12
      (by decide), hpcStr, hpc E]
  have htail := absDom_regPcTailA σ swept E (.lit 0) RD 0
    hrd (by rfl) hpcSwept c
  change Hw.absDom ((Act.seq (Hw.writeReg E Hw.rdE (.lit 0))
    (Hw.pcAdvA E)).run σ swept) c = _ at htail
  rw [habs E, habs c] at htail
  have hrun : (revSuccessA E).run σ acc =
      (Hw.seqAll [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E]).run σ swept := by
    unfold revSuccessA
    rw [show revNodeIx.map revNodeA ++ revCellIx.map revCellA ++
        [Hw.sweepRegionsA Hw.revKilled, Hw.writeReg E Hw.rdE (.lit 0),
          Hw.pcAdvA E] =
        (revNodeIx.map revNodeA ++ revCellIx.map revCellA ++
          [Hw.sweepRegionsA Hw.revKilled]) ++
          [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E] by simp]
    rw [seqAll_append_run]
    dsimp [swept, str, revStructuralA]
    rw [seqAll_append_run]
    rfl
  rw [hrun]
  change Hw.absDom ((Act.seq (Hw.writeReg E Hw.rdE (.lit 0))
    (Hw.pcAdvA E)).run σ swept) c = _
  exact htail

end Machines.Lnp64u.Theorems.RMC
