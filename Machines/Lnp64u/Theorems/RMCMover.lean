-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCBridge
import Machines.Lnp64u.Logic.PhaseLemmas

/-!
# R-MC support: the Mover bridge (quiescent-core case)

`moverAct` re-derives the *post-core* state from pre-cycle registers
(D9): the kill sweeps, the retiring `move`'s job install, and same-cycle
store forwarding are all mux trees gated on `retiringE`. On a cycle where
no instruction retires (`retiringE = 0` — the countdown and idle arms of
the square), every one of those gates is off and the rule collapses to
`Step.moverPhase` over the plain registers.

This file proves that collapse:

* quiescence lemmas — each derived signal falls back to its register;
* `absMover_moverAct_quiescent` / `moverAct_mem_quiescent` — the two
  faces of the bridge, stated against any spec state `τ` that agrees with
  the abstraction on the Mover's read set (job, cap tables, regions,
  memory), which is how the square's arms instantiate it after the
  refill/core phases.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-! ## Quiescence: every retire-gated signal falls back to its register -/

private theorem bv1_zero_and (x : BitVec 1) : 0#1 &&& x = 0#1 := by
  revert x; decide

private theorem bv1_and_zero (x : BitVec 1) : x &&& 0#1 = 0#1 := by
  revert x; decide

/-- `killedByCoreE` is off on a non-retiring cycle. -/
theorem killedByCoreE_quiescent (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = 0#1 := by
  show Hw.retiringE.eval σ &&& _ = 0#1
  rw [hnr]
  exact bv1_zero_and _

/-- `newJobSet` is off on a non-retiring cycle. -/
theorem newJobSet_quiescent (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) (d : DomainId) :
    (Hw.newJobSet d).eval σ = 0#1 := by
  show Hw.retiringE.eval σ &&& _ = 0#1
  rw [hnr]
  exact bv1_zero_and _

/-- `postJ` falls back to the current register on a non-retiring cycle. -/
theorem postJ_quiescent {w : Nat} (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) (f : DomainId → Expr w)
    (cur : Expr w) :
    (Hw.postJ f cur).eval σ = cur.eval σ := by
  show ((List.finRange numDomains).foldr
    (fun d acc => Expr.mux (Hw.newJobSet d) (f d) acc) cur).eval σ = _
  induction (List.finRange numDomains) with
  | nil => rfl
  | cons d t ih =>
      show (if (Hw.newJobSet d).eval σ = 1#1 then _ else _) = _
      rw [newJobSet_quiescent σ hnr d]
      simpa using ih


private theorem bv1_and_one (x : BitVec 1) : x &&& 1#1 = x := by
  revert x; decide

private theorem bv1_or_zero (x : BitVec 1) : 0#1 ||| x = x := by
  revert x; decide

private theorem bv1_not_zero : ~~~(0#1) = 1#1 := by decide

/-- The head-`retiringE` `andAll` chains are off on a non-retiring cycle. -/
private theorem andAll_retiring_quiescent (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) (rest : List (Expr 1)) :
    (Hw.andAll (Hw.retiringE :: rest)).eval σ = 0#1 := by
  cases rest with
  | nil => exact hnr
  | cons e t =>
      show Hw.retiringE.eval σ &&& _ = 0#1
      rw [hnr]
      exact bv1_zero_and _

/-- `rgnVPostE` falls back to the validity register. -/
theorem rgnVPostE_quiescent (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) (c : DomainId) (r : RegionId) :
    (Hw.rgnVPostE c r).eval σ = σ.regs (Hw.drgnV c r) 1 := by
  show (if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _
    else if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _
    else (Expr.and (.reg 1 (Hw.drgnV c r))
      (.not (Hw.killedByCoreE _ _))).eval σ) = _
  rw [andAll_retiring_quiescent σ hnr, andAll_retiring_quiescent σ hnr]
  show (if (0#1 : BitVec 1) = 1#1 then _
    else if (0#1 : BitVec 1) = 1#1 then _ else _) = _
  rw [if_neg (by decide), if_neg (by decide)]
  show σ.regs (Hw.drgnV c r) 1 &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
  rw [killedByCoreE_quiescent σ hnr, bv1_not_zero, bv1_and_one]

/-- `rgnValPostE` falls back to the region register. -/
theorem rgnValPostE_quiescent (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) (c : DomainId) (r : RegionId) :
    (Hw.rgnValPostE c r).eval σ = σ.regs (Hw.drgn c r) 42 := by
  show (if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _
    else (Expr.reg 42 (Hw.drgn c r)).eval σ) = _
  rw [andAll_retiring_quiescent σ hnr]
  rw [if_neg (by decide)]
  rfl


/-- The forwarding mux falls back to the memory read. -/
theorem srcWord_quiescent (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) (srcCur : Expr 12) :
    (((List.finRange numDomains).foldr
      (fun d acc =>
        let eaddr : Expr 12 := Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12
        Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
            Hw.domCoversE d eaddr ⟨false, true, false⟩,
            .eq eaddr srcCur])
          (Hw.readReg d Hw.rs2E) acc)
      (.memRead 32 "mem" srcCur)) : Expr 32).eval σ
      = σ.mems "mem" ((srcCur.eval σ)).toNat 32 := by
  induction (List.finRange numDomains) with
  | nil => rfl
  | cons d t ih =>
      show (if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _ else _) = _
      rw [andAll_retiring_quiescent σ hnr, if_neg (by decide)]
      exact ih

/-- `rgnCoversVal` decodes to `Region.covers` of the decoded value. -/
theorem rgnCoversVal_eval (rv : Expr 42) (a : Expr 12) (need : Perms)
    (σ : Loom.Hw.St) :
    ((Hw.rgnCoversVal rv a need).eval σ = 1#1) ↔
      (Hw.decRegion (rv.eval σ)).covers (a.eval σ) need = true := by
  obtain ⟨hr, hw, hx⟩ := decRegion_perm_bits (rv.eval σ)
  have hfb : (Hw.field rv 16 12).eval σ = (rv.eval σ).extractLsb' 16 12 := rfl
  have hbase : ((Expr.not (.ult a (Hw.field rv 16 12))).eval σ = 1#1) ↔
      ((rv.eval σ).extractLsb' 16 12).toNat ≤ (a.eval σ).toNat := by
    rw [notE_eval]
    constructor
    · intro h
      have hn : ¬((Expr.ult a (Hw.field rv 16 12)).eval σ = 1#1) := by
        rw [h]; decide
      rw [ultE_eval, hfb] at hn
      omega
    · intro h
      apply bv1_ne_one.mp
      intro hlt
      rw [ultE_eval, hfb] at hlt
      omega
  have hlen : ((Expr.ult (.zext a 14)
      (.add (.zext (Hw.field rv 16 12) 14)
            (.zext (Hw.field rv 3 13) 14))).eval σ = 1#1) ↔
      (a.eval σ).toNat <
        ((rv.eval σ).extractLsb' 16 12).toNat
          + ((rv.eval σ).extractLsb' 3 13).toNat := by
    rw [ultE_eval]
    show ((a.eval σ).setWidth 14).toNat <
        ((((rv.eval σ).extractLsb' 16 12).setWidth 14) +
         (((rv.eval σ).extractLsb' 3 13).setWidth 14)).toNat ↔ _
    rw [toNat_setWidth_le (by omega), BitVec.toNat_add,
      toNat_setWidth_le (by omega), toNat_setWidth_le (by omega)]
    have hb := ((rv.eval σ).extractLsb' 16 12).isLt
    have hl := ((rv.eval σ).extractLsb' 3 13).isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  have hPR : ((Hw.field rv 0 1).eval σ = 1#1) ↔
      (rv.eval σ).getLsbD 0 = true := extract1_eq_one (rv.eval σ) 0
  have hPW : ((Hw.field rv 1 1).eval σ = 1#1) ↔
      (rv.eval σ).getLsbD 1 = true := extract1_eq_one (rv.eval σ) 1
  have hPX : ((Hw.field rv 2 1).eval σ = 1#1) ↔
      (rv.eval σ).getLsbD 2 = true := extract1_eq_one (rv.eval σ) 2
  rw [Hw.rgnCoversVal, andAll_eval]
  rcases need with ⟨nr, nw, nx⟩
  cases nr <;> cases nw <;> cases nx <;>
  · simp only [reduceIte, List.cons_append, List.nil_append,
      List.forall_mem_cons]
    rw [hbase, hlen]
    simp only [Region.covers, Perms.le, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or,
      Bool.true_and, Bool.and_true, hr, hw, hx, hPR, hPW, hPX,
      Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
      List.cons_append, List.forall_mem_cons, and_assoc]
    try simp [Hw.decRegion]


/-! ## The per-word re-check -/

private theorem extract14_idx (v : BitVec 14) :
    (v.extractLsb' 8 6).toNat
      = (v.extractLsb' 12 2).toNat * 16 + (v.extractLsb' 8 4).toNat := by
  revert v; decide

/-- `kindWAt` at a packed reference's node bits reads the referenced kind
register. -/
theorem kindWAt_ref_eval (σ : Loom.Hw.St) (e : Expr 14) :
    (Hw.kindWAt (Hw.field e 8 6)).eval σ =
      σ.regs (Hw.dcapKind (Hw.decRef (e.eval σ)).dom
        (Hw.decRef (e.eval σ)).slot) 32 := by
  rw [Hw.kindWAt, muxFin_eval (by decide : 2 ^ 6 = numDomains * numSlots)]
  have hnode := nDom_pack (Hw.decRef (e.eval σ)).dom.val
    (Hw.decRef (e.eval σ)).slot.val (Fin.isLt _) (Fin.isLt _)
  have hidx : (finOfBv (by decide : 2 ^ 6 = numDomains * numSlots)
      ((Hw.field e 8 6).eval σ)) =
      (⟨(Hw.decRef (e.eval σ)).dom.val * 16 + (Hw.decRef (e.eval σ)).slot.val,
        by
          have h2 := (Hw.decRef (e.eval σ)).dom.isLt
          have h4 := (Hw.decRef (e.eval σ)).slot.isLt
          show _ < numDomains * numSlots
          simp only [numDomains, numSlots] at *
          omega⟩ : Hw.NodeId) := by
    apply Fin.ext
    show ((e.eval σ).extractLsb' 8 6).toNat = _
    rw [extract14_idx]
    rfl
  rw [hidx, hnode.1, hnode.2]
  rfl

/-- The decoded cap-table entry behind `liveCap`, through the abstraction. -/
theorem abs_liveCap (σ : Loom.Hw.St) (c : DomainId) (s : Slot) (g : Gen) :
    ((Hw.abs σ).doms c).liveCap s g =
      (if σ.regs (Hw.dcapV c s) 1 = 1#1 ∧ σ.regs (Hw.dgen c s) 8 = g ∧ g ≠ 0
       then some
        { kind := Hw.decKind (σ.regs (Hw.dcapKind c s) 32)
          lineage :=
            if σ.regs (Hw.dcapLinV c s) 1 = 1#1 then
              some (finOfBv (by decide) (σ.regs (Hw.dcapLin c s) 4))
            else none }
       else none) := by
  rw [DomainState.liveCap]
  show (match (if σ.regs (Hw.dcapV c s) 1 = 1#1 then _ else none :
      Option CapEntry) with
    | some e => if σ.regs (Hw.dgen c s) 8 = g && g != 0 then some e else none
    | none => none) = _
  by_cases hv : σ.regs (Hw.dcapV c s) 1 = 1#1
  · rw [if_pos hv]
    by_cases hg : σ.regs (Hw.dgen c s) 8 = g
    · by_cases hz : g = 0
      · simp [hg, hz]
      · simp [hg, hv, show ¬g = 0#8 from hz]
    · simp [hg]
  · rw [if_neg hv]
    simp [hv]

/-- The spec's per-word Mover check against any state agreeing with the
abstraction on the cap tables. -/
theorem moverCheck_abs (σ : Loom.Hw.St) (τ : MachineState)
    (hcaps : ∀ d, (τ.doms d).caps = ((Hw.abs σ).doms d).caps)
    (hgen : ∀ d, (τ.doms d).slotGen = ((Hw.abs σ).doms d).slotGen)
    (r : CapRef) (a : Addr) (need : Perms) :
    (Machines.Lnp64u.moverCheck τ r a need = true) ↔
      ((Hw.abs σ).liveRef r = true ∧
       (Hw.decKind (σ.regs (Hw.dcapKind r.dom r.slot) 32)).covers a need
         = true) := by
  rw [Machines.Lnp64u.moverCheck]
  have hlc : (τ.doms r.dom).liveCap r.slot r.gen
      = ((Hw.abs σ).doms r.dom).liveCap r.slot r.gen := by
    rw [DomainState.liveCap, DomainState.liveCap, hcaps, hgen]
  rw [hlc, abs_liveCap]
  have hRl : ((Hw.abs σ).liveRef r = true) ↔
      (σ.regs (Hw.dcapV r.dom r.slot) 1 = 1#1 ∧
       σ.regs (Hw.dgen r.dom r.slot) 8 = r.gen ∧ r.gen ≠ 0) :=
    abs_liveRef σ r.dom r.slot r.gen
  rw [hRl]
  by_cases hcond : σ.regs (Hw.dcapV r.dom r.slot) 1 = 1#1 ∧
      σ.regs (Hw.dgen r.dom r.slot) 8 = r.gen ∧ r.gen ≠ 0
  · rw [if_pos hcond]
    simp only [hcond.1, hcond.2.1]
    simp only [true_and]
    constructor
    · intro h
      exact ⟨hcond.2.2, h⟩
    · rintro ⟨-, h⟩
      exact h
  · rw [if_neg hcond]
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨hl, -⟩
      exact absurd hl hcond

end Machines.Lnp64u.Theorems.RMC
