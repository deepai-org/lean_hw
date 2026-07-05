-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCFrames
import Machines.Lnp64u.Theorems.RMCEnc

/-!
# R-MC support: expression-level evaluation bridges

The workhorse evaluation lemmas connecting `Hw/Enc.lean`'s `Expr`
combinators to their spec-side meanings:

* `muxFin_eval` — a `muxFin` selection tree evaluates to the selected
  branch (**the** workhorse: every dynamic register-file/cap-table/gate
  lookup in the design goes through it). Requires the index width to be
  exact (`2 ^ iw = n`), which holds for every `Fin`-indexed family in the
  µ design.
* `orAll_eval` / `andAll_eval` — the OR/AND trees as existential/universal
  quantification over the branch list.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

/-! ## Boolean-vector helpers -/

private theorem bv1_or_eq_one (a b : BitVec 1) :
    (a ||| b = 1#1) ↔ (a = 1#1 ∨ b = 1#1) := by
  revert a b; decide

private theorem bv1_and_eq_one (a b : BitVec 1) :
    (a &&& b = 1#1) ↔ (a = 1#1 ∧ b = 1#1) := by
  revert a b; decide

/-! ## The `muxFin` selection tree -/

/-- Chain step: walking the mux chain over a list `l`, the result is the
branch of the selected index provided it occurs in `l`. -/
private theorem muxChain_eval {n iw w : Nat} (h : 2 ^ iw = n)
    (f : Fin n → Expr w) (idx : Expr iw) (σ : Loom.Hw.St) :
    ∀ (l : List (Fin n)) (dflt : Expr w),
      finOfBv h (idx.eval σ) ∈ l →
      (l.foldr (fun i acc =>
          Expr.mux (.eq idx (.lit (BitVec.ofNat iw i.val))) (f i) acc)
        dflt).eval σ = (f (finOfBv h (idx.eval σ))).eval σ
  | [], _, hmem => absurd hmem (List.not_mem_nil)
  | i :: t, dflt, hmem => by
      simp only [List.foldr]
      show (if (if idx.eval σ = BitVec.ofNat iw i.val then 1#1 else 0#1) = 1#1
        then (f i).eval σ else _) = _
      by_cases heq : idx.eval σ = BitVec.ofNat iw i.val
      · have : finOfBv h (idx.eval σ) = i := by
          apply Fin.ext
          show (idx.eval σ).toNat = i.val
          rw [heq, BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
        rw [this]
        simp [heq]
      · have hne : finOfBv h (idx.eval σ) ≠ i := by
          intro hcon
          apply heq
          have : (idx.eval σ).toNat = i.val := congrArg Fin.val hcon
          apply BitVec.eq_of_toNat_eq
          rw [this, BitVec.toNat_ofNat]
          exact (Nat.mod_eq_of_lt (by have := i.isLt; omega)).symm
      -- the head test is false; recurse into the tail
        have hmem' : finOfBv h (idx.eval σ) ∈ t := by
          rcases List.mem_cons.mp hmem with hh | ht
          · exact absurd hh hne
          · exact ht
        simp only [heq, if_false]
        exact muxChain_eval h f idx σ t dflt hmem'

/-- **The `muxFin` evaluation workhorse**: with an exact index width, the
selection tree evaluates to the branch at the decoded index. -/
theorem muxFin_eval {n iw w : Nat} (h : 2 ^ iw = n)
    (f : Fin n → Expr w) (idx : Expr iw) (σ : Loom.Hw.St) :
    (Hw.muxFin f idx).eval σ = (f (finOfBv h (idx.eval σ))).eval σ :=
  muxChain_eval h f idx σ (List.finRange n) (.lit 0)
    (List.mem_finRange _)

/-! ## OR / AND trees -/

theorem orAll_eval (σ : Loom.Hw.St) :
    ∀ (l : List (Expr 1)),
      ((Hw.orAll l).eval σ = 1#1) ↔ (∃ e ∈ l, e.eval σ = 1#1)
  | [] => by simp [Hw.orAll, Expr.eval]
  | [e] => by simp [Hw.orAll]
  | e :: e' :: t => by
      show ((e.eval σ ||| (Hw.orAll (e' :: t)).eval σ) = 1#1) ↔ _
      rw [bv1_or_eq_one, orAll_eval σ (e' :: t)]
      simp

theorem andAll_eval (σ : Loom.Hw.St) :
    ∀ (l : List (Expr 1)),
      ((Hw.andAll l).eval σ = 1#1) ↔ (∀ e ∈ l, e.eval σ = 1#1)
  | [] => by simp [Hw.andAll, Expr.eval]
  | [e] => by simp [Hw.andAll]
  | e :: e' :: t => by
      show ((e.eval σ &&& (Hw.andAll (e' :: t)).eval σ) = 1#1) ↔ _
      rw [bv1_and_eq_one, andAll_eval σ (e' :: t)]
      simp

/-- A 1-bit expression evaluates to `0` or `1`; `≠ 1 ↔ = 0`. -/
theorem bv1_ne_one {b : BitVec 1} : b ≠ 1#1 ↔ b = 0#1 := by
  revert b; decide

/-- `neqE` evaluates to disequality. -/
theorem neqE_eval {w : Nat} (a b : Expr w) (σ : Loom.Hw.St) :
    ((Hw.neqE a b).eval σ = 1#1) ↔ a.eval σ ≠ b.eval σ := by
  show ((~~~(if a.eval σ = b.eval σ then 1#1 else 0#1)) = 1#1) ↔ _
  by_cases h : a.eval σ = b.eval σ <;> simp [h]

/-! ## Bit-field helpers -/

private theorem bv1_eq_one_iff_getLsb (b : BitVec 1) :
    (b = 1#1) ↔ b.getLsbD 0 = true := by
  revert b; decide

/-- A 1-bit slice equals `1` iff the source bit is set. -/
theorem extract1_eq_one {n : Nat} (w : BitVec n) (i : Nat) :
    (w.extractLsb' i 1 = 1#1) ↔ w.getLsbD i = true := by
  rw [bv1_eq_one_iff_getLsb]
  simp

/-- A 1-bit slice equals `0` iff the source bit is clear. -/
theorem extract1_eq_zero {n : Nat} (w : BitVec n) (i : Nat) :
    (w.extractLsb' i 1 = 0#1) ↔ w.getLsbD i = false := by
  constructor
  · intro h
    by_contra hb
    have := (extract1_eq_one w i).mpr (by revert hb; cases w.getLsbD i <;> simp)
    rw [h] at this
    exact absurd this (by decide)
  · intro h
    have : ¬(w.extractLsb' i 1 = 1#1) := by
      rw [extract1_eq_one, h]; simp
    exact bv1_ne_one.mp this

/-! ## The machine-wide node index (`idx6` = dom ∥ slot) -/

private theorem idx6_toNat (dv : BitVec 2) (sv : BitVec 4) :
    ((dv.setWidth 6 <<< (4 : Nat)) ||| sv.setWidth 6).toNat
      = dv.toNat * 16 + sv.toNat := by
  revert dv sv; decide

private theorem idx6_eval (domE : Expr 2) (slotE : Expr 4) (σ : Loom.Hw.St) :
    ((Hw.idx6 domE slotE).eval σ).toNat
      = (domE.eval σ).toNat * 16 + (slotE.eval σ).toNat := by
  show (((domE.eval σ).setWidth 6 <<< ((Expr.lit (4:BitVec 6)).eval σ).toNat)
      ||| (slotE.eval σ).setWidth 6).toNat = _
  rw [show ((Expr.lit (4:BitVec 6)).eval σ).toNat = 4 from rfl]
  exact idx6_toNat _ _

/-- Node lookup decomposition: reading a per-node register family at a
packed `idx6` index is reading it at the decoded (domain, slot). -/
theorem nodeAt_eval {w : Nat} (f : Hw.NodeId → Expr w)
    (domE : Expr 2) (slotE : Expr 4) (σ : Loom.Hw.St) :
    ((Hw.muxFin f (Hw.idx6 domE slotE)).eval σ) =
      (f ⟨(domE.eval σ).toNat * 16 + (slotE.eval σ).toNat, by
        have h2 := (domE.eval σ).isLt
        have h4 := (slotE.eval σ).isLt
        show _ < numDomains * numSlots
        simp only [numDomains, numSlots]
        omega⟩).eval σ := by
  rw [muxFin_eval (by decide : 2 ^ 6 = numDomains * numSlots)]
  have heq : (finOfBv (by decide : 2 ^ 6 = numDomains * numSlots)
      ((Hw.idx6 domE slotE).eval σ)) =
      (⟨(domE.eval σ).toNat * 16 + (slotE.eval σ).toNat, by
        have h2 := (domE.eval σ).isLt
        have h4 := (slotE.eval σ).isLt
        show _ < numDomains * numSlots
        simp only [numDomains, numSlots]
        omega⟩ : Hw.NodeId) :=
    Fin.ext (idx6_eval domE slotE σ)
  rw [heq]

/-- `nDom`/`nSlot` of the packed node. -/
theorem nDom_pack (dn sn : Nat) (h2 : dn < 4) (h4 : sn < 16) :
    Hw.nDom ⟨dn * 16 + sn, by show _ < numDomains * numSlots; simp only [numDomains, numSlots]; omega⟩
        = ⟨dn, h2⟩ ∧
    Hw.nSlot ⟨dn * 16 + sn, by show _ < numDomains * numSlots; simp only [numDomains, numSlots]; omega⟩
        = ⟨sn, h4⟩ := by
  constructor
  · apply Fin.ext
    show (dn * 16 + sn) / 16 = dn
    omega
  · apply Fin.ext
    show (dn * 16 + sn) % 16 = sn
    omega

/-! ## Capability liveness (`liveRefE` ↔ `MachineState.liveRef`) -/

/-- Spec-side unfolding of `liveRef` through the abstraction. -/
theorem abs_liveRef (σ : Loom.Hw.St) (c : DomainId) (s : Slot) (g : Gen) :
    ((Hw.abs σ).liveRef ⟨c, s, g⟩ = true) ↔
      (σ.regs (Hw.dcapV c s) 1 = 1#1 ∧ σ.regs (Hw.dgen c s) 8 = g ∧ g ≠ 0) := by
  show ((((Hw.abs σ).doms c).liveCap s g).isSome = true) ↔ _
  rw [DomainState.liveCap]
  show ((match (if σ.regs (Hw.dcapV c s) 1 = 1#1 then _ else none : Option CapEntry) with
    | some e => if σ.regs (Hw.dgen c s) 8 = g && g != 0 then some e else none
    | none => none).isSome = true) ↔ _
  by_cases hv : σ.regs (Hw.dcapV c s) 1 = 1#1
  · rw [if_pos hv]
    by_cases hg : σ.regs (Hw.dgen c s) 8 = g
    · by_cases hz : g = 0
      · simp [hg, hz]
      · simp [hg, hv]
    · simp [hg, hv]
  · rw [if_neg hv]
    simp [hv]

/-- `Expr.eq` evaluates to equality. -/
theorem eqE_eval {w : Nat} (a b : Expr w) (σ : Loom.Hw.St) :
    ((Expr.eq a b).eval σ = 1#1) ↔ a.eval σ = b.eval σ := by
  show ((if a.eval σ = b.eval σ then 1#1 else 0#1) = 1#1) ↔ _
  by_cases h : a.eval σ = b.eval σ <;> simp [h]

/-- The machine-wide liveness circuit decodes to the spec's `liveRef` on
the abstraction. -/
theorem liveRefE_eval (σ : Loom.Hw.St) (domE : Expr 2) (slotE : Expr 4)
    (genE : Expr 8) (c : DomainId) (s : Slot)
    (hc : c.val = (domE.eval σ).toNat) (hs : s.val = (slotE.eval σ).toNat) :
    ((Hw.liveRefE domE slotE genE).eval σ = 1#1) ↔
      (Hw.abs σ).liveRef ⟨c, s, genE.eval σ⟩ = true := by
  have hnode := nDom_pack (domE.eval σ).toNat (slotE.eval σ).toNat
    (domE.eval σ).isLt (slotE.eval σ).isLt
  have hcfin : (⟨(domE.eval σ).toNat, (domE.eval σ).isLt⟩ : DomainId) = c :=
    Fin.ext hc.symm
  have hsfin : (⟨(slotE.eval σ).toNat, (slotE.eval σ).isLt⟩ : Slot) = s :=
    Fin.ext hs.symm
  have hcapV : (Hw.capVAt (Hw.idx6 domE slotE)).eval σ =
      σ.regs (Hw.dcapV c s) 1 := by
    rw [Hw.capVAt, nodeAt_eval]
    show σ.regs (Hw.dcapV (Hw.nDom _) (Hw.nSlot _)) 1 = _
    rw [hnode.1, hnode.2, hcfin, hsfin]
  have hgen : (Hw.genAt (Hw.idx6 domE slotE)).eval σ =
      σ.regs (Hw.dgen c s) 8 := by
    rw [Hw.genAt, nodeAt_eval]
    show σ.regs (Hw.dgen (Hw.nDom _) (Hw.nSlot _)) 8 = _
    rw [hnode.1, hnode.2, hcfin, hsfin]
  rw [show (Hw.liveRefE domE slotE genE).eval σ =
      ((Hw.capVAt (Hw.idx6 domE slotE)).eval σ &&&
       ((Expr.eq (Hw.genAt (Hw.idx6 domE slotE)) genE).eval σ &&&
        (Hw.neqE genE (.lit 0)).eval σ)) from rfl,
    bv1_and_eq_one, bv1_and_eq_one, abs_liveRef, hcapV]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · rw [eqE_eval, hgen]
  · rw [neqE_eval]
    show genE.eval σ ≠ (0 : BitVec 8) ↔ _
    rfl

end Machines.Lnp64u.Theorems.RMC
