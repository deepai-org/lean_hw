-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCIsa
import Machines.Lnp64u.Theorems.RMCMover
import Machines.Lnp64u.Theorems.RMCCanon

/-!
# R-MC support: per-op value and check bridges

The Stage-1 experiment for the deferred tagless-final refactor
(NEXTSTEPS §6), and its verdict. Each lemma here is one of the
"datapath equivalences" the refactor was meant to collapse — and each
falls in a couple of dozen mechanical lines with the existing bridge
machinery (`encMem_pack`-style packings, `orAll_eval`, bit-slice tests).
The per-op cost center is *not* the datapath values: it is the errno
ladders and the kernel-write structure, which are shared-helper-shaped
(`installA`, `clearSlotA`, `transferA`, the sweeps) and untouched by a
tagless-final source refactor. Decision recorded in NEXTSTEPS §6: keep
the circuits as they are (zero RTL/golden churn) and grow this file plus
the kernel-helper bridges instead.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw Machines.Lnp64u.Isa

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-- Widening is `ofNat` of `toNat`. -/
theorem setWidth_eq_ofNat {n : Nat} (x : BitVec n) (h : n ≤ 32) :
    x.setWidth 32 = BitVec.ofNat 32 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth_le h, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt
    (Nat.pow_le_pow_right (by omega) h))).symm

/-- A decided 1-bit slice test is the source bit. -/
theorem decide_extract1 {n : Nat} (w : BitVec n) (i : Nat) :
    decide (w.extractLsb' i 1 = 1#1) = w.getLsbD i := by
  cases h : w.getLsbD i
  · simp [decide_eq_false_iff_not]
    intro hc
    have := (extract1_eq_one w i).mp hc
    rw [this] at h
    exact absurd h (by simp)
  · simp [decide_eq_true_eq]
    exact (extract1_eq_one w i).mpr h

/-- The handle circuit packs `Handle.encode`. -/
theorem handleE_pack (σ : Loom.Hw.St) (sE : Expr 4) (gE : Expr 8)
    (cE : Expr 1) (cls : CapClass)
    (hcls : cE.eval σ = if cls = .gate then 1#1 else 0#1) :
    (Hw.handleE sE gE cE).eval σ =
      Handle.encode ⟨finOfBv (by decide) (sE.eval σ), gE.eval σ, cls⟩ := by
  show (sE.eval σ).setWidth 32 |||
      (((gE.eval σ).setWidth 32) <<< ((Expr.lit (4:BitVec 32)).eval σ).toNat |||
       ((cE.eval σ).setWidth 32) <<< ((Expr.lit (12:BitVec 32)).eval σ).toNat)
      = _
  rw [show ((Expr.lit (4:BitVec 32)).eval σ).toNat = 4 from rfl,
    show ((Expr.lit (12:BitVec 32)).eval σ).toNat = 12 from rfl, hcls,
    Handle.encode]
  rw [← BitVec.or_assoc]
  congr 2
  rw [setWidth_eq_ofNat _ (by omega)]
  rfl

/-- The narrowing circuit packs the narrowed kind's encoding. -/
theorem narrowKindE_pack (σ : Loom.Hw.St) (kw dw : Expr 32) :
    (Hw.narrowKindE kw dw).eval σ =
      Hw.encKind (.mem ((kw.eval σ).extractLsb' 1 12 + descOff (dw.eval σ))
        (descLen (dw.eval σ)) (descPerms (dw.eval σ))) := by
  show ((((kw.eval σ).extractLsb' 1 12 + (dw.eval σ).extractLsb' 5 12).setWidth 32
      <<< ((Expr.lit (1:BitVec 32)).eval σ).toNat) |||
    (((dw.eval σ).extractLsb' 17 13).setWidth 32
      <<< ((Expr.lit (13:BitVec 32)).eval σ).toNat |||
     ((((dw.eval σ).extractLsb' 2 1).setWidth 32)
      <<< ((Expr.lit (26:BitVec 32)).eval σ).toNat |||
      ((((dw.eval σ).extractLsb' 3 1).setWidth 32)
        <<< ((Expr.lit (27:BitVec 32)).eval σ).toNat |||
       (((dw.eval σ).extractLsb' 4 1).setWidth 32)
        <<< ((Expr.lit (28:BitVec 32)).eval σ).toNat)))) = _
  rw [show ((Expr.lit (1:BitVec 32)).eval σ).toNat = 1 from rfl,
    show ((Expr.lit (13:BitVec 32)).eval σ).toNat = 13 from rfl,
    show ((Expr.lit (26:BitVec 32)).eval σ).toNat = 26 from rfl,
    show ((Expr.lit (27:BitVec 32)).eval σ).toNat = 27 from rfl,
    show ((Expr.lit (28:BitVec 32)).eval σ).toNat = 28 from rfl]
  rw [encMem_pack]
  have hperms : Perms.mk (decide ((dw.eval σ).extractLsb' 2 1 = 1#1))
      (decide ((dw.eval σ).extractLsb' 3 1 = 1#1))
      (decide ((dw.eval σ).extractLsb' 4 1 = 1#1))
      = descPerms (dw.eval σ) := by
    rw [show descPerms (dw.eval σ) = ⟨(dw.eval σ).getLsbD 2,
      (dw.eval σ).getLsbD 3, (dw.eval σ).getLsbD 4⟩ from rfl,
      decide_extract1, decide_extract1, decide_extract1]
  rw [hperms]
  rfl


/-- The free-slot OR-tree is `freeSlot` existence. -/
theorem freeSlotV_eval (σ : Loom.Hw.St) (c : DomainId) :
    ((Hw.freeSlotV c).eval σ = 1#1) ↔
      ((Hw.abs σ).freeSlot c).isSome := by
  rw [Hw.freeSlotV, orAll_eval, MachineState.freeSlot,
    List.find?_isSome]
  constructor
  · rintro ⟨e, hmem, he⟩
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hmem
    refine ⟨s, List.mem_finRange s, ?_⟩
    show ((((Hw.abs σ).doms c).caps s).isNone &&
      (((Hw.abs σ).doms c).slotGen s != genRetired)) = true
    have hsplit : (Hw.freeSlotOk c s).eval σ =
        ((Expr.not (.reg 1 (Hw.dcapV c s))).eval σ &&&
         (Hw.neqE (.reg 8 (Hw.dgen c s)) (.lit 255)).eval σ) := rfl
    rw [hsplit, bv1_and_eq_one] at he
    obtain ⟨h1, h2⟩ := he
    rw [notE_eval] at h1
    have h1' : σ.regs (Hw.dcapV c s) 1 = 0#1 := h1
    rw [neqE_eval] at h2
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne]
    constructor
    · show (if σ.regs (Hw.dcapV c s) 1 = 1#1 then _ else none) = none
      rw [if_neg (fun hc => by rw [hc] at h1'; exact absurd h1' (by decide))]
    · exact h2
  · rintro ⟨s, -, hs⟩
    refine ⟨Hw.freeSlotOk c s, List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩, ?_⟩
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne] at hs
    obtain ⟨h1, h2⟩ := hs
    show ((Expr.not (.reg 1 (Hw.dcapV c s))).eval σ &&&
      (Hw.neqE (.reg 8 (Hw.dgen c s)) (.lit 255)).eval σ) = 1#1
    rw [bv1_and_eq_one]
    constructor
    · rw [notE_eval]
      show σ.regs (Hw.dcapV c s) 1 = 0#1
      apply bv1_ne_one.mp
      intro hc
      have : ((Hw.abs σ).doms c).caps s ≠ none := by
        show (if σ.regs (Hw.dcapV c s) 1 = 1#1 then _ else none) ≠ none
        rw [if_pos hc]
        simp
      exact this h1
    · rw [neqE_eval]
      exact h2


end Machines.Lnp64u.Theorems.RMC
