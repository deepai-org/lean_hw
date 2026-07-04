-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Hw.Enc
import Mathlib.Tactic.IntervalCases

/-!
# R-MC support: encoder/decoder round trips

The `Hw/Enc.lean` bit packings decode back to the spec values they encode.
These are the leaf lemmas of `abs_reset` (decoding the declared reset
values recovers `m.initState`) and of the per-opcode square cases (decoding
a circuit's freshly written field recovers the spec's written value).

Exact-width packings (`encRef`/`decRef`, 14 = 8+4+2 bits) are bijections;
the lossy ones (`decKind` ignores kind-word bits 29–31 and the gate arm's
bits 3+; `decRun` sends the impossible `11` to `.running`) round-trip in
the dec ∘ enc direction, which is the direction `abs` consumes.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Machines.Lnp64u.Hw

/-! ## Small exact packings (kernel-decidable) -/

theorem decPerms_encPerms (p : Perms) : decPerms (encPerms p) = p := by
  rcases p with ⟨r, w, x⟩
  cases r <;> cases w <;> cases x <;> rfl

theorem decRun_encRun (rs : RunState) : decRun (encRun rs) (encRunG rs) = rs := by
  cases rs with
  | running => rfl
  | halted => rfl
  | blocked g => revert g; decide

set_option maxHeartbeats 1000000 in
theorem decRef_encRef (c : CapRef) : decRef (encRef c) = c := by
  obtain ⟨d, s, g⟩ := c
  revert d s g
  decide

set_option maxHeartbeats 1000000 in
theorem encRef_decRef (b : BitVec 14) : encRef (decRef b) = b := by
  revert b
  decide

/-- `finOfBv` undoes the exact-width `Fin` encoding. -/
theorem finOfBv_ofNat {w n : Nat} (h : 2 ^ w = n) (i : Fin n) :
    finOfBv h (BitVec.ofNat w i.val) = i := by
  apply Fin.ext
  show (BitVec.ofNat w i.val).toNat = i.val
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (h ▸ i.isLt)

/-! ## The kind word (32 bits, lossy high bits) -/

theorem decKind_encKind (k : CapKind) : decKind (encKind k) = k := by
  cases k with
  | gate g => revert g; decide
  | mem base len perms =>
      have h0 : (encKind (.mem base len perms)).getLsbD 0 = false := by
        simp [encKind]
      rw [decKind, h0]
      simp only [Bool.false_eq_true, if_false, CapKind.mem.injEq]
      refine ⟨?_, ?_, ?_⟩
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [encKind, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
        interval_cases i <;> simp
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [encKind, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
        interval_cases i <;> simp
      · rw [show BitVec.extractLsb' 26 3 (encKind (.mem base len perms))
            = encPerms perms from ?_]
        · exact decPerms_encPerms perms
        · apply BitVec.eq_of_getLsbD_eq
          intro i hi
          simp only [encKind, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
            BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
          interval_cases i <;> simp

/-! ## The region word (42 = 3+13+12+14 bits, exact) -/

theorem decRegion_encRegion (rg : Region) : decRegion (encRegion rg) = rg := by
  obtain ⟨base, len, perms, backing⟩ := rg
  simp only [decRegion, Region.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [encRegion, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    interval_cases i <;> simp
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [encRegion, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    interval_cases i <;> simp
  · rw [show BitVec.extractLsb' 0 3 (encRegion ⟨base, len, perms, backing⟩)
        = encPerms perms from ?_]
    · exact decPerms_encPerms perms
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [encRegion, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      interval_cases i <;> simp
  · rw [show BitVec.extractLsb' 28 14 (encRegion ⟨base, len, perms, backing⟩)
        = encRef backing from ?_]
    · exact decRef_encRef backing
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [encRegion, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      interval_cases i <;> simp

end Machines.Lnp64u.Theorems.RMC
