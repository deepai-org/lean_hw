-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
/-!
# Core word types and bit-field kit

Layer-neutral word abbreviations and the extract/insert kit used by the ISA
encoding framework (`Loom.Isa`) and the netlist IR (`Loom.Hw`). Generic over
word width: machines choose their own instruction and data widths. No machine
knowledge lives here.
-/

namespace Loom

/-- A 32-bit word. -/
abbrev Word32 := BitVec 32

/-- An 8-bit word. -/
abbrev Word8 := BitVec 8

namespace Word

/-- Extract a `width`-bit field starting at bit `lo` (LSB-indexed). -/
def extract {n : Nat} (lo width : Nat) (w : BitVec n) : BitVec width :=
  w.extractLsb' lo width

/-- Insert a `width`-bit field into `w` at bit `lo` (LSB-indexed), replacing
the bits previously there. -/
def insert {n : Nat} (lo : Nat) {width : Nat} (f : BitVec width) (w : BitVec n) :
    BitVec n :=
  let mask : BitVec n := (BitVec.allOnes width).setWidth n <<< lo
  (w &&& ~~~mask) ||| ((f.setWidth n) <<< lo)

theorem getLsbD_insert {n : Nat} (lo : Nat) {width : Nat}
    (f : BitVec width) (w : BitVec n) (j : Nat) (hj : j < n) :
    (insert lo f w).getLsbD j =
      if lo ≤ j ∧ j < lo + width then f.getLsbD (j - lo) else w.getLsbD j := by
  simp only [insert, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  by_cases hlo : lo ≤ j
  · by_cases hhi : j < lo + width
    · have h1 : j - lo < width := by omega
      have h2 : ¬ j < lo := by omega
      have h3 : j - lo < n := by omega
      simp [h1, h2, h3, hj, hlo, hhi]
    · have h1 : ¬ (j - lo < width) := by omega
      have h2 : ¬ j < lo := by omega
      simp [h1, h2, hj, hhi, BitVec.getLsbD_of_ge f (j - lo) (by omega)]
  · have h2 : j < lo := by omega
    simp [h2, hj, hlo]

/-- Round-trip: extracting the field just inserted. -/
theorem extract_insert_self {n : Nat} (lo : Nat) {width : Nat}
    (f : BitVec width) (w : BitVec n) (h : lo + width ≤ n) :
    extract lo width (insert lo f w) = f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extract, BitVec.getLsbD_extractLsb']
  rw [getLsbD_insert lo f w (lo + i) (by omega)]
  simp [Nat.add_sub_cancel_left, hi, show lo ≤ lo + i by omega,
    show lo + i < lo + width by omega]

/-- Frame: inserting into a disjoint field leaves an extraction unchanged. -/
theorem extract_insert_of_disjoint {n : Nat} {lo₁ w₁ lo₂ w₂ : Nat}
    (f : BitVec w₂) (w : BitVec n) (hn : lo₁ + w₁ ≤ n)
    (hdisj : lo₁ + w₁ ≤ lo₂ ∨ lo₂ + w₂ ≤ lo₁) :
    extract lo₁ w₁ (insert lo₂ f w) = extract lo₁ w₁ w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extract, BitVec.getLsbD_extractLsb']
  rw [getLsbD_insert lo₂ f w (lo₁ + i) (by omega)]
  have : ¬ (lo₂ ≤ lo₁ + i ∧ lo₁ + i < lo₂ + w₂) := by omega
  simp [this]

end Word
end Loom
