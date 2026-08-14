-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Data.Nat.Bitwise

/-!
# Binary-reflected Gray-code adjacency

This file proves the digital fact used by Gray-pointer clock crossings.  It
does not model analog metastability: it proves that an incrementing pointer's
Gray encoding changes exactly one bit, including finite-width wraparound.

The one-bit statement is expressed without a bespoke Hamming-distance
definition: the XOR of the two encodings is a power of two.  A natural number
whose value is `2 ^ bit` has exactly the single bit `bit` set.
-/

namespace Loom.Hw.Cdc.Gray

/-- Binary-reflected Gray encoding, matching `(value >> 1) ^ value` in the
stock asynchronous FIFO renderer. -/
def encode (value : Nat) : Nat :=
  value ^^^ (value >>> 1)

/-- Right shift distributes over XOR. Kept here because the Gray decoder
proof uses it repeatedly and no hardware-specific fact is involved. -/
theorem shiftRight_xor (left right amount : Nat) :
    (left ^^^ right) >>> amount = (left >>> amount) ^^^ (right >>> amount) := by
  apply Nat.eq_of_testBit_eq
  intro bit
  simp only [Nat.testBit_shiftRight, Nat.testBit_xor]

/-- XOR-prefix decoder after consuming shifts `1 .. steps + 1`. -/
def decodePrefix (gray : Nat) : Nat → Nat
  | 0 => gray
  | steps + 1 => decodePrefix gray steps ^^^ (gray >>> (steps + 1))

/-- The prefix XOR telescopes when its input is a binary-reflected Gray
code. This is the arithmetic theorem used by the compiled controller's
technology-neutral combinational decoder. -/
theorem decodePrefix_encode (value steps : Nat) :
    decodePrefix (encode value) steps = value ^^^ (value >>> (steps + 1)) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [decodePrefix, ih, encode, shiftRight_xor]
      have shifted : value >>> 1 >>> (steps + 1) = value >>> (steps + 2) := by
        rw [← Nat.shiftRight_add]
        congr 1
        omega
      rw [shifted]
      rw [show steps + (1 + 1) = steps + 2 by omega]
      rw [Nat.xor_assoc, Nat.xor_xor_cancel_left]

/-- A width-bounded Gray code decodes to its original binary word after the
full prefix. -/
theorem decodePrefix_encode_width {value width : Nat} (positive : 0 < width)
    (bounded : value < 2 ^ width) :
    decodePrefix (encode value) (width - 1) = value := by
  rw [decodePrefix_encode]
  have shifted : value >>> width = 0 := Nat.shiftRight_eq_zero value width bounded
  simp [Nat.sub_add_cancel (Nat.succ_le_iff.mp positive), shifted]

/-- Structural form of Gray encoding over one binary digit. -/
theorem encode_bit (b : Bool) (n : Nat) :
    encode (Nat.bit b n) = Nat.bit (b != n.testBit 0) (encode n) := by
  calc
    encode (Nat.bit b n) = Nat.bit b n ^^^ n := by
      simp [encode, Nat.bit_shiftRight_one]
    _ = Nat.bit b n ^^^ Nat.bit (n.testBit 0) (n >>> 1) := by
      rw [Nat.bit_testBit_zero_shiftRight_one]
    _ = Nat.bit (b != n.testBit 0) (encode n) := by
      rw [Nat.xor_bit]
      rfl

private theorem testBit_zero_succ (n : Nat) :
    (n + 1).testBit 0 = !n.testBit 0 := by
  rw [Nat.testBit, Nat.shiftRight_zero, Nat.testBit, Nat.shiftRight_zero]
  simp only [Nat.one_and_eq_mod_two]
  cases Nat.mod_two_eq_zero_or_one n with
  | inl h => simp [Nat.add_mod, h]
  | inr h => simp [Nat.add_mod, h]

/-- Successive unbounded Gray codes differ in exactly one bit: their XOR is
a power of two. -/
theorem succ_xor_oneBit (n : Nat) :
    ∃ bit : Nat, encode n ^^^ encode (n + 1) = 2 ^ bit := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      let k := n >>> 1
      have rebuild : Nat.bit (n.testBit 0) k = n :=
        Nat.bit_testBit_zero_shiftRight_one n
      cases parity : n.testBit 0 with
      | false =>
          refine ⟨0, ?_⟩
          have nEq : n = Nat.bit false k := by simpa [parity] using rebuild.symm
          have bitSuccEq : Nat.bit false k + 1 = Nat.bit true k := by
            simp [Nat.bit]
          rw [nEq, bitSuccEq, encode_bit, encode_bit, Nat.xor_bit]
          simp
      | true =>
          have nEq : n = Nat.bit true k := by simpa [parity] using rebuild.symm
          have bitSuccEq : Nat.bit true k + 1 = Nat.bit false (k + 1) := by
            simp [Nat.bit]
            omega
          have kLt : k < n := by
            have nArithmetic : n = 2 * k + 1 := by simpa [Nat.bit] using nEq
            omega
          obtain ⟨bit, adjacent⟩ := ih k kLt
          refine ⟨bit + 1, ?_⟩
          rw [nEq, bitSuccEq, encode_bit, encode_bit, Nat.xor_bit,
            testBit_zero_succ, adjacent]
          simp [Nat.bit, Nat.pow_succ, Nat.mul_comm]

/-- Pointwise form of `succ_xor_oneBit`: there is one bit, and only that bit,
whose Boolean value differs between successive encodings. -/
theorem succ_differs_exactly_one (n : Nat) :
    ∃ bit, ∀ i,
      (encode n).testBit i ≠ (encode (n + 1)).testBit i ↔ i = bit := by
  obtain ⟨bit, adjacent⟩ := succ_xor_oneBit n
  refine ⟨bit, fun i => ?_⟩
  rw [← Bool.xor_iff_ne, ← Nat.testBit_xor, adjacent, Nat.testBit_two_pow]
  simp [eq_comm]

theorem encode_lt_two_pow {value width : Nat} (bound : value < 2 ^ width) :
    encode value < 2 ^ width := by
  exact Nat.xor_lt_two_pow bound
    (lt_of_le_of_lt (Nat.shiftRight_le value 1) bound)

/-- Before finite-width wrap, the unique changing bit is representable in the
declared pointer width. -/
theorem succ_xor_oneBit_within {n width : Nat}
    (bound : n + 1 < 2 ^ width) :
    ∃ bit, bit < width ∧ encode n ^^^ encode (n + 1) = 2 ^ bit := by
  obtain ⟨bit, adjacent⟩ := succ_xor_oneBit n
  refine ⟨bit, ?_, adjacent⟩
  by_contra outside
  have widthLe : width ≤ bit := Nat.le_of_not_gt outside
  have powerLe : 2 ^ width ≤ 2 ^ bit :=
    Nat.pow_le_pow_right (by omega) widthLe
  have nBound : n < 2 ^ width := by omega
  have differenceBound : encode n ^^^ encode (n + 1) < 2 ^ width :=
    Nat.xor_lt_two_pow (encode_lt_two_pow nBound) (encode_lt_two_pow bound)
  rw [adjacent] at differenceBound
  omega

theorem encode_max (width : Nat) (positive : 0 < width) :
    encode (2 ^ width - 1) = 2 ^ (width - 1) := by
  induction width with
  | zero => omega
  | succ width ih =>
      cases width with
      | zero => rfl
      | succ width =>
          have previous := ih (by omega)
          have decomposition :
              2 ^ (Nat.succ (Nat.succ width)) - 1 =
                Nat.bit true (2 ^ (Nat.succ width) - 1) := by
            have powerPositive : 0 < 2 ^ (Nat.succ width) := Nat.two_pow_pos _
            simp [Nat.bit, Nat.pow_succ]
            omega
          rw [decomposition, encode_bit, Nat.testBit_two_pow_sub_one, previous]
          simp [Nat.bit, Nat.pow_succ, Nat.mul_comm]

/-- The finite-width Gray ring changes one representable bit at wraparound
from the all-ones binary pointer to zero. -/
theorem wrap_xor_oneBit (width : Nat) (positive : 0 < width) :
    encode (2 ^ width - 1) ^^^ encode 0 = 2 ^ (width - 1) := by
  rw [encode_max width positive]
  simp [encode]

end Loom.Hw.Cdc.Gray
