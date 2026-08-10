-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CdcContract

/-!
# Coherent multi-bit crossings: why a snapshot works and a raw sampler tears

`CdcContract` (D21) proves the *control* half of a crossing: a toggle plus a
settling chain delivers exactly one destination pulse per source event, for
every metastability oracle. That is enough for a one-bit level and for a
data-plus-handshake payload whose fields are latched before the toggle flips.

It is **not** enough for the pattern a board wrapper reaches for when it wants
to look at a running machine: an independent two-flop chain per observed
value, sampling a signal that keeps changing. Each bit of such a value crosses
on its own schedule, so the destination can assemble a word the source never
held — the classic torn read. The wrapper this file was written for had 35 of
them, several 64 bits wide, and they were safe only because an operator
stopped the core first. Operational discipline is not a property.

This file states both halves of that in one place:

* `sample_coherent_of_stable` — if the source value is **stable** across the
  window the sampling spans, then *every* per-bit arrival, at any cycle in
  that window and under any oracle, reconstructs exactly one source word.
  Coherence needs no assumption about the sampler at all; it needs the source
  to hold still. That is the whole reason a capture register works.
* `torn_read_exists` — a concrete two-bit counter and two per-bit arrival
  times whose reconstruction is a word the source never held, at any cycle.
  The defect is real, not hypothetical, and this is the witness.

The design consequence, and the only one: to observe a running domain
coherently, **capture into a register in the source domain and cross the
capture's toggle**, never the live value. `holdStable` is the register's
half of the argument; composing it with `sample_coherent_of_stable` gives the
crossing its theorem.

Nothing here models two clocks. `τ` is an arbitrary per-bit arrival function
— an adversary that may deliver bits in any order at any cycles in range,
which over-approximates any real sampler including a metastable one. The
physical MTBF assumption is the one `CdcContract` already states.
-/

namespace Loom.Hw.Cdc

/-- `r` is a word a destination could assemble when bit `i` arrives from
source cycle `τ i`. Stated as a predicate rather than a construction: it
characterises *every* word an independent-per-bit sampler could produce, and
`τ` is unconstrained — any order, any cycles in range. -/
def Assembles {w : Nat} (v : Nat → BitVec w) (τ : Nat → Nat) (r : BitVec w) : Prop :=
  ∀ i, i < w → r.getLsbD i = (v (τ i)).getLsbD i

/-- A source value is stable over `[a, b]` when it does not change there. -/
def StableOn {w : Nat} (v : Nat → BitVec w) (a b : Nat) : Prop :=
  ∀ j, a ≤ j → j ≤ b → v j = v a

/-- **Coherence comes from source stability, not from the sampler.** If the
value holds still across the window every bit arrives from, the assembled
word is exactly the source word — whatever order the bits arrived in, and
whatever a metastable first stage did with them. -/
theorem sample_coherent_of_stable {w : Nat} {v : Nat → BitVec w} {τ : Nat → Nat}
    {r : BitVec w} {a b : Nat} (hstable : StableOn v a b)
    (hwin : ∀ i, a ≤ τ i ∧ τ i ≤ b) (hr : Assembles v τ r) :
    r = v a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hr i hi, hstable (τ i) (hwin i).1 (hwin i).2]

/-- A capture register: latch on `C`, hold otherwise. This is the source-side
half of a snapshot crossing. -/
def hold {w : Nat} (C : Nat → Bool) (v : Nat → BitVec w) (init : BitVec w) :
    Nat → BitVec w
  | 0 => init
  | n + 1 => if C n then v n else hold C v init n

/-- Between captures the held word does not change — so it satisfies
`StableOn`, and `sample_coherent_of_stable` applies to it. A destination that
samples `hold` while no capture occurs therefore reads one source word, by
theorem rather than by operator discipline. -/
theorem holdStable {w : Nat} {C : Nat → Bool} {v : Nat → BitVec w}
    {init : BitVec w} {a b : Nat}
    (hquiet : ∀ j, a ≤ j → j < b → C j = false) :
    StableOn (hold C v init) a b := by
  intro j haj hjb
  induction j with
  | zero =>
      have : a = 0 := by omega
      subst this; rfl
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le haj with heq | hlt
      · rw [← heq]
      · have hn : a ≤ n := by omega
        have hstep : C n = false := hquiet n hn (by omega)
        have hs : hold C v init (n + 1) = hold C v init n := by
          simp [hold, hstep]
        rw [hs]
        exact ih hn (by omega)

/-- **The defect, witnessed.** A bus whose bits change *together* — the
everyday case of a value going `0b00 → 0b11` and back, e.g. a flag word
being set and cleared — sampled with bit 0 taken one cycle earlier than
bit 1, assembles `0b01`: a word the source holds at *no* cycle whatsoever.
No metastability is involved; the two bits simply crossed on their own
schedules. This is the pattern the board wrapper used on 35 free-running
values, several of them 64 bits wide. -/
theorem torn_read_exists :
    ∃ (v : Nat → BitVec 2) (τ : Nat → Nat) (r : BitVec 2) (a b : Nat),
      (∀ i, a ≤ τ i ∧ τ i ≤ b) ∧ Assembles v τ r ∧ (∀ n, r ≠ v n) := by
  refine ⟨fun n => if n % 2 = 0 then 0#2 else 3#2,
          fun i => if i = 0 then 1 else 2, 1#2, 1, 2, ?_, ?_, ?_⟩
  · intro i; by_cases h : i = 0 <;> simp [h]
  · intro i hi
    match i, hi with
    | 0, _ => decide
    | 1, _ => decide
  · intro n
    by_cases h : n % 2 = 0
    · simp only [h, if_pos]; decide
    · simp only [h, if_false]; decide

end Loom.Hw.Cdc
