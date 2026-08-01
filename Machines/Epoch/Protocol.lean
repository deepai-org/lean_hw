-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Core.Ts
import Mathlib

/-!
# The LNP64 epoch-cell protocol, mechanized (Layer 1)

Normative source: `lnp64_isa.md` §3 ("Epoch cells — the one freshness
primitive, Law 2") and Appendix F, mandatory protocol machine 1 ("Epoch
coherence — bump, broadcast, ack reduction"). Appendix F makes the
mechanized protocol spec *the* behavioral definition; this file is the
candidate normative artifact for that machine, and `Machines/Epoch/
EPOCH_SPEC.md` is the binding scope/obligation document it discharges.

The model, exactly as `EPOCH_SPEC.md` §"Protocol model (Layer 1)" fixes it:

* `N` cells, each `{epoch : BitVec W, rc, poison, dead, occupied}` — `dead`
  is the saturated-forever bit, `occupied` carries §3's empty-slot clause
  (a v1 addition, recorded in `EPOCH_SPEC.md` §Deviations);
* `K` referent volumes, each holding a *replica* of every cell's epoch —
  §3's "a shared cell's epoch is replicated per referent-holding volume";
* at most one bump in flight, with a per-volume ack vector — §3's
  "the architected bump linearizes when that broadcast is acknowledged by
  the tracked referent span".

`use` is §3's single check `ref.epoch == cell.epoch` performed against the
**volume-local replica** (Appendix C class 0: one compare, local,
tile-bounded — never a fabric transaction), with §3's failure precedence
*structural → poison → freshness → rights* exactly.

Everything here is a kernel proof: no `sorry`, no `native_decide`, no new
axioms.
-/

namespace Machines.Epoch.Protocol

open Loom

/-! ## §3 vocabulary -/

/-- The five architected outcomes of an epoch-qualified use. §3 names four
failures (`-BADREF`, `-POISONED`, `-STALE`, `-DENIED`) plus success. -/
inductive Outcome where
  | ok
  | badref
  | poisoned
  | stale
  | denied
  deriving DecidableEq, Repr, Inhabited

/-- §3's bump policies. v1 mechanizes `lazy` and `poison`; `cancel` and
`quiesce` are staged out (they need the park/wake directory and the DMA
drain — `EPOCH_SPEC.md` §Scope). -/
inductive Policy where
  | lazy
  | poison
  deriving DecidableEq, Repr, Inhabited

/-- Does this bump carry §3's `poison` disposition? -/
def Policy.isPoison : Policy → Bool
  | .poison => true
  | .lazy => false

/-- A cell: §3's hardware-owned `{epoch, referent_count}` pair plus the two
dispositions §3 gives it (`poison`, saturated-`dead`) and the slot-occupancy
bit §3's empty-slot clause reads. -/
structure Cell (W : Nat) where
  /-- The home epoch. Saturating, never wrapping (§3). -/
  epoch : BitVec W
  /-- §3's `referent_count`: metadata referents, not object lifetime. -/
  rc : Nat
  /-- §3's `poison` disposition: future references fail, not just stale ones. -/
  poison : Bool
  /-- Saturation is permanent death (§3). -/
  dead : Bool
  /-- Is the indexed slot occupied? (§3's empty-slot clause.) -/
  occupied : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The one in-flight bump: which cell, the epoch being broadcast, its
policy, and the per-volume acknowledgement vector (§3's "acknowledged by the
tracked referent span"). -/
structure Bump (W N K : Nat) where
  /-- The cell whose epoch was incremented. -/
  cell : Fin N
  /-- The new home epoch being broadcast. -/
  target : BitVec W
  /-- The policy this bump carries. -/
  policy : Policy
  /-- Which referent volumes have acknowledged. -/
  acked : Fin K → Bool

/-- Protocol state: `N` cells at their homes (§3's "every cell has a home"),
one epoch replica per referent volume per cell, and at most one bump in
flight. -/
structure St (W N K : Nat) where
  /-- The home cells. -/
  cells : Fin N → Cell W
  /-- `repl k i` is volume `k`'s replica of cell `i`'s epoch. -/
  repl : Fin K → Fin N → BitVec W
  /-- The one in-flight bump, if any (v1: at most one). -/
  pending : Option (Bump W N K)

/-- A presented time-qualified reference plus the structural and rights
facts §3's precedence consults. `cellIx` is a *raw* index: out-of-range is
§3's "malformed/out-of-range is `-BADREF`". -/
structure Req (W : Nat) where
  /-- The raw cell index carried by the handle. -/
  cellIx : Nat
  /-- The reference's inline check value — §3's `ref.epoch`. -/
  epoch : BitVec W
  /-- Handle shape validates (§3: "first validate handle shape/index"). -/
  wellFormed : Bool
  /-- The requested class matches the occupant (§3's second `-BADREF`). -/
  classOk : Bool
  /-- The rights check, which §3 puts strictly last. -/
  rights : Bool
  deriving DecidableEq, Repr, Inhabited

/-! ## The saturating counter (§3's one temporal primitive) -/

/-- The saturation value at width `W`. -/
def maxE (W : Nat) : BitVec W := BitVec.allOnes W

/-- §3's saturating increment: "an epoch counter saturates rather than
wraps". At the maximum the counter stands still — it never rolls to a live
value. -/
def satInc {W : Nat} (e : BitVec W) : BitVec W :=
  if e = maxE W then e else BitVec.ofNat W (e.toNat + 1)

theorem toNat_maxE (W : Nat) : (maxE W).toNat = 2 ^ W - 1 := by
  simp [maxE]

theorem satInc_eq_of_max {W : Nat} {e : BitVec W} (h : e = maxE W) :
    satInc e = e := by simp [satInc, h]

theorem toNat_satInc_of_ne {W : Nat} {e : BitVec W} (h : e ≠ maxE W) :
    (satInc e).toNat = e.toNat + 1 := by
  have h1 : e.toNat < 2 ^ W := e.isLt
  have h2 : e.toNat ≠ 2 ^ W - 1 := fun hEq =>
    h (BitVec.eq_of_toNat_eq (by rw [hEq, toNat_maxE]))
  have hlt : e.toNat + 1 < 2 ^ W := by omega
  simp only [satInc, if_neg h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The counter is monotone at every width. -/
theorem toNat_le_satInc {W : Nat} (e : BitVec W) : e.toNat ≤ (satInc e).toNat := by
  by_cases h : e = maxE W
  · rw [satInc_eq_of_max h]
  · rw [toNat_satInc_of_ne h]; omega

/-- Saturation is a fixed point: once at the maximum the counter cannot
produce anything else (§3: "the counter never rolls to a live value"). -/
theorem satInc_max (W : Nat) : satInc (maxE W) = maxE W := satInc_eq_of_max rfl

/-- The home-side effect of a bump: §3's O(1) increment, saturating into
permanent death, plus the policy's disposition. -/
def Cell.bumped {W : Nat} (c : Cell W) (p : Policy) : Cell W where
  epoch := satInc c.epoch
  rc := c.rc
  poison := c.poison || p.isPoison
  dead := c.dead || (satInc c.epoch = maxE W)
  occupied := c.occupied

/-- Move §3's `referent_count`. -/
def Cell.setRc {W : Nat} (c : Cell W) (n : Nat) : Cell W := { c with rc := n }

@[simp] theorem Cell.bumped_epoch {W : Nat} (c : Cell W) (p : Policy) :
    (c.bumped p).epoch = satInc c.epoch := rfl
@[simp] theorem Cell.bumped_occupied {W : Nat} (c : Cell W) (p : Policy) :
    (c.bumped p).occupied = c.occupied := rfl
@[simp] theorem Cell.bumped_poison {W : Nat} (c : Cell W) (p : Policy) :
    (c.bumped p).poison = (c.poison || p.isPoison) := rfl
@[simp] theorem Cell.bumped_dead {W : Nat} (c : Cell W) (p : Policy) :
    (c.bumped p).dead = (c.dead || decide (satInc c.epoch = maxE W)) := rfl
@[simp] theorem Cell.setRc_epoch {W : Nat} (c : Cell W) (n : Nat) :
    (c.setRc n).epoch = c.epoch := rfl
@[simp] theorem Cell.setRc_poison {W : Nat} (c : Cell W) (n : Nat) :
    (c.setRc n).poison = c.poison := rfl
@[simp] theorem Cell.setRc_dead {W : Nat} (c : Cell W) (n : Nat) :
    (c.setRc n).dead = c.dead := rfl
@[simp] theorem Cell.setRc_occupied {W : Nat} (c : Cell W) (n : Nat) :
    (c.setRc n).occupied = c.occupied := rfl

/-! ## §3's check: the five-outcome `use`

The precedence is **structural → poison → freshness → rights**, with §3's
exact sub-clauses:

* malformed handle / out-of-range index ⇒ `-BADREF`;
* an *empty* slot is `-STALE` when its embedded epoch mismatches and
  `-BADREF` only for a matching-epoch empty reference;
* on an occupied slot, class mismatch ⇒ `-BADREF`;
* poison is inspected **before** comparing epochs, so a poison-marked
  current cell returns `-POISONED` "even when its publishing bump also made
  the handle's epoch unequal";
* then freshness: saturated death and any epoch mismatch ⇒ `-STALE`;
* only "a current live reference reaches the rights check last"
  (`-DENIED`), and only then `ok`.
-/

/-- The class-0 check as the hardware performs it: one compare of the
presented epoch against the **volume-local replica** `re`, plus the cell's
dispositions. Local, tile-bounded, size-independent. -/
def useLocal {W : Nat} (c : Cell W) (re : BitVec W) (r : Req W) : Outcome :=
  if r.wellFormed = false then .badref
  else if c.occupied = false then
    (if re = r.epoch then .badref else .stale)
  else if r.classOk = false then .badref
  else if c.poison = true then .poisoned
  else if c.dead = true then .stale
  else if re ≠ r.epoch then .stale
  else if r.rights = false then .denied
  else .ok

/-- §3's `use`, at volume `k`. Out-of-range indices are structural
`-BADREF`; otherwise the local check runs against volume `k`'s replica. -/
def use {W N K : Nat} (s : St W N K) (k : Fin K) (r : Req W) : Outcome :=
  if h : r.cellIx < N then useLocal (s.cells ⟨r.cellIx, h⟩) (s.repl k ⟨r.cellIx, h⟩) r
  else .badref

/-! ## Transitions -/

/-- The protocol's transition alphabet. `use` is an observation: §3's check
is a pure read, so it is modelled as an enabled stutter step, which is what
lets a run interleave uses with a bump (see `T_E7`). -/
inductive Ev (W N K : Nat) where
  | use (k : Fin K) (r : Req W)
  | bump (i : Fin N) (p : Policy)
  | ack (k : Fin K)
  | bumpReturn
  | acquire (i : Fin N)
  | release (i : Fin N)

/-- The transition function: `none` = the event is disabled in this state.

* `bump` is enabled only when no bump is in flight (v1's one-in-flight
  restriction); it does §3's O(1) home increment, applies the policy's
  disposition, and *starts* the broadcast.
* `ack k` is volume `k` adopting the broadcast epoch — the replica update
  and the ack are the same event, which is what makes the ack meaningful.
* `bumpReturn` is enabled **only when every volume in the referent span has
  acked** — §3's return guarantee: "post-return success through an old
  remote replica is forbidden".
* `acquire`/`release` move §3's `referent_count`. -/
def stepEv {W N K : Nat} (s : St W N K) : Ev W N K → Option (St W N K)
  | .use _ _ => some s
  | .bump i p =>
      match s.pending with
      | some _ => none
      | none =>
          some { s with
            cells := Function.update s.cells i ((s.cells i).bumped p)
            pending := some { cell := i, target := satInc (s.cells i).epoch, policy := p,
                              acked := fun _ => false } }
  | .ack k =>
      match s.pending with
      | none => none
      | some b =>
          some { s with
            repl := Function.update s.repl k
              (Function.update (s.repl k) b.cell b.target)
            pending := some { b with acked := Function.update b.acked k true } }
  | .bumpReturn =>
      match s.pending with
      | none => none
      | some b => if (∀ k, b.acked k = true) then some { s with pending := none } else none
  | .acquire i =>
      some { s with
        cells := Function.update s.cells i ((s.cells i).setRc ((s.cells i).rc + 1)) }
  | .release i =>
      some { s with
        cells := Function.update s.cells i ((s.cells i).setRc ((s.cells i).rc - 1)) }

/-- The step relation. -/
def Step {W N K : Nat} (s s' : St W N K) : Prop := ∃ e, stepEv s e = some s'

/-- Reset states: no bump in flight, no poison, `dead` exactly at
saturation, epoch `0` reserved-invalid (§3), and every replica in step with
its home. -/
structure Init {W N K : Nat} (s : St W N K) : Prop where
  quiet : s.pending = none
  clean : ∀ i, (s.cells i).poison = false
  deadIffMax : ∀ i, (s.cells i).dead = decide ((s.cells i).epoch = maxE W)
  nonzero : ∀ i, (s.cells i).epoch ≠ 0#W
  coherent : ∀ k i, s.repl k i = (s.cells i).epoch

/-- The epoch protocol as a `Loom.TSys` — the shape the Layer-3 refinement
obligation (`Machines/Epoch/Refines.lean`) will consume. -/
def sys (W N K : Nat) : Loom.TSys where
  S := St W N K
  init := Init
  step := Step

/-- Multi-step reachability *from a given state* — the "forever" of §3's
guarantees. -/
abbrev Run {W N K : Nat} (s t : St W N K) : Prop :=
  Relation.ReflTransGen (@Step W N K) s t

/-! ## The inductive invariant -/

/-- The protocol invariant. `coherent` is the *settled* form of §3's return
guarantee: with no bump in flight, every replica equals its home epoch. -/
structure Inv {W N K : Nat} (s : St W N K) : Prop where
  /-- `dead` is exactly saturation. -/
  deadIffMax : ∀ i, (s.cells i).dead = decide ((s.cells i).epoch = maxE W)
  /-- Epoch `0` is reserved-invalid at every width (§3). -/
  nonzero : ∀ i, (s.cells i).epoch ≠ 0#W
  /-- No replica ever runs ahead of its home. -/
  replLe : ∀ k i, (s.repl k i).toNat ≤ ((s.cells i).epoch).toNat
  /-- Settled states are coherent: this is the return guarantee. -/
  coherent : s.pending = none → ∀ k i, s.repl k i = (s.cells i).epoch
  /-- The in-flight bump broadcasts exactly the current home epoch. -/
  pendTarget : ∀ b, s.pending = some b → b.target = (s.cells b.cell).epoch
  /-- A volume that has acked holds the broadcast epoch. -/
  pendAcked : ∀ b, s.pending = some b → ∀ k, b.acked k = true → s.repl k b.cell = b.target
  /-- The bump disturbs no other cell's replicas. -/
  pendOther : ∀ b, s.pending = some b → ∀ k i, i ≠ b.cell → s.repl k i = (s.cells i).epoch

theorem Init.inv {W N K : Nat} {s : St W N K} (h : Init s) : Inv s where
  deadIffMax := h.deadIffMax
  nonzero := h.nonzero
  replLe := fun k i => by rw [h.coherent k i]
  coherent := fun _ => h.coherent
  pendTarget := fun b hb => by rw [h.quiet] at hb; exact absurd hb (by simp)
  pendAcked := fun b hb => by rw [h.quiet] at hb; exact absurd hb (by simp)
  pendOther := fun b hb => by rw [h.quiet] at hb; exact absurd hb (by simp)

/-! ### Per-step facts

Each `Ev` is dispatched by `cases`; `Function.update` bookkeeping is the
only real content. -/

section StepLemmas

variable {W N K : Nat} {s s' : St W N K}

/-- The shape of a single step on the cell table: occupancy is untouched,
the epoch is non-decreasing, and both dispositions are set-only. One case
analysis, four consequences. -/
theorem step_cells_shape (h : Step s s') (i : Fin N) :
    (s'.cells i).occupied = (s.cells i).occupied ∧
    ((s.cells i).epoch).toNat ≤ ((s'.cells i).epoch).toNat ∧
    ((s.cells i).poison = true → (s'.cells i).poison = true) ∧
    ((s.cells i).dead = true → (s'.cells i).dead = true) := by
  obtain ⟨e, he⟩ := h
  cases e with
  | use k r =>
      simp only [stepEv, Option.some.injEq] at he
      subst he; exact ⟨rfl, Nat.le_refl _, id, id⟩
  | bump j p =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he
        subst he
        dsimp only
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self]
          exact ⟨rfl, toNat_le_satInc _, fun hp => by simp [hp], fun hd => by simp [hd]⟩
        · rw [Function.update_of_ne hij]
          exact ⟨rfl, Nat.le_refl _, id, id⟩
  | ack k =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he
        subst he; exact ⟨rfl, Nat.le_refl _, id, id⟩
  | bumpReturn =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · split at he
        · simp only [Option.some.injEq] at he
          subst he; exact ⟨rfl, Nat.le_refl _, id, id⟩
        · exact absurd he (by simp)
  | acquire j =>
      simp only [stepEv, Option.some.injEq] at he
      subst he
      dsimp only
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self]
        exact ⟨rfl, Nat.le_refl _, id, id⟩
      · rw [Function.update_of_ne hij]
        exact ⟨rfl, Nat.le_refl _, id, id⟩
  | release j =>
      simp only [stepEv, Option.some.injEq] at he
      subst he
      dsimp only
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self]
        exact ⟨rfl, Nat.le_refl _, id, id⟩
      · rw [Function.update_of_ne hij]
        exact ⟨rfl, Nat.le_refl _, id, id⟩

/-- Slot occupancy is not a v1 transition target: no step changes it. -/
theorem step_occupied (h : Step s s') (i : Fin N) :
    (s'.cells i).occupied = (s.cells i).occupied := (step_cells_shape h i).1

/-- The home epoch is non-decreasing at every step (half of T-E6). -/
theorem step_epoch_mono (h : Step s s') (i : Fin N) :
    ((s.cells i).epoch).toNat ≤ ((s'.cells i).epoch).toNat := (step_cells_shape h i).2.1

/-- Poison is set-only. -/
theorem step_poison_sticky (h : Step s s') (i : Fin N)
    (hp : (s.cells i).poison = true) : (s'.cells i).poison = true :=
  (step_cells_shape h i).2.2.1 hp

/-- Death is set-only: no bump revives a saturated cell. -/
theorem step_dead_sticky (h : Step s s') (i : Fin N)
    (hd : (s.cells i).dead = true) : (s'.cells i).dead = true :=
  (step_cells_shape h i).2.2.2 hd

/-- Replicas are non-decreasing (the other half of T-E6). Needs the
invariant: a replica adopts the broadcast epoch, which `Inv.replLe` and
`Inv.pendTarget` place at or above it. -/
theorem step_repl_mono (hi : Inv s) (h : Step s s') (k : Fin K) (i : Fin N) :
    (s.repl k i).toNat ≤ (s'.repl k i).toNat := by
  obtain ⟨e, he⟩ := h
  cases e with
  | use a b => simp only [stepEv, Option.some.injEq] at he; subst he; exact Nat.le_refl _
  | bump j p =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he; subst he; exact Nat.le_refl _
  | ack k' =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · rename_i b hb
        simp only [Option.some.injEq] at he
        subst he
        dsimp only
        by_cases hk : k = k'
        · subst hk
          by_cases hc : i = b.cell
          · subst hc
            rw [Function.update_self, Function.update_self, hi.pendTarget b hb]
            exact hi.replLe k b.cell
          · rw [Function.update_self, Function.update_of_ne hc]
        · rw [Function.update_of_ne hk]
  | bumpReturn =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · split at he
        · simp only [Option.some.injEq] at he; subst he; exact Nat.le_refl _
        · exact absurd he (by simp)
  | acquire j => simp only [stepEv, Option.some.injEq] at he; subst he; exact Nat.le_refl _
  | release j => simp only [stepEv, Option.some.injEq] at he; subst he; exact Nat.le_refl _

end StepLemmas

/-! ### `Inv` is inductive -/

theorem inv_step {W N K : Nat} {s s' : St W N K} (hi : Inv s) (h : Step s s') : Inv s' := by
  obtain ⟨e, he⟩ := h
  cases e with
  | use a b =>
      simp only [stepEv, Option.some.injEq] at he; subst he; exact hi
  | bump j p =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · rename_i hnone
        simp only [Option.some.injEq] at he
        subst he
        have hcoh := hi.coherent hnone
        have hdm : (s.cells j).dead = true → satInc (s.cells j).epoch = maxE W := by
          intro hd
          have h1 := hi.deadIffMax j
          rw [hd] at h1
          have h2 : (s.cells j).epoch = maxE W := of_decide_eq_true h1.symm
          rw [satInc_eq_of_max h2]; exact h2
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i
          dsimp only
          rw [Function.update_apply]
          by_cases hij : i = j
          · rw [if_pos hij, Cell.bumped_dead, Cell.bumped_epoch]
            by_cases hd : (s.cells j).dead = true
            · rw [hd, Bool.true_or]
              exact (decide_eq_true (hdm hd)).symm
            · simp only [Bool.not_eq_true] at hd
              rw [hd, Bool.false_or]
          · rw [if_neg hij]; exact hi.deadIffMax i
        · intro i
          dsimp only
          rw [Function.update_apply]
          by_cases hij : i = j
          · rw [if_pos hij, Cell.bumped_epoch]
            by_cases hm : (s.cells j).epoch = maxE W
            · rw [satInc_eq_of_max hm]; exact hi.nonzero j
            · intro hz
              have h3 := toNat_satInc_of_ne hm
              rw [hz] at h3
              exact absurd h3 (by simp)
          · rw [if_neg hij]; exact hi.nonzero i
        · intro k i
          dsimp only
          rw [Function.update_apply]
          by_cases hij : i = j
          · rw [if_pos hij, Cell.bumped_epoch, hij, hcoh k j]
            exact toNat_le_satInc _
          · rw [if_neg hij, hcoh k i]
        · intro hq; exact absurd hq (by simp)
        · intro b hb
          simp only [Option.some.injEq] at hb
          subst hb
          dsimp only
          rw [Function.update_apply, if_pos rfl, Cell.bumped_epoch]
        · intro b hb k hk
          simp only [Option.some.injEq] at hb
          subst hb
          exact absurd hk (by simp)
        · intro b hb k i hne
          simp only [Option.some.injEq] at hb
          subst hb
          dsimp only at hne ⊢
          rw [Function.update_apply, if_neg hne]
          exact hcoh k i
  | ack k' =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · rename_i b hb
        simp only [Option.some.injEq] at he
        subst he
        have htgt := hi.pendTarget b hb
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hi.deadIffMax
        · exact hi.nonzero
        · intro k i
          dsimp only
          rw [Function.update_apply]
          by_cases hk : k = k'
          · rw [if_pos hk, Function.update_apply]
            by_cases hc : i = b.cell
            · rw [if_pos hc, htgt, hc]
            · rw [if_neg hc, ← hk]; exact hi.replLe k i
          · rw [if_neg hk]; exact hi.replLe k i
        · intro hq; exact absurd hq (by simp)
        · intro b' hb'
          simp only [Option.some.injEq] at hb'
          subst hb'
          exact htgt
        · intro b' hb' k hk
          simp only [Option.some.injEq] at hb'
          subst hb'
          dsimp only at hk ⊢
          rw [Function.update_apply]
          by_cases hkk : k = k'
          · rw [if_pos hkk, Function.update_apply, if_pos rfl]
          · rw [if_neg hkk]
            rw [Function.update_apply, if_neg hkk] at hk
            exact hi.pendAcked b hb k hk
        · intro b' hb' k i hne
          simp only [Option.some.injEq] at hb'
          subst hb'
          dsimp only at hne ⊢
          rw [Function.update_apply]
          by_cases hkk : k = k'
          · rw [if_pos hkk, Function.update_apply, if_neg hne, ← hkk]
            exact hi.pendOther b hb k i hne
          · rw [if_neg hkk]; exact hi.pendOther b hb k i hne
  | bumpReturn =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · rename_i b hb
        split at he
        · rename_i hall
          simp only [Option.some.injEq] at he
          subst he
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact hi.deadIffMax
          · exact hi.nonzero
          · exact hi.replLe
          · intro _ k i
            by_cases hc : i = b.cell
            · rw [hc, hi.pendAcked b hb k (hall k), hi.pendTarget b hb]
            · exact hi.pendOther b hb k i hc
          · intro b' hb'; exact absurd hb' (by simp)
          · intro b' hb'; exact absurd hb' (by simp)
          · intro b' hb'; exact absurd hb' (by simp)
        · exact absurd he (by simp)
  | acquire j =>
      simp only [stepEv, Option.some.injEq] at he
      subst he
      have hupd : ∀ i : Fin N,
          (Function.update s.cells j ((s.cells j).setRc ((s.cells j).rc + 1)) i).epoch
            = (s.cells i).epoch ∧
          (Function.update s.cells j ((s.cells j).setRc ((s.cells j).rc + 1)) i).dead
            = (s.cells i).dead := by
        intro i
        rw [Function.update_apply]
        by_cases hij : i = j
        · rw [if_pos hij, Cell.setRc_epoch, Cell.setRc_dead, hij]; exact ⟨rfl, rfl⟩
        · rw [if_neg hij]; exact ⟨rfl, rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; dsimp only; rw [(hupd i).2, (hupd i).1]; exact hi.deadIffMax i
      · intro i; dsimp only; rw [(hupd i).1]; exact hi.nonzero i
      · intro k i; dsimp only; rw [(hupd i).1]; exact hi.replLe k i
      · intro hq k i; dsimp only; rw [(hupd i).1]; exact hi.coherent hq k i
      · intro b hb; dsimp only at hb ⊢; rw [(hupd b.cell).1]; exact hi.pendTarget b hb
      · intro b hb k hk; exact hi.pendAcked b hb k hk
      · intro b hb k i hne; dsimp only at hb ⊢; rw [(hupd i).1]
        exact hi.pendOther b hb k i hne
  | release j =>
      simp only [stepEv, Option.some.injEq] at he
      subst he
      have hupd : ∀ i : Fin N,
          (Function.update s.cells j ((s.cells j).setRc ((s.cells j).rc - 1)) i).epoch
            = (s.cells i).epoch ∧
          (Function.update s.cells j ((s.cells j).setRc ((s.cells j).rc - 1)) i).dead
            = (s.cells i).dead := by
        intro i
        rw [Function.update_apply]
        by_cases hij : i = j
        · rw [if_pos hij, Cell.setRc_epoch, Cell.setRc_dead, hij]; exact ⟨rfl, rfl⟩
        · rw [if_neg hij]; exact ⟨rfl, rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; dsimp only; rw [(hupd i).2, (hupd i).1]; exact hi.deadIffMax i
      · intro i; dsimp only; rw [(hupd i).1]; exact hi.nonzero i
      · intro k i; dsimp only; rw [(hupd i).1]; exact hi.replLe k i
      · intro hq k i; dsimp only; rw [(hupd i).1]; exact hi.coherent hq k i
      · intro b hb; dsimp only at hb ⊢; rw [(hupd b.cell).1]; exact hi.pendTarget b hb
      · intro b hb k hk; exact hi.pendAcked b hb k hk
      · intro b hb k i hne; dsimp only at hb ⊢; rw [(hupd i).1]
        exact hi.pendOther b hb k i hne

/-- `Inv` is an inductive invariant of the `TSys`. -/
theorem inv_inductive (W N K : Nat) : (sys W N K).Inductive Inv where
  init := fun _ h => Init.inv h
  step := fun _ _ hi h => inv_step hi h

/-- Every reachable state satisfies `Inv`. -/
theorem inv_invariant (W N K : Nat) : (sys W N K).Invariant Inv :=
  (inv_inductive W N K).invariant

/-! ### Run-level (transitive) closures -/

section RunLemmas

variable {W N K : Nat}

theorem run_inv {s t : St W N K} (hi : Inv s) (h : Run s t) : Inv t := by
  induction h with
  | refl => exact hi
  | tail _ hst ih => exact inv_step ih hst

theorem run_epoch_mono {s t : St W N K} (h : Run s t) (i : Fin N) :
    ((s.cells i).epoch).toNat ≤ ((t.cells i).epoch).toNat := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hst ih => exact Nat.le_trans ih (step_epoch_mono hst i)

theorem run_repl_mono {s t : St W N K} (hi : Inv s) (h : Run s t)
    (k : Fin K) (i : Fin N) : (s.repl k i).toNat ≤ (t.repl k i).toNat := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail hrun hst ih => exact Nat.le_trans ih (step_repl_mono (run_inv hi hrun) hst k i)

theorem run_poison_sticky {s t : St W N K} (h : Run s t) (i : Fin N)
    (hp : (s.cells i).poison = true) : (t.cells i).poison = true := by
  induction h with
  | refl => exact hp
  | tail _ hst ih => exact step_poison_sticky hst i ih

theorem run_dead_sticky {s t : St W N K} (h : Run s t) (i : Fin N)
    (hd : (s.cells i).dead = true) : (t.cells i).dead = true := by
  induction h with
  | refl => exact hd
  | tail _ hst ih => exact step_dead_sticky hst i ih

theorem run_occupied {s t : St W N K} (h : Run s t) (i : Fin N) :
    (t.cells i).occupied = (s.cells i).occupied := by
  induction h with
  | refl => rfl
  | tail _ hst ih => rw [step_occupied hst i, ih]

end RunLemmas

/-! ## The safety theorems (T-E1 … T-E7) -/

namespace Theorems

open Machines.Epoch.Protocol

variable {W N K : Nat}

/-! ### T-E4 — failure precedence

§3: "**Failure precedence is structural, then poison, then freshness, then
rights.**" Stated as the five exhaustive precedence facts, each at
*arbitrary* width. `T_E4_exhaustive` re-establishes the same order by
exhaustive `decide` at the model's bounds, as `EPOCH_SPEC.md` asks. -/

/-- Structural outranks everything: a malformed handle is `-BADREF`
whatever the cell says. -/
theorem T_E4_structural_first (c : Cell W) (re : BitVec W) (r : Req W)
    (h : r.wellFormed = false) : useLocal c re r = .badref := by
  simp [useLocal, h]

/-- Class mismatch on an occupied slot is `-BADREF`, still ahead of poison. -/
theorem T_E4_class_before_poison (c : Cell W) (re : BitVec W) (r : Req W)
    (hw : r.wellFormed = true) (ho : c.occupied = true) (hc : r.classOk = false) :
    useLocal c re r = .badref := by
  simp [useLocal, hw, ho, hc]

/-- §3: "inspect poison before comparing epochs: a poison-marked current
cell returns `-POISONED` **even when its publishing bump also made the
handle's epoch unequal**." -/
theorem T_E4_poison_before_freshness (c : Cell W) (re : BitVec W) (r : Req W)
    (hw : r.wellFormed = true) (ho : c.occupied = true) (hc : r.classOk = true)
    (hp : c.poison = true) : useLocal c re r = .poisoned := by
  simp [useLocal, hw, ho, hc, hp]

/-- §3: "With no such poison, any embedded/shared epoch mismatch is
`-STALE`" — and saturated death is a freshness failure too. Freshness
outranks rights. -/
theorem T_E4_freshness_before_rights (c : Cell W) (re : BitVec W) (r : Req W)
    (hw : r.wellFormed = true) (ho : c.occupied = true) (hc : r.classOk = true)
    (hp : c.poison = false) (hf : c.dead = true ∨ re ≠ r.epoch) :
    useLocal c re r = .stale := by
  rcases hf with hd | hne
  · simp [useLocal, hw, ho, hc, hp, hd]
  · by_cases hd : c.dead = true <;> simp [useLocal, hw, ho, hc, hp, hd, hne]

/-- §3: "A current live reference reaches the rights check last
(`-DENIED`)." -/
theorem T_E4_rights_last (c : Cell W) (re : BitVec W) (r : Req W)
    (hw : r.wellFormed = true) (ho : c.occupied = true) (hc : r.classOk = true)
    (hp : c.poison = false) (hd : c.dead = false) (hm : re = r.epoch) :
    useLocal c re r = (if r.rights = false then .denied else .ok) := by
  simp [useLocal, hw, ho, hc, hp, hd, hm]

/-- §3's empty-slot clause: "an empty slot is `-STALE` when its embedded
epoch mismatches and `-BADREF` only for a matching-epoch empty reference."
Slot reuse installs an entry with no inherited poison, so an old handle
observes `-STALE`, never poison from the retired object. -/
theorem T_E4_empty_slot (c : Cell W) (re : BitVec W) (r : Req W)
    (hw : r.wellFormed = true) (ho : c.occupied = false) :
    useLocal c re r = (if re = r.epoch then .badref else .stale) := by
  simp [useLocal, hw, ho]

/-- The precedence order, re-derived by exhaustive enumeration at the
model's bounds (epoch width 2 — every cell disposition, every replica
value, every request). This is `EPOCH_SPEC.md`'s "decidable statement over
all inputs at the model's bounds": the priority function below is written
independently of `useLocal` and the two are checked equal on all
`2^2 · 2^3 · 2^2 · 2^3 = 2^10` local views. -/
def priority (c : Cell 2) (re : BitVec 2) (r : Req 2) : Outcome :=
  -- structural
  if !r.wellFormed then .badref
  else if !c.occupied then (if re == r.epoch then .badref else .stale)
  else if !r.classOk then .badref
  -- poison
  else if c.poison then .poisoned
  -- freshness
  else if c.dead || re != r.epoch then .stale
  -- rights
  else if !r.rights then .denied
  else .ok

theorem T_E4_exhaustive :
    ∀ (ep re rq : BitVec 2) (poison dead occ wf cls rts : Bool),
      useLocal { epoch := ep, rc := 0, poison := poison, dead := dead, occupied := occ } re
          { cellIx := 0, epoch := rq, wellFormed := wf, classOk := cls, rights := rts }
        = priority { epoch := ep, rc := 0, poison := poison, dead := dead, occupied := occ } re
          { cellIx := 0, epoch := rq, wellFormed := wf, classOk := cls, rights := rts } := by
  decide

/-! ### T-E6 — monotonicity

§3: the epoch counter is a "monotone saturating counter"; a replica only
ever adopts the broadcast (higher) epoch. -/

/-- Home epochs and replicas are non-decreasing along any run. -/
theorem T_E6_monotone {s t : St W N K} (hi : Inv s) (h : Run s t) :
    (∀ i, ((s.cells i).epoch).toNat ≤ ((t.cells i).epoch).toNat) ∧
    (∀ k i, (s.repl k i).toNat ≤ (t.repl k i).toNat) :=
  ⟨fun i => run_epoch_mono h i, fun k i => run_repl_mono hi h k i⟩

/-! ### T-E2 — saturation is permanent death

§3: "**Saturation is permanent death.** An epoch counter saturates rather
than wraps: a cell at its maximum value is permanently dead — the counter
never rolls to a live value, so 'stale fails forever' is a hard guarantee
in every embedding." -/

/-- A dead cell never returns `ok`, at any volume, for any reference. -/
theorem dead_never_ok {s : St W N K} {i : Fin N} (hd : (s.cells i).dead = true)
    (k : Fin K) (r : Req W) (hr : r.cellIx = i.val) : use s k r ≠ .ok := by
  have hlt : r.cellIx < N := hr ▸ i.isLt
  have hfin : (⟨r.cellIx, hlt⟩ : Fin N) = i := Fin.ext hr
  simp only [use, dif_pos hlt, hfin]
  rcases Or.symm <| Bool.eq_false_or_eq_true r.wellFormed with hw | hw
  · rw [T_E4_structural_first _ _ _ hw]; simp
  rcases Or.symm <| Bool.eq_false_or_eq_true (s.cells i).occupied with ho | ho
  · rw [T_E4_empty_slot _ _ _ hw ho]; split <;> simp
  rcases Or.symm <| Bool.eq_false_or_eq_true r.classOk with hc | hc
  · rw [T_E4_class_before_poison _ _ _ hw ho hc]; simp
  rcases Or.symm <| Bool.eq_false_or_eq_true (s.cells i).poison with hp | hp
  · rw [T_E4_freshness_before_rights _ _ _ hw ho hc hp (Or.inl hd)]; simp
  · rw [T_E4_poison_before_freshness _ _ _ hw ho hc hp]; simp

/-- **T-E2.** Once dead, dead forever: the counter stays at saturation, the
bit never clears, and no use anywhere ever returns `ok` again. -/
theorem T_E2_death_permanent {s t : St W N K} (hi : Inv s) (h : Run s t) (i : Fin N)
    (hd : (s.cells i).dead = true) :
    (t.cells i).dead = true ∧ (t.cells i).epoch = maxE W ∧
    ∀ (k : Fin K) (r : Req W), r.cellIx = i.val → use t k r ≠ .ok := by
  have hdt : (t.cells i).dead = true := run_dead_sticky h i hd
  refine ⟨hdt, ?_, fun k r hr => dead_never_ok hdt k r hr⟩
  have := (run_inv hi h).deadIffMax i
  rw [hdt] at this
  exact of_decide_eq_true this.symm

/-! ### T-E3 — poison permanence

§3: the `poison` policy "also mark[s] the cell so future *references* to it
(not just stale ones) fail — for teardown-forever". §Appendix F's fail-stop
rule: "poisoned scope fails closed forever". -/

/-- **T-E3.** After a poison bump the mark never clears, and *every*
structurally valid reference to the cell — current-epoch ones included —
fails `-POISONED` at every volume, forever. -/
theorem T_E3_poison_permanent {s t : St W N K} (h : Run s t) (i : Fin N)
    (hp : (s.cells i).poison = true) (ho : (s.cells i).occupied = true) :
    (t.cells i).poison = true ∧
    ∀ (k : Fin K) (r : Req W), r.cellIx = i.val → r.wellFormed = true →
      r.classOk = true → use t k r = .poisoned := by
  have hpt : (t.cells i).poison = true := run_poison_sticky h i hp
  refine ⟨hpt, fun k r hr hw hc => ?_⟩
  have hot : (t.cells i).occupied = true := by rw [run_occupied h i]; exact ho
  have hlt : r.cellIx < N := hr ▸ i.isLt
  have hfin : (⟨r.cellIx, hlt⟩ : Fin N) = i := Fin.ext hr
  simp only [use, dif_pos hlt, hfin]
  exact T_E4_poison_before_freshness _ _ _ hw hot hc hpt

/-! ### T-E1 — stale fails forever

§3's return guarantee: "after the bump operation returns, no new use may
validate the old epoch **anywhere**… post-return success through an old
remote replica is forbidden while checks remain local and bounded." -/

/-- In a settled state (no bump in flight) every volume's replica is the
home epoch — the post-`bumpReturn` condition. -/
theorem settled_repl {s : St W N K} (hi : Inv s) (hq : s.pending = none)
    (k : Fin K) (i : Fin N) : s.repl k i = (s.cells i).epoch := hi.coherent hq k i

/-- **T-E1.** Let `e₀` be any epoch strictly below cell `i`'s home epoch in
a settled (post-bump-return) state `s`. Then in *every* state reachable
from `s`, at *every* volume, a structurally valid reference carrying `e₀`
fails — `-STALE`, or `-POISONED` if the publishing bump also poisoned the
cell. Forever. -/
theorem T_E1_stale_fails_forever {s t : St W N K} (hi : Inv s)
    (hq : s.pending = none) (h : Run s t) (i : Fin N) (e₀ : BitVec W)
    (hstale : e₀.toNat < ((s.cells i).epoch).toNat)
    (k : Fin K) (r : Req W) (hr : r.cellIx = i.val) (hre : r.epoch = e₀)
    (hw : r.wellFormed = true) (hc : r.classOk = true)
    (ho : (s.cells i).occupied = true) :
    use t k r = .stale ∨ use t k r = .poisoned := by
  have hot : (t.cells i).occupied = true := by rw [run_occupied h i]; exact ho
  have hlt : r.cellIx < N := hr ▸ i.isLt
  have hfin : (⟨r.cellIx, hlt⟩ : Fin N) = i := Fin.ext hr
  have hmono : (s.repl k i).toNat ≤ (t.repl k i).toNat := run_repl_mono hi h k i
  have hsettled : s.repl k i = (s.cells i).epoch := settled_repl hi hq k i
  have hne : t.repl k i ≠ r.epoch := by
    intro hEq
    have : (t.repl k i).toNat = e₀.toNat := by rw [hEq, hre]
    rw [hsettled] at hmono
    omega
  simp only [use, dif_pos hlt, hfin]
  by_cases hpois : (t.cells i).poison = true
  · exact Or.inr (T_E4_poison_before_freshness _ _ _ hw hot hc hpois)
  · exact Or.inl (T_E4_freshness_before_rights _ _ _ hw hot hc
      (by simpa using hpois) (Or.inr hne))

/-- The `ok`-free corollary, with no structural hypotheses on the handle:
a stale reference never succeeds. -/
theorem T_E1_never_ok {s t : St W N K} (hi : Inv s) (hq : s.pending = none)
    (h : Run s t) (i : Fin N) (e₀ : BitVec W)
    (hstale : e₀.toNat < ((s.cells i).epoch).toNat)
    (k : Fin K) (r : Req W) (hr : r.cellIx = i.val) (hre : r.epoch = e₀) :
    use t k r ≠ .ok := by
  have hlt : r.cellIx < N := hr ▸ i.isLt
  have hfin : (⟨r.cellIx, hlt⟩ : Fin N) = i := Fin.ext hr
  have hmono : (s.repl k i).toNat ≤ (t.repl k i).toNat := run_repl_mono hi h k i
  have hsettled : s.repl k i = (s.cells i).epoch := settled_repl hi hq k i
  have hne : t.repl k i ≠ r.epoch := by
    intro hEq
    have hEq' : (t.repl k i).toNat = e₀.toNat := by rw [hEq, hre]
    rw [hsettled] at hmono
    omega
  simp only [use, dif_pos hlt, hfin]
  rcases Or.symm <| Bool.eq_false_or_eq_true r.wellFormed with hw | hw
  · rw [T_E4_structural_first _ _ _ hw]; simp
  rcases Or.symm <| Bool.eq_false_or_eq_true (t.cells i).occupied with ho | ho
  · rw [T_E4_empty_slot _ _ _ hw ho, if_neg hne]; simp
  rcases Or.symm <| Bool.eq_false_or_eq_true r.classOk with hc | hc
  · rw [T_E4_class_before_poison _ _ _ hw ho hc]; simp
  rcases Or.symm <| Bool.eq_false_or_eq_true (t.cells i).poison with hp | hp
  · rw [T_E4_freshness_before_rights _ _ _ hw ho hc hp (Or.inr hne)]; simp
  · rw [T_E4_poison_before_freshness _ _ _ hw ho hc hp]; simp

/-! ### T-E5 — the no-stale-access point

§3's safe-reuse corollary: the **no-stale-access point** is "quiescence
after invalidation acknowledgement… no previously initiated use can land
afterward". T-E1's temporal half, stated over the `bumpReturn` transition
itself. -/

/-- `bumpReturn` is enabled only when the whole referent span has acked,
and it leaves every replica equal to the home epoch. This *is* §3's return
guarantee as a transition property. -/
theorem bumpReturn_all_acked {s s' : St W N K} {b : Bump W N K}
    (hb : s.pending = some b) (he : stepEv s .bumpReturn = some s') :
    (∀ k, b.acked k = true) ∧ s'.pending = none ∧ s'.repl = s.repl ∧
      s'.cells = s.cells := by
  simp only [stepEv, hb] at he
  split at he
  · rename_i hall
    simp only [Option.some.injEq] at he
    exact ⟨hall, by subst he; rfl, by subst he; rfl, by subst he; rfl⟩
  · simp at he

/-- **T-E5.** Take the very transition in which a bump for cell `i`
returns. From the post-return state onwards — forever, at every volume —
no reference carrying an epoch below the new home epoch validates. -/
theorem T_E5_no_stale_access_point {s s' t : St W N K} {b : Bump W N K}
    (hi : Inv s) (hb : s.pending = some b) (he : stepEv s .bumpReturn = some s')
    (h : Run s' t) (e₀ : BitVec W)
    (hstale : e₀.toNat < ((s.cells b.cell).epoch).toNat)
    (k : Fin K) (r : Req W) (hr : r.cellIx = b.cell.val) (hre : r.epoch = e₀) :
    use t k r ≠ .ok ∧ (t.repl k b.cell).toNat > e₀.toNat := by
  obtain ⟨hall, hq', hrepl, hcells⟩ := bumpReturn_all_acked hb he
  have hi' : Inv s' := inv_step hi ⟨.bumpReturn, he⟩
  have hs'e : (s'.cells b.cell).epoch = (s.cells b.cell).epoch := by rw [hcells]
  have hs'r : s'.repl k b.cell = (s'.cells b.cell).epoch := hi'.coherent hq' k b.cell
  have hmono : (s'.repl k b.cell).toNat ≤ (t.repl k b.cell).toNat :=
    run_repl_mono hi' h k b.cell
  rw [hs'r, hs'e] at hmono
  refine ⟨?_, by omega⟩
  exact T_E1_never_ok hi' hq' h b.cell e₀ (by rw [hs'e]; exact hstale) k r
    (by rw [hr]) hre

/-! ### T-E7 — in-flight liberty (a non-theorem, exhibited)

§3: "**A use concurrent with the bump may linearize before it and
succeed**; after the bump operation returns, no new use may validate the
old epoch anywhere." T-E1 must not be strengthened into forbidding the
first sentence. The witness below is a genuine run of `sys 3 1 2`: from a
reset state, one `bump` step, after which the home epoch has already moved
but volume 0's replica has not been acked — and a use carrying the *old*
epoch returns `ok`. -/

/-- The reset state of the witness: one cell at epoch 1, two volumes in
step with it. -/
def demoInit : St 3 1 2 where
  cells := fun _ => { epoch := 1#3, rc := 1, poison := false, dead := false, occupied := true }
  repl := fun _ _ => 1#3
  pending := none

/-- The concurrent reference: cell 0, the pre-bump epoch, structurally
valid and rights-bearing. -/
def demoRef : Req 3 :=
  { cellIx := 0, epoch := 1#3, wellFormed := true, classOk := true, rights := true }

theorem demoInit_init : Init demoInit where
  quiet := rfl
  clean := fun _ => rfl
  deadIffMax := by decide
  nonzero := by decide
  coherent := fun _ _ => rfl

/-- **T-E7.** A use concurrent with an in-flight bump MAY succeed: after
the `bump` step the home epoch is 2 and the reference carries 1, yet the
volume-local check passes because the broadcast has not been acknowledged
there. The spec is not over-constrained. -/
theorem T_E7_inflight_use_may_succeed :
    ∃ s1 : St 3 1 2,
      Init demoInit ∧ Step demoInit s1 ∧
      use s1 0 demoRef = .ok ∧
      (s1.cells 0).epoch ≠ demoRef.epoch ∧
      s1.pending ≠ none := by
  refine ⟨_, demoInit_init, ⟨Ev.bump 0 Policy.lazy, rfl⟩, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp [demoInit]

/-! ### Axiom closures — the 3-axiom kernel closure on every headline. -/

#print axioms T_E1_stale_fails_forever
#print axioms T_E1_never_ok
#print axioms T_E2_death_permanent
#print axioms T_E3_poison_permanent
#print axioms T_E4_structural_first
#print axioms T_E4_class_before_poison
#print axioms T_E4_poison_before_freshness
#print axioms T_E4_freshness_before_rights
#print axioms T_E4_rights_last
#print axioms T_E4_empty_slot
#print axioms T_E4_exhaustive
#print axioms T_E5_no_stale_access_point
#print axioms T_E6_monotone
#print axioms T_E7_inflight_use_may_succeed

end Theorems
end Machines.Epoch.Protocol
