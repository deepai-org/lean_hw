-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Protocol.Machine
import Loom.Protocol.Priority
import Machines.CapWalk.Protocol
import Machines.Epoch.ProtocolLib

/-!
# The capability protocol, expressed through the protocol library (D34/D36)

The second half of D34/D36's validation. `Machines/CapWalk/Protocol.lean`
is untouched; this file rebuilds its `sys`, `Inv`, `Run`, run-level
closures and §2.2 check order out of `Loom/Protocol/Machine.lean` and
`Loom/Protocol/Priority.lean`, and proves the reconstructions agree with
the originals.

This engine is the harder test, because it does something the epoch engine
does not: it **embeds another protocol machine** and lifts that machine's
theorems through an abstraction (`absLin`, `run_absLin`, T-C4 = §3's
`T_E1_never_ok` transported). The library had to leave that route open, and
does: since `(spec …).Run` is *definitionally* the frozen `Run`, the
abstraction and its simulation are stated exactly as before, and
`revoke_absLin'` below shows the three-event §3 run the abstraction needs
being produced by the library's event-list runner instead of by hand.

## What did not fit

* the `dup` guard `dupOk` is a Boolean side condition on the step, not an
  invariant — D34 has no notion of a guard *language*, only of a partial
  step, which is the honest boundary;
* `absLin` is an abstraction between two `ProtocolSpec`s and the library
  offers no protocol-morphism combinator: what carries the theorems here is
  `Loom.Simulation`-style reasoning on the `TSys` side plus explicit runs.
  A `ProtocolSpec`-level morphism is not built, because one engine pair is
  not enough evidence for its shape (the ledger's rule).
-/

namespace Machines.CapWalk.ProtocolLib

open Loom
open Machines.CapWalk.Protocol
open Machines.Epoch.Protocol (Cell Policy)

/-! ## D34: the protocol machine -/

/-- §2.2's capability protocol as a `Loom.ProtocolSpec`. -/
def spec (W N L : Nat) : Loom.ProtocolSpec where
  S := St W N L
  E := Ev W N L
  init := Init
  stepEv := stepEv

theorem step_eq (W N L : Nat) : (spec W N L).Step = @Step W N L := rfl

/-- The library's `TSys` *is* the frozen `sys`. -/
theorem toTSys_eq (W N L : Nat) : (spec W N L).toTSys = sys W N L := rfl

theorem run_eq (W N L : Nat) : (spec W N L).Run = @Run W N L := rfl

theorem reachable_eq (W N L : Nat) : (spec W N L).Reachable = (sys W N L).Reachable := rfl

/-- The invariant bundle: the frozen nine-field `Inv` with its two frozen
obligations. -/
def invSpec (W N L : Nat) : Loom.ProtocolSpec.InvSpec (spec W N L) where
  Inv := Inv
  init := fun _ h => Init.inv h
  step := fun _ e _ hi he => inv_step hi ⟨e, he⟩

theorem inv_inductive' (W N L : Nat) : (sys W N L).Inductive Inv :=
  (invSpec W N L).inductive_

theorem inv_invariant' (W N L : Nat) : (sys W N L).Invariant Inv :=
  (invSpec W N L).invariant

example : @inv_inductive = @inv_inductive' := rfl
example : @inv_invariant = @inv_invariant' := rfl

/-! ### The run-level closures -/

section RunLemmas

variable {W N L : Nat}

theorem run_inv' {s t : St W N L} (hi : Inv s) (h : Run s t) : Inv t :=
  (invSpec W N L).run hi h

theorem run_cell_epoch_mono' {s t : St W N L} (h : Run s t) (i : Fin N) :
    ((s.cell i).epoch).toNat ≤ ((t.cell i).epoch).toNat :=
  ProtocolSpec.run_mono (P := spec W N L) (fun u => ((u.cell i).epoch).toNat)
    (fun _ _ hst => step_cell_epoch_mono hst i) h

theorem run_cell_dead_sticky' {s t : St W N L} (h : Run s t) (i : Fin N)
    (hd : (s.cell i).dead = true) : (t.cell i).dead = true :=
  ProtocolSpec.run_closure (P := spec W N L) (p := fun u => (u.cell i).dead = true)
    (fun _ _ hst hq => step_cell_dead_sticky hst i hq) h hd

end RunLemmas

example : @run_inv = @run_inv' := rfl
example : @run_cell_epoch_mono = @run_cell_epoch_mono' := rfl
example : @run_cell_dead_sticky = @run_cell_dead_sticky' := rfl

/-! ### The event-list runner

Two uses, both real. `demo_run` replays `CAPWALK_SPEC.md`'s Layer-4 witness
(mint, then revoke) as a run; `revoke_absLin'` produces the *epoch*
protocol's three-event bump/ack/return sequence — the one §2.2's revocation
argument needs — through the same combinator, instead of chaining
`ReflTransGen` by hand. -/

/-- The Layer-4 demo, as a run of the protocol machine. -/
theorem demo_run :
    ∃ t : St 3 2 1, (spec 3 2 1).Run Theorems.demoInit t ∧ use t Theorems.demoQuery = .stale := by
  refine ⟨_, ProtocolSpec.run_of_runEvents
    [Ev.dup 0 1 Theorems.demoChild, Ev.revoke 0] rfl, ?_⟩
  decide

/-- A `cap_revoke` is a complete §3 bump/ack/return on the lineage cell —
here as a three-event list run through `Loom.ProtocolSpec.run_of_runEvents`
on the *epoch* machine. Same statement as the frozen `revoke_absLin`. -/
theorem revoke_absLin' {W N L : Nat} (s : St W N L) (l : Fin L) :
    Machines.Epoch.Protocol.Run (absLin s)
      (absLin { s with lin := Function.update s.lin l ((s.lin l).bumped Policy.lazy) }) := by
  refine ProtocolSpec.run_of_runEvents (P := Machines.Epoch.ProtocolLib.spec W L 1)
    [Machines.Epoch.Protocol.Ev.bump l Policy.lazy,
     Machines.Epoch.Protocol.Ev.ack 0,
     Machines.Epoch.Protocol.Ev.bumpReturn] ?_
  have hall : ∀ (k : Fin 1), Function.update (fun _ : Fin 1 => false) 0 true k = true := by
    intro k
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk; simp
  simp only [ProtocolSpec.runEvents, Machines.Epoch.ProtocolLib.spec,
    Machines.Epoch.Protocol.stepEv, absLin, Option.bind_some]
  have hrepl : Function.update (fun (_ : Fin 1) (i : Fin L) => (s.lin i).epoch) 0
        (Function.update (fun (i : Fin L) => (s.lin i).epoch) l
          (Machines.Epoch.Protocol.satInc (s.lin l).epoch))
      = fun (_ : Fin 1) (i : Fin L) =>
          ((Function.update s.lin l ((s.lin l).bumped Policy.lazy)) i).epoch := by
    funext k i
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    simp only [Function.update_self, Function.update_apply]
    by_cases hil : i = l
    · subst hil; simp
    · simp [hil]
  rw [if_pos hall, Option.bind_some, ← hrepl]

example : @revoke_absLin = @revoke_absLin' := rfl

/-! ## D36: §2.2's check order as a priority order -/

/-- The scalars §2.2's check reads — exactly the arguments of the frozen
`outcome`, which is already written on derived scalars. -/
structure CapView (W : Nat) where
  /-- Slot occupancy. -/
  occ : Bool
  /-- The embedded cell's saturated-death bit. -/
  dead : Bool
  /-- The embedded cell's epoch. -/
  cep : BitVec W
  /-- The handle's epoch field. -/
  qep : BitVec W
  /-- Handle shape validates. -/
  wf : Bool
  /-- The shared lineage cell's verdict is not `ok`. -/
  linFail : Bool
  /-- The required rights are present. -/
  rightsOk : Bool
  /-- The object/interface class matches. -/
  clsOk : Bool
  /-- The request lies in the entry's range. -/
  rangeOk : Bool
  deriving DecidableEq

/-- The frozen `outcome`, read as a function of the view. -/
def CapView.eval {W : Nat} (v : CapView W) : Outcome :=
  outcome v.occ v.dead v.cep v.qep v.wf v.linFail v.rightsOk v.clsOk v.rangeOk

/-- The view a concrete check presents. -/
def viewOf {W N L : Nat} (c lc : Cell W) (ed : EntryData W N L) (q : Query W) :
    CapView W where
  occ := c.occupied
  dead := c.dead
  cep := c.epoch
  qep := q.epoch
  wf := q.wellFormed
  linFail := linOutcome lc ed != Machines.Epoch.Protocol.Outcome.ok
  rightsOk := rightsSub q.need ed.rights
  clsOk := ed.cls == q.cls
  rangeOk := rangeIn q.off q.len ed.base ed.len

@[simp] theorem eval_viewOf {W N L : Nat} (c lc : Cell W) (ed : EntryData W N L)
    (q : Query W) : (viewOf c lc ed q).eval = check c lc ed q := rfl

/-! ### The clauses of §2.2's order, named

Naming them keeps the `X_before_Y` derivations below readable: each one is
`Agrees.fires` at a split of this list. -/

/-- Structural: malformed / out-of-range handle. -/
def kStruct (W : Nat) : Loom.Clause (CapView W) Outcome :=
  { guard := fun v => !v.wf, out := fun _ => .badref }
/-- 1. slot occupied (empty + matching embedded epoch is `-BADREF`). -/
def kOcc (W : Nat) : Loom.Clause (CapView W) Outcome :=
  { guard := fun v => !v.occ, out := fun v => if v.cep = v.qep then .badref else .stale }
/-- 2. handle epoch == slot-cell epoch. -/
def kEpoch (W : Nat) : Loom.Clause (CapView W) Outcome :=
  { guard := fun v => v.cep != v.qep, out := fun _ => .stale }
/-- 2'. saturated death is in the same freshness class. -/
def kDead (W : Nat) : Loom.Clause (CapView W) Outcome :=
  { guard := fun v => v.dead, out := fun _ => .stale }
/-- 3. lineage-cell epoch current. -/
def kLineage (W : Nat) : Loom.Clause (CapView W) Outcome :=
  { guard := fun v => v.linFail, out := fun _ => .stale }
/-- 4. required rights present. -/
def kRights (W : Nat) : Loom.Clause (CapView W) Outcome :=
  { guard := fun v => !v.rightsOk, out := fun _ => .denied }
/-- 5a. class valid. -/
def kClass (W : Nat) : Loom.Clause (CapView W) Outcome :=
  { guard := fun v => !v.clsOk, out := fun _ => .badref }
/-- 5b. range valid. -/
def kRange (W : Nat) : Loom.Clause (CapView W) Outcome :=
  { guard := fun v => !v.rangeOk, out := fun _ => .denied }

/-- **§2.2's check order, as data.** "slot occupied, handle epoch ==
slot-cell epoch, lineage-cell epoch current, required rights present,
range/class valid. … Checks occur in that order." -/
def capPriority (W : Nat) : Loom.Priority (CapView W) Outcome where
  clauses := [kStruct W, kOcc W, kEpoch W, kDead W, kLineage W, kRights W,
              kClass W, kRange W]
  fallback := fun _ => .ok

/-- **The bridge, at arbitrary width.** -/
theorem outcome_agrees (W : Nat) :
    Loom.Priority.Agrees (CapView.eval (W := W)) (capPriority W) := by
  intro v
  obtain ⟨occ, dead, cep, qep, wf, linFail, rightsOk, clsOk, rangeOk⟩ := v
  by_cases hm : cep = qep <;>
    cases wf <;> cases occ <;> cases dead <;> cases linFail <;> cases rightsOk <;>
      cases clsOk <;> cases rangeOk <;>
        simp [CapView.eval, outcome, capPriority, kStruct, kOcc, kEpoch, kDead,
          kLineage, kRights, kClass, kRange, Loom.Priority.eval,
          Loom.Priority.evalList, hm]

/-- **The exhaustive check**: the same statement at epoch width 2 — all
2048 local views — decided in the kernel against the clause list. This is
the frozen `T_C2_exhaustive`'s content. -/
theorem T_C2_exhaustive' :
    Loom.Priority.Agrees (CapView.eval (W := 2)) (capPriority 2) := by
  intro v
  obtain ⟨occ, dead, cep, qep, wf, linFail, rightsOk, clsOk, rangeOk⟩ := v
  revert occ dead cep qep wf linFail rightsOk clsOk rangeOk
  decide

/-- The two routes to the same statement coincide. -/
example : Loom.Priority.Agrees (CapView.eval (W := 2)) (capPriority 2) := outcome_agrees 2

/-! ### T-C2, generated -/

section TC2

variable {W N L : Nat} (c lc : Cell W) (ed : EntryData W N L) (q : Query W)

/-- The guards of the clauses that outrank freshness, at a live handle. -/
private theorem pre2 (hw : q.wellFormed = true) (ho : c.occupied = true) :
    ∀ d ∈ [kStruct W, kOcc W], d.guard (viewOf c lc ed q) = false := by
  simp [viewOf, kStruct, kOcc, hw, ho]

private theorem pre5 (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false) :
    ∀ d ∈ [kStruct W, kOcc W, kEpoch W, kDead W], d.guard (viewOf c lc ed q) = false := by
  simp [viewOf, kStruct, kOcc, kEpoch, kDead, hw, ho, he, hd]

private theorem pre6 (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false)
    (hl : linOutcome lc ed = Machines.Epoch.Protocol.Outcome.ok) :
    ∀ d ∈ [kStruct W, kOcc W, kEpoch W, kDead W, kLineage W],
      d.guard (viewOf c lc ed q) = false := by
  simp [viewOf, kStruct, kOcc, kEpoch, kDead, kLineage, hw, ho, he, hd, hl]

private theorem pre7 (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false)
    (hl : linOutcome lc ed = Machines.Epoch.Protocol.Outcome.ok)
    (hr : rightsSub q.need ed.rights = true) :
    ∀ d ∈ [kStruct W, kOcc W, kEpoch W, kDead W, kLineage W, kRights W],
      d.guard (viewOf c lc ed q) = false := by
  simp [viewOf, kStruct, kOcc, kEpoch, kDead, kLineage, kRights, hw, ho, he, hd, hl, hr]

theorem T_C2_structural_first' (h : q.wellFormed = false) :
    check c lc ed q = .badref := by
  have := (outcome_agrees W).fires (v := viewOf c lc ed q) (pre := []) (c := kStruct W) rfl
    (by simp) (by simp [viewOf, kStruct, h])
  simpa [kStruct] using this

theorem T_C2_empty_slot' (hw : q.wellFormed = true) (ho : c.occupied = false) :
    check c lc ed q = (if c.epoch = q.epoch then .badref else .stale) := by
  have := (outcome_agrees W).fires (v := viewOf c lc ed q)
    (pre := [kStruct W]) (c := kOcc W) rfl
    (by simp [viewOf, kStruct, hw]) (by simp [viewOf, kOcc, ho])
  simpa [kOcc, viewOf] using this

theorem T_C2_embedded_epoch_before_lineage' (hw : q.wellFormed = true)
    (ho : c.occupied = true) (hf : c.epoch ≠ q.epoch ∨ c.dead = true) :
    check c lc ed q = .stale := by
  rcases hf with hne | hd
  · have := (outcome_agrees W).fires (v := viewOf c lc ed q)
      (pre := [kStruct W, kOcc W]) (c := kEpoch W) rfl (pre2 c lc ed q hw ho)
      (by simp [viewOf, kEpoch, hne])
    simpa [kEpoch] using this
  · by_cases hne : c.epoch = q.epoch
    · have := (outcome_agrees W).fires (v := viewOf c lc ed q)
        (pre := [kStruct W, kOcc W, kEpoch W]) (c := kDead W) rfl
        (by simp [viewOf, kStruct, kOcc, kEpoch, hw, ho, hne])
        (by simp [viewOf, kDead, hd])
      simpa [kDead] using this
    · have := (outcome_agrees W).fires (v := viewOf c lc ed q)
        (pre := [kStruct W, kOcc W]) (c := kEpoch W) rfl (pre2 c lc ed q hw ho)
        (by simp [viewOf, kEpoch, hne])
      simpa [kEpoch] using this

theorem T_C2_lineage_before_rights' (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false)
    (hl : linOutcome lc ed ≠ Machines.Epoch.Protocol.Outcome.ok) :
    check c lc ed q = .stale := by
  have := (outcome_agrees W).fires (v := viewOf c lc ed q)
    (pre := [kStruct W, kOcc W, kEpoch W, kDead W]) (c := kLineage W) rfl
    (pre5 c lc ed q hw ho he hd) (by simp [viewOf, kLineage, hl])
  simpa [kLineage] using this

theorem T_C2_rights_before_class' (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false)
    (hl : linOutcome lc ed = Machines.Epoch.Protocol.Outcome.ok)
    (hr : rightsSub q.need ed.rights = false) : check c lc ed q = .denied := by
  have := (outcome_agrees W).fires (v := viewOf c lc ed q)
    (pre := [kStruct W, kOcc W, kEpoch W, kDead W, kLineage W]) (c := kRights W) rfl
    (pre6 c lc ed q hw ho he hd hl) (by simp [viewOf, kRights, hr])
  simpa [kRights] using this

theorem T_C2_class_and_range_last' (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false)
    (hl : linOutcome lc ed = Machines.Epoch.Protocol.Outcome.ok)
    (hr : rightsSub q.need ed.rights = true) :
    check c lc ed q =
      (if ed.cls ≠ q.cls then .badref
       else if rangeIn q.off q.len ed.base ed.len = false then .denied else .ok) := by
  by_cases hc : ed.cls = q.cls
  · rw [if_neg (by simpa using hc)]
    by_cases hg : rangeIn q.off q.len ed.base ed.len = false
    · have := (outcome_agrees W).fires (v := viewOf c lc ed q)
        (pre := [kStruct W, kOcc W, kEpoch W, kDead W, kLineage W, kRights W, kClass W])
        (c := kRange W) rfl (by
          intro d hd'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
          rcases hd' with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · simpa [kStruct, viewOf] using hw
          · simpa [kOcc, viewOf] using ho
          · simpa [kEpoch, viewOf] using he
          · simpa [kDead, viewOf] using hd
          · simpa [kLineage, viewOf] using hl
          · simpa [kRights, viewOf] using hr
          · simpa [kClass, viewOf] using hc)
        (by simp [viewOf, kRange, hg])
      rw [if_pos hg]; simpa [kRange] using this
    · simp only [Bool.not_eq_false] at hg
      have := (outcome_agrees W).falls (v := viewOf c lc ed q) (by
        intro d hd'
        simp only [capPriority, List.mem_cons, List.not_mem_nil, or_false] at hd'
        rcases hd' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        · simpa [kStruct, viewOf] using hw
        · simpa [kOcc, viewOf] using ho
        · simpa [kEpoch, viewOf] using he
        · simpa [kDead, viewOf] using hd
        · simpa [kLineage, viewOf] using hl
        · simpa [kRights, viewOf] using hr
        · simpa [kClass, viewOf] using hc
        · simpa [kRange, viewOf] using hg)
      rw [if_neg (by simp [hg])]; simpa [capPriority] using this
  · rw [if_pos hc]
    have := (outcome_agrees W).fires (v := viewOf c lc ed q)
      (pre := [kStruct W, kOcc W, kEpoch W, kDead W, kLineage W, kRights W])
      (c := kClass W) rfl (pre7 c lc ed q hw ho he hd hl hr)
      (by simp [viewOf, kClass, hc])
    simpa [kClass] using this

end TC2

example : @Theorems.T_C2_structural_first = @T_C2_structural_first' := rfl
example : @Theorems.T_C2_empty_slot = @T_C2_empty_slot' := rfl
example : @Theorems.T_C2_embedded_epoch_before_lineage =
    @T_C2_embedded_epoch_before_lineage' := rfl
example : @Theorems.T_C2_lineage_before_rights = @T_C2_lineage_before_rights' := rfl
example : @Theorems.T_C2_rights_before_class = @T_C2_rights_before_class' := rfl
example : @Theorems.T_C2_class_and_range_last = @T_C2_class_and_range_last' := rfl

/-! ### Axiom closures for the reconstructions. -/

#print axioms toTSys_eq
#print axioms inv_invariant'
#print axioms revoke_absLin'
#print axioms outcome_agrees
#print axioms T_C2_exhaustive'
#print axioms T_C2_class_and_range_last'

end Machines.CapWalk.ProtocolLib
