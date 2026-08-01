-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Protocol.Machine
import Loom.Protocol.Priority
import Machines.Epoch.Protocol

/-!
# The epoch protocol, expressed through the protocol library (D34/D36)

`Machines/Epoch/Protocol.lean` is frozen: it is the candidate normative
artifact for Appendix F machine 1 and nothing here edits it. This file is
the **validation the ledger demands** for D34 and D36 — the same engine,
reconstructed through `Loom/Protocol/Machine.lean` and
`Loom/Protocol/Priority.lean`, with every reconstruction proved to agree
with the frozen original.

Where the agreement is *definitional* it is stated as `rfl`: `sys`, `Step`,
`Run` and `Reachable` are literally the library's derivations, not merely
isomorphic to them. Where the reconstruction is a proof (the run-level
closures, the T-E4 family) the frozen statement is reproduced verbatim and
the `example`s below check that the two theorems have the *same type*.

## What did not fit

Recorded honestly, because a library that claims 100 % is not a result:

* the per-event case analysis (`inv_step`, `step_cells_shape`,
  `step_repl_mono`) is the engine's actual content and stays hand-written —
  D34 supplies the skeleton around it, not the work inside it;
* `Machines/Epoch/Bounded.lean`'s `ackSys` is a *restricted* transition
  system (a fairness schedule over `Step`), which is a `TSys` and not a
  `ProtocolSpec`: its step relation is not "some event of an alphabet is
  enabled". D34 does not model schedules;
* the observation `use` is not part of the protocol machine at all — it is
  a pure read, and D34 offers only `stutter`, the fact that the *event*
  that models it does not move the state.
-/

namespace Machines.Epoch.ProtocolLib

open Loom
open Machines.Epoch.Protocol

/-! ## D34: the protocol machine -/

/-- §3's epoch protocol as a `Loom.ProtocolSpec`: the state structure, the
event alphabet, the reset predicate and the partial step, with nothing
added. -/
def spec (W N K : Nat) : Loom.ProtocolSpec where
  S := St W N K
  E := Ev W N K
  init := Init
  stepEv := stepEv

/-- The library's step relation *is* the frozen one. -/
theorem step_eq (W N K : Nat) : (spec W N K).Step = @Step W N K := rfl

/-- The library's `TSys` *is* the frozen `sys`. Everything already stated
over `sys` — the Layer-3 refinement, `Loom/Core/Bounded.lean`'s bounds —
therefore applies unchanged. -/
theorem toTSys_eq (W N K : Nat) : (spec W N K).toTSys = sys W N K := rfl

/-- The library's `Run` *is* the frozen one. -/
theorem run_eq (W N K : Nat) : (spec W N K).Run = @Run W N K := rfl

/-- …and so is reachability. -/
theorem reachable_eq (W N K : Nat) : (spec W N K).Reachable = (sys W N K).Reachable := rfl

/-- The invariant bundle: the frozen seven-field `Inv` with its two frozen
obligations, packaged. -/
def invSpec (W N K : Nat) : Loom.ProtocolSpec.InvSpec (spec W N K) where
  Inv := Inv
  init := fun _ h => Init.inv h
  step := fun _ e _ hi he => inv_step hi ⟨e, he⟩

/-- `inv_inductive`, from the bundle. Same statement as the frozen one. -/
theorem inv_inductive' (W N K : Nat) : (sys W N K).Inductive Inv :=
  (invSpec W N K).inductive_

/-- `inv_invariant`, from the bundle. -/
theorem inv_invariant' (W N K : Nat) : (sys W N K).Invariant Inv :=
  (invSpec W N K).invariant

example : @inv_inductive = @inv_inductive' := rfl
example : @inv_invariant = @inv_invariant' := rfl

/-! ### The run-level closures

The frozen file's whole `RunLemmas` section, re-derived from the four
generic combinators. Each `example` below checks that the reconstruction
has exactly the frozen theorem's type. -/

section RunLemmas

variable {W N K : Nat}

theorem run_inv' {s t : St W N K} (hi : Inv s) (h : Run s t) : Inv t :=
  (invSpec W N K).run hi h

theorem run_epoch_mono' {s t : St W N K} (h : Run s t) (i : Fin N) :
    ((s.cells i).epoch).toNat ≤ ((t.cells i).epoch).toNat :=
  ProtocolSpec.run_mono (P := spec W N K) (fun u => ((u.cells i).epoch).toNat)
    (fun _ _ hst => step_epoch_mono hst i) h

theorem run_repl_mono' {s t : St W N K} (hi : Inv s) (h : Run s t)
    (k : Fin K) (i : Fin N) : (s.repl k i).toNat ≤ (t.repl k i).toNat :=
  (invSpec W N K).run_mono (fun u => (u.repl k i).toNat)
    (fun _ _ hI hst => step_repl_mono hI hst k i) hi h

theorem run_poison_sticky' {s t : St W N K} (h : Run s t) (i : Fin N)
    (hp : (s.cells i).poison = true) : (t.cells i).poison = true :=
  ProtocolSpec.run_closure (P := spec W N K) (p := fun u => (u.cells i).poison = true)
    (fun _ _ hst hq => step_poison_sticky hst i hq) h hp

theorem run_dead_sticky' {s t : St W N K} (h : Run s t) (i : Fin N)
    (hd : (s.cells i).dead = true) : (t.cells i).dead = true :=
  ProtocolSpec.run_closure (P := spec W N K) (p := fun u => (u.cells i).dead = true)
    (fun _ _ hst hq => step_dead_sticky hst i hq) h hd

theorem run_occupied' {s t : St W N K} (h : Run s t) (i : Fin N) :
    (t.cells i).occupied = (s.cells i).occupied :=
  ProtocolSpec.run_const (P := spec W N K) (fun u => (u.cells i).occupied)
    (fun _ _ hst => step_occupied hst i) h

end RunLemmas

example : @run_inv = @run_inv' := rfl
example : @run_epoch_mono = @run_epoch_mono' := rfl
example : @run_repl_mono = @run_repl_mono' := rfl
example : @run_poison_sticky = @run_poison_sticky' := rfl
example : @run_dead_sticky = @run_dead_sticky' := rfl
example : @run_occupied = @run_occupied' := rfl

/-! ### The event-list runner, and the stutter glue

T-E7's witness is a one-event run; the general shape (an explicit event
sequence turned into a `Run`) is `run_of_runEvents`. -/

/-- The `bump` step of T-E7's witness, as an event list. -/
theorem demo_run :
    (spec 3 1 2).Run Theorems.demoInit
      { Theorems.demoInit with
        cells := Function.update Theorems.demoInit.cells 0
          ((Theorems.demoInit.cells 0).bumped Policy.lazy)
        pending := some { cell := 0, target := satInc (Theorems.demoInit.cells 0).epoch,
                          policy := Policy.lazy, acked := fun _ => false } } :=
  ProtocolSpec.run_of_runEvents [Ev.bump 0 Policy.lazy] rfl

/-- §3's `use` is an observation: the event is always enabled and never
moves the state. That is the library's `stutter`, at this engine. -/
theorem use_stutters {W N K : Nat} (s : St W N K) (k : Fin K) (r : Req W) :
    (spec W N K).Step s s :=
  ProtocolSpec.stutter (e := Ev.use k r) rfl

/-! ## D36: §3's failure precedence as a priority order

The frozen file states the order twice: once as six `X_before_Y` lemmas at
arbitrary width, once as an independently written `priority` function
checked by `decide` at width 2. Here it is stated **once**, as data. -/

/-- The scalars §3's local check actually reads. `useLocal` ignores the
cell's `rc` and the request's `cellIx`, so this is the whole view — and it
is finite, which is what the exhaustive check needs. -/
structure LocalView (W : Nat) where
  /-- The cell's home epoch (unused by the order; carried for completeness). -/
  ep : BitVec W
  /-- The volume-local replica the check compares against. -/
  re : BitVec W
  /-- The presented reference's epoch. -/
  rq : BitVec W
  /-- The cell's poison disposition. -/
  poison : Bool
  /-- The cell's saturated-death bit. -/
  dead : Bool
  /-- Slot occupancy. -/
  occ : Bool
  /-- Handle shape validates. -/
  wf : Bool
  /-- The class check. -/
  cls : Bool
  /-- The rights check. -/
  rts : Bool
  deriving DecidableEq

namespace LocalView

variable {W : Nat}

/-- The cell this view presents. -/
def cell (v : LocalView W) : Cell W :=
  { epoch := v.ep, rc := 0, poison := v.poison, dead := v.dead, occupied := v.occ }

/-- The request this view presents. -/
def req (v : LocalView W) : Req W :=
  { cellIx := 0, epoch := v.rq, wellFormed := v.wf, classOk := v.cls, rights := v.rts }

/-- The frozen `useLocal`, read as a function of the view. -/
def check (v : LocalView W) : Outcome := useLocal v.cell v.re v.req

end LocalView

/-- The view a concrete cell/replica/request triple presents. -/
def viewOf {W : Nat} (c : Cell W) (re : BitVec W) (r : Req W) : LocalView W :=
  { ep := c.epoch, re := re, rq := r.epoch, poison := c.poison, dead := c.dead,
    occ := c.occupied, wf := r.wellFormed, cls := r.classOk, rts := r.rights }

@[simp] theorem check_viewOf {W : Nat} (c : Cell W) (re : BitVec W) (r : Req W) :
    (viewOf c re r).check = useLocal c re r := rfl

/-! ### The clauses of §3's precedence, named

Naming them keeps the `X_before_Y` derivations below to one line of
hypotheses each: every one is `Agrees.fires` at a split of this list. -/

/-- Structural: a malformed handle. -/
def kWf (W : Nat) : Loom.Clause (LocalView W) Outcome :=
  { guard := fun v => !v.wf, out := fun _ => .badref }
/-- Structural: §3's empty-slot clause. -/
def kEmpty (W : Nat) : Loom.Clause (LocalView W) Outcome :=
  { guard := fun v => !v.occ, out := fun v => if v.re = v.rq then .badref else .stale }
/-- Structural: class mismatch on an occupied slot. -/
def kClass (W : Nat) : Loom.Clause (LocalView W) Outcome :=
  { guard := fun v => !v.cls, out := fun _ => .badref }
/-- Poison, inspected before epochs are compared. -/
def kPoison (W : Nat) : Loom.Clause (LocalView W) Outcome :=
  { guard := fun v => v.poison, out := fun _ => .poisoned }
/-- Freshness: saturated death. -/
def kDead (W : Nat) : Loom.Clause (LocalView W) Outcome :=
  { guard := fun v => v.dead, out := fun _ => .stale }
/-- Freshness: epoch mismatch against the volume-local replica. -/
def kFresh (W : Nat) : Loom.Clause (LocalView W) Outcome :=
  { guard := fun v => v.re != v.rq, out := fun _ => .stale }
/-- Rights, strictly last. -/
def kRights (W : Nat) : Loom.Clause (LocalView W) Outcome :=
  { guard := fun v => !v.rts, out := fun _ => .denied }

/-- **§3's failure precedence, as data.** Structural → poison → freshness →
rights, with §3's sub-clauses in order. This list is the *whole*
specification of the order: the `X_before_Y` lemmas and the exhaustive
check below are both derived from it. -/
def epochPriority (W : Nat) : Loom.Priority (LocalView W) Outcome where
  clauses := [kWf W, kEmpty W, kClass W, kPoison W, kDead W, kFresh W, kRights W]
  fallback := fun _ => .ok

/-- **The bridge, at arbitrary width**: the frozen `useLocal` *is* that
priority order. Everything below is a corollary. -/
theorem useLocal_agrees (W : Nat) :
    Loom.Priority.Agrees (LocalView.check (W := W)) (epochPriority W) := by
  intro v
  obtain ⟨ep, re, rq, poison, dead, occ, wf, cls, rts⟩ := v
  by_cases hm : re = rq <;>
    cases wf <;> cases occ <;> cases cls <;> cases poison <;> cases dead <;> cases rts <;>
      simp [LocalView.check, LocalView.cell, LocalView.req, useLocal, epochPriority,
        kWf, kEmpty, kClass, kPoison, kDead, kFresh, kRights,
        Loom.Priority.eval, Loom.Priority.evalList, hm]

/-- **The exhaustive check** (`EPOCH_SPEC.md`'s "decidable statement over
all inputs at the model's bounds"): the same `Agrees` statement at epoch
width 2 — all `2^10` local views — decided in the kernel against the clause
list rather than proved. This is the frozen `T_E4_exhaustive`'s content:
an independently written statement of the order, checked by enumeration. -/
theorem T_E4_exhaustive' :
    Loom.Priority.Agrees (LocalView.check (W := 2)) (epochPriority 2) := by
  intro v
  obtain ⟨ep, re, rq, poison, dead, occ, wf, cls, rts⟩ := v
  revert ep re rq poison dead occ wf cls rts
  decide

/-- The two routes to the same statement coincide. -/
example : Loom.Priority.Agrees (LocalView.check (W := 2)) (epochPriority 2) :=
  useLocal_agrees 2

/-! ### T-E4, generated

Each frozen lemma is `Agrees.fires` at one split of the clause list. The
statements are reproduced verbatim; the `example`s check that. -/

section TE4

variable {W : Nat} (c : Cell W) (re : BitVec W) (r : Req W)

/-- The three structural guards, false at a well-formed, occupied, in-class
reference. -/
private theorem pre3 (hw : r.wellFormed = true) (ho : c.occupied = true)
    (hc : r.classOk = true) :
    ∀ d ∈ [kWf W, kEmpty W, kClass W], d.guard (viewOf c re r) = false := by
  simp [viewOf, kWf, kEmpty, kClass, hw, ho, hc]

private theorem pre4 (hw : r.wellFormed = true) (ho : c.occupied = true)
    (hc : r.classOk = true) (hp : c.poison = false) :
    ∀ d ∈ [kWf W, kEmpty W, kClass W, kPoison W], d.guard (viewOf c re r) = false := by
  simp [viewOf, kWf, kEmpty, kClass, kPoison, hw, ho, hc, hp]

private theorem pre6 (hw : r.wellFormed = true) (ho : c.occupied = true)
    (hc : r.classOk = true) (hp : c.poison = false) (hd : c.dead = false)
    (hm : re = r.epoch) :
    ∀ d ∈ [kWf W, kEmpty W, kClass W, kPoison W, kDead W, kFresh W],
      d.guard (viewOf c re r) = false := by
  simp [viewOf, kWf, kEmpty, kClass, kPoison, kDead, kFresh, hw, ho, hc, hp, hd, hm]

theorem T_E4_structural_first' (h : r.wellFormed = false) :
    useLocal c re r = .badref := by
  have := (useLocal_agrees W).fires (v := viewOf c re r) (pre := []) (c := kWf W) rfl
    (by simp) (by simp [viewOf, kWf, h])
  simpa [kWf] using this

theorem T_E4_empty_slot' (hw : r.wellFormed = true) (ho : c.occupied = false) :
    useLocal c re r = (if re = r.epoch then .badref else .stale) := by
  have := (useLocal_agrees W).fires (v := viewOf c re r)
    (pre := [kWf W]) (c := kEmpty W) rfl
    (by simp [viewOf, kWf, hw]) (by simp [viewOf, kEmpty, ho])
  simpa [kEmpty, viewOf] using this

theorem T_E4_class_before_poison' (hw : r.wellFormed = true) (ho : c.occupied = true)
    (hc : r.classOk = false) : useLocal c re r = .badref := by
  have := (useLocal_agrees W).fires (v := viewOf c re r)
    (pre := [kWf W, kEmpty W]) (c := kClass W) rfl
    (by simp [viewOf, kWf, kEmpty, hw, ho]) (by simp [viewOf, kClass, hc])
  simpa [kClass] using this

theorem T_E4_poison_before_freshness' (hw : r.wellFormed = true) (ho : c.occupied = true)
    (hc : r.classOk = true) (hp : c.poison = true) : useLocal c re r = .poisoned := by
  have := (useLocal_agrees W).fires (v := viewOf c re r)
    (pre := [kWf W, kEmpty W, kClass W]) (c := kPoison W) rfl (pre3 c re r hw ho hc)
    (by simp [viewOf, kPoison, hp])
  simpa [kPoison] using this

theorem T_E4_freshness_before_rights' (hw : r.wellFormed = true) (ho : c.occupied = true)
    (hc : r.classOk = true) (hp : c.poison = false) (hf : c.dead = true ∨ re ≠ r.epoch) :
    useLocal c re r = .stale := by
  by_cases hd : c.dead = true
  · have := (useLocal_agrees W).fires (v := viewOf c re r)
      (pre := [kWf W, kEmpty W, kClass W, kPoison W]) (c := kDead W) rfl
      (pre4 c re r hw ho hc hp) (by simp [viewOf, kDead, hd])
    simpa [kDead] using this
  · simp only [Bool.not_eq_true] at hd
    have hne : re ≠ r.epoch := by rcases hf with h | h; · rw [hd] at h; simp at h
                                  · exact h
    have := (useLocal_agrees W).fires (v := viewOf c re r)
      (pre := [kWf W, kEmpty W, kClass W, kPoison W, kDead W]) (c := kFresh W) rfl
      (by simp [viewOf, kWf, kEmpty, kClass, kPoison, kDead, hw, ho, hc, hp, hd])
      (by simp [viewOf, kFresh, hne])
    simpa [kFresh] using this

theorem T_E4_rights_last' (hw : r.wellFormed = true) (ho : c.occupied = true)
    (hc : r.classOk = true) (hp : c.poison = false) (hd : c.dead = false)
    (hm : re = r.epoch) :
    useLocal c re r = (if r.rights = false then .denied else .ok) := by
  by_cases hr : r.rights = false
  · have := (useLocal_agrees W).fires (v := viewOf c re r)
      (pre := [kWf W, kEmpty W, kClass W, kPoison W, kDead W, kFresh W]) (c := kRights W)
      rfl (pre6 c re r hw ho hc hp hd hm) (by simp [viewOf, kRights, hr])
    rw [if_pos hr]; simpa [kRights] using this
  · simp only [Bool.not_eq_false] at hr
    have := (useLocal_agrees W).falls (v := viewOf c re r) (by
      intro d hd'
      simp only [epochPriority, List.mem_cons, List.not_mem_nil, or_false] at hd'
      rcases hd' with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · simpa [kWf, viewOf] using hw
      · simpa [kEmpty, viewOf] using ho
      · simpa [kClass, viewOf] using hc
      · simpa [kPoison, viewOf] using hp
      · simpa [kDead, viewOf] using hd
      · simpa [kFresh, viewOf] using hm
      · simpa [kRights, viewOf] using hr)
    rw [if_neg (by simp [hr])]; simpa [epochPriority] using this

end TE4

example : @Theorems.T_E4_structural_first = @T_E4_structural_first' := rfl
example : @Theorems.T_E4_empty_slot = @T_E4_empty_slot' := rfl
example : @Theorems.T_E4_class_before_poison = @T_E4_class_before_poison' := rfl
example : @Theorems.T_E4_poison_before_freshness = @T_E4_poison_before_freshness' := rfl
example : @Theorems.T_E4_freshness_before_rights = @T_E4_freshness_before_rights' := rfl
example : @Theorems.T_E4_rights_last = @T_E4_rights_last' := rfl

/-! ### Axiom closures for the reconstructions. -/

#print axioms toTSys_eq
#print axioms inv_invariant'
#print axioms run_repl_mono'
#print axioms useLocal_agrees
#print axioms T_E4_exhaustive'
#print axioms T_E4_rights_last'

end Machines.Epoch.ProtocolLib
