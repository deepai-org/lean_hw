import Machines.Lnp64u.SpecM

/-!
# The capability kernel: pure state functions (L0)

The shared mechanics under the system ops: slot/lineage allocation,
generation bumping, lineage reparenting, the descendant marking that
`cap_revoke` sweeps, and the region/Mover sweeps. These are *pure functions
on `MachineState`* — the system instructions are thin monadic wrappers — so
the T2/T3/T9 invariant proofs reason about plain functions, and these
definitions literally are the induction-hypothesis material (the same terms
in the same file, per the charter's L3 discipline).

Design decisions recorded here:

* **Generations bump saturating** (`bumpGen`): 255 = retired forever; no
  reuse, which is T3's no-resurrection.
* **Lineage chains always point at live ancestors.** Transfer reparents
  children to the moved capability's new reference; drop splices children to
  the dropped capability's parent (or orphans them to roots when the dropped
  capability was itself a root). Revoke therefore finds every descendant by
  following parent pointers only through live references.
* **Revoke keeps the revoked capability and destroys its strict
  descendants**, then sweeps region registers and the Mover: cached
  authority never outlives the capability it caches.
-/

namespace Machines.Lnp64u

open Loom

/-- Saturating generation bump: 255 is retirement, never reused. -/
def bumpGen (g : Gen) : Gen := if g = genRetired then g else g + 1

namespace MachineState

variable (σ : MachineState)

/-- The current reference of the live capability in `(d, s)`, if any. -/
def refOf (d : DomainId) (s : Slot) : Option CapRef :=
  match (σ.doms d).caps s with
  | some _ => some ⟨d, s, (σ.doms d).slotGen s⟩
  | none => none

/-- Is `r` a live reference (entry present at its generation)? -/
def liveRef (r : CapRef) : Bool :=
  ((σ.doms r.dom).liveCap r.slot r.gen).isSome

/-- The parent reference of the capability in `(d, s)`, if it is derived. -/
def parentOf (d : DomainId) (s : Slot) : Option CapRef := do
  let e ← (σ.doms d).caps s
  let l ← e.lineage
  let cell ← (σ.doms d).lineage l
  pure cell.parent

/-- Lowest free capability slot of domain `d` (unoccupied and not retired). -/
def freeSlot (d : DomainId) : Option Slot :=
  (List.finRange numSlots).find? fun s =>
    ((σ.doms d).caps s).isNone && (σ.doms d).slotGen s != genRetired

/-- Lowest free lineage cell of domain `d`. -/
def freeCell (d : DomainId) : Option LineageId :=
  (List.finRange numLineage).find? fun l => ((σ.doms d).lineage l).isNone

/-- Install a fresh derived capability in `(d, s)` with lineage cell `l`
pointing at `parent`. Caller guarantees `s`/`l` are free. Returns the new
state and the new capability's reference. -/
def installDerived (d : DomainId) (s : Slot) (l : LineageId)
    (kind : CapKind) (parent : CapRef) : MachineState × CapRef :=
  let g := (σ.doms d).slotGen s
  (σ.setDom d fun ds =>
    { ds with
      caps := Loom.Fun.update ds.caps s (some { kind := kind, lineage := some l })
      lineage := Loom.Fun.update ds.lineage l (some { parent := parent }) },
   ⟨d, s, g⟩)

/-- Rewrite every lineage cell whose parent is `old` to point at `new`
(the reparent pass under capability transfer). -/
def reparent (old new : CapRef) : MachineState :=
  { σ with doms := fun d =>
      let ds := σ.doms d
      { ds with lineage := fun l =>
          match ds.lineage l with
          | some cell => some (if cell.parent = old then { parent := new } else cell)
          | none => none } }

/-- Orphan every child of `old`: children become roots (their cells are
freed, their entries drop the lineage index). Used when a *root* capability
is dropped or moved: there is no ancestor to splice to. -/
def orphanChildren (old : CapRef) : MachineState :=
  { σ with doms := fun d =>
      let ds := σ.doms d
      let isChild : LineageId → Bool := fun l =>
        match ds.lineage l with
        | some cell => cell.parent = old
        | none => false
      { ds with
        caps := fun s =>
          match ds.caps s with
          | some e =>
            match e.lineage with
            | some l => some (if isChild l then { e with lineage := none } else e)
            | none => some e
          | none => none
        lineage := fun l => if isChild l then none else ds.lineage l } }

/-- Remove the capability in `(d, s)`: clear the entry, free its lineage
cell, bump the slot generation (saturating). Children must have been
reparented or orphaned by the caller. -/
def clearSlot (d : DomainId) (s : Slot) : MachineState :=
  σ.setDom d fun ds =>
    { ds with
      caps := Loom.Fun.update ds.caps s none
      lineage := match ds.caps s with
        | some e => match e.lineage with
          | some l => Loom.Fun.update ds.lineage l none
          | none => ds.lineage
        | none => ds.lineage
      slotGen := Loom.Fun.update ds.slotGen s (bumpGen (ds.slotGen s)) }

/-- Halt domain `d` with the given cause word, unwinding a gate activation
if `d` was serving one: the suspended caller resumes with `-ECALLEEFAULT`
in its reply register and the gate frees. The T6 no-hostage mechanism — a
server that faults, halts, or exhausts its donation cannot hold its caller
blocked. -/
def haltBase (d : DomainId) (cause : Loom.Word32) : MachineState :=
  σ.setDom d fun ds => { ds with run := .halted, cause := cause, serving := none }

/-- Free gate `g` and resume its caller `cl` (reply register `rd`) as running,
delivering `-ECALLEEFAULT`. The unwind step of `haltDom`, factored out so its
projections have clean equation lemmas. -/
def unwindGate (g : GateId) (cl : DomainId) (rd : RegId) : MachineState :=
  ({ σ with gates := Loom.Fun.update σ.gates g { (σ.gates g) with act := none } }).setDom
    cl fun ds => ({ ds with run := .running } : DomainState).setReg rd Errno.calleeFault.toWord

def haltDom (d : DomainId) (cause : Loom.Word32) : MachineState :=
  match (σ.doms d).serving with
  | none => σ.haltBase d cause
  | some g =>
      match (σ.gates g).act with
      | none => σ.haltBase d cause
      | some a => (σ.haltBase d cause).unwindGate g a.caller a.callerRd

/-! ## Descendant marking (the revoke sweep) -/

/-- One propagation step of descendant marking from `root`: a capability is
marked if its parent is `root`, or its parent is a live, already-marked
capability. -/
def markStep (root : CapRef) (m : DomainId → Slot → Bool) :
    DomainId → Slot → Bool :=
  fun d s =>
    m d s ||
    match σ.parentOf d s with
    | some p =>
        p = root ||
        (decide (p.gen = (σ.doms p.dom).slotGen p.slot) && m p.dom p.slot)
    | none => false

/-- Iterate `markStep` to fixpoint: `numDomains × numSlots` iterations bound
every chain. -/
def marks (root : CapRef) : DomainId → Slot → Bool :=
  (numDomains * numSlots).fold (fun _ _ m => σ.markStep root m) (fun _ _ => false)

/-- Destroy every marked capability: clear entries and their cells, bump
slot generations. One pointwise pass. -/
def destroyMarked (m : DomainId → Slot → Bool) : MachineState :=
  { σ with doms := fun d =>
      let ds := σ.doms d
      let cellDead : LineageId → Bool := fun l =>
        (List.finRange numSlots).any fun s =>
          m d s &&
          match ds.caps s with
          | some e => e.lineage == some l
          | none => false
      { ds with
        caps := fun s => if m d s then none else ds.caps s
        lineage := fun l => if cellDead l then none else ds.lineage l
        slotGen := fun s => if m d s && (ds.caps s).isSome
                            then bumpGen (ds.slotGen s) else ds.slotGen s } }

/-! ## Cached-authority sweeps -/

/-- Clear every region register whose backing reference is no longer live.
Idempotent normalization; `cap_revoke` runs it machine-wide. -/
def sweepRegions : MachineState :=
  { σ with doms := fun d =>
      let ds := σ.doms d
      { ds with regions := fun r =>
          match ds.regions r with
          | some rg => if σ.liveRef rg.backing then some rg else none
          | none => none } }

/-- Abort the Mover if either of its capabilities is no longer live: the
job is cleared and the status word receives `-errno staleHandle` — but only
under the owner's still-current write authority (the status write is itself
an authorized access, re-checked like every Mover access). -/
def sweepMover : MachineState :=
  match σ.mover with
  | none => σ
  | some job =>
      if σ.liveRef job.src && σ.liveRef job.dst then σ
      else
        let σ' := { σ with mover := none }
        if σ'.domCovers job.owner job.statusAddr { r := false, w := true, x := false }
        then σ'.write job.statusAddr (Errno.staleHandle.toWord)
        else σ'

/-- Transfer the live capability `(from_, s)` to domain `to_`: the entry
moves to a fresh slot (recipient's generation), its lineage cell — if any —
moves to the recipient's lineage table, children are reparented to the new
reference, and the source slot is cleared. Returns `none` when the
recipient lacks a free slot (or lineage cell, for derived capabilities).
The transferred capability's *reference identity changes*; the reparent
pass keeps every chain pointing at live references. -/
def transferCap (from_ : DomainId) (s : Slot) (to_ : DomainId) :
    Option (MachineState × CapRef) := do
  let e ← (σ.doms from_).caps s
  let oldRef : CapRef := ⟨from_, s, (σ.doms from_).slotGen s⟩
  let s' ← σ.freeSlot to_
  let newRef : CapRef := ⟨to_, s', (σ.doms to_).slotGen s'⟩
  let σ₁ ←
    match e.lineage with
    | some l => do
        let cell ← (σ.doms from_).lineage l
        let l' ← σ.freeCell to_
        -- install entry + moved cell at recipient
        let σa := σ.setDom to_ fun ds =>
          { ds with
            caps := Loom.Fun.update ds.caps s' (some { kind := e.kind, lineage := some l' })
            lineage := Loom.Fun.update ds.lineage l' (some cell) }
        pure σa
    | none =>
        pure (σ.setDom to_ fun ds =>
          { ds with caps := Loom.Fun.update ds.caps s' (some { kind := e.kind, lineage := none }) })
  let σ₂ := σ₁.reparent oldRef newRef
  -- Sweep after the move: the source domain must not retain cached authority
  -- (regions) or in-flight Mover traffic under the reference it just gave
  -- away. Found while stating T3/T8 (2026-07-03) — the proof-forced fix the
  -- charter predicts: without this sweep, gate-transferring a capability
  -- leaves the giver a live region register over the moved range.
  pure ((((σ₂.clearSlot from_ s).sweepRegions).sweepMover), newRef)

end MachineState
end Machines.Lnp64u
