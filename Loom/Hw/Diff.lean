-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Syntax
import Loom.Hw.Semantics
import Loom.Hw.StateCover
import Loom.Hw.FastEval
import Loom.Runner

/-!
# Derived state comparison (PLATONIC W5)

`StateCover.lean` checks that a *hand-written* comparator covers every declared
register and memory. That is the weaker half of the idea: it turns forgetting
into a named failure, but somebody still writes and maintains the comparator,
and every machine writes its own.

This file removes the hand-written comparator. The `Design` already declares
its registers (name, width) and memories (name, address width, data width), so
the complete comparison is *derivable* — and a comparison derived from the
declarations cannot omit a declaration. There is nothing left to cover-check.

That matters because the omissions were not hypothetical. `lnp64mini`'s
hand-written `cmpStates` silently skipped EXT-2's `tdom`, EXT-7's five TLB
memories, and EXT-5/EXT-6's gate table, continuation and capability inbox —
each time leaving a cross-check that reported agreement it had never tested.
Each was found later, by accident.

## Scope, honestly

This is the *comparator* half of W5. The other half — deriving the reference
model itself from the `Design`, so that equality is a theorem rather than a
test — is not done, and nothing here should be read as claiming it. What this
gives is: whatever reference a machine compares against, the comparison itself
is complete by construction.
-/

namespace Loom.Hw

/-- One observable state coordinate: a register entry or a memory cell. -/
structure Coord where
  kind  : String          -- "reg" or "mem"
  name  : String
  addr  : Nat             -- 0 for registers
  width : Nat
  deriving Repr, BEq

/-- Render a coordinate the way a failure message wants it. -/
def Coord.render (c : Coord) : String :=
  if c.kind = "reg" then c.name else s!"{c.name}[{c.addr}]"

/-- Every register coordinate a design declares. -/
def Design.regCoords (d : Design) : List Coord :=
  d.regs.map fun r => { kind := "reg", name := r.name, addr := 0, width := r.width }

/-- Every memory coordinate a design declares, up to `cap` cells per memory.

The cap exists because a memory's address space is `2 ^ addrWidth` and some are
large enough that enumerating them all would dominate a cycle-level run. It is
an explicit argument rather than a constant so a caller can say what it wants,
and `memCoordsFull` is available when the answer is "all of them". -/
def Design.memCoords (d : Design) (cap : Nat) : List Coord :=
  d.mems.flatMap fun m =>
    (List.range (min cap (2 ^ m.addrWidth))).map fun a =>
      { kind := "mem", name := m.name, addr := a, width := m.dataWidth }

def Design.memCoordsFull (d : Design) : List Coord :=
  d.mems.flatMap fun m =>
    (List.range (2 ^ m.addrWidth)).map fun a =>
      { kind := "mem", name := m.name, addr := a, width := m.dataWidth }

/-- The complete observable footprint of a design, derived from its own
declarations. Nothing here is hand-maintained, so nothing here can be
forgotten. -/
def Design.coords (d : Design) (cap : Nat) : List Coord :=
  d.regCoords ++ d.memCoords cap

/-- Read a coordinate out of a state. -/
def St.at (σ : St) (c : Coord) : Nat :=
  if c.kind = "reg" then (σ.regs c.name c.width).toNat
  else (σ.mems c.name c.addr c.width).toNat

/-- Every coordinate on which two states of the same design differ. -/
def Design.diffCoords (d : Design) (cap : Nat) (σ τ : St) : List Coord :=
  (d.coords cap).filter fun c => σ.at c ≠ τ.at c

/-- Compare a design state against a reference *reader*.

The reference model is not a `St` — it is whatever the machine's ISS or
emulator happens to be — so it is supplied as a function from a coordinate to
its value there. `none` means "the reference does not model this coordinate",
which is reported separately from a mismatch: an unmodelled coordinate is a
gap in the reference, not a disagreement, and conflating the two is how a
comparator ends up quietly skipping state. -/
def Design.diffAgainst (d : Design) (cap : Nat) (σ : St)
    (ref : Coord → Option Nat) : List Coord × List Coord :=
  let cs := d.coords cap
  let mism := cs.filter fun c => match ref c with
    | some v => σ.at c ≠ v
    | none   => false
  let unmodelled := cs.filter fun c => (ref c).isNone
  (mism, unmodelled)

/-- A ready-made failure message naming the first `k` differing coordinates and
the values on each side. -/
def Design.diffReport (d : Design) (cap : Nat) (σ : St)
    (ref : Coord → Option Nat) (k : Nat) : String :=
  let (mism, unmodelled) := d.diffAgainst cap σ ref
  if mism.isEmpty then ""
  else
    let lines := (mism.take k).map fun c =>
      s!"  {c.render}: design={σ.at c} reference={(ref c).getD 0}"
    s!"{d.name}: {mism.length} coordinate(s) differ" ++
    (if unmodelled.isEmpty then "" else
      s!" ({unmodelled.length} not modelled by the reference)") ++ "\n" ++
    String.intercalate "\n" lines

/-! ## Index-resolved comparison against `FastEval`

Comparing against the closure-based `St` is correct and slow: `RegEnv` is a
*function*, so each read walks a closure chain that grows with the cycle count.
A 39-opcode by 9-vector matrix did not finish in twenty minutes that way.

`FastEval` already flattens the state into two `Array Nat`s. What was missing
is a way to read *coordinates* out of it without a name lookup per access —
`peek` does `findIdx?` over the register names every call, which is fine for
readback and quadratic inside a comparison loop.

A `CoordPlan` resolves every coordinate to its flat index **once**, so a
per-cycle comparison is a walk of array reads. The plan depends only on the
design, so it is built outside the loop and reused for the whole run. -/

/-- A coordinate with its flat index already resolved. -/
structure CoordSlot where
  coord : Coord
  isReg : Bool
  idx   : Nat
  deriving Repr

/-- Resolve every coordinate of a design to a flat `FastSt` index, once.

Coordinates that do not resolve are dropped rather than silently read as zero:
a coordinate the flat layout has no slot for is a bug in the plan, and reading
it as zero would manufacture agreement — the exact failure mode this whole file
exists to remove. -/
def Design.coordPlan (d : Design) (cap : Nat) : Array CoordSlot :=
  (d.coords cap).foldl (fun acc c =>
    if c.kind = "reg" then
      match d.regIdx c.name with
      | some i => acc.push { coord := c, isReg := true, idx := i }
      | none   => acc
    else
      match d.memIdx c.name with
      | some k => acc.push { coord := c, isReg := false, idx := d.memBase k + c.addr }
      | none   => acc) #[]

/-- Fail-closed coordinate-plan construction. The raw `coordPlan` is useful
for proofs and inspection, but executable comparison paths must not accept a
plan that resolved fewer entries than `Design.coords` declared. -/
def Design.coordPlan? (d : Design) (cap : Nat) : Option (Array CoordSlot) :=
  let plan := d.coordPlan cap
  if plan.size = (d.coords cap).length then some plan else none

/-- IO adapter for executable gates. A layout/declaration disagreement names
the design and both counts instead of silently shrinking comparison coverage. -/
def Design.prepareCoordPlan (d : Design) (cap : Nat) : IO (Array CoordSlot) :=
  match d.coordPlan? cap with
  | some plan => pure plan
  | none => throw <| IO.userError (
      s!"{d.name}: derived coordinate plan failed: " ++
      s!"declared={(d.coords cap).length}, resolved={(d.coordPlan cap).size}")

/-- Read a resolved coordinate out of a flat state: two array reads, no lookup. -/
def FastSt.atSlot (fs : FastSt) (s : CoordSlot) : Nat :=
  if s.isReg then fs.regs.getD s.idx 0 else fs.mems.getD s.idx 0

/-! ## Oracles with declared coverage

`diffAgainst` reports unmodelled coordinates, but reporting is not refusing:
a machine's harness that only *counts* them lets NEW design state join the
unmodelled set silently, and the run stays green — an omission
indistinguishable from agreement, the exact failure mode this file exists to
remove, one level up. (Found live on `lnp64mini`, 2026-08-06: the ISS oracle's
fall-through answered `none` for any memory it did not know, so the unmodelled
set was open-ended and only its count was visible.)

An `Oracle` therefore carries its exclusions as a CLOSED, named list. The
comparison then has three outcomes per coordinate, not two: agree/disagree,
declared-unmodelled, and **undeclared-unmodelled — which is a failure**, named
after the coordinate, not a count. -/

/-- A reference model with declared coverage: the reader, plus the names of
the design state it deliberately does not model (with the reason kept at the
declaration site). `none` from `read` on a name outside `unmodelled` is a
harness bug or a new design element nobody taught the oracle about — either
way it must fail the run, not shrink it. -/
structure Oracle where
  read       : Coord → Option Nat
  unmodelled : List String := []

/-- Compare against an oracle with declared coverage.

Returns `(mismatches, undeclared)`: `undeclared` is every coordinate the
oracle failed to model WITHOUT declaring it, and a caller must treat a
non-empty `undeclared` exactly like a mismatch. Declared-unmodelled
coordinates are accounted (they are the third component) but are not
failures — they are the oracle's honest, named scope boundary. -/
def Design.diffAgainstOracle (d : Design) (cap : Nat) (σ : St)
    (o : Oracle) : List Coord × List Coord × List Coord :=
  let (mism, unm) := d.diffAgainst cap σ o.read
  let (declared, undeclared) := unm.partition (fun c => o.unmodelled.contains c.name)
  (mism, undeclared, declared)

/-- Compare a flat state against a reference reader over a prepared plan.

Same contract as `diffAgainst`: mismatches and unmodelled coordinates are
returned separately, because a reference that does not model a coordinate has
not agreed about it.


Mismatches carry BOTH values, so a caller can report them without going back
to the plan to re-resolve the index -- doing that by hand is easy to get wrong
(reconstructing a slot with the wrong index prints a plausible, false value). -/
def diffFastAgainst (plan : Array CoordSlot) (fs : FastSt)
    (ref : Coord → Option Nat) : List (Coord × Nat × Nat) × List Coord :=
  plan.foldl (fun (acc : List (Coord × Nat × Nat) × List Coord) s =>
    match ref s.coord with
    | some v =>
        let got := fs.atSlot s
        if got ≠ v then ((s.coord, got, v) :: acc.1, acc.2) else acc
    | none   => (acc.1, s.coord :: acc.2)) ([], [])

/-- The flat-state comparison against an `Oracle` with declared coverage —
same three-way contract as `Design.diffAgainstOracle`: mismatches,
UNDECLARED-unmodelled (a failure), declared-unmodelled (the oracle's named
scope boundary). Every comparison loop should go through one of these two;
calling `diffFastAgainst` and dropping its second component re-opens the
silent-omission hole at the call site. -/
def diffFastAgainstOracle (plan : Array CoordSlot) (fs : FastSt)
    (o : Oracle) : List (Coord × Nat × Nat) × List Coord × List Coord :=
  let (mism, unm) := diffFastAgainst plan fs o.read
  let (declared, undeclared) := unm.partition (fun c => o.unmodelled.contains c.name)
  (mism, undeclared, declared)

/-! ## Generic-runner adapters

These are the only bridge the differential runner needs to know about hardware
coordinates. Machines provide an `Oracle`; Loom derives the complete surface
and turns every undeclared omission into a named coverage failure. -/

def Coord.event (c : Coord) (actual expected : Nat) : Loom.Runner.Event :=
  { subject := c.render, actual := some (toString actual),
    expected := some (toString expected) }

/-- Compare a closure state and package the result for `Loom.Runner.run`. -/
def Design.sampleAgainstOracle (d : Design) (cap : Nat) (σ : St)
    (o : Oracle) : Loom.Runner.Sample :=
  let (mism, undeclared, declared) := d.diffAgainstOracle cap σ o
  { mismatches := mism.map fun c => c.event (σ.at c) ((o.read c).getD 0)
    coverageGaps := undeclared.map (·.render)
    excluded := declared.map (·.render) }

/-- Compare a prepared flat state and package the result for
`Loom.Runner.run`. -/
def sampleFastAgainstOracle (plan : Array CoordSlot) (fs : FastSt)
    (o : Oracle) : Loom.Runner.Sample :=
  let (mism, undeclared, declared) := diffFastAgainstOracle plan fs o
  { mismatches := mism.map fun (c, actual, expected) => c.event actual expected
    coverageGaps := undeclared.map (·.render)
    excluded := declared.map (·.render) }

end Loom.Hw
