-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Syntax
import Loom.Hw.Semantics
import Loom.Hw.StateCover

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

end Loom.Hw
