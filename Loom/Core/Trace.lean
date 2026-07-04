-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
/-!
# The lockstep trace format (frozen, task 0.15)

One event stream, three producers: a machine's ISS, its RTL simulation
(L3), and hardware capture (L7). The lockstep harness diffs streams; a
divergence localizes a bug (or a vendor miscompilation) below the boundary.

Machine-generic by construction: all payloads are `Nat` (machines have
different widths), producers agree on meaning per event kind. The text
codec is part of the freeze — hardware-side capture scripts parse it, so
`parse ∘ print = id` is checked in `Tests/`.

Granularity: retirements, halts, Mover/DMA words, and status writes — the
observable protocol events. Full-state divergence hunting uses the ISS
directly; the trace is the cross-producer format.
-/

namespace Loom.Trace

/-- One trace event. -/
inductive Event where
  /-- An instruction retired: executing unit (domain), its PC (word
  address), the instruction word. -/
  | retire (dom pc word : Nat)
  /-- A unit halted (voluntarily or by fault), with its cause code. -/
  | halt (dom cause : Nat)
  /-- A DMA master (the Mover) copied one word. -/
  | dma (srcAddr dstAddr : Nat)
  /-- A completion-status write: address and value. -/
  | status (addr value : Nat)
deriving Repr, DecidableEq

/-- A timestamped event. -/
structure Line where
  cycle : Nat
  event : Event
deriving Repr, DecidableEq

/-- The frozen text form: one line per event, space-separated fields. -/
def Line.print (l : Line) : String :=
  match l.event with
  | .retire d p w => s!"{l.cycle} R {d} {p} {w}"
  | .halt d c     => s!"{l.cycle} H {d} {c}"
  | .dma s d      => s!"{l.cycle} D {s} {d}"
  | .status a v   => s!"{l.cycle} S {a} {v}"

/-- Parse one trace line (the harness side of the codec). -/
def Line.parse (s : String) : Option Line := do
  match s.splitOn " " with
  | [c, "R", d, p, w] => do
      pure { cycle := ← c.toNat?, event := .retire (← d.toNat?) (← p.toNat?) (← w.toNat?) }
  | [c, "H", d, cs] => do
      pure { cycle := ← c.toNat?, event := .halt (← d.toNat?) (← cs.toNat?) }
  | [c, "D", sa, da] => do
      pure { cycle := ← c.toNat?, event := .dma (← sa.toNat?) (← da.toNat?) }
  | [c, "S", a, v] => do
      pure { cycle := ← c.toNat?, event := .status (← a.toNat?) (← v.toNat?) }
  | _ => none

/-- Codec round-trip, proved once for the format (a small `decide`-free
structural proof is Phase-2 work with the µVerilog parser; checked by
golden tests until then). -/
def roundTrips (l : Line) : Bool := Line.parse (Line.print l) == some l

end Loom.Trace
