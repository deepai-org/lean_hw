-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Std.Tactic.BVDecide

/-!
# LRAT certificates (L2, the trusted piece)

The certificate boundary of the whole decision-procedure layer: SAT solvers
(untrusted, subprocess — `Loom/Dp/Solver.lean`) answer UNSAT with an LRAT
proof, and the *only* thing the trusted path consumes is
`Loom.Dp.Cert.unsatOfLrat`, whose checking happens by kernel reduction of
the verified checker.

Per Rule 4 / P8 the checker itself is Lean core's (`Std.Tactic.BVDecide.LRAT`)
— a generic, kernel-checked lemma library, not domain code. What we do *not*
inherit is `bv_decide`'s trust posture: that tactic evaluates the checker
with `ofReduceBool` (native code). Rule 1 forbids that on our trusted path,
so engines discharge certificates with plain `decide` (kernel reduction).
The Phase-0 benchmark for this trade lives in `Tests/LratBench.lean`; its
numbers are recorded at PLAN.md D2.
-/

namespace Loom.Dp.Cert

open Std.Sat Std.Tactic.BVDecide

/-- A CNF formula over `Nat` variables (`Std.Sat.CNF`: a list of clauses,
each a list of (variable, polarity) pairs). -/
abbrev Cnf := CNF Nat

/-- An LRAT certificate. -/
abbrev LratCert := Array LRAT.IntAction

/-- Parse a textual (or binary) LRAT proof as produced by cadical. -/
def parseLrat (bytes : ByteArray) : Except String LratCert :=
  LRAT.parseLRATProof bytes

/-- Run the verified checker. Engines call this inside `decide` so the
judgment is established by the kernel, never by compiled code. -/
def checkLrat (cert : LratCert) (f : Cnf) : Bool :=
  LRAT.check cert f

/-- The certificate theorem: a checked LRAT proof establishes
unsatisfiability. This is the single entry point from solver output to the
trusted path. -/
theorem unsatOfLrat (cert : LratCert) (f : Cnf)
    (h : checkLrat cert f = true) : f.Unsat :=
  LRAT.check_sound cert f h

end Loom.Dp.Cert
