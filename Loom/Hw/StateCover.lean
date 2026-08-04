-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Syntax
import Loom.Hw.Semantics

/-!
# Complete state coverage for derived simulation (PLATONIC W5)

`FastEval.lean` already generates the evaluator from `Design`. The other half
of W5 — "the complete state comparator is part of the feature, not follow-up
documentation" — is this file.

**Why it exists.** A cycle-accurate cross-check is only as good as the state it
compares, and on this project the comparator has been hand-maintained. Twice
that produced tests that were green for free:

* EXT-2 added the per-thread domain tag `tdom`, and `cmpStates` did not compare
  it — so "EDSL ≡ ISS" meant "they agree on everything *except* the thing the
  increment added";
* EXT-7 added five TLB memories with the same result. A green `MMU-XLAT` meant
  the legs agreed on `core_addr`, not on the TLB.

Both were found by accident, later, and the standing rule written down
afterwards was "any increment that adds state must add it to `cmpStates` in the
same commit". That rule relies on memory. This file replaces it with a check:
the *design* enumerates its own state, the harness declares what it compared,
and anything declared-but-uncompared is a **named obligation** rather than a
silent pass.

This is deliberately the same shape as W1.1's emit-time gates: the analysis is
syntactic, it runs off the `Design`, and its failure names the missing thing.
-/

namespace Loom.Hw

/-- Every register entry a design declares, as `(name, width)`. -/
def Design.regEntries (d : Design) : List (String × Nat) :=
  d.regs.map fun r => (r.name, r.width)

/-- Every memory a design declares, as `(name, dataWidth)`. -/
def Design.memEntries (d : Design) : List (String × Nat) :=
  d.mems.map fun m => (m.name, m.dataWidth)

/-- Declared registers a comparator does not claim to cover.

`covered` is the list of names the cross-check actually compares. Inputs are
excluded on purpose: they are environment-owned (D15), driven each cycle rather
than carried in the state, so a comparator has nothing of its own to check. -/
def Design.uncoveredRegs (d : Design) (covered : List String) : List String :=
  (d.regEntries.filter fun e => !covered.contains e.1).map (·.1)

/-- Declared memories a comparator does not claim to cover. -/
def Design.uncoveredMems (d : Design) (covered : List String) : List String :=
  (d.memEntries.filter fun e => !covered.contains e.1).map (·.1)

/-- The comparator covers every declared register and memory. -/
def Design.coverageOkB (d : Design) (coveredRegs coveredMems : List String) : Bool :=
  (d.uncoveredRegs coveredRegs).isEmpty && (d.uncoveredMems coveredMems).isEmpty

/-- A report naming exactly what a comparator leaves out, for use in the
failure message. Empty string when coverage is complete. -/
def Design.coverageReport (d : Design) (coveredRegs coveredMems : List String) : String :=
  let ur := d.uncoveredRegs coveredRegs
  let um := d.uncoveredMems coveredMems
  if ur.isEmpty && um.isEmpty then ""
  else
    let regPart := if ur.isEmpty then "" else s!"registers not compared: {ur}\n"
    let memPart := if um.isEmpty then "" else s!"memories not compared: {um}\n"
    s!"{d.name}: the cross-check does not cover all declared state.\n" ++
    regPart ++ memPart ++
    "A comparator that skips state reports agreement it never checked. Add " ++
    "these to the comparator, or name them explicitly as deliberately " ++
    "unobservable."

/-- Coverage is exactly "no declared entry is missing from `covered`". Stated
so a caller can turn the Boolean check into the membership fact it wants. -/
theorem Design.mem_of_coverageOkB_regs {d : Design} {cr cm : List String}
    (h : d.coverageOkB cr cm = true) :
    ∀ e ∈ d.regEntries, cr.contains e.1 = true := by
  intro e he
  have h1 : (d.uncoveredRegs cr).isEmpty = true := by
    simp only [Design.coverageOkB, Bool.and_eq_true] at h; exact h.1
  have h2 : (d.regEntries.filter fun e => !cr.contains e.1) = [] := by
    simpa [Design.uncoveredRegs, List.isEmpty_iff, List.map_eq_nil_iff] using h1
  have := List.filter_eq_nil_iff.mp h2 e he
  simpa using this

theorem Design.mem_of_coverageOkB_mems {d : Design} {cr cm : List String}
    (h : d.coverageOkB cr cm = true) :
    ∀ e ∈ d.memEntries, cm.contains e.1 = true := by
  intro e he
  have h1 : (d.uncoveredMems cm).isEmpty = true := by
    simp only [Design.coverageOkB, Bool.and_eq_true] at h; exact h.2
  have h2 : (d.memEntries.filter fun e => !cm.contains e.1) = [] := by
    simpa [Design.uncoveredMems, List.isEmpty_iff, List.map_eq_nil_iff] using h1
  have := List.filter_eq_nil_iff.mp h2 e he
  simpa using this

/-- Fail loudly at check time, naming what is missing. The intended use is one
call at the top of a cross-check, so that adding state to a design breaks the
test that would otherwise have passed without looking at it. -/
def Design.assertCoverage (d : Design) (coveredRegs coveredMems : List String) :
    IO Unit := do
  let r := d.coverageReport coveredRegs coveredMems
  if r ≠ "" then throw <| IO.userError r

end Loom.Hw
