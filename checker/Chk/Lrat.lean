-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# `Chk.Lrat` — the independent RUP/LRAT cross-validator

This package is the *independent-implementation* leg of the certificate
story (charter Phase 3; PLAN P6 / §8 4.2): a second checker, written from
the LRAT semantics alone, that cross-validates the verdicts of the
proved-in-Lean checker consumed by `Loom.Dp.Cert` — on the very same
DIMACS/LRAT files. Diversity over proof: this code carries **no**
soundness theorem and makes **no** trusted claims, so `partial`
functions, `Array`, hash maps, and compiled execution are all fine here.
It must never import Loom, Machines, Std.Sat, or Mathlib.

## Formats

* **DIMACS CNF** (what cadical reads): `c` comment lines, one
  `p cnf <vars> <clauses>` header, then clauses as whitespace-separated
  nonzero integer literals each terminated by `0`. Clauses are implicitly
  numbered `1..n` in order of appearance.

* **LRAT, textual** (what `cadical --lrat --no-binary` emits):
  - addition line: `<id> <lit>* 0 <hint>* 0` — clause `<id>` (strictly
    increasing) with a RUP derivation given by the positive clause-id
    hints, in propagation order. Negative hints (RAT steps) are rejected;
    cadical's native LRAT is RUP-only.
  - deletion line: `<id> d <clauseId>* 0` — the leading `<id>` is
    ignored (it is just the current step counter); each listed clause is
    removed from the live set and may not be referenced afterwards.
  - the proof succeeds when an addition of the *empty* clause checks.

## RUP checking

To check clause `C` with hint list `H` against the live clauses: assume
every literal of `C` false (if `C` is a tautology this is already
contradictory and `C` is trivially valid), then process hints in order —
each hinted clause must be either falsified (conflict: done) or unit
under the current assignment, in which case its remaining literal is
asserted. Anything else (satisfied hint, non-unit hint, dead or unknown
clause id, hints exhausted without conflict) is a rejection.
-/

namespace Chk

/-- A DIMACS literal: a nonzero integer, sign = polarity. -/
abbrev Lit := Int

/-- A clause, as parsed (no dedup, no sorting — we check what's on disk). -/
abbrev Clause := Array Lit

/-- A parsed DIMACS formula. -/
structure Cnf where
  numVars : Nat
  clauses : Array Clause
  deriving Repr

/-- One LRAT proof step. -/
inductive Step where
  /-- `id lits 0 hints 0` — add clause `id` justified by RUP over `hints`. -/
  | add (id : Nat) (lits : Array Lit) (hints : Array Nat)
  /-- `_ d ids 0` — delete the listed live clauses. -/
  | del (ids : Array Nat)
  deriving Repr

/-! ## Parsing -/

private def parseInt (tok : String) : Except String Int :=
  match tok.toInt? with
  | some i => .ok i
  | none => .error s!"not an integer: '{tok}'"

/-- Parse DIMACS CNF text. Tolerates leading comments and blank lines;
requires exactly one `p cnf` header before the clauses. -/
def parseDimacs (text : String) : Except String Cnf := do
  let mut numVars : Nat := 0
  let mut numClauses : Nat := 0
  let mut sawHeader := false
  let mut clauses : Array Clause := #[]
  let mut cur : Array Lit := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "c" then
      continue
    if line.startsWith "p" then
      if sawHeader then throw "duplicate DIMACS header"
      match line.splitOn " " |>.filter (· ≠ "") with
      | ["p", "cnf", v, n] =>
        numVars := (← parseInt v).toNat
        numClauses := (← parseInt n).toNat
        sawHeader := true
      | _ => throw s!"malformed DIMACS header: '{line}'"
      continue
    if !sawHeader then throw "clause before 'p cnf' header"
    for tok in line.splitOn " " |>.filter (· ≠ "") do
      let l ← parseInt tok
      if l == 0 then
        clauses := clauses.push cur
        cur := #[]
      else
        if l.natAbs > numVars then
          throw s!"literal {l} exceeds declared variable count {numVars}"
        cur := cur.push l
  if !sawHeader then throw "missing 'p cnf' header"
  if !cur.isEmpty then throw "unterminated final clause (missing 0)"
  if clauses.size ≠ numClauses then
    throw s!"header declares {numClauses} clauses, found {clauses.size}"
  return { numVars, clauses }

/-- Parse one non-empty LRAT line into a `Step`. -/
def parseLratLine (line : String) : Except String Step := do
  let toks := line.splitOn " " |>.filter (· ≠ "")
  match toks with
  | [] => throw "empty LRAT line"
  | idTok :: rest =>
    let id ← parseInt idTok
    if id ≤ 0 then throw s!"non-positive step id {id}"
    match rest with
    | "d" :: ds =>
      -- deletion: ids terminated by 0
      let mut ids : Array Nat := #[]
      let mut closed := false
      for t in ds do
        if closed then throw s!"trailing tokens after deletion terminator: '{line}'"
        let i ← parseInt t
        if i == 0 then closed := true
        else if i < 0 then throw s!"negative clause id {i} in deletion"
        else ids := ids.push i.toNat
      if !closed then throw s!"deletion line missing terminating 0: '{line}'"
      return .del ids
    | _ =>
      -- addition: lits 0 hints 0
      let mut lits : Array Lit := #[]
      let mut hints : Array Nat := #[]
      let mut phase : Nat := 0   -- 0 = literals, 1 = hints, 2 = done
      for t in rest do
        let i ← parseInt t
        if i == 0 then
          if phase ≥ 2 then throw s!"extra terminator in: '{line}'"
          phase := phase + 1
        else if phase == 0 then
          lits := lits.push i
        else if phase == 1 then
          if i < 0 then
            throw s!"negative hint {i}: RAT steps unsupported (cadical LRAT is RUP-only)"
          hints := hints.push i.toNat
        else
          throw s!"trailing tokens after hints terminator: '{line}'"
      if phase ≠ 2 then throw s!"LRAT addition line missing terminator(s): '{line}'"
      return .add id.toNat lits hints

/-- Parse a full textual LRAT proof. -/
def parseLrat (text : String) : Except String (Array Step) := do
  let mut steps : Array Step := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "c" then
      continue
    steps := steps.push (← parseLratLine line)
  return steps

/-! ## Checking -/

/-- The live clause database, keyed by LRAT clause id. -/
abbrev Db := Std.HashMap Nat Clause

/-- Partial assignment as the set of literals currently assumed true. -/
abbrev Asg := Std.HashSet Lit

/-- Check one RUP addition: clause `c` with hint chain `hints` against the
live database. Returns `()` on success, a reason on failure. -/
def checkRup (db : Db) (c : Clause) (hints : Array Nat) : Except String Unit := do
  -- Assume every literal of `c` false.
  let mut asg : Asg := {}
  for l in c do
    if asg.contains l then
      -- `c` contains both l and -l: tautology, trivially valid.
      return ()
    asg := asg.insert (-l)
  -- Hint-driven unit propagation.
  for h in hints do
    match db.get? h with
    | none => throw s!"hint {h}: clause is not live (never added or deleted)"
    | some d =>
      let mut unassigned : Option Lit := none
      let mut count : Nat := 0
      for l in d do
        if asg.contains l then
          throw s!"hint {h}: clause is satisfied, not unit/false"
        if !asg.contains (-l) then
          unassigned := some l
          count := count + 1
      match count, unassigned with
      | 0, _ => return ()                    -- conflict reached: RUP holds
      | 1, some l => asg := asg.insert l     -- unit: propagate
      | _, _ => throw s!"hint {h}: clause has {count} unassigned literals (not unit)"
  throw "hints exhausted without reaching a conflict"

/-- Check a whole proof against a formula. `.ok ()` means VERIFIED UNSAT. -/
def check (cnf : Cnf) (steps : Array Step) : Except String Unit := do
  let mut db : Db := {}
  let mut maxId : Nat := 0
  for c in cnf.clauses do
    maxId := maxId + 1
    db := db.insert maxId c
  for step in steps do
    match step with
    | .del ids =>
      for i in ids do
        if !db.contains i then
          throw s!"delete {i}: clause is not live"
        db := db.erase i
    | .add id lits hints =>
      if id ≤ maxId then
        throw s!"add {id}: clause ids must be strictly increasing (last was {maxId})"
      match checkRup db lits hints with
      | .ok () => pure ()
      | .error e => throw s!"add {id}: {e}"
      if lits.isEmpty then
        return ()                            -- empty clause verified: UNSAT
      db := db.insert id lits
      maxId := id
  throw "proof ends without deriving the empty clause"

end Chk
