-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Dp.Cert.Lrat

/-!
Loom-side leg of the LRAT cross-check (`scripts/crosscheck_lrat.sh`).

Runs the *proved* checker (`Loom.Dp.Cert.checkLrat`, i.e. Lean core's
verified `Std.Tactic.BVDecide.LRAT.check`) on the same DIMACS/LRAT files
that the independent `checker/` package checks, so the two
implementations' verdicts can be compared. Evaluation here is by the
interpreter (`lake env lean --run`), not by `decide` — this script is a
cross-validation harness, not the trusted path (which lives in engine
proofs).

Usage: `lake env lean --run scripts/loom_check_lrat.lean f.cnf p.lrat`
-/

open Loom.Dp.Cert

/-- Minimal DIMACS parser for the harness: DIMACS literal `l` becomes
`(l.natAbs - 1, l > 0)` in `Std.Sat.CNF Nat` — the checker's conversion
shifts `Nat` variables up by one (`CNF.lift`), while the LRAT proof's
literals map to internal variable `l.natAbs` directly, so DIMACS variable
`d` must enter the CNF as `d - 1`. -/
def parseDimacs (text : String) : Except String Cnf := do
  let mut clauses : Cnf := []
  let mut cur : List (Nat × Bool) := []
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "c" || line.startsWith "p" then
      continue
    for tok in line.splitOn " " |>.filter (· ≠ "") do
      match tok.toInt? with
      | none => throw s!"not an integer: '{tok}'"
      | some 0 => clauses := clauses ++ [cur.reverse]; cur := []
      | some l => cur := (l.natAbs - 1, l > 0) :: cur
  unless cur.isEmpty do throw "unterminated final clause"
  return clauses

def main (args : List String) : IO UInt32 := do
  let [cnfPath, lratPath] := args
    | IO.eprintln "usage: loom_check_lrat.lean f.cnf p.lrat"; return 2
  let cnfText ← IO.FS.readFile cnfPath
  let lratBytes ← IO.FS.readBinFile lratPath
  match parseDimacs cnfText with
  | .error e => IO.eprintln s!"loom-side: DIMACS parse error: {e}"; return 1
  | .ok cnf =>
    match parseLrat lratBytes with
    | .error e => IO.eprintln s!"loom-side: LRAT parse error: {e}"; return 1
    | .ok cert =>
      if checkLrat cert cnf then
        IO.println "loom-side: VERIFIED UNSAT"; return 0
      else
        IO.eprintln "loom-side: REJECTED"; return 1
