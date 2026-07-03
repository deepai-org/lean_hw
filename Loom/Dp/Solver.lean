import Loom.Dp.Cnf
import Loom.Dp.Bmc

/-!
# Untrusted SAT-solver driver (task 1.2, decision D2/D4)

IO glue that ships a `CNF Nat` to `cadical --no-binary --lrat`, reads back
the LRAT refutation, and translates it into the `Check.Step` list the
kernel-reducible checker (`Loom/Dp/Cert/Check.lean`) re-verifies. **Nothing
here is on any theorem's trusted path** — the solver may be buggy, absent,
or adversarial; a returned certificate is only believed once
`Check.check … = true` reduces in the kernel (`Bmc.bmc_sound`).

If `cadical` is not installed, `solve` returns `.error "cadical unavailable"`
and callers fall back to a pre-generated committed certificate (see
`Tests/Acc8Bmc.lean`, whose certificate was produced by this exact
translation, mirrored in `scripts/lrat_to_step.py`).

The DIMACS/LRAT variable space is compacted to `1 … N`; the translation
un-compacts literals back to the original `Var`-renamed ids and converts
LRAT clause ids to newest-first accumulator *positions* exactly as
`Check.check` consumes them (learned clauses prepended; see that file).
-/

namespace Loom.Dp.Solver

open Loom.Dp.Cnf Loom.Dp.Cert Std.Sat

/-- Collect the distinct variables of a formula, in first-occurrence order:
compact id `i+1` denotes `vars[i]`. -/
def collectVars (F : CNF Nat) : Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Nat := #[]
  for c in F do
    for (v, _) in c do
      if !seen.contains v then
        seen := seen.insert v
        out := out.push v
  return out

/-- DIMACS text for `F` plus the compact→original variable table. -/
def toDimacs (F : CNF Nat) : String × Array Nat := Id.run do
  let vars := collectVars F
  let mut idx : Std.HashMap Nat Nat := {}
  for h : i in [0:vars.size] do
    idx := idx.insert vars[i] (i + 1)
  let mut lines : Array String := #[s!"p cnf {vars.size} {F.length}"]
  for c in F do
    let mut line := ""
    for (v, pol) in c do
      let cid := idx.getD v 0
      line := line ++ (if pol then "" else "-") ++ toString cid ++ " "
    lines := lines.push (line ++ "0")
  return (String.intercalate "\n" lines.toList ++ "\n", vars)

/-- Parse a single ASCII-LRAT addition line into `(clause, hints)` in
`Check.Step` form, given the original-variable table and the number of
original clauses `norig`, and the count `m` of clauses learned so far. -/
def parseAddLine (orig : Array Nat) (norig m : Nat) (toks : List Nat)
    (neg : List Bool) : Option (Check.Step) := do
  -- `toks`/`neg` are the token magnitudes / signs after the clause id.
  -- Layout: <lits> 0 <hints> 0.
  let z ← toks.idxOf? 0
  let litToks := (toks.take z).zip (neg.take z)
  let clause : Check.Clause :=
    litToks.filterMap (fun (mag, isNeg) =>
      if mag = 0 then none
      else some (orig[mag - 1]!, !isNeg))
  let afterLits := toks.drop (z + 1)
  let z2 ← afterLits.idxOf? 0
  let hintIds := afterLits.take z2
  let hints := hintIds.map (fun idv =>
    if idv ≤ norig then m + (idv - 1) else m - 1 - (idv - norig - 1))
  return .add clause hints

/-- Translate a whole ASCII-LRAT proof into a `Check.Step` list (deletions
dropped — the checker ignores them). -/
def parseLrat (orig : Array Nat) (norig : Nat) (lrat : String) : List Check.Step := Id.run do
  let mut steps : Array Check.Step := #[]
  let mut m := 0
  for line in lrat.splitOn "\n" do
    let toks := (line.splitOn " ").filter (· ≠ "")
    if toks.length < 2 then continue
    if toks[1]! == "d" then continue        -- deletion line
    -- drop the clause id (toks[0]); parse the rest
    let rest := toks.drop 1
    let mags := rest.map (fun s => (s.toInt?.getD 0).natAbs)
    let negs := rest.map (fun s => decide ((s.toInt?.getD 0) < 0))
    match parseAddLine orig norig m mags negs with
    | some st => steps := steps.push st; m := m + 1
    | none => pure ()
  return steps.toList

/-- Run cadical on `F` and return a translated certificate, or an error
(e.g. cadical unavailable). Untrusted. -/
def solve (F : CNF Nat) : IO (Except String (List Check.Step)) := do
  let (dimacs, vars) := toDimacs F
  let tmp ← IO.FS.createTempFile
  let base := tmp.2.toString
  let cnfPath := base ++ ".cnf"
  let lratPath := base ++ ".lrat"
  IO.FS.writeFile cnfPath dimacs
  try
    let out ← IO.Process.output
      { cmd := "cadical", args := #["--no-binary", "--lrat", cnfPath, lratPath] }
    -- cadical exits 20 on UNSAT.
    if out.exitCode ≠ 20 then
      return .error s!"cadical did not report UNSAT (exit {out.exitCode})"
    let lrat ← IO.FS.readFile lratPath
    return .ok (parseLrat vars F.length lrat)
  catch e =>
    return .error s!"cadical unavailable: {e.toString}"

end Loom.Dp.Solver
