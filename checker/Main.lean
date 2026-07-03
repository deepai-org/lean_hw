import Chk.Lrat

/-!
`chk formula.cnf proof.lrat` — exit 0 and print `VERIFIED UNSAT` iff the
LRAT proof checks against the formula; exit 1 with a reason otherwise.
Untrusted compiled cross-validator (see `Chk.Lrat` module docstring).
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | [cnfPath, lratPath] =>
    let run : ExceptT String IO Unit := do
      let cnfText ← IO.FS.readFile cnfPath
      let lratText ← IO.FS.readFile lratPath
      let cnf ← ExceptT.mk (pure (Chk.parseDimacs cnfText))
      let steps ← ExceptT.mk (pure (Chk.parseLrat lratText))
      ExceptT.mk (pure (Chk.check cnf steps))
    match ← run.run.toBaseIO with
    | .ok (.ok ()) =>
      IO.println "VERIFIED UNSAT"
      return 0
    | .ok (.error e) =>
      IO.eprintln s!"REJECTED: {e}"
      return 1
    | .error e =>
      IO.eprintln s!"ERROR: {e}"
      return 1
  | _ =>
    IO.eprintln "usage: chk formula.cnf proof.lrat"
    return 1
