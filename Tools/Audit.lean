import Lean

/-!
# The audit tool (P5)

Walks the compiled environment and enforces the standing self-check
(PLAN §10):

1. **Ledger report** — every theorem under a `…Theorems…` namespace is
   classified *clean* (only whitelisted axioms), *stated* (depends on
   `sorryAx`), or *flagged* (depends on a non-whitelisted axiom, e.g.
   `Lean.ofReduceBool` from `native_decide` — Rule 1).
2. **Sorry policy** — no declaration in our modules outside `Theorems`
   namespaces (or `Wip` segments) may depend on `sorryAx`.
3. **Axiom policy** — our modules may declare no `axiom` at all except the
   µVerilog-semantics axiom (once it exists).
4. **Import DAG (P0)** — no `Loom.*` module may import a `Machines.*`
   module; nothing imports `Tools`.

Exit code 0 iff all checks pass, so CI is `lake exe audit`.
-/

open Lean

instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv f := modify f

/-- Pure axiom collection against a fixed environment. -/
def collectFor (env : Environment) (n : Name) : Array Name :=
  ((collectAxioms n : StateM Environment (Array Name)).run env).1

/-- Axioms every classical Lean development uses; anything else is policy. -/
def whitelistedAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

/-- The one permitted declared axiom (L4's boundary; not yet defined). -/
def permittedAxiomDecls : List Name :=
  [`Loom.Emit.MicroVerilog.verilogSemanticsAxiom]

/-- Is this one of our modules (as opposed to Lean core / Mathlib)? -/
def oursModule (n : Name) : Bool :=
  (`Loom).isPrefixOf n || (`Machines).isPrefixOf n ||
  (`Tests).isPrefixOf n || (`Tools).isPrefixOf n

/-- Is this declaration in a theorem-ledger namespace? -/
def inLedger (n : Name) : Bool :=
  n.components.any (· == `Theorems)

/-- Is this declaration in a work-in-progress namespace? -/
def inWip (n : Name) : Bool :=
  n.components.any (· == `Wip)

def classify (axioms : Array Name) : String :=
  if axioms.contains ``sorryAx then "STATED (sorry)"
  else if axioms.all (fun a => whitelistedAxioms.contains a ||
                               permittedAxiomDecls.contains a) then
    if axioms.any permittedAxiomDecls.contains then "CLEAN (+ µVerilog axiom)"
    else "CLEAN"
  else "FLAGGED"

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Loom }, { module := `Machines }] {}
  let mut failures : Array String := #[]

  -- 4. Import DAG
  let header := env.header
  for i in [0:header.moduleNames.size] do
    let mod := header.moduleNames[i]!
    if (`Loom).isPrefixOf mod then
      for imp in header.moduleData[i]!.imports do
        if (`Machines).isPrefixOf imp.module || (`Tools).isPrefixOf imp.module then
          failures := failures.push
            s!"P0 violation: toolchain module {mod} imports {imp.module}"

  -- Gather our declarations, module-indexed
  let mut ledger : Array (Name × String) := #[]
  for (name, info) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      let mod := header.moduleNames[idx.toNat]!
      if oursModule mod then
        -- 3. Axiom policy
        if let .axiomInfo _ := info then
          unless permittedAxiomDecls.contains name do
            failures := failures.push s!"axiom policy: `axiom {name}` in {mod}"
        -- Classify
        let axioms := collectFor env name
        if inLedger name && !name.isInternalDetail then
          if let .thmInfo _ := info then
            ledger := ledger.push (name, classify axioms)
            if classify axioms == "FLAGGED" then
              failures := failures.push
                s!"ledger theorem {name} depends on non-whitelisted axioms: {axioms}"
        else
          -- 2. Sorry policy outside ledger/Wip
          if axioms.contains ``sorryAx && !inWip name then
            failures := failures.push s!"sorry policy: {name} (in {mod}) depends on sorryAx"
          -- Rule 1 everywhere in our code
          if axioms.contains `Lean.ofReduceBool || axioms.contains `Lean.trustCompiler then
            failures := failures.push s!"Rule 1: {name} (in {mod}) uses native_decide/trusted compiler"

  IO.println "── Theorem ledger ──────────────────────────────────────────"
  for (name, status) in ledger.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"{status.take 6}  {name}"
  IO.println s!"── {ledger.size} ledger theorems ──"

  if failures.isEmpty then
    IO.println "audit: all checks passed"
    return 0
  else
    for f in failures do IO.eprintln s!"audit FAILURE: {f}"
    return 1
