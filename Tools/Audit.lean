-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lean

/-!
# The audit tool (P5)

Walks the compiled environment and enforces the standing self-check
(the repository trust policy):

1. **Ledger report** — every theorem under a `…Theorems…` namespace is
   classified *clean* (only whitelisted axioms), *stated* (depends on
   `sorryAx`), or *flagged* (depends on a non-whitelisted axiom, e.g.
   `Lean.ofReduceBool` from `native_decide` — Rule 1).
2. **Sorry policy** — no declaration in our modules outside `Theorems`
   namespaces (or `Wip` segments) may depend on `sorryAx`.
3. **Axiom policy** — our modules may declare no `axiom` at all except the
   two declarations that expose the µVerilog tool-boundary assumption:
   `ImplementsStandard` and `implements_standard_spec`.
4. **Import DAG (P0)** — no `Loom.*` module may import `Machines.*`,
   `Evidence.*`, or `Tools.*`; nothing imports `Tools`.
5. **Executable trust surface** — every project `unsafe` declaration and
   `implemented_by` replacement is an explicit declaration-level whitelist;
   source `partial` and `extern` declarations are forbidden. Compiler-
   generated structural-recursion helpers ending in `_unsafe_rec` are not
   source `partial` declarations and are ignored.

Exit code 0 iff all checks pass, so CI is `lake exe audit`.
-/

open Lean

/-- State shared by all axiom-closure queries. Lean's stock `collectAxioms`
memoizes only within one query; the audit asks thousands of overlapping
queries, so retaining completed closures is essential. -/
structure AxiomCache where
  done : NameMap (Array Name) := {}
  visiting : NameSet := {}

private def unionAxioms (a b : Array Name) : Array Name :=
  b.foldl (fun out n => if out.contains n then out else out.push n) a

/-- Bottom-up axiom closure with a global memo table. `fuel` is initialized
to the number of declarations, which bounds every simple path in the
constant-dependency graph; `visiting` cuts mutual-inductive cycles. -/
private def collectForMemo (env : Environment) : Nat → Name →
    StateM AxiomCache (Array Name)
  | 0, _ => pure #[]
  | fuel + 1, n => do
      if let some out := (← get).done.find? n then return out
      if (← get).visiting.contains n then return #[]
      modify fun s => { s with visiting := s.visiting.insert n }
      let mut out := #[]
      if let some info := env.constants.find? n then
        for dep in info.getUsedConstantsAsSet.toArray do
          out := unionAxioms out (← collectForMemo env fuel dep)
        if let .axiomInfo _ := info then
          out := unionAxioms out #[n]
      modify fun s =>
        { done := s.done.insert n out, visiting := s.visiting.erase n }
      return out

/-- Axioms every classical Lean development uses; anything else is policy. -/
def whitelistedAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

/-- The only permitted project axiom declarations: one boundary assumption
exposed as an opaque predicate plus its semantic eliminator. -/
def permittedAxiomDecls : List Name :=
  [`Loom.Emit.MicroVerilog.ImplementsStandard,
   `Loom.Emit.MicroVerilog.implements_standard_spec]

/-- The complete executable unsafe surface. These private names are stable
module-local declarations; any new unsafe helper fails the audit until its
purpose and trust impact are reviewed here and in `TRUST.md`. -/
def permittedUnsafeDecls : List String :=
  ["Loom.Hw.Compile.compileExprFast",
   "_private.Loom.Hw.Compile.0.Loom.Hw.Compile.ceGo",
   "_private.Loom.Hw.Compile.0.Loom.Hw.Compile.ceImpl",
   "_private.Loom.Hw.Compile.0.Loom.Hw.Compile.wrImpl",
   "_private.Loom.Hw.Compile.0.Loom.Hw.Compile.nrImpl",
   "_private.Loom.Hw.Compile.0.Loom.Hw.Compile.ptImpl",
   "_private.Loom.Hw.Compile.0.Loom.Hw.Compile.mpImpl",
   "_private.Loom.Hw.Compile.0.Loom.Hw.Compile.compileImpl",
   "_private.Loom.Emit.MicroVerilog.Print.0.Loom.Emit.MicroVerilog.Print.pExprMGo",
   "_private.Loom.Emit.MicroVerilog.Print.0.Loom.Emit.MicroVerilog.Print.pExprM",
   "_private.Loom.Emit.MicroVerilog.Print.0.Loom.Emit.MicroVerilog.Print.printImpl",
   -- `Design.toProgram`'s pointer-memoized executable twin. Same trust shape
   -- as `printImpl`: the memo only skips re-walks whose CSE keys would hit
   -- the same table entries, so compiled output equals the reference
   -- `flatten`; nothing kernel-facing depends on the replacement.
   "_private.Loom.Release.ToProgram.0.Loom.Release.SSA.flattenMGo",
   "_private.Loom.Release.ToProgram.0.Loom.Release.SSA.flattenM",
   "_private.Loom.Release.ToProgram.0.Loom.Release.SSA.flattenModuleImpl.build",
   "_private.Loom.Release.ToProgram.0.Loom.Release.SSA.flattenModuleImpl",
   "_private.Loom.Release.ToProgram.0.Loom.Release.SSA.toProgramImpl",
   "_private.Loom.Release.ToProgram.0.Loom.Release.SSA.toIndexedWiresImpl",
   -- D19 `Expr.readsMem`'s pointer-memoized executable twin. Same trust
   -- shape as `printImpl`: the memo is keyed on pointer identity, so a hit
   -- means the *same* term, and the twin returns the reference definition's
   -- Boolean. Nothing kernel-facing depends on it — `syncReadOkB` is an
   -- emission-shape diagnostic (Loom/Hw/D19_SPEC.md), not a hypothesis of
   -- any theorem; the twin exists only so the check does not re-walk the
   -- compiler's shared expression DAGs exponentially (the D13 cost caveat).
   "_private.Loom.Hw.SyncRead.0.Loom.Hw.readsMemImpl.go",
   "_private.Loom.Hw.SyncRead.0.Loom.Hw.readsMemImpl",
   -- The friendly `hardware`/`system` front end must inspect elaborated closed
   -- values and register source metadata with Lean's environment.  Lean marks
   -- that metaprogramming API unsafe.  These declarations run only while
   -- elaborating source: they construct ordinary kernel-checked definitions
   -- and proofs and are not reachable from Design semantics, the compiler, or
   -- a release theorem.  Keep the list declaration-granular so a new escape or
   -- inspector still fails this audit pending review.
   "Loom.Hw.Dsl.elabHardwareCommand",
   "Loom.Hw.Dsl.elabSystemCommand",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.inspectBaseDesign",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.inspectClosedValue",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.inspectInputDecl",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.inspectMemDecl",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.inspectRegDecl",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.inspectString",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.reducedHandleName?",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.registerReconstructedHardware",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.validateExtensionBase",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.validateExtensionIdentifier",
   "_private.Loom.Hw.Dsl.0.Loom.Hw.Dsl.validateRawStatementEscape"]

/-- The reference definitions whose compiled execution is replaced. -/
def permittedImplementedBy : List (String × String) :=
  [("Loom.Hw.Compile.compile",
    "_private.Loom.Hw.Compile.0.Loom.Hw.Compile.compileImpl"),
   ("Loom.Emit.MicroVerilog.Print.print",
    "_private.Loom.Emit.MicroVerilog.Print.0.Loom.Emit.MicroVerilog.Print.printImpl"),
   ("Loom.Hw.Design.toProgram",
    "_private.Loom.Release.ToProgram.0.Loom.Release.SSA.toProgramImpl"),
   ("Loom.Hw.Design.toIndexedWires",
    "_private.Loom.Release.ToProgram.0.Loom.Release.SSA.toIndexedWiresImpl"),
   ("Loom.Hw.Expr.readsMem",
    "_private.Loom.Hw.SyncRead.0.Loom.Hw.readsMemImpl")]

/-- Lean generates partial `_unsafe_rec` helpers while elaborating some
ordinary structural definitions. They are compiler artifacts, not uses of
the source-level `partial def` escape hatch. -/
def generatedUnsafeRec (n : Name) : Bool :=
  n.toString.endsWith "._unsafe_rec"

/-- Is this one of our modules (as opposed to Lean core / Mathlib)? -/
def oursModule (n : Name) : Bool :=
  (`Loom).isPrefixOf n || (`Machines).isPrefixOf n ||
  (`Evidence).isPrefixOf n || (`Tests).isPrefixOf n || (`Tools).isPrefixOf n

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

def formatAxiomList (axioms : Array Name) : String :=
  let names := (axioms.map (fun a => a.toString)).qsort (· < ·)
  if names.isEmpty then
    "[]"
  else
    "[" ++ String.intercalate ", " names.toList ++ "]"

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
        if (`Machines).isPrefixOf imp.module || (`Evidence).isPrefixOf imp.module ||
            (`Tools).isPrefixOf imp.module then
          failures := failures.push
            s!"P0 violation: toolchain module {mod} imports {imp.module}"

  -- Gather our declarations, module-indexed
  let mut ledger : Array (Name × String × Array Name) := #[]
  let mut unsafeDecls : Array Name := #[]
  let mut implementedByDecls : Array (Name × Name) := #[]
  let mut axiomCache : AxiomCache := {}
  let axiomFuel := env.constants.toList.length + 1
  for (name, info) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      let mod := header.moduleNames[idx.toNat]!
      if oursModule mod then
        -- 5. Executable trust surface
        if info.isUnsafe then
          unsafeDecls := unsafeDecls.push name
          unless permittedUnsafeDecls.contains name.toString do
            failures := failures.push s!"unsafe policy: unreviewed unsafe declaration {name} in {mod}"
        if info.isPartial && !generatedUnsafeRec name then
          failures := failures.push s!"partial policy: source partial declaration {name} in {mod}"
        if (Lean.getExternAttrData? env name).isSome then
          failures := failures.push s!"extern policy: project extern declaration {name} in {mod}"
        if let some impl := Lean.Compiler.getImplementedBy? env name then
          implementedByDecls := implementedByDecls.push (name, impl)
          unless permittedImplementedBy.contains (name.toString, impl.toString) do
            failures := failures.push
              s!"implemented_by policy: unreviewed replacement {name} => {impl} in {mod}"
        -- 3. Axiom policy
        if let .axiomInfo _ := info then
          unless permittedAxiomDecls.contains name do
            failures := failures.push s!"axiom policy: `axiom {name}` in {mod}"
        -- Classify
        let (axioms, nextCache) :=
          (collectForMemo env axiomFuel name).run axiomCache
        axiomCache := nextCache
        if inLedger name && !name.isInternalDetail then
          if let .thmInfo _ := info then
            ledger := ledger.push (name, classify axioms, axioms)
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
  let sortedLedger := ledger.qsort (fun a b => a.1.toString < b.1.toString)
  for (name, status, _) in sortedLedger do
    IO.println s!"{status.take 6}  {name}"
  IO.println s!"── {ledger.size} ledger theorems ──"
  IO.println "── Ledger axiom closures ───────────────────────────────────"
  for (name, _, axioms) in sortedLedger do
    IO.println s!"axioms {name}: {formatAxiomList axioms}"

  IO.println "── Executable trust inventory ──────────────────────────────"
  let sortedUnsafe := unsafeDecls.qsort (fun a b => a.toString < b.toString)
  for name in sortedUnsafe do
    IO.println s!"unsafe {name}"
  let sortedImplementedBy := implementedByDecls.qsort
    (fun a b => a.1.toString < b.1.toString)
  for (name, impl) in sortedImplementedBy do
    IO.println s!"implemented_by {name} => {impl}"
  IO.println (s!"── {unsafeDecls.size} unsafe declarations; " ++
    s!"{implementedByDecls.size} implemented_by replacements; 0 partial; 0 extern ──")

  if failures.isEmpty then
    IO.println "audit: all checks passed"
    return 0
  else
    for f in failures do IO.eprintln s!"audit FAILURE: {f}"
    return 1
