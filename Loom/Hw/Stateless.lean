-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component
import Loom.Artifact

/-!
# First-class stateless components

A stateless implementation is still an ordinary `Design`, so it reuses the
same expression semantics and proved compiler.  The checked wrapper proves
that there is no sequential state or rule action.  Its µVerilog artifact is
marked stateless and therefore has no synthetic clock/reset ports or
event-control block.

The component boundary is domain-polymorphic: `bind?` assigns only nominal
port ownership to a selected typed domain.  Since the implementation contains
no state, that operation does not assign or move a storage element.
-/

namespace Loom.Hw

universe v

/-- An ordinary Design whose complete behavior is its same-cycle outputs. -/
structure StatelessDesign where
  design : Design
  stateless : design.statelessB = true
  readsOk : design.readsOkB = true

namespace StatelessDesign

/-- Fail-closed construction; all normal Design emission/read checks still
apply before the stateless witness is issued. -/
def check? (design : Design) : Except String StatelessDesign := do
  design.emitCheck
  if hStateless : design.statelessB = true then
    if hReads : design.readsOkB = true then
      return ⟨design, hStateless, hReads⟩
    throw s!"stateless design '{design.name}' contains an undeclared or wrong-width read"
  throw s!"design '{design.name}' contains state, rules, or sequential-memory policy"

/-- The same proved expression compilation, carried by an explicitly
clockless module kind. -/
def compile (design : StatelessDesign) :
    Loom.Emit.MicroVerilog.Module :=
  Compile.compileStateless design.design

def renderedVerilog (design : StatelessDesign) : String :=
  Loom.Emit.MicroVerilog.Print.print design.compile

/-- Exact printer/parser coverage remains mandatory for clockless artifacts. -/
def parseCheck (design : StatelessDesign) : Bool :=
  design.compile.parseCheck

def emit (design : StatelessDesign) (path : System.FilePath) : IO Unit := do
  unless design.parseCheck do
    throw <| IO.userError s!"stateless design '{design.design.name}' failed µVerilog round-trip checking"
  let changed ← Loom.Artifact.writeText path design.renderedVerilog
  IO.println s!"{path} {if changed then "written" else "unchanged"}"

/-- Every output expression retains the ordinary Loom expression meaning.
The stateless wrapper changes only the physical module frame. -/
theorem compileOutput_eval (output : CombOutput) (state : St) :
    Compile.mvEval (Compile.convSt state) (Compile.compileExpr output.value) =
      output.value.eval state :=
  Compile.compileCombOutput_eval output state

end StatelessDesign

/-- Domain-independent port declaration used by a reusable stateless
component template. -/
structure StatelessPortDecl where
  name : String
  direction : PortDirection
  width : Nat
  semanticType : String
  deriving Repr, DecidableEq, BEq

/-- A combinational component before choosing the typed domain in which its
pins are used. -/
structure StatelessComponent where
  name : String
  ports : List StatelessPortDecl
  implementation : StatelessDesign

namespace StatelessComponent

private def interfaceIn {δ : Type v} [ClockDomain δ]
    (component : StatelessComponent) : ComponentInterface :=
  ⟨component.ports.map fun port =>
    ⟨port.name, port.direction, port.width, port.semanticType,
      ClockDomain.name δ⟩⟩

/-- Bind a stateless component's pins into any one typed domain.  The
resulting ordinary `DomainComponent` participates in the existing checked
graph and canonical flattening, while hierarchy emission sees its stateless
kind and omits clock/reset hookups. -/
def bind? {δ : Type v} [ClockDomain δ]
    (component : StatelessComponent) : Except String (DomainComponent δ) := do
  unless component.name == component.implementation.design.name do
    throw s!"stateless component name '{component.name}' does not match Design name '{component.implementation.design.name}'"
  DomainComponent.seal? component.name (component.interfaceIn (δ := δ))
    (DomainDesign.authored component.implementation.design)

end StatelessComponent

end Loom.Hw
