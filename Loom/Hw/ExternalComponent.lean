-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component
import Loom.Artifact

/-!
# Contract-bearing external components

An external component is a technology-neutral behavioral contract plus exact
interface, clock/reset, dependency, and latency metadata.  Bindings identify
external bytes and assumptions, but do not inject HDL into the Loom language
and do not become kernel proofs merely because a tool reported `PASS`.
-/

namespace Loom.Hw

/-- Heterogeneous port valuation, identical in shape to an open Design input
environment but used for both input and output sides of a component contract. -/
abbrev PortEnv := String → (width : Nat) → BitVec width

namespace PortEnv

/-- Environments agree on every port in an erased interface selection. -/
def AgreeOn (ports : List PortDecl) (left right : PortEnv) : Prop :=
  ∀ port ∈ ports, left port.name port.width = right port.name port.width

@[refl] theorem agreeOn_refl (ports : List PortDecl) (env : PortEnv) :
    AgreeOn ports env env := by
  intro _ _
  rfl

theorem agreeOn_symm {ports : List PortDecl} {left right : PortEnv}
    (agree : AgreeOn ports left right) : AgreeOn ports right left := by
  intro port member
  exact (agree port member).symm

theorem agreeOn_trans {ports : List PortDecl} {left middle right : PortEnv}
    (first : AgreeOn ports left middle)
    (second : AgreeOn ports middle right) : AgreeOn ports left right := by
  intro port member
  exact (first port member).trans (second port member)

end PortEnv

/-- One logical scheduling observation supplied to a multi-domain contract.
Physical frequency, duty cycle, jitter, and MTBF are deliberately absent. -/
structure ComponentEvent where
  ticks : String → Bool
  resets : String → Bool

/-- A possibly nondeterministic technology-neutral component contract.
Input extensionality prevents the behavior from depending on undeclared
coordinates of the erased `PortEnv`. -/
structure ComponentContract (interface : ComponentInterface) where
  State : Type
  init : State → Prop
  step : ComponentEvent → PortEnv → State → State → Prop
  observe : PortEnv → State → PortEnv
  step_input_congr : ∀ event state next left right,
    PortEnv.AgreeOn interface.inputs left right →
      (step event left state next ↔ step event right state next)
  observe_input_congr : ∀ state left right,
    PortEnv.AgreeOn interface.inputs left right →
      PortEnv.AgreeOn interface.outputs
        (observe left state) (observe right state)

namespace ComponentContract

/-- Forward refinement between two contracts over the same exact interface.
This is a kernel proposition; it says nothing by itself about external bytes. -/
structure Refinement {interface : ComponentInterface}
    (specification implementation : ComponentContract interface) where
  abstract : implementation.State → specification.State
  init : ∀ state, implementation.init state →
    specification.init (abstract state)
  step : ∀ event input before after,
    implementation.step event input before after →
      specification.step event input (abstract before) (abstract after)
  observe : ∀ input state,
    PortEnv.AgreeOn interface.outputs
      (implementation.observe input state)
      (specification.observe input (abstract state))

@[refl] def Refinement.refl {interface : ComponentInterface}
    (contract : ComponentContract interface) : Refinement contract contract where
  abstract := id
  init := by intros; assumption
  step := by intros; assumption
  observe := by
    intro input state
    exact PortEnv.agreeOn_refl interface.outputs _

/-- Contract refinement composes without inspecting either implementation. -/
def Refinement.comp {interface : ComponentInterface}
    {a b c : ComponentContract interface}
    (ab : Refinement a b) (bc : Refinement b c) : Refinement a c where
  abstract := ab.abstract ∘ bc.abstract
  init := by
    intro state initial
    exact ab.init _ (bc.init state initial)
  step := by
    intro event input before after transition
    exact ab.step event input _ _ (bc.step event input before after transition)
  observe := by
    intro input state port member
    exact (bc.observe input state port member).trans
      (ab.observe input (bc.abstract state) port member)

end ComponentContract

inductive ClockEdge where
  | rising
  | falling
  deriving Repr, DecidableEq, BEq

inductive ResetBehavior where
  | resetless
  | synchronous (activeHigh : Bool)
  | asynchronousAssertSynchronousRelease (activeHigh : Bool)
  deriving Repr, DecidableEq, BEq

/-- Logical clock/reset behavior of one named domain. -/
structure DomainContract where
  domain : String
  edge : ClockEdge
  reset : ResetBehavior
  deriving Repr, DecidableEq, BEq

/-- One allowed same-cycle output dependency.  Absence from this list means
the external leaf promises no such combinational path. -/
structure CombinationalDependency where
  output : String
  input : String
  deriving Repr, DecidableEq, BEq

/-- Tick latency from an optional named input acceptance point to an output.
`maximum = none` means no finite unconditional upper bound is claimed. -/
structure PortLatency where
  output : String
  source : Option String
  minimum : Nat
  maximum : Option Nat
  deriving Repr, DecidableEq, BEq

namespace PortLatency

def validB (latency : PortLatency) : Bool :=
  match latency.maximum with
  | none => true
  | some maximum => latency.minimum ≤ maximum

end PortLatency

/-- The full assumption boundary for one external component family. -/
structure ExternalComponent where
  name : String
  version : String
  interface : ComponentInterface
  behavior : ComponentContract interface
  domains : List DomainContract
  combinational : List CombinationalDependency
  latency : List PortLatency

namespace ExternalComponent

private def inputNamed (specification : ExternalComponent) (name : String) : Bool :=
  specification.interface.inputs.any (·.name == name)

private def outputNamed (specification : ExternalComponent) (name : String) : Bool :=
  specification.interface.outputs.any (·.name == name)

def validB (specification : ExternalComponent) : Bool :=
  let domainNames := specification.domains.map (·.domain)
  let latencyOutputs := specification.latency.map (·.output)
  !specification.name.isEmpty && !specification.version.isEmpty &&
    specification.interface.locallyValidB &&
    Inventory.uniqueB domainNames &&
    specification.interface.ports.all
      (fun port => domainNames.contains port.domain) &&
    specification.combinational.all (fun dependency =>
      specification.inputNamed dependency.input &&
        specification.outputNamed dependency.output) &&
    Inventory.uniqueB latencyOutputs &&
    specification.latency.all (fun latency =>
      specification.outputNamed latency.output &&
      latency.source.all specification.inputNamed && latency.validB)

def check (specification : ExternalComponent) : Except String Unit := do
  if specification.validB then pure ()
  else throw s!"external component '{specification.name}' has an incomplete or inconsistent interface contract"

end ExternalComponent

/-- External syntax accepted by a downstream integration flow.  This is
provenance metadata, never an extension of Loom's core expression language. -/
inductive ExternalFormat where
  | verilog
  | vhdl
  | neutralNetlist
  | other (name : String)
  deriving Repr, DecidableEq, BEq

/-- A premise not proved by Loom. -/
structure NamedAssumption where
  name : String
  statement : String
  deriving Repr, DecidableEq, BEq

/-- Classification of evidence supplied by an external flow.  Neither case is
silently promoted to a kernel theorem. -/
inductive ExternalEvidence where
  | assumptionOnly
  | toolReport (tool version result : String)
  deriving Repr, DecidableEq, BEq

/-- Exact artifact binding for a contracted leaf.  Parameters are part of the
identity-bearing configuration and therefore cannot be an unrecorded command
line detail. -/
structure ExternalBinding (specification : ExternalComponent) where
  format : ExternalFormat
  moduleName : String
  parameters : List (String × String)
  artifact : Loom.Artifact.Identity
  evidence : ExternalEvidence
  assumptions : List NamedAssumption

namespace ExternalBinding

def validB {specification : ExternalComponent}
    (binding : ExternalBinding specification) : Bool :=
  let parameterNames := binding.parameters.map (·.1)
  let assumptionNames := binding.assumptions.map (·.name)
  specification.validB && !binding.moduleName.isEmpty &&
    Inventory.uniqueB parameterNames && Inventory.uniqueB assumptionNames &&
    binding.assumptions.all fun assumption =>
      !assumption.name.isEmpty && !assumption.statement.isEmpty

def check {specification : ExternalComponent}
    (binding : ExternalBinding specification) : Except String Unit := do
  if binding.validB then pure ()
  else throw s!"external binding for '{specification.name}' is incomplete or does not match its contract"

end ExternalBinding

/-- A proved logical implementation of an external specification.  This can
discharge the *behavioral* contract in Loom.  Connecting particular Verilog,
VHDL, or macro bytes to `implementation` is a separate equivalence obligation;
an `ExternalBinding` alone never fills it. -/
structure RefinedExternalModel (specification : ExternalComponent) where
  implementation : ComponentContract specification.interface
  refinement : ComponentContract.Refinement
    specification.behavior implementation

end Loom.Hw
