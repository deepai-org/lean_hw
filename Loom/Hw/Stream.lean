-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component

/-!
# Same-clock ready/valid streams

Streams are a verified-library protocol over ordinary component ports.  They
add no core expression, action, or syntax.  A transfer occurs exactly when
`valid && ready`; a blocked producer must retain both `valid` and `payload`.
-/

namespace Loom.Hw

universe u v

namespace Stream

variable {α : Type u}

/-- Producer-facing stream port bundle.  `ready` runs in the reverse
direction, so direction errors remain type errors at each scalar connection. -/
structure SourcePorts (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  valid : Port .output δ (BitVec 1)
  payload : Port .output δ α
  ready : Port .input δ (BitVec 1)

/-- Consumer-facing dual of `SourcePorts`. -/
structure SinkPorts (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  valid : Port .input δ (BitVec 1)
  payload : Port .input δ α
  ready : Port .output δ (BitVec 1)

def sourcePorts {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (stem semanticType : String) : SourcePorts δ α where
  valid := Port.bits .output 1 (stem ++ "_valid")
  payload := ⟨stem ++ "_payload", semanticType⟩
  ready := Port.bits .input 1 (stem ++ "_ready")

def sinkPorts {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (stem semanticType : String) : SinkPorts δ α where
  valid := Port.bits .input 1 (stem ++ "_valid")
  payload := ⟨stem ++ "_payload", semanticType⟩
  ready := Port.bits .output 1 (stem ++ "_ready")

def SourcePorts.decls {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (ports : SourcePorts δ α) : List PortDecl :=
  [ports.valid.decl, ports.payload.decl, ports.ready.decl]

def SinkPorts.decls {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (ports : SinkPorts δ α) : List PortDecl :=
  [ports.valid.decl, ports.payload.decl, ports.ready.decl]

/-- Resolved endpoints for one source instance. -/
structure SourceEndpoint (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  valid : OutputEndpoint δ (BitVec 1)
  payload : OutputEndpoint δ α
  ready : InputEndpoint δ (BitVec 1)

/-- Resolved endpoints for one sink instance. -/
structure SinkEndpoint (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  valid : InputEndpoint δ (BitVec 1)
  payload : InputEndpoint δ α
  ready : OutputEndpoint δ (BitVec 1)

def SourcePorts.resolve {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (ports : SourcePorts δ α)
    (inst : ComponentInstance) : Except String (SourceEndpoint δ α) := do
  return { valid := ← inst.output? ports.valid
           payload := ← inst.output? ports.payload
           ready := ← inst.input? ports.ready }

def SinkPorts.resolve {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (ports : SinkPorts δ α)
    (inst : ComponentInstance) : Except String (SinkEndpoint δ α) := do
  return { valid := ← inst.input? ports.valid
           payload := ← inst.input? ports.payload
           ready := ← inst.output? ports.ready }

/-- Connect the three wires of one same-clock stream.  Payload and domain
compatibility are established by the shared `α` and `δ`; no runtime heuristic
chooses a CDC adapter. -/
def connect {δ : Type v} {α : Type u} [ClockDomain δ] [HwPacked α]
    (graph : ComponentGraph) (source : SourceEndpoint δ α)
    (sink : SinkEndpoint δ α) : Except String ComponentGraph := do
  let graph ← graph.connect (← Connection.typed source.valid sink.valid)
  let graph ← graph.connect (← Connection.typed source.payload sink.payload)
  graph.connect (← Connection.typed sink.ready source.ready)

/-- One cycle's logical handshake observation. -/
structure Sample (α : Type u) where
  valid : Bool
  ready : Bool
  payload : α
  deriving Repr, DecidableEq

def Sample.accepted (sample : Sample α) : Bool := sample.valid && sample.ready

/-- The mandatory stability condition between adjacent samples. -/
def Stable (before after : Sample α) : Prop :=
  before.valid = true → before.ready = false →
    after.valid = true ∧ after.payload = before.payload

/-- Protocol validity over a finite trace. -/
def Valid : List (Sample α) → Prop
  | [] | [_] => True
  | before :: after :: rest => Stable before after ∧ Valid (after :: rest)

/-- Accepted transaction sequence, forgetting all stalled cycles. -/
def transactions : List (Sample α) → List α
  | [] => []
  | sample :: rest =>
      if sample.accepted then sample.payload :: transactions rest
      else transactions rest

@[simp] theorem transactions_cons_accepted (sample : Sample α)
    (rest : List (Sample α)) (accepted : sample.accepted = true) :
    transactions (sample :: rest) = sample.payload :: transactions rest := by
  simp [transactions, accepted]

@[simp] theorem transactions_cons_blocked (sample : Sample α)
    (rest : List (Sample α)) (blocked : sample.accepted = false) :
    transactions (sample :: rest) = transactions rest := by
  simp [transactions, blocked]

/-- Abstract state of a one-entry registered stream slice. -/
abbrev RegisterState (α : Type u) := Option α

/-- Whether the registered slice can accept an upstream item this cycle. -/
def registerReady (state : RegisterState α) (downstreamReady : Bool) : Bool :=
  state.isNone || downstreamReady

/-- One abstract registered-slice transition.  Replacement on simultaneous
dequeue/enqueue is explicit; no item is dropped. -/
def registerStep (state : RegisterState α) (upstreamValid : Bool)
    (upstreamPayload : α) (downstreamReady : Bool) : RegisterState α :=
  if registerReady state downstreamReady then
    if upstreamValid then some upstreamPayload else none
  else state

theorem registerStep_blocked (state : RegisterState α) (payload : α)
    (full : state.isSome = true) :
    registerStep state true payload false = state := by
  cases state <;> simp_all [registerStep, registerReady]

theorem registerStep_replace (old payload : α) :
    registerStep (some old) true payload true = some payload := by
  simp [registerStep, registerReady]

/-- Ports of a one-entry registered stream slice. -/
structure RegisterSlicePorts (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  input : SinkPorts δ α
  output : SourcePorts δ α

def registerSlicePorts {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (semanticType : String) :
    RegisterSlicePorts δ α :=
  ⟨sinkPorts "in" semanticType, sourcePorts "out" semanticType⟩

private def sliceFull : Reg 1 := ⟨"full"⟩
private def slicePayload (width : Nat) : Reg width := ⟨"payload"⟩

/-- Ordinary Loom implementation of a one-entry elastic register.  It accepts
and emits in the same tick when replacing a consumed item, but exposes no
combinational payload path. -/
def registerSliceComponent {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (name semanticType : String) : Component :=
  let ports : RegisterSlicePorts δ α := registerSlicePorts semanticType
  let payload := slicePayload (HwPacked.width α)
  let canAccept : Expr 1 :=
    .or (.not sliceFull.rd) ports.output.ready.bitReg.rd
  let update : Act :=
    .ite canAccept
      (.seq (sliceFull.set ports.input.valid.bitReg.rd)
        (.ite ports.input.valid.bitReg.rd
          (payload.set ports.input.payload.reg.rd) .skip))
      .skip
  { name
    interface := ⟨ports.input.decls ++ ports.output.decls⟩
    design :=
      { name
        regs := [sliceFull.decl 0, payload.decl 0]
        mems := []
        inputs := [ports.input.valid.bitReg.input,
          ports.input.payload.reg.input, ports.output.ready.bitReg.input]
        rules := [⟨"transfer", update⟩]
        outputs := []
        combOutputs :=
          [⟨ports.input.ready.name, 1, canAccept⟩,
           ⟨ports.output.valid.name, 1, sliceFull.rd⟩,
           ⟨ports.output.payload.name, HwPacked.width α, payload.rd⟩] } }

def registerSlice? {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (name semanticType : String) :
    Except String Component.Sealed :=
  (registerSliceComponent (δ := δ) (α := α) name semanticType).seal?

/-- Abstract the two implementation registers to the protocol's optional
buffered transaction. -/
def registerSliceState {α : Type u} [HwPacked α] (state : St) :
    RegisterState (BitVec (HwPacked.width α)) :=
  if state.regs sliceFull.name 1 = 1#1 then
    some (state.regs (slicePayload (HwPacked.width α)).name (HwPacked.width α))
  else none

private def asserted (value : BitVec 1) : Bool := value = 1#1

/-- The generated slice's state transition is exactly the abstract one-entry
stream transition.  This is the first protocol refinement theorem; users never
need to unfold the generated rules to rely on buffering behavior. -/
theorem registerSlice_cycle_refines {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (name semanticType : String)
    (input : InEnv) (state : St) :
    registerSliceState (α := α)
        ((registerSliceComponent (δ := δ) (α := α) name semanticType).design.cycleOpen
          input state) =
      registerStep (registerSliceState (α := α) state)
        (asserted (input "in_valid" 1))
        (input "in_payload" (HwPacked.width α))
        (asserted (input "out_ready" 1)) := by
  rcases Loom.Hw.bv1_cases (state.regs sliceFull.name 1) with full | full <;>
    rcases Loom.Hw.bv1_cases (input "in_valid" 1) with valid | valid <;>
    rcases Loom.Hw.bv1_cases (input "out_ready" 1) with ready | ready <;>
    simp [sliceFull] at full <;>
    simp [registerSliceState, registerSliceComponent, Design.cycleOpen,
      Design.cycle, St.setInputs, Act.run, Expr.eval, RegEnv.set,
      registerStep, registerReady, asserted, sliceFull, slicePayload,
      registerSlicePorts, sourcePorts, sinkPorts, Port.reg, Port.bits,
      Reg.rd, Reg.set, Reg.input,
      Port.bitReg,
      full, valid, ready]

end Stream

end Loom.Hw
