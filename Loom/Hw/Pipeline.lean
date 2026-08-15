-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Stream

/-!
# Elastic pipelines

The abstract model below is a chain of one-entry registered stream stages.
It states buffering and backpressure independently of RTL and proves exact
transaction conservation for every step. The construction helper assembles
the concrete pipeline from the already-refined stream register-slice
components; no pipeline constructor is added to the hardware core.
-/

namespace Loom.Hw

universe u v

namespace Pipeline

variable {α : Type u}

private def present (value : Option α) : Bool := value.isSome

def accepted (value : Option α) (ready : Bool) : Nat :=
  if value.isSome && ready then 1 else 0

def occupancy (slots : List (Option α)) : Nat :=
  (slots.map present).count true

@[simp] theorem occupancy_cons (state : Option α) (rest : List (Option α)) :
    occupancy (state :: rest) = accepted state true + occupancy rest := by
  cases state
  all_goals simp [occupancy, present, accepted]
  all_goals omega

def stageReady (state : Option α) (downstreamReady : Bool) : Bool :=
  state.isNone || downstreamReady

def stageStep (state incoming : Option α) (downstreamReady : Bool) : Option α :=
  if stageReady state downstreamReady then incoming else state

theorem stage_conservation (state incoming : Option α) (downstreamReady : Bool) :
    accepted (stageStep state incoming downstreamReady) true +
        accepted state downstreamReady =
      accepted state true + accepted incoming (stageReady state downstreamReady) := by
  cases state
  all_goals cases incoming
  all_goals cases downstreamReady
  all_goals simp [stageStep, stageReady, accepted]

/-- Internal registered-chain transition. The returned Boolean is upstream
ready. Empty lists are a zero-stage combinational path. -/
def advance : List (Option α) → Option α → Bool → List (Option α) × Bool
  | [], _, outputReady => ([], outputReady)
  | state :: rest, incoming, outputReady =>
      let advanced := advance rest state outputReady
      let ready := stageReady state advanced.2
      (stageStep state incoming advanced.2 :: advanced.1, ready)

@[simp] theorem advance_length (slots : List (Option α))
    (incoming : Option α) (outputReady : Bool) :
    (advance slots incoming outputReady).1.length = slots.length := by
  induction slots generalizing incoming with
  | nil => rfl
  | cons state rest ih =>
      simp [advance, ih]

private def lastValue (head : Option α) : List (Option α) → Option α
  | [] => head
  | next :: tail => lastValue next tail

def outputAccepted (slots : List (Option α)) (incoming : Option α)
    (outputReady : Bool) : Nat := match slots with
  | [] => accepted incoming outputReady
  | head :: tail => accepted (lastValue head tail) outputReady

/-- No elastic stage creates or loses a transaction. Items may move between
slots, one item may enter, and one item may leave. -/
theorem advance_conservation (slots : List (Option α))
    (incoming : Option α) (outputReady : Bool) :
    occupancy (advance slots incoming outputReady).1 +
        outputAccepted slots incoming outputReady =
      occupancy slots + accepted incoming (advance slots incoming outputReady).2 := by
  induction slots generalizing incoming with
  | nil => simp [advance, occupancy, outputAccepted, accepted]
  | cons state rest ih =>
      cases rest with
      | nil =>
          cases state <;> cases incoming <;> cases outputReady <;>
            simp [advance, occupancy, outputAccepted, lastValue, present, accepted,
              stageStep, stageReady]
      | cons next tail =>
          have tailConservation := ih state
          let advanced := advance (next :: tail) state outputReady
          have stageConservation := stage_conservation state incoming advanced.2
          change
            occupancy (stageStep state incoming advanced.2 :: advanced.1) +
                outputAccepted (state :: next :: tail) incoming outputReady =
              occupancy (state :: next :: tail) +
                accepted incoming (stageReady state advanced.2)
          rw [occupancy_cons (stageStep state incoming advanced.2) advanced.1]
          rw [occupancy_cons state (next :: tail)]
          have outputTail :
              outputAccepted (state :: next :: tail) incoming outputReady =
                outputAccepted (next :: tail) state outputReady := rfl
          rw [outputTail]
          change
            accepted (stageStep state incoming advanced.2) true +
                occupancy advanced.1 + outputAccepted (next :: tail) state outputReady =
              accepted state true + occupancy (next :: tail) +
                accepted incoming (stageReady state advanced.2)
          change occupancy advanced.1 + outputAccepted (next :: tail) state outputReady =
              occupancy (next :: tail) + accepted state advanced.2 at tailConservation
          omega

/-- Depth-indexed pipeline state. The length proof prevents a configured
pipeline from silently gaining or losing storage stages. -/
structure State (depth : Nat) (α : Type u) where
  slots : List (Option α)
  depth_eq : slots.length = depth

namespace State

def empty (depth : Nat) : State depth α :=
  ⟨List.replicate depth none, by simp⟩

structure StepResult (depth : Nat) (α : Type u) where
  state : State depth α
  inputReady : Bool
  /-- Current output transaction, whether or not the consumer accepts it. -/
  output : Option α
  /-- Output transaction accepted on this step. -/
  acceptedOutput : Option α

def step {depth : Nat} (state : State depth α)
    (incoming : Option α) (outputReady : Bool) : StepResult depth α :=
  let result := advance state.slots incoming outputReady
  let output := match state.slots with
    | [] => incoming
    | _ => state.slots.getLast?.join
  { state :=
      { slots := result.1
        depth_eq := by
          rw [advance_length]
          exact state.depth_eq }
    inputReady := result.2
    output
    acceptedOutput := if outputReady then output else none }

@[simp] theorem occupancy_replicate_none (depth : Nat) :
    occupancy (List.replicate depth (none : Option α)) = 0 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [List.replicate_succ, occupancy_cons, ih]
      simp [accepted]

/-- Flush has an explicit loss contract: it accepts no input or output on the
flush step and reports exactly the number of discarded buffered items. -/
def advanceWithFlush (slots : List (Option α)) (incoming : Option α)
    (outputReady flush : Bool) : List (Option α) × Bool :=
  if flush then (List.replicate slots.length none, false)
  else advance slots incoming outputReady

def discardedByFlush (slots : List (Option α)) (flush : Bool) : Nat :=
  if flush then occupancy slots else 0

def outputAcceptedWithFlush (slots : List (Option α)) (incoming : Option α)
    (outputReady flush : Bool) : Nat :=
  if flush then 0 else outputAccepted slots incoming outputReady

theorem advanceWithFlush_conservation (slots : List (Option α))
    (incoming : Option α) (outputReady flush : Bool) :
    occupancy (advanceWithFlush slots incoming outputReady flush).1 +
        outputAcceptedWithFlush slots incoming outputReady flush +
        discardedByFlush slots flush =
      occupancy slots +
        accepted incoming (advanceWithFlush slots incoming outputReady flush).2 := by
  cases flush
  · simpa [advanceWithFlush, outputAcceptedWithFlush, discardedByFlush] using
      advance_conservation slots incoming outputReady
  · cases incoming <;>
      simp [advanceWithFlush, outputAcceptedWithFlush, discardedByFlush,
        accepted]

structure FlushResult (depth : Nat) (α : Type u) where
  state : State depth α
  inputReady : Bool
  output : Option α
  acceptedOutput : Option α
  discarded : Nat

def stepWithFlush {depth : Nat} (state : State depth α)
    (incoming : Option α) (outputReady flush : Bool) : FlushResult depth α :=
  let result := advanceWithFlush state.slots incoming outputReady flush
  let output := if flush then none else match state.slots with
    | [] => incoming
    | _ => state.slots.getLast?.join
  { state :=
      { slots := result.1
        depth_eq := by
          change (advanceWithFlush state.slots incoming outputReady flush).1.length = depth
          simp only [advanceWithFlush]
          split
          · simp [state.depth_eq]
          · rw [advance_length]
            exact state.depth_eq }
    inputReady := result.2
    output
    acceptedOutput := if outputReady then output else none
    discarded := discardedByFlush state.slots flush }

end State

/-! ## Concrete link components -/

/-- Common stream boundary of one pipeline link. -/
def linkPorts {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (semanticType : String) :
    Stream.RegisterSlicePorts δ α :=
  Stream.registerSlicePorts semanticType

/-- A zero-state combinational link. It is explicit because bypass changes
latency and combinational-path structure even though it does not change the
stream transaction sequence. -/
def bypassComponent? {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (name semanticType : String) :
    Except String (DomainComponent δ) := do
  let ports := linkPorts (δ := δ) (α := α) semanticType
  let component : Component :=
    { name
      interface := ⟨ports.input.decls ++ ports.output.decls⟩
      design :=
        { name
          regs := []
          mems := []
          inputs := [ports.input.valid.bitReg.input,
            ports.input.payload.reg.input, ports.output.ready.bitReg.input]
          rules := []
          outputs := []
          combOutputs :=
            [⟨ports.input.ready.name, 1, ports.output.ready.bitReg.rd⟩,
             ⟨ports.output.valid.name, 1, ports.input.valid.bitReg.rd⟩,
             ⟨ports.output.payload.name, HwPacked.width α,
                ports.input.payload.reg.rd⟩] } }
  DomainComponent.seal? component.name component.interface
    (DomainDesign.authored component.design)

/-- Extra control port of a flushable link. Flush is synchronous to `δ`;
when asserted, the link accepts and presents no transaction on that cycle and
discards its buffered item at the edge. -/
def flushPort {δ : Type v} [ClockDomain δ] :
    Port .input δ (BitVec 1) := Port.bits .input 1 "flush"

/-- One-entry registered link with an explicit loss-bearing flush input. -/
def flushableComponent? {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (name semanticType : String) :
    Except String (DomainComponent δ) := do
  let ports := linkPorts (δ := δ) (α := α) semanticType
  let flush := flushPort (δ := δ)
  let full : Reg 1 := ⟨"full"⟩
  let payload : Reg (HwPacked.width α) := ⟨"payload"⟩
  let active := .not flush.bitReg.rd
  let canAccept := .and active
    (.or (.not full.rd) ports.output.ready.bitReg.rd)
  let outputValid := .and active full.rd
  let transfer :=
    .ite canAccept
      (.seq (full.set ports.input.valid.bitReg.rd)
        (.ite ports.input.valid.bitReg.rd
          (payload.set ports.input.payload.reg.rd) .skip))
      .skip
  let update := .ite flush.bitReg.rd (full.set (.lit 0)) transfer
  let component : Component :=
    { name
      interface := ⟨ports.input.decls ++ ports.output.decls ++ [flush.decl]⟩
      design :=
        { name
          regs := [full.decl 0, payload.decl 0]
          mems := []
          inputs := [ports.input.valid.bitReg.input,
            ports.input.payload.reg.input, ports.output.ready.bitReg.input,
            flush.bitReg.input]
          rules := [⟨"transfer_or_flush", update⟩]
          outputs := []
          combOutputs :=
            [⟨ports.input.ready.name, 1, canAccept⟩,
             ⟨ports.output.valid.name, 1, outputValid⟩,
             ⟨ports.output.payload.name, HwPacked.width α, payload.rd⟩] } }
  DomainComponent.seal? component.name component.interface
    (DomainDesign.authored component.design)

/-- Assemble a concrete same-clock pipeline from an explicit nonempty link
inventory. Every link has the same typed stream boundary; individual links
may be registered, flushable, bypassing, or supplied by a plugin. -/
def componentGraphOf? {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (name semanticType : String) (stages : List (DomainComponent δ)) :
    Except String (DomainComponentGraph δ) := do
  if stages.isEmpty then
    throw "a concrete pipeline requires at least one link"
  let ports := Stream.registerSlicePorts (δ := δ) (α := α) semanticType
  let mut graph := DomainComponentGraph.empty (δ := δ) name
  for (stage, index) in stages.zipIdx do
    graph ← graph.addInstance ⟨s!"stage{index}", stage⟩
  for index in List.range (stages.length - 1) do
    let some sourceInstance := graph.findInstance? s!"stage{index}"
      | throw "internal pipeline source-stage construction failure"
    let some sinkInstance := graph.findInstance? s!"stage{index + 1}"
      | throw "internal pipeline sink-stage construction failure"
    let source ← ports.output.resolve sourceInstance
    let sink ← ports.input.resolve sinkInstance
    graph ← Stream.connect graph source sink
  let last := stages.length - 1
  graph ← graph.expose "stage0" ports.input.ready.name
  graph ← graph.expose s!"stage{last}" ports.output.valid.name
  graph ← graph.expose s!"stage{last}" ports.output.payload.name
  return graph

/-- Assemble a homogeneous concrete pipeline from verified one-entry slices.
The stage count is an ordinary Lean parameter. -/
def componentGraph? {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (name semanticType : String) (depth : Nat) :
    Except String (DomainComponentGraph δ) := do
  if depth == 0 then
    throw "a concrete registered pipeline requires at least one stage"
  let slice ← Stream.registerSlice? (δ := δ) (α := α)
    (name ++ "_stage") semanticType
  componentGraphOf? (δ := δ) (α := α) name semanticType
    (List.replicate depth slice)

/-- Typed boundary of a configured registered pipeline after its internal
slice hierarchy is sealed. The boundary names are derived from the same stage
paths used by `componentGraph?`, so hierarchy and interface cannot drift. -/
structure ComponentPorts (δ : Type v) (α : Type u)
    [ClockDomain δ] [HwPacked α] where
  input : Stream.SinkPorts δ α
  output : Stream.SourcePorts δ α

def componentPorts {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α] (semanticType : String) (depth : Nat) :
    ComponentPorts δ α :=
  { input := Stream.sinkPorts "stage0__in" semanticType
    output := Stream.sourcePorts s!"stage{depth - 1}__out" semanticType }

/-- Close a parameterized pipeline hierarchy into one reusable
`DomainComponent δ`. This uses the ordinary canonical flattening and scalar
compiler/simulator boundary; it is a construction convenience, not a claim
of semantic separate compilation for the child slices. -/
def component? {δ : Type v} {α : Type u}
    [ClockDomain δ] [HwPacked α]
    (name semanticType : String) (depth : Nat) :
    Except String (DomainComponent δ) := do
  let graph ← componentGraph? (δ := δ) (α := α) name semanticType depth
  let implementation ← graph.flatten?
  let ports := componentPorts (δ := δ) (α := α) semanticType depth
  DomainComponent.seal? name
    ⟨ports.input.decls ++ ports.output.decls⟩ implementation

end Pipeline

end Loom.Hw
