-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CertifiedSystemArtifact
import Loom.Hw.ChannelProtocol
import Loom.Hw.Packed
import Loom.Hw.SystemRecovery
import Loom.Hw.CertifiedSystemRecovery
import Loom.Hw.ChanRecovery
import Loom.Hw.RecoveryProtocol
import Loom.Hw.RecoveryProtocolDesign
import Loom.Hw.Component

/-!
# Application-facing multiclock facade

The declarations in `System`, `Chan`, and `Design` are the public description
of a multiclock application.  This file closes the mechanical gap between
that description and Loom's certified simulator/emitter: one whole-System
check derives the dependent island certificates, portable channel bindings,
coverage proof, and clock-rule proof.

`CertifiedSystem`, `Chan.Refinement`, storage witnesses, and lookup equalities
remain available to realization experts, but stock application code should
not have to construct them.
-/

namespace Loom.Hw

universe u v

/-! ## Typed application handles

The semantic and generator layers retain strings because names must eventually
be rendered.  Application code passes these handles instead.  In particular,
channel routes cannot contain a separately typed source-name and sink-name
string, and directional endpoints expose only operations legal at that end.
-/

/-- A named clock domain.  Clock names become strings only when lowering to
the executable named-schedule and emitted-port layers. -/
structure ClockHandle where
  name : String
  deriving Repr, DecidableEq

namespace ClockHandle

def named (name : String) : ClockHandle := ⟨name⟩

/-- One executable event in which this clock ticks. -/
def tick (clock : ClockHandle) : NamedClockEvent := ⟨[clock.name]⟩

end ClockHandle

/-- A clock whose identity is tied to the same phantom domain used by
components, streams, memories, and reset policy.  Unlike `ClockHandle`, this
cannot be paired with an unrelated domain-owned design. -/
structure Clock (δ : Type v) [ClockDomain δ] where
  name : String
  matchesDomain : name = ClockDomain.name δ

namespace Clock

/-- The canonical clock for a nominal domain. -/
def domain (δ : Type v) [ClockDomain δ] : Clock δ :=
  ⟨ClockDomain.name δ, rfl⟩

def erase {δ : Type v} [ClockDomain δ] (clock : Clock δ) : ClockHandle :=
  ⟨clock.name⟩

def tick {δ : Type v} [ClockDomain δ] (clock : Clock δ) : NamedClockEvent :=
  clock.erase.tick

end Clock

/-- An ordinary synchronous Design placed in one clock domain.  The handle is
reused by topology, inspection, and later hierarchical export APIs. -/
structure IslandHandle where
  name : String
  clock : ClockHandle
  design : Design

namespace IslandHandle

def named (name : String) (design : Design) (clock : ClockHandle) : IslandHandle :=
  ⟨name, clock, design⟩

def toSystemIsland (island : IslandHandle) : SystemIsland :=
  ⟨island.name, island.clock.name, island.design⟩

end IslandHandle

/-- An island whose synchronous design and executable clock share the same
domain index.  This is the ordinary-user island handle; `IslandHandle` is its
erased generator/compatibility representation. -/
structure DomainIslandHandle (δ : Type v) [ClockDomain δ] where
  name : String
  clock : Clock δ
  design : DomainDesign δ

namespace DomainIslandHandle

def named {δ : Type v} [ClockDomain δ] (name : String)
    (design : DomainDesign δ) (clock : Clock δ := Clock.domain δ) :
    DomainIslandHandle δ := ⟨name, clock, design⟩

def erase {δ : Type v} [ClockDomain δ]
    (island : DomainIslandHandle δ) : IslandHandle :=
  ⟨island.name, island.clock.erase, island.design.design⟩

def toSystemIsland {δ : Type v} [ClockDomain δ]
    (island : DomainIslandHandle δ) : SystemIsland := island.erase.toSystemIsland

end DomainIslandHandle

/-- Add a clock-checked island.  Heterogeneous domains erase only after the
type checker has established each design/clock pairing. -/
def _root_.Loom.Hw.SystemBuilder.addDomainIsland {δ : Type v} [ClockDomain δ]
    (builder : SystemBuilder) (island : DomainIslandHandle δ) : SystemBuilder :=
  { builder with islands := builder.islands ++ [island.toSystemIsland] }

/-- Add an erased island handle at an importer/generator boundary. Ordinary
application code should retain a `DomainIslandHandle δ`. -/
def _root_.Loom.Hw.SystemBuilder.addErasedIsland (builder : SystemBuilder)
    (island : IslandHandle) : SystemBuilder :=
  { builder with islands := builder.islands ++ [island.toSystemIsland] }

@[deprecated SystemBuilder.addErasedIsland (since := "2026-08-15")]
def _root_.Loom.Hw.SystemBuilder.addIsland (builder : SystemBuilder)
    (island : IslandHandle) : SystemBuilder :=
  builder.addErasedIsland island

namespace Chan

/-- Directional handle available inside a channel's source island. -/
structure SourceEndpoint (width : Nat) where
  channel : Chan width
  deriving Repr

/-- Directional handle available inside a channel's sink island. -/
structure SinkEndpoint (width : Nat) where
  channel : Chan width
  deriving Repr

def source {width : Nat} (channel : Chan width) : SourceEndpoint width := ⟨channel⟩
def sink {width : Nat} (channel : Chan width) : SinkEndpoint width := ⟨channel⟩

def SourceEndpoint.canSend {width : Nat} (endpoint : SourceEndpoint width) : Expr 1 :=
  endpoint.channel.canEnq

def SourceEndpoint.send {width : Nat} (endpoint : SourceEndpoint width)
    (payload : Expr width) : Act := endpoint.channel.enq payload

def SinkEndpoint.hasData {width : Nat} (endpoint : SinkEndpoint width) : Expr 1 :=
  endpoint.channel.canDeq

def SinkEndpoint.data {width : Nat} (endpoint : SinkEndpoint width) : Expr width :=
  endpoint.channel.deq

def SinkEndpoint.consume {width : Nat} (endpoint : SinkEndpoint width) : Act :=
  endpoint.channel.pop

end Chan

/-- One point-to-point logical route.  Its width and channel identity are
shared by construction; source and sink are typed island handles rather than
independently spelled strings. -/
structure ChannelRoute (width : Nat) where
  channel : Chan width
  source : IslandHandle
  sink : IslandHandle

def Chan.between {width : Nat} (channel : Chan width) (source sink : IslandHandle) :
    ChannelRoute width := ⟨channel, source, sink⟩

def ChannelRoute.toSystemConnection {width : Nat} (route : ChannelRoute width) :
    SystemConnection :=
  ⟨width, route.channel, route.source.name, route.sink.name⟩

def ChannelRoute.key {width : Nat} (route : ChannelRoute width) : System.ConnectionKey :=
  route.toSystemConnection.key

/-- Bind a typed application route to one checked System exactly once.  The
result is the stable proof handle used by capacity, conservation, endpoint
safety, and later progress theorems; applications do not pass lookup
equalities again. -/
def ChannelRoute.proofHandle {width : Nat} (route : ChannelRoute width)
    (system : System)
    (found : system.connections.find? (fun candidate =>
      candidate.chan.name == route.channel.name) =
        some route.toSystemConnection) :
    System.ConnectionHandle system route.toSystemConnection :=
  System.ConnectionHandle.ofFound system route.toSystemConnection found

/-! ## Typed hierarchical endpoints -/

/-- Open source endpoint exported by a reusable block. Indexing the structure
by the `Chan` value makes it impossible to connect it to a sink for a different
channel merely because the widths happen to agree. -/
structure ExportedSource {width : Nat} (channel : Chan width) where
  owner : IslandHandle

/-- Open sink endpoint exported by a reusable block. -/
structure ExportedSink {width : Nat} (channel : Chan width) where
  owner : IslandHandle

/-- Checked exported source on a sealed `System`. -/
structure DeclaredSource (system : System) {width : Nat}
    (channel : Chan width) extends ExportedSource channel where
  declared : system.openSources.any (fun endpoint =>
    System.openEndpointMatches endpoint channel owner.name) = true

/-- Checked exported sink on a sealed `System`. -/
structure DeclaredSink (system : System) {width : Nat}
    (channel : Chan width) extends ExportedSink channel where
  declared : system.openSinks.any (fun endpoint =>
    System.openEndpointMatches endpoint channel owner.name) = true

def Chan.exportSource {width : Nat} (channel : Chan width)
    (owner : IslandHandle) : ExportedSource channel := ⟨owner⟩

def Chan.exportSink {width : Nat} (channel : Chan width)
    (owner : IslandHandle) : ExportedSink channel := ⟨owner⟩

/-- Generate and record one open source endpoint. It remains a checked top
port until a parent closes it with `connectExports`. -/
def _root_.Loom.Hw.SystemBuilder.exportSource (builder : SystemBuilder)
    {width : Nat} {channel : Chan width} (endpoint : ExportedSource channel) :
    SystemBuilder :=
  builder.openSource channel endpoint.owner.name

def _root_.Loom.Hw.SystemBuilder.exportSink (builder : SystemBuilder)
    {width : Nat} {channel : Chan width} (endpoint : ExportedSink channel) :
    SystemBuilder :=
  builder.openSink channel endpoint.owner.name

/-- Close two already-generated block endpoints. Both arguments share the
same dependent `channel` index, so identity/width/depth/policy cannot drift.
The lowering removes the two open declarations and adds one connection
without duplicating endpoint state. -/
def _root_.Loom.Hw.SystemBuilder.connectExports (builder : SystemBuilder)
    {width : Nat} {channel : Chan width} (source : ExportedSource channel)
    (sink : ExportedSink channel) : SystemBuilder :=
  builder.connectOpen channel source.owner.name sink.owner.name

def _root_.Loom.Hw.SystemBuilder.connectDeclaredExports (builder : SystemBuilder)
    {sourceSystem sinkSystem : System} {width : Nat} {channel : Chan width}
    (source : DeclaredSource sourceSystem channel)
    (sink : DeclaredSink sinkSystem channel) : SystemBuilder :=
  builder.connectOpen channel source.owner.name sink.owner.name

/-- Flatten a checked child System into a parent declaration. The parent owns
the full-chip clock relation, while final assembly requires its reset policy
to agree with every included child. Child islands, internal connections, and
still-open typed endpoints are retained verbatim. Name and policy collisions
fail in the ordinary final `SystemBuilder.check`. -/
def _root_.Loom.Hw.SystemBuilder.includeSystem (builder : SystemBuilder)
    (child : System) : SystemBuilder :=
  { builder with
    islands := builder.islands ++ child.islands
    connections := builder.connections ++ child.connections
    openSources := builder.openSources ++ child.openSources
    openSinks := builder.openSinks ++ child.openSinks
    includedResetPolicies := builder.includedResetPolicies ++
      [child.resetPolicy] }

/-- The intentionally small stock realization set. `synchronous` compiles
the ordinary proved FIFO and is legal only when endpoint clocks agree;
`portableAsync` compiles the portable Gray FIFO and register-bank storage;
`recoveryPortableAsync` adds the compiled independent-reset protocol and
datapath guards around that same portable FIFO. -/
inductive RealizationKind where
  | synchronous
  | portableAsync
  | recoveryPortableAsync
  deriving DecidableEq, Repr

/-- A total per-channel realization selector. Starting from a stock default
and overriding typed routes makes omission impossible: System assembly asks
the plan exactly once for every declared connection key. -/
structure RealizationPlan where
  select : System.ConnectionKey → RealizationKind

namespace RealizationPlan

def portable : RealizationPlan := ⟨fun _ => .portableAsync⟩
def synchronous : RealizationPlan := ⟨fun _ => .synchronous⟩
def recoveryPortable : RealizationPlan := ⟨fun _ => .recoveryPortableAsync⟩

def set {width : Nat} (plan : RealizationPlan) (route : ChannelRoute width)
    (kind : RealizationKind) : RealizationPlan :=
  ⟨fun key => if key = route.key then kind else plan.select key⟩

def useSynchronous {width : Nat} (plan : RealizationPlan)
    (route : ChannelRoute width) : RealizationPlan :=
  plan.set route .synchronous

def usePortableAsync {width : Nat} (plan : RealizationPlan)
    (route : ChannelRoute width) : RealizationPlan :=
  plan.set route .portableAsync

def useRecoveryPortableAsync {width : Nat} (plan : RealizationPlan)
    (route : ChannelRoute width) : RealizationPlan :=
  plan.set route .recoveryPortableAsync

@[simp] theorem select_set_self {width : Nat} (plan : RealizationPlan)
    (route : ChannelRoute width) (kind : RealizationKind) :
    (plan.set route kind).select route.key = kind := by
  simp [set]

end RealizationPlan

namespace PackedChan

variable {alpha : Type u} [HwPacked alpha]

/-- Payload-typed source endpoint.  It erases to the same scalar channel used
by the CDC semantics, proofs, and physical realization. -/
structure SourceEndpoint (alpha : Type u) [HwPacked alpha] where
  channel : PackedChan alpha

/-- Payload-typed sink endpoint. -/
structure SinkEndpoint (alpha : Type u) [HwPacked alpha] where
  channel : PackedChan alpha

/-- A hierarchical source export that retains the semantic payload type.
The scalar endpoint is available explicitly for the implementation layer. -/
structure ExportedSource (channel : PackedChan alpha) where
  bits : _root_.Loom.Hw.ExportedSource channel.bits

/-- A hierarchical sink export that retains the semantic payload type. -/
structure ExportedSink (channel : PackedChan alpha) where
  bits : _root_.Loom.Hw.ExportedSink channel.bits

/-- Checked packed source exported by a sealed System. -/
structure DeclaredSource (system : System) (channel : PackedChan alpha) where
  bits : _root_.Loom.Hw.DeclaredSource system channel.bits

/-- Checked packed sink exported by a sealed System. -/
structure DeclaredSink (system : System) (channel : PackedChan alpha) where
  bits : _root_.Loom.Hw.DeclaredSink system channel.bits

def source (channel : PackedChan alpha) : SourceEndpoint alpha := ⟨channel⟩
def sink (channel : PackedChan alpha) : SinkEndpoint alpha := ⟨channel⟩

def SourceEndpoint.canSend (endpoint : SourceEndpoint alpha) : Expr 1 :=
  endpoint.channel.canEnq

def SourceEndpoint.send (endpoint : SourceEndpoint alpha)
    (payload : PackedExpr alpha) : Act := endpoint.channel.enq payload

def SinkEndpoint.hasData (endpoint : SinkEndpoint alpha) : Expr 1 :=
  endpoint.channel.canDeq

def SinkEndpoint.data (endpoint : SinkEndpoint alpha) : PackedExpr alpha :=
  endpoint.channel.deq

def SinkEndpoint.consume (endpoint : SinkEndpoint alpha) : Act :=
  endpoint.channel.pop

/-- Structured payloads use exactly the same topology and realization path as
their canonical packed bits. -/
def between (channel : PackedChan alpha) (source sink : IslandHandle) :
    ChannelRoute (HwPacked.width alpha) :=
  channel.bits.between source sink

def exportSource (channel : PackedChan alpha) (owner : IslandHandle) :
    ExportedSource channel := ⟨channel.bits.exportSource owner⟩

def exportSink (channel : PackedChan alpha) (owner : IslandHandle) :
    ExportedSink channel := ⟨channel.bits.exportSink owner⟩

end PackedChan

/-- Record a packed hierarchical source without erasing its payload type at
the public composition boundary. -/
def _root_.Loom.Hw.SystemBuilder.exportPackedSource (builder : SystemBuilder)
    {alpha : Type u} [HwPacked alpha] {channel : PackedChan alpha}
    (endpoint : PackedChan.ExportedSource channel) : SystemBuilder :=
  builder.exportSource endpoint.bits

/-- Record a packed hierarchical sink. -/
def _root_.Loom.Hw.SystemBuilder.exportPackedSink (builder : SystemBuilder)
    {alpha : Type u} [HwPacked alpha] {channel : PackedChan alpha}
    (endpoint : PackedChan.ExportedSink channel) : SystemBuilder :=
  builder.exportSink endpoint.bits

/-- Close packed block endpoints while retaining one shared semantic payload
type as well as one shared scalar channel identity. -/
def _root_.Loom.Hw.SystemBuilder.connectPackedExports (builder : SystemBuilder)
    {alpha : Type u} [HwPacked alpha] {channel : PackedChan alpha}
    (source : PackedChan.ExportedSource channel)
    (sink : PackedChan.ExportedSink channel) : SystemBuilder :=
  builder.connectExports source.bits sink.bits

def _root_.Loom.Hw.SystemBuilder.connectPackedDeclaredExports
    (builder : SystemBuilder)
    {alpha : Type u} [HwPacked alpha] {channel : PackedChan alpha}
    {sourceSystem sinkSystem : System}
    (source : PackedChan.DeclaredSource sourceSystem channel)
    (sink : PackedChan.DeclaredSink sinkSystem channel) : SystemBuilder :=
  builder.connectDeclaredExports source.bits sink.bits

/-! ## Channel vocabulary for compatibility and generated code -/

/-- Application-facing spelling of `canEnq`. -/
abbrev Chan.canSend {width : Nat} (channel : Chan width) : Expr 1 :=
  channel.canEnq

/-- Application-facing spelling of `enq`. -/
abbrev Chan.send {width : Nat} (channel : Chan width)
    (payload : Expr width) : Act := channel.enq payload

/-- Application-facing spelling of `canDeq`. -/
abbrev Chan.hasData {width : Nat} (channel : Chan width) : Expr 1 :=
  channel.canDeq

/-- The value currently offered at the receive endpoint. -/
abbrev Chan.data {width : Nat} (channel : Chan width) : Expr width :=
  channel.deq

/-- Accept the value currently offered at the receive endpoint. -/
abbrev Chan.consume {width : Nat} (channel : Chan width) : Act :=
  channel.pop

namespace System

/-- Declare an application channel and generate both endpoint adapters in the
named island Designs. The lower-level `SystemBuilder.connect` remains
available to experts assembling already-adapted islands. Structural checking
fails closed if either named endpoint is absent. -/
def _root_.Loom.Hw.SystemBuilder.channel (builder : SystemBuilder)
    {width : Nat} (channel : Chan width) (source sink : String) : SystemBuilder :=
  let withSource := builder.islands.map fun island =>
    if island.name == source then
      { island with design := channel.withSource island.design }
    else island
  let withSink := withSource.map fun island =>
    if island.name == sink then
      { island with design := channel.withSink island.design }
    else island
  { builder with
    islands := withSink
    connections := builder.connections ++ [⟨width, channel, source, sink⟩] }

/-- Opt-in one-item-per-destination-tick presentation endpoint.  The channel
and its CDC realization are unchanged; only destination-local buffering and
the reported application issue interval differ. -/
def _root_.Loom.Hw.SystemBuilder.channelFullRate (builder : SystemBuilder)
    {width : Nat} (channel : Chan width) (source sink : String) : SystemBuilder :=
  let withSource := builder.islands.map fun island =>
    if island.name == source then
      { island with design := channel.withSource island.design }
    else island
  let withSink := withSource.map fun island =>
    if island.name == sink then
      { island with design := channel.withFullRateSink island.design }
    else island
  { builder with
    islands := withSink
    connections := builder.connections ++ [⟨width, channel, source, sink⟩] }

/-- Application-facing typed channel assembly.  Endpoint adapters are still
generated by the single lower-level implementation above. -/
def _root_.Loom.Hw.SystemBuilder.addChannel (builder : SystemBuilder)
    {width : Nat} (route : ChannelRoute width) : SystemBuilder :=
  builder.channel route.channel route.source.name route.sink.name

def _root_.Loom.Hw.SystemBuilder.addFullRateChannel (builder : SystemBuilder)
    {width : Nat} (route : ChannelRoute width) : SystemBuilder :=
  builder.channelFullRate route.channel route.source.name route.sink.name

/-- Component-level readiness for Loom's compiler-produced portable FIFO.
Realization experts may use this with `portableBindingFromCheck`; application
authors normally use the whole-System readiness report. -/
def portableConnectionCheck (system : System)
    (connection : SystemConnection) : Bool :=
  if depthAtLeastTwo : 2 ≤ connection.chan.depth then
  if powerOfTwo : 2 ^ Nat.log2 connection.chan.depth = connection.chan.depth then
  let fifo := CertifiedPortable.fifoParameters connection depthAtLeastTwo powerOfTwo
  let shape := CertifiedPortable.storageShape connection depthAtLeastTwo
  (system.findIsland? connection.source).isSome &&
    (system.findIsland? connection.sink).isSome &&
    Compile.designWFCheck (Cdc.AsyncFifoDesign.sourceControl fifo) &&
    (Cdc.AsyncFifoDesign.sourceControl fifo).fastWFB &&
    Compile.designWFCheck (Cdc.AsyncFifoDesign.sinkControl fifo) &&
    (Cdc.AsyncFifoDesign.sinkControl fifo).fastWFB &&
    Compile.designWFCheck (Cdc.AsyncQueueStorage.Portable.writerDesign shape) &&
    Compile.designWFCheck (Cdc.AsyncQueueStorage.Portable.readerDesign shape) &&
    (Cdc.AsyncQueueStorage.Portable.writerDesign shape).fastWFB &&
    (Cdc.AsyncQueueStorage.Portable.readerDesign shape).fastWFB
  else false
  else false

/-- Cacheable readiness gate for ordinary synchronous islands. It is
independent of channel realization choices. -/
def islandsCheck (system : System) : Bool :=
  system.islands.all (fun island =>
    Compile.designWFCheck island.design && island.design.fastWFB)

def stockChannelsCheck (system : System) : Bool :=
  system.connections.all (portableConnectionCheck system)

/-- The single stock-path gate exposed to application code. It checks every
island and every generated portable power-of-two channel component. -/
def stockCheck (system : System) : Bool :=
  system.resetPolicy == .coordinated && system.islandsCheck &&
    system.stockChannelsCheck

/-- One actionable failure from the stock realization readiness gate.  This
is diagnostic data only; `stockCheck` remains the compact proposition used by
kernel-checked release definitions. -/
structure ReadinessIssue where
  subject : String
  detail : String
  deriving Repr, DecidableEq

private def islandReadinessIssues (island : SystemIsland) : List ReadinessIssue :=
  (if Compile.designWFCheck island.design then [] else
    [⟨s!"island {island.name}", "compiler well-formedness check failed"⟩]) ++
  (if island.design.fastWFB then [] else
    [⟨s!"island {island.name}", "certified DAG simulator preparation failed"⟩])

private def connectionReadinessIssues (system : System)
    (connection : SystemConnection) : List ReadinessIssue :=
  let subject := s!"channel {connection.chan.name}"
  if depthAtLeastTwo : 2 ≤ connection.chan.depth then
  if powerOfTwo : 2 ^ Nat.log2 connection.chan.depth = connection.chan.depth then
  let fifo := CertifiedPortable.fifoParameters connection depthAtLeastTwo powerOfTwo
  let shape := CertifiedPortable.storageShape connection depthAtLeastTwo
  (if (system.findIsland? connection.source).isSome then [] else
    [⟨subject, s!"source island '{connection.source}' is absent"⟩]) ++
  (if (system.findIsland? connection.sink).isSome then [] else
    [⟨subject, s!"sink island '{connection.sink}' is absent"⟩]) ++
  (if Compile.designWFCheck (Cdc.AsyncFifoDesign.sourceControl fifo) then [] else
    [⟨subject, "source controller compiler check failed"⟩]) ++
  (if (Cdc.AsyncFifoDesign.sourceControl fifo).fastWFB then [] else
    [⟨subject, "source controller simulator preparation failed"⟩]) ++
  (if Compile.designWFCheck (Cdc.AsyncFifoDesign.sinkControl fifo) then [] else
    [⟨subject, "sink controller compiler check failed"⟩]) ++
  (if (Cdc.AsyncFifoDesign.sinkControl fifo).fastWFB then [] else
    [⟨subject, "sink controller simulator preparation failed"⟩]) ++
  (if Compile.designWFCheck (Cdc.AsyncQueueStorage.Portable.writerDesign shape) then [] else
    [⟨subject, "portable storage writer compiler check failed"⟩]) ++
  (if Compile.designWFCheck (Cdc.AsyncQueueStorage.Portable.readerDesign shape) then [] else
    [⟨subject, "portable storage reader compiler check failed"⟩]) ++
  (if (Cdc.AsyncQueueStorage.Portable.writerDesign shape).fastWFB then [] else
    [⟨subject, "portable storage writer simulator preparation failed"⟩]) ++
  (if (Cdc.AsyncQueueStorage.Portable.readerDesign shape).fastWFB then [] else
    [⟨subject, "portable storage reader simulator preparation failed"⟩])
  else [⟨subject,
    s!"portable Gray FIFO depth must be a power of two; declared {connection.chan.depth}"⟩]
  else [⟨subject,
    s!"portable Gray FIFO depth must be at least 2; declared {connection.chan.depth}"⟩]

/-- Complete named readiness report. Unlike a nested `by decide` failure it
identifies the precise island or channel component that prevented assembly. -/
def readinessIssues (system : System) : List ReadinessIssue :=
  (if system.resetPolicy = .coordinated then [] else
    [⟨"system reset",
      "realizePortable selects the coordinated-reset FIFO; use RealizationPlan.recoveryPortable for independentFlush"⟩]) ++
  system.islands.flatMap islandReadinessIssues ++
    system.connections.flatMap (connectionReadinessIssues system)

def ReadinessIssue.render (issue : ReadinessIssue) : String :=
  issue.subject ++ ": " ++ issue.detail

def readinessReport (system : System) : String :=
  String.intercalate "\n" (system.readinessIssues.map ReadinessIssue.render)

private theorem islandChecks_of_stockCheck {system : System}
    (ready : stockCheck system = true) (island : SystemIsland)
    (member : island ∈ system.islands) :
    Compile.designWFCheck island.design = true ∧ island.design.fastWFB = true := by
  have islandsReady := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp ready).1).2
  exact Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp islandsReady island member)

private theorem connectionCheck_of_stockCheck {system : System}
    (ready : stockCheck system = true) (connection : SystemConnection)
    (member : connection ∈ system.connections) :
    portableConnectionCheck system connection = true := by
  have connectionsReady := (Bool.and_eq_true_iff.mp ready).2
  exact List.all_eq_true.mp connectionsReady connection member

private structure StockConnectionFacts (system : System)
    (connection : SystemConnection) : Prop where
  depthAtLeastTwo : 2 ≤ connection.chan.depth
  powerOfTwo : 2 ^ Nat.log2 connection.chan.depth = connection.chan.depth
  sourceSome : (system.findIsland? connection.source).isSome = true
  sinkSome : (system.findIsland? connection.sink).isSome = true
  sourceCompiler : Compile.designWFCheck (Cdc.AsyncFifoDesign.sourceControl
    (CertifiedPortable.fifoParameters connection depthAtLeastTwo powerOfTwo)) = true
  sourceFast : (Cdc.AsyncFifoDesign.sourceControl
    (CertifiedPortable.fifoParameters connection depthAtLeastTwo powerOfTwo)).fastWFB = true
  sinkCompiler : Compile.designWFCheck (Cdc.AsyncFifoDesign.sinkControl
    (CertifiedPortable.fifoParameters connection depthAtLeastTwo powerOfTwo)) = true
  sinkFast : (Cdc.AsyncFifoDesign.sinkControl
    (CertifiedPortable.fifoParameters connection depthAtLeastTwo powerOfTwo)).fastWFB = true
  writerCompiler : Compile.designWFCheck
    (Cdc.AsyncQueueStorage.Portable.writerDesign
      (CertifiedPortable.storageShape connection depthAtLeastTwo)) = true
  readerCompiler : Compile.designWFCheck
    (Cdc.AsyncQueueStorage.Portable.readerDesign
      (CertifiedPortable.storageShape connection depthAtLeastTwo)) = true
  writerFast : (Cdc.AsyncQueueStorage.Portable.writerDesign
    (CertifiedPortable.storageShape connection depthAtLeastTwo)).fastWFB = true
  readerFast : (Cdc.AsyncQueueStorage.Portable.readerDesign
    (CertifiedPortable.storageShape connection depthAtLeastTwo)).fastWFB = true

private def stockConnectionFacts {system : System}
    (connection : SystemConnection)
    (checked : portableConnectionCheck system connection = true) :
    StockConnectionFacts system connection := by
  unfold portableConnectionCheck at checked
  split at checked
  · rename_i depthAtLeastTwo
    split at checked
    · rename_i powerOfTwo
      simp only [Bool.and_eq_true_iff] at checked
      rcases checked with
        ⟨⟨⟨⟨⟨⟨⟨⟨⟨sourceSome, sinkSome⟩,
          sourceCompiler⟩, sourceFast⟩, sinkCompiler⟩, sinkFast⟩,
          writerCompiler⟩, readerCompiler⟩, writerFast⟩, readerFast⟩
      exact ⟨depthAtLeastTwo, powerOfTwo, sourceSome, sinkSome,
        sourceCompiler, sourceFast, sinkCompiler, sinkFast, writerCompiler,
        readerCompiler, writerFast, readerFast⟩
    · simp at checked
  · simp at checked

/-- Presentation is derived from the structurally checked destination Design,
not included in abstract connection identity. -/
def bufferedSinkEndpoint (system : System) (connection : SystemConnection) : Bool :=
  match system.findIsland? connection.sink with
  | none => false
  | some sink => connection.chan.hasFullRateSinkShape sink.design

/-- Construct the closed portable binding after its executable component gate.
This is the CDC-expert layer beneath `System.realizeWith`. -/
def portableBindingFromCheck {system : System}
    (connection : SystemConnection)
    (checked : portableConnectionCheck system connection = true) :
    CertifiedPortableBinding :=
  let facts := stockConnectionFacts connection checked
  let fifo := CertifiedPortable.fifoParameters connection
    facts.depthAtLeastTwo facts.powerOfTwo
  let shape := CertifiedPortable.storageShape connection facts.depthAtLeastTwo
  let controls : Cdc.AsyncFifoDesign.Controls fifo :=
    Cdc.AsyncFifoDesign.certify fifo
      facts.sourceCompiler facts.sourceFast facts.sinkCompiler facts.sinkFast
  let storageReady : Cdc.AsyncQueueStorage.Portable.compilerReady shape :=
    ⟨facts.writerCompiler, facts.readerCompiler, facts.writerFast, facts.readerFast⟩
  { connection
    bufferedSink := bufferedSinkEndpoint system connection
    depthAtLeastTwo := facts.depthAtLeastTwo
    powerOfTwo := facts.powerOfTwo
    controls
    storage := Cdc.AsyncQueueStorage.Portable.certify shape storageReady }

/-- Add the proved graceful-recovery endpoint and datapath guards around one
portable FIFO. This constructs a channel leaf only; whole-island coordination
is a separate System-level obligation. -/
def recoveryPortableBindingFromCheck {system : System}
    (connection : SystemConnection)
    (checked : portableConnectionCheck system connection = true)
    (endpointReady : Chan.RecoveryProtocol.Design.compilerReady = true)
    (datapathReady : Chan.RecoveryDatapath.compilerReady
      { width := connection.width } = true) :
    CertifiedRecoveryPortableBinding :=
  { base := portableBindingFromCheck connection checked
    endpoint := Chan.RecoveryProtocol.Design.certify endpointReady
    datapath := Chan.RecoveryDatapath.certify
      { width := connection.width } datapathReady }

private def stockBinding {system : System} (ready : stockCheck system = true)
    (connection : SystemConnection) (member : connection ∈ system.connections) :
    CertifiedPortableBinding :=
  portableBindingFromCheck connection
    (connectionCheck_of_stockCheck ready connection member)

private def stockBindings {system : System} (ready : stockCheck system = true) :
    List CertifiedChannelBinding :=
  system.connections.attach.map fun connection =>
    .portable (stockBinding ready connection.1 connection.2)

@[simp] private theorem stockBinding_connection {system : System}
    (ready : stockCheck system = true) (connection : SystemConnection)
    (member : connection ∈ system.connections) :
    (stockBinding ready connection member).connection = connection := by
  rfl

private theorem stockBindings_coverage {system : System}
    (ready : stockCheck system = true) :
    (stockBindings ready).map CertifiedChannelBinding.key =
      system.connections.map SystemConnection.key := by
  unfold stockBindings
  rw [List.map_map]
  calc
    _ = system.connections.attach.map (fun connection => connection.1.key) := by
      apply List.map_congr_left
      intro connection _
      simp [CertifiedChannelBinding.key, CertifiedChannelBinding.connection]
    _ = system.connections.map SystemConnection.key := List.attach_map_val

private theorem stockBinding_clockRule {system : System}
    (ready : stockCheck system = true) (connection : SystemConnection)
    (member : connection ∈ system.connections) :
    clockRuleOk system (stockBinding ready connection member).toPhysical = true := by
  have checked := connectionCheck_of_stockCheck ready connection member
  have facts := stockConnectionFacts connection checked
  have sourceSome := facts.sourceSome
  have sinkSome := facts.sinkSome
  cases sourceFound : system.findIsland? connection.source with
  | none => simp [sourceFound] at sourceSome
  | some source =>
      cases sinkFound : system.findIsland? connection.sink with
      | none => simp [sinkFound] at sinkSome
      | some sink =>
          by_cases same : source.clock = sink.clock
          · simp [clockRuleOk, CertifiedPortableBinding.toPhysical,
              portablePhysicalIntent,
              BoundImplementation.custom, sourceFound, sinkFound, same,
              stockBinding_connection]
          · simp [clockRuleOk, CertifiedPortableBinding.toPhysical,
              portablePhysicalIntent,
              BoundImplementation.custom, sourceFound, sinkFound, same,
              stockBinding_connection]

private theorem stockBindings_clockRules {system : System}
    (ready : stockCheck system = true) :
    ((stockBindings ready).map CertifiedChannelBinding.toPhysical).all
      (clockRuleOk system) = true := by
  simp only [stockBindings, List.map_map, List.all_map]
  apply List.all_eq_true.mpr
  intro attached _
  exact stockBinding_clockRule ready attached.1 attached.2

/-! ## Per-channel realization planning -/

private def syncConnectionCheck (system : System)
    (connection : SystemConnection) : Bool :=
  if _positive : 0 < connection.chan.depth then
    match system.findIsland? connection.source,
        system.findIsland? connection.sink with
    | some source, some sink =>
        (source.clock == sink.clock) &&
          (Compile.designWFCheck connection.chan.physicalAdapter &&
            connection.chan.physicalAdapter.fastWFB)
    | _, _ => false
  else false

private structure SyncConnectionFacts (system : System)
    (connection : SystemConnection) where
  positiveDepth : 0 < connection.chan.depth
  source : SystemIsland
  sink : SystemIsland
  sourceFound : system.findIsland? connection.source = some source
  sinkFound : system.findIsland? connection.sink = some sink
  sameClock : source.clock = sink.clock
  compiler : Compile.designWFCheck connection.chan.physicalAdapter = true
  fast : connection.chan.physicalAdapter.fastWFB = true

private def syncConnectionFacts {system : System}
    (connection : SystemConnection)
    (checked : syncConnectionCheck system connection = true) :
    SyncConnectionFacts system connection := by
  unfold syncConnectionCheck at checked
  split at checked
  · rename_i positiveDepth
    split at checked
    · rename_i sourceFound sinkFound
      simp only [Bool.and_eq_true_iff, beq_iff_eq] at checked
      exact ⟨positiveDepth, _, _, sourceFound, sinkFound,
        checked.1, checked.2.1, checked.2.2⟩
    · simp at checked
  · simp at checked

private def selectedConnectionCheck (system : System)
    (plan : RealizationPlan) (connection : SystemConnection) : Bool :=
  match plan.select connection.key with
  | .synchronous => syncConnectionCheck system connection
  | .portableAsync => portableConnectionCheck system connection
  | .recoveryPortableAsync =>
      portableConnectionCheck system connection &&
        Chan.RecoveryProtocol.Design.compilerReady &&
        Chan.RecoveryDatapath.compilerReady { width := connection.width }

/-- Reset policy and selected channel leaves agree. Coordinated systems use
ordinary bindings; independent-flush systems require recovery-capable bindings
on every incident channel. -/
def selectedResetCheck (system : System) (plan : RealizationPlan) : Bool :=
  match system.resetPolicy with
  | .coordinated => system.connections.all fun connection =>
      plan.select connection.key != .recoveryPortableAsync
  | .independentFlush => system.connections.all fun connection =>
      plan.select connection.key == .recoveryPortableAsync

def selectedChannelsCheck (system : System) (plan : RealizationPlan) : Bool :=
  system.connections.all (selectedConnectionCheck system plan)

/-- Whole-System readiness for one explicit realization decision per channel.
Unlike `stockCheck`, this validates same-clock and asynchronous choices with
their distinct depth and clock requirements. -/
def selectedCheck (system : System) (plan : RealizationPlan) : Bool :=
  system.selectedResetCheck plan && system.islandsCheck &&
    system.selectedChannelsCheck plan

private def syncConnectionReadinessIssues (system : System)
    (connection : SystemConnection) : List ReadinessIssue :=
  let subject := s!"channel {connection.chan.name}"
  (if 0 < connection.chan.depth then [] else
    [⟨subject, "synchronous FIFO depth must be positive"⟩]) ++
  (match system.findIsland? connection.source,
      system.findIsland? connection.sink with
    | none, _ => [⟨subject, s!"source island '{connection.source}' is absent"⟩]
    | _, none => [⟨subject, s!"sink island '{connection.sink}' is absent"⟩]
    | some source, some sink =>
        if source.clock = sink.clock then [] else
          [⟨subject,
            s!"synchronous realization requires one clock; source '{source.clock}', sink '{sink.clock}'"⟩]) ++
  (if Compile.designWFCheck connection.chan.physicalAdapter then [] else
    [⟨subject, "synchronous FIFO compiler well-formedness check failed"⟩]) ++
  (if connection.chan.physicalAdapter.fastWFB then [] else
    [⟨subject, "synchronous FIFO simulator preparation failed"⟩])

/-- Named readiness diagnostics for the selected realization of each channel.
The report names the channel, the selected implementation constraint, and the
component that failed rather than exposing a nested dependent proof. -/
def selectedReadinessIssues (system : System)
    (plan : RealizationPlan) : List ReadinessIssue :=
  (system.connections.flatMap fun connection =>
    match system.resetPolicy, plan.select connection.key with
    | .coordinated, .recoveryPortableAsync =>
        [⟨s!"channel {connection.chan.name}",
          "recovery-capable realization requires independentFlush reset policy"⟩]
    | .independentFlush, .recoveryPortableAsync => []
    | .independentFlush, _ =>
        [⟨s!"channel {connection.chan.name}",
          "independentFlush reset policy requires a recovery-capable realization"⟩]
    | .coordinated, _ => []) ++
  system.islands.flatMap islandReadinessIssues ++
    system.connections.flatMap fun connection =>
      match plan.select connection.key with
      | .synchronous => syncConnectionReadinessIssues system connection
      | .portableAsync => connectionReadinessIssues system connection
      | .recoveryPortableAsync =>
          connectionReadinessIssues system connection ++
          (if Chan.RecoveryProtocol.Design.compilerReady then [] else
            [⟨s!"channel {connection.chan.name}",
              "recovery endpoint compiler/simulator preparation failed"⟩]) ++
          (if Chan.RecoveryDatapath.compilerReady
              { width := connection.width } then [] else
            [⟨s!"channel {connection.chan.name}",
              "recovery datapath compiler/simulator preparation failed"⟩])

def selectedReadinessReport (system : System) (plan : RealizationPlan) : String :=
  String.intercalate "\n"
    ((system.selectedReadinessIssues plan).map ReadinessIssue.render)

private theorem selectedIslandChecks {system : System} {plan : RealizationPlan}
    (ready : selectedCheck system plan = true) (island : SystemIsland)
    (member : island ∈ system.islands) :
    Compile.designWFCheck island.design = true ∧ island.design.fastWFB = true := by
  have islandsReady := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp ready).1).2
  exact Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp islandsReady island member)

private theorem selectedConnectionChecked {system : System}
    {plan : RealizationPlan} (ready : selectedChannelsCheck system plan = true)
    (connection : SystemConnection) (member : connection ∈ system.connections) :
    selectedConnectionCheck system plan connection = true := by
  exact List.all_eq_true.mp ready connection member

private structure SelectedBindingFor (system : System)
    (plan : RealizationPlan) (connection : SystemConnection) where
  binding : CertifiedChannelBinding
  connectionEq : binding.connection = connection
  clockRule : clockRuleOk system binding.toPhysical = true
  recoveryRule : binding.recoveryCapable =
    (plan.select connection.key == .recoveryPortableAsync)

private def selectedBindingFor {system : System} {plan : RealizationPlan}
    (ready : selectedChannelsCheck system plan = true)
    (connection : SystemConnection) (member : connection ∈ system.connections) :
    SelectedBindingFor system plan connection := by
  have checked := selectedConnectionChecked ready connection member
  cases selected : plan.select connection.key with
  | synchronous =>
      have syncChecked : syncConnectionCheck system connection = true := by
        simpa [selectedConnectionCheck, selected] using checked
      have facts := syncConnectionFacts connection syncChecked
      let syncBinding : CertifiedSyncBinding :=
        { connection
          bufferedSink := bufferedSinkEndpoint system connection
          positiveDepth := facts.positiveDepth
          adapter := CertifiedDesign.ofChecks facts.compiler facts.fast }
      let binding : CertifiedChannelBinding := .synchronous syncBinding
      have clockRule : clockRuleOk system binding.toPhysical = true := by
        simp [binding, syncBinding, clockRuleOk,
          CertifiedChannelBinding.toPhysical, CertifiedSyncBinding.toPhysical,
          BoundImplementation.custom, facts.sourceFound, facts.sinkFound,
          facts.sameClock]
      exact ⟨binding, rfl, clockRule, by rw [selected]; rfl⟩
  | portableAsync =>
      have portableChecked : portableConnectionCheck system connection = true := by
        simpa [selectedConnectionCheck, selected] using checked
      have facts := stockConnectionFacts connection portableChecked
      let portableBinding := portableBindingFromCheck connection portableChecked
      let binding : CertifiedChannelBinding := .portable portableBinding
      have clockRule : clockRuleOk system binding.toPhysical = true := by
        have portableConnection : portableBinding.connection = connection := rfl
        have sourceSome := facts.sourceSome
        have sinkSome := facts.sinkSome
        cases sourceFound : system.findIsland? connection.source with
        | none => simp [sourceFound] at sourceSome
        | some source =>
            cases sinkFound : system.findIsland? connection.sink with
            | none => simp [sinkFound] at sinkSome
            | some sink =>
                by_cases same : source.clock = sink.clock
                · simp [binding, portableBinding, clockRuleOk,
                    CertifiedChannelBinding.toPhysical,
                    CertifiedPortableBinding.toPhysical,
                    portablePhysicalIntent,
                    BoundImplementation.custom, portableConnection,
                    sourceFound, sinkFound, same]
                · simp [binding, portableBinding, clockRuleOk,
                    CertifiedChannelBinding.toPhysical,
                    CertifiedPortableBinding.toPhysical,
                    portablePhysicalIntent,
                    BoundImplementation.custom, portableConnection,
                    sourceFound, sinkFound, same]
      exact ⟨binding, rfl, clockRule, by rw [selected]; rfl⟩
  | recoveryPortableAsync =>
      have recoveryChecked :
          (portableConnectionCheck system connection &&
            Chan.RecoveryProtocol.Design.compilerReady &&
            Chan.RecoveryDatapath.compilerReady
              { width := connection.width }) = true := by
        simpa [selectedConnectionCheck, selected] using checked
      have parts := Bool.and_eq_true_iff.mp recoveryChecked
      have head := Bool.and_eq_true_iff.mp parts.1
      have portableChecked : portableConnectionCheck system connection = true :=
        head.1
      have facts := stockConnectionFacts connection portableChecked
      let recoveryBinding := recoveryPortableBindingFromCheck connection
        portableChecked head.2 parts.2
      let binding : CertifiedChannelBinding := .recoveryPortable recoveryBinding
      have clockRule : clockRuleOk system binding.toPhysical = true := by
        have connectionEq : recoveryBinding.connection = connection := rfl
        have sourceSome := facts.sourceSome
        have sinkSome := facts.sinkSome
        cases sourceFound : system.findIsland? connection.source with
        | none => simp [sourceFound] at sourceSome
        | some source =>
            cases sinkFound : system.findIsland? connection.sink with
            | none => simp [sinkFound] at sinkSome
            | some sink =>
                by_cases same : source.clock = sink.clock
                · simp [binding, recoveryBinding, clockRuleOk,
                    CertifiedChannelBinding.toPhysical,
                    CertifiedRecoveryPortableBinding.toPhysical,
                    portablePhysicalIntent,
                    BoundImplementation.customInstance, connectionEq,
                    sourceFound, sinkFound, same]
                · simp [binding, recoveryBinding, clockRuleOk,
                    CertifiedChannelBinding.toPhysical,
                    CertifiedRecoveryPortableBinding.toPhysical,
                    portablePhysicalIntent,
                    BoundImplementation.customInstance, connectionEq,
                    sourceFound, sinkFound, same]
      exact ⟨binding, rfl, clockRule, by rw [selected]; rfl⟩

private def selectedBinding {system : System} {plan : RealizationPlan}
    (ready : selectedChannelsCheck system plan = true)
    (connection : SystemConnection) (member : connection ∈ system.connections) :
    CertifiedChannelBinding :=
  (selectedBindingFor ready connection member).binding

@[simp] private theorem selectedBinding_connection {system : System}
    {plan : RealizationPlan} (ready : selectedChannelsCheck system plan = true)
    (connection : SystemConnection) (member : connection ∈ system.connections) :
    (selectedBinding ready connection member).connection = connection := by
  exact (selectedBindingFor ready connection member).connectionEq

private def selectedBindings {system : System} {plan : RealizationPlan}
    (ready : selectedChannelsCheck system plan = true) : List CertifiedChannelBinding :=
  system.connections.attach.map fun connection =>
    selectedBinding ready connection.1 connection.2

private theorem selectedBindings_coverage {system : System}
    {plan : RealizationPlan} (ready : selectedChannelsCheck system plan = true) :
    (selectedBindings ready).map CertifiedChannelBinding.key =
      system.connections.map SystemConnection.key := by
  unfold selectedBindings
  rw [List.map_map]
  calc
    _ = system.connections.attach.map (fun connection => connection.1.key) := by
      apply List.map_congr_left
      intro connection _
      simp [CertifiedChannelBinding.key, selectedBinding_connection]
    _ = system.connections.map SystemConnection.key := List.attach_map_val

private theorem selectedBinding_clockRule {system : System}
    {plan : RealizationPlan} (ready : selectedChannelsCheck system plan = true)
    (connection : SystemConnection) (member : connection ∈ system.connections) :
    clockRuleOk system (selectedBinding ready connection member).toPhysical = true := by
  exact (selectedBindingFor ready connection member).clockRule

private theorem selectedBinding_recoveryCapable {system : System}
    {plan : RealizationPlan} (ready : selectedChannelsCheck system plan = true)
    (connection : SystemConnection) (member : connection ∈ system.connections) :
    (selectedBinding ready connection member).recoveryCapable =
      (plan.select connection.key == .recoveryPortableAsync) :=
  (selectedBindingFor ready connection member).recoveryRule

private theorem selectedBindings_clockRules {system : System}
    {plan : RealizationPlan} (ready : selectedChannelsCheck system plan = true) :
    ((selectedBindings ready).map CertifiedChannelBinding.toPhysical).all
      (clockRuleOk system) = true := by
  simp only [selectedBindings, List.map_map, List.all_map]
  apply List.all_eq_true.mpr
  intro attached _
  exact selectedBinding_clockRule ready attached.1 attached.2

private theorem selectedBindings_resetCompatibility {system : System}
    {plan : RealizationPlan}
    (channelsReady : selectedChannelsCheck system plan = true)
    (resetReady : selectedResetCheck system plan = true) :
    resetBindingsCheck system (selectedBindings channelsReady) = true := by
  cases policyEq : system.resetPolicy with
  | coordinated =>
      simp only [selectedResetCheck, policyEq] at resetReady
      simp only [resetBindingsCheck, policyEq]
      have noRecovery :
          (selectedBindings channelsReady).any
            CertifiedChannelBinding.recoveryCapable = false := by
        apply List.any_eq_false.mpr
        intro binding member capable
        simp only [selectedBindings, List.mem_map] at member
        obtain ⟨attached, _, rfl⟩ := member
        rw [selectedBinding_recoveryCapable] at capable
        have compatible := List.all_eq_true.mp resetReady
          attached.1 attached.2
        exact (bne_iff_ne.mp compatible) (beq_iff_eq.mp capable)
      simp [noRecovery]
  | independentFlush =>
      simp only [selectedResetCheck, policyEq] at resetReady
      simp only [resetBindingsCheck, policyEq]
      apply List.all_eq_true.mpr
      intro binding member
      simp only [selectedBindings, List.mem_map] at member
      obtain ⟨attached, _, rfl⟩ := member
      rw [selectedBinding_recoveryCapable]
      exact List.all_eq_true.mp resetReady attached.1 attached.2

private theorem stockBindings_resetCompatibility {system : System}
    (ready : stockCheck system = true) :
    resetBindingsCheck system (stockBindings ready) = true := by
  have policyReady : (system.resetPolicy == .coordinated) = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready).1).1
  have policyEq : system.resetPolicy = .coordinated := beq_iff_eq.mp policyReady
  simp [resetBindingsCheck, policyEq, stockBindings,
    CertifiedChannelBinding.recoveryCapable]

/-- Reusable island-only certificate cache. Defining one of these at module
scope lets Lean's object cache retain expensive compiler/DAG readiness proofs
while several channel plans or top-level assemblies reuse the islands. -/
structure CertifiedIslands (system : System) where
  certificate : ∀ (name : String) (island : SystemIsland),
    system.findIsland? name = some island → CertifiedDesign island.design

def certifyIslands (system : System) (ready : islandsCheck system = true) :
    CertifiedIslands system where
  certificate := by
    intro name island found
    have member : island ∈ system.islands := List.mem_of_find?_eq_some found
    have checked := List.all_eq_true.mp ready island member
    have checks := Bool.and_eq_true_iff.mp checked
    exact CertifiedDesign.ofChecks checks.1 checks.2

/-- Opaque reusable hierarchy node. The interface is chosen by the block
author and normally consists of `DeclaredSource`/`DeclaredSink` values; the
theorem bundle may depend on that exact checked System and interface. Island
certificates are stored once beside the block. -/
structure SealedBlock (Interface : System → Type u)
    (TheoremBundle : (system : System) → Interface system → Type u) where
  system : System
  islands : CertifiedIslands system
  interface : Interface system
  theorems : TheoremBundle system interface

def _root_.Loom.Hw.SystemBuilder.includeBlock
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (builder : SystemBuilder) (block : SealedBlock Interface TheoremBundle) :
    SystemBuilder :=
  builder.includeSystem block.system

/-- Realization-only gate used with a cached `CertifiedIslands`. -/
def realizationCheck (system : System) (plan : RealizationPlan) : Bool :=
  system.selectedResetCheck plan && system.selectedChannelsCheck plan

/-- A reusable multi-island subsystem. Unlike a scalar component it retains
its separate islands, open typed channel endpoints, child theorem bundle, and
an explicit realization choice already checked against its own System. -/
structure SystemFragment (Interface : System → Type u)
    (TheoremBundle : (system : System) → Interface system → Type u) where
  block : SealedBlock Interface TheoremBundle
  plan : RealizationPlan
  realizationReady : realizationCheck block.system plan = true

namespace SystemFragment

def system {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (fragment : SystemFragment Interface TheoremBundle) : System :=
  fragment.block.system

def interface {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (fragment : SystemFragment Interface TheoremBundle) :
    Interface fragment.system := fragment.block.interface

/-- Evidence that a theorem about one fragment island came from its ordinary
open-Design semantics. This provenance is what makes the theorem transportable
to a parent; an arbitrary proposition over the child System is not silently
assumed to survive new parent connections. -/
structure LocalInvariant
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (fragment : SystemFragment Interface TheoremBundle)
    (property : St → Prop) where
  island : SystemIsland
  found : fragment.system.findIsland? island.name = some island
  localInvariant :
    (island.design.toAssumedOpenTSys (fun _ _ => True)).Invariant property

theorem LocalInvariant.inChild
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    {fragment : SystemFragment Interface TheoremBundle}
    {property : St → Prop} (certificate : LocalInvariant fragment property) :
    fragment.system.Invariant
      (System.atIsland certificate.island.name property) :=
  fragment.system.liftIsland certificate.island certificate.found
    certificate.localInvariant

/-- Explicit compatibility premise for fragment theorem transport. A parent
may restrict a child's schedules, but may not admit an event trace the child
relation excluded. -/
structure ClockCompatible
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (parent : System) (fragment : SystemFragment Interface TheoremBundle) : Prop where
  refines : parent.clockRel.Refines fragment.system.clockRel

/-- Lift a genuinely island-local theorem into any parent containing the same
island. Local open-Design invariants already quantify over arbitrary inputs,
so neither the surrounding channel graph nor its clock relation is relevant.
Schedule-sensitive, fragment-wide theorem transport uses an execution
projection rather than this operation. -/
theorem liftLocalInvariant
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (parent : System) (fragment : SystemFragment Interface TheoremBundle)
    {property : St → Prop} (certificate : LocalInvariant fragment property)
    (found : parent.findIsland? certificate.island.name = some certificate.island) :
    parent.Invariant (System.atIsland certificate.island.name property) :=
  parent.liftIsland certificate.island found certificate.localInvariant

end SystemFragment

/-- Include a fragment without flattening its islands or CDC channels. -/
def _root_.Loom.Hw.SystemBuilder.includeFragment
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (builder : SystemBuilder) (fragment : SystemFragment Interface TheoremBundle) :
    SystemBuilder :=
  builder.includeBlock fragment.block

/-- Preserve a child's explicit realization choices when building the parent
plan. Final parent checking still detects key collisions or incompatibility. -/
def _root_.Loom.Hw.RealizationPlan.includeFragment
    {Interface : System → Type u}
    {TheoremBundle : (system : System) → Interface system → Type u}
    (parent : RealizationPlan) (fragment : SystemFragment Interface TheoremBundle) :
    RealizationPlan :=
  ⟨fun key =>
    if fragment.system.connections.any (fun connection => connection.key == key) then
      fragment.plan.select key
    else parent.select key⟩

/-- The complete stock application package. The fields are projections for
advanced use; ordinary execution, inspection, and emission are provided as
methods below. -/
structure Application (system : System) where
  certified : CertifiedSystem system
  artifact : CertifiedRealizedSystem system certified

/-! ### Certified realization overlays

Target evidence often changes only a few physical leaves while retaining the
exact logical System and stock bindings everywhere else.  The overlay keeps
that operation separate from the technology-neutral `system` declaration and
derives ordered coverage instead of asking the evidence package to rebuild the
complete heterogeneous binding inventory by hand. -/

private def replaceCertifiedBinding
    (replacement current : CertifiedChannelBinding) : CertifiedChannelBinding :=
  if replacement.key = current.key then replacement else current

private def replaceCertifiedBindingIn
    (bindings : List CertifiedChannelBinding)
    (replacement : CertifiedChannelBinding) : List CertifiedChannelBinding :=
  bindings.map (replaceCertifiedBinding replacement)

@[simp] private theorem replaceCertifiedBinding_key
    (replacement current : CertifiedChannelBinding) :
    (replaceCertifiedBinding replacement current).key = current.key := by
  simp only [replaceCertifiedBinding]
  split <;> simp_all

@[simp] private theorem replaceCertifiedBindingIn_keys
    (bindings : List CertifiedChannelBinding)
    (replacement : CertifiedChannelBinding) :
    (replaceCertifiedBindingIn bindings replacement).map
        CertifiedChannelBinding.key =
      bindings.map CertifiedChannelBinding.key := by
  simp [replaceCertifiedBindingIn]

/-- A sparse, fail-closed physical overlay. Every replacement must name one
existing binding exactly once. The replacement itself carries its channel
refinement and any target-storage assumption; this structure adds no new
semantic or technology-specific trust. -/
structure CertifiedBindingOverlay (base : List CertifiedChannelBinding) where
  replacements : List CertifiedChannelBinding
  distinct : (replacements.map CertifiedChannelBinding.key).Nodup
  covered : ∀ replacement ∈ replacements,
    replacement.key ∈ base.map CertifiedChannelBinding.key

namespace CertifiedBindingOverlay

def apply {base : List CertifiedChannelBinding}
    (overlay : CertifiedBindingOverlay base) : List CertifiedChannelBinding :=
  overlay.replacements.foldl replaceCertifiedBindingIn base

private theorem foldl_replaceCertifiedBindingIn_keys
    (replacements base : List CertifiedChannelBinding) :
    (replacements.foldl replaceCertifiedBindingIn base).map
        CertifiedChannelBinding.key =
      base.map CertifiedChannelBinding.key := by
  induction replacements generalizing base with
  | nil => rfl
  | cons replacement rest ih =>
      simp only [List.foldl_cons]
      rw [ih, replaceCertifiedBindingIn_keys]

@[simp] theorem apply_keys {base : List CertifiedChannelBinding}
    (overlay : CertifiedBindingOverlay base) :
    overlay.apply.map CertifiedChannelBinding.key =
      base.map CertifiedChannelBinding.key := by
  exact foldl_replaceCertifiedBindingIn_keys overlay.replacements base

end CertifiedBindingOverlay

/-- Apply a sparse binding overlay to an existing certified artifact. Ordered
connection coverage is inherited mechanically. Only the physical clock/reset
compatibility checks for the replacement bindings remain as explicit local
obligations, normally discharged by `decide` in the evidence package. -/
def CertifiedRealizedSystem.withOverlay
    {system : System} {certified : CertifiedSystem system}
    (artifact : CertifiedRealizedSystem system certified)
    (overlay : CertifiedBindingOverlay artifact.bindings)
    (clockRules : (overlay.apply.map CertifiedChannelBinding.toPhysical).all
      (clockRuleOk system) = true)
    (resetCompatibility : resetBindingsCheck system overlay.apply = true) :
    CertifiedRealizedSystem system certified where
  bindings := overlay.apply
  coverage := by
    rw [CertifiedBindingOverlay.apply_keys]
    exact artifact.coverage
  clockRules := clockRules
  resetCompatibility := resetCompatibility

/-- Assemble a new physical plan around already-certified islands. Only the
reset/connection realization checks are redone. -/
def realizeWithCertified (system : System) (islands : CertifiedIslands system)
    (plan : RealizationPlan) (ready : realizationCheck system plan = true) :
    Application system := by
  have channelsReady : selectedChannelsCheck system plan = true :=
    (Bool.and_eq_true_iff.mp ready).2
  have resetReady : selectedResetCheck system plan = true :=
    (Bool.and_eq_true_iff.mp ready).1
  let certified : CertifiedSystem system :=
    { islandCertificate := islands.certificate
      channelCertificate := by
        intro connection member
        let binding := selectedBinding channelsReady connection member
        have connectionEq : binding.connection = connection :=
          selectedBinding_connection channelsReady connection member
        rw [← connectionEq]
        exact binding.refinement }
  exact
    { certified
      artifact :=
        { bindings := selectedBindings channelsReady
          coverage := selectedBindings_coverage channelsReady
          clockRules := selectedBindings_clockRules channelsReady
          resetCompatibility := selectedBindings_resetCompatibility
            channelsReady resetReady } }

/-- Realize each declared channel according to a total typed plan. Every
choice stays on Loom's closed compiler-produced path; the assembly proof
retains the exact ordered connection inventory. -/
def realizeWith (system : System) (plan : RealizationPlan)
    (ready : selectedCheck system plan = true) : Application system := by
  have islandsReady : islandsCheck system = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready).1).2
  have physicalReady : realizationCheck system plan = true := by
    exact Bool.and_eq_true_iff.mpr
      ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready).1).1,
        (Bool.and_eq_true_iff.mp ready).2⟩
  exact system.realizeWithCertified (system.certifyIslands islandsReady)
    plan physicalReady

def realizeWithChecked (system : System) (plan : RealizationPlan) :
    Except String (Application system) :=
  match ready : selectedCheck system plan with
  | true => pure (system.realizeWith plan ready)
  | false =>
      let report := system.selectedReadinessReport plan
      throw <| if report.isEmpty then
        "selected multiclock readiness failed without a diagnostic (internal error)"
      else report

/-- Select Loom's portable certified power-of-two crossing implementation for
every declared channel. This is the ordinary application-level `realize`.
The sole proof is the result of the derived whole-System `stockCheck`. -/
def realizePortable (system : System) (ready : stockCheck system = true) :
    Application system := by
  let certified : CertifiedSystem system :=
    { islandCertificate := by
        intro name island found
        have member : island ∈ system.islands := by
          exact List.mem_of_find?_eq_some found
        have checks := islandChecks_of_stockCheck ready island member
        exact CertifiedDesign.ofChecks checks.1 checks.2
      channelCertificate := by
        intro connection member
        simpa only [stockBinding_connection] using
          (stockBinding ready connection member).refinement }
  exact
    { certified
      artifact :=
        { bindings := stockBindings ready
          coverage := stockBindings_coverage ready
          clockRules := stockBindings_clockRules ready
          resetCompatibility := stockBindings_resetCompatibility ready } }

/-- Runtime/generator entry point with actionable failures. Successful
preparation returns the same proof-carrying `Application` as
`realizePortable`; release sources may keep the theorem-valued form so Lean's
compiled object cache stores the result. -/
def realizePortableChecked (system : System) : Except String (Application system) :=
  match ready : stockCheck system with
  | true => pure (system.realizePortable ready)
  | false =>
      let report := system.readinessReport
      throw <| if report.isEmpty then
        "portable multiclock readiness failed without a diagnostic (internal error)"
      else report

namespace Application

abbrev State {system : System} (application : Application system) :=
  application.certified.State

/-- Replay a concrete schedule without exposing simulator certificates. -/
def run {system : System} (application : Application system)
    (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : application.State :=
  application.certified.runPrefix events inputs

/-- Public correspondence theorem for the executor application authors
actually call.  No `CertifiedSystem.State` internals or simulator agreement
relation appears in the statement. -/
theorem run_semantic_eq {system : System} (application : Application system)
    (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) :
    (application.run events inputs).semantic =
      system.runPrefix events inputs :=
  application.certified.runPrefix_semantic_eq events inputs

/-- Replay and retain only the flat island states, channel graph, and event
time.  This is the preferred result for long campaigns that do not need the
closure-based semantic island states after the correspondence theorem has
been established. -/
def runCompact {system : System} (application : Application system)
    (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) :
    application.certified.Snapshot :=
  application.certified.runCompact events inputs

theorem runCompact_agrees {system : System} (application : Application system)
    (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) :
    (application.runCompact events inputs).Agrees
      (system.runPrefix events inputs) :=
  application.certified.runCompact_agrees events inputs

/-- Fail-closed replay against the declared clock relation. -/
def runChecked {system : System} (application : Application system)
    (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) :
    Except String application.State :=
  application.certified.runPrefixChecked events inputs

/-- A successful fail-closed application run is the same certified execution
as `run`; checking the clock relation cannot substitute another runner. -/
theorem runChecked_eq_run {system : System} (application : Application system)
    (events : SchedulePrefix) (inputs : ExternalInputs)
    (accepted : system.clockRel.accepts events = true) :
    application.runChecked events inputs = .ok (application.run events inputs) := by
  simp [Application.runChecked, CertifiedSystem.runPrefixChecked, accepted,
    Application.run]
  rfl

/-- Replay explicit graceful-recovery events through the same certified DAG
island states used by ordinary application execution. -/
def runRecovery {system : System} (application : Application system)
    (events : RecoverySchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : application.State :=
  application.certified.runRecoveryPrefix events inputs

/-- Fail closed on the declared reset policy, island names, and clock
relation before certified recovery replay. -/
def runRecoveryChecked {system : System} (application : Application system)
    (events : RecoverySchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) :
    Except String application.State :=
  application.certified.runRecoveryPrefixChecked events inputs

theorem runRecovery_semantic_eq {system : System}
    (application : Application system) (events : RecoverySchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) :
    (application.runRecovery events inputs).semantic =
      system.runRecoveryPrefix events inputs :=
  application.certified.runRecoveryPrefix_semantic_eq events inputs

/-- Read an island register from the authoritative semantic projection without
reintroducing a user-spelled island name.  Membership is checked by System
assembly; `coords`/`requireCoverage` remain the strict comparison surface. -/
def readReg {system : System} (application : Application system)
    {width : Nat} (state : application.State) (island : IslandHandle)
    (reg : Reg width) : Nat :=
  (state.semantic.island island.name).regs reg.name width |>.toNat

/-- Lower-level name-based inspection for generated tooling. -/
def readRegNamed {system : System} (application : Application system)
    {width : Nat} (state : application.State) (island : String)
    (reg : Reg width) : Nat :=
  (state.semantic.island island).regs reg.name width |>.toNat

/-- Inspect the current abstract contents of a width-typed channel. -/
def readChannel {system : System} (application : Application system)
    {width : Nat} (state : application.State) (channel : Chan width) :
    List (BitVec width) :=
  (state.semantic.channel channel.name).asWidth width

/-- Inspect a structured channel using the same canonical pack/unpack relation
as registers, memories, and combinational packed expressions. -/
def readPackedChannel {system : System} (application : Application system)
    {alpha : Type u} [HwPacked alpha] (state : application.State)
    (channel : PackedChan alpha) : List alpha :=
  (application.readChannel state channel.bits).map HwPacked.unpack

/-- The exact timing rows carried by the selected physical realization. The
list has the same proved connection-key domain as RTL, constraints, and the
crossing inventory. -/
def timingGroups {system : System} (application : Application system) :
    List TimingGroup :=
  application.artifact.realized.artifacts.timing

/-- Inspect the timing contract for one typed route. `none` can only indicate
that the supplied route is not a connection in this Application; realized
connections are covered by `timing_keys_complete`. -/
def timingFor {system : System} (application : Application system)
    {width : Nat} (route : ChannelRoute width) : Option ChannelTiming :=
  (application.timingGroups.find? fun group => group.key = route.key).map
    (fun group => group.timing)

/-- Human-readable technology-neutral timing diagnostic, produced only when
requested; normal emission writes no timing sidecar. -/
def timingReport {system : System} (application : Application system) : String :=
  String.intercalate "\n\n" (application.timingGroups.map TimingGroup.describe)

theorem timingKeys_complete {system : System} (application : Application system) :
    application.timingGroups.map (fun group => group.key) =
      system.connections.map SystemConnection.key :=
  application.artifact.realized.timing_keys_complete

/-- Emit the certified stock artifact. -/
def emit {system : System} (application : Application system)
    (directory : System.FilePath) : IO Unit :=
  application.artifact.emit directory

end Application
end System
end Loom.Hw
