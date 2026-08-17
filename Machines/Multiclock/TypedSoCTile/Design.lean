-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Arbiter
import Loom.Hw.ComponentHierarchy
import Loom.Hw.MemoryPort
import Loom.Hw.Pipeline
import Loom.Hw.Plugin
import Loom.Hw.Multiclock

/-!
# Typed SoC composition tile

This deliberately small SoC vertical slice crosses Loom's construction
boundaries in one value.  A plugin-selected typed component graph produces a
tagged request stream in the core clock domain.  One endpoint broadcasts each
accepted request atomically to two asynchronous channels.  Two memory-domain
services execute the same synchronous-read, byte-masked memory protocol and
return responses over independent asynchronous channels.  A sibling monitor
fragment closes those response endpoints and checks the two implementations,
the request protocol, memory contents, ordering, digest, and transfer ledger.

The second memory remains an ordinary Loom memory in this neutral System.  A
separate contracted target binding may replace only its physical island
module; that assumption is not promoted into the logical certificate here.
-/

namespace Machines.Multiclock.TypedSoCTile

open Loom.Hw
open Loom.Hw.Plugin

set_option maxHeartbeats 10000000

abbrev requestWidth : Nat := 66
abbrev responseWidth : Nat := 62

abbrev RequestBits := BitVec requestWidth
abbrev ResponseBits := BitVec responseWidth

abbrev requestType := "TypedSoCTile.Request"
abbrev responseType := "TypedSoCTile.Response"

/- Request layout, MSB first: sequence[19:0], client, write, address[7:0],
data[31:0], byte mask[3:0].  The 20-bit tag is sufficient for a one-million
transaction campaign. -/
namespace Request

def sequence (value : Expr requestWidth) : Expr 20 := .slice value 46 20
def client (value : Expr requestWidth) : Expr 1 := .slice value 45 1
def write (value : Expr requestWidth) : Expr 1 := .slice value 44 1
def address (value : Expr requestWidth) : Expr 8 := .slice value 36 8
def data (value : Expr requestWidth) : Expr 32 := .slice value 4 32
def mask (value : Expr requestWidth) : Expr 4 := .slice value 0 4

def make (clientId : BitVec 1) (sequenceValue : Expr 20) : Expr requestWidth :=
  let extended : Expr 32 := .zext sequenceValue 32
  Expr.concat sequenceValue <| Expr.concat (.lit clientId) <|
    Expr.concat (.slice extended 8 1) <| Expr.concat (.slice extended 0 8) <|
      Expr.concat (.xor extended
        (.lit (if clientId = 0 then 0x13579bdf else 0x2468ace0)))
        (.slice extended 0 4)

def memoryAddress (value : Expr requestWidth) : Expr 9 :=
  Expr.concat (client value) (address value)

end Request

/- Response layout, MSB first: sequence[19:0], client, address[7:0], write,
result[31:0]. -/
namespace Response

def sequence (value : Expr responseWidth) : Expr 20 := .slice value 42 20
def client (value : Expr responseWidth) : Expr 1 := .slice value 41 1
def address (value : Expr responseWidth) : Expr 8 := .slice value 33 8
def write (value : Expr responseWidth) : Expr 1 := .slice value 32 1
def result (value : Expr responseWidth) : Expr 32 := .slice value 0 32

def make (request : Expr requestWidth) (resultValue : Expr 32) : Expr responseWidth :=
  Expr.concat (Request.sequence request) <| Expr.concat (Request.client request) <|
    Expr.concat (Request.address request) <|
      Expr.concat (Request.write request) resultValue

end Response

def maskedWord (old data : Expr 32) (mask : Expr 4) : Expr 32 :=
  Expr.concat
    (.mux (.slice mask 3 1) (.slice data 24 8) (.slice old 24 8)) <|
  Expr.concat
    (.mux (.slice mask 2 1) (.slice data 16 8) (.slice old 16 8)) <|
  Expr.concat
    (.mux (.slice mask 1 1) (.slice data 8 8) (.slice old 8 8))
    (.mux (.slice mask 0 1) (.slice data 0 8) (.slice old 0 8))

inductive CoreDomain
inductive MemoryDomain
inductive MonitorDomain

instance : ClockDomain CoreDomain where name := "tile_core_clk"
instance : ClockDomain MemoryDomain where name := "tile_memory_clk"
instance : ClockDomain MonitorDomain where name := "tile_core_clk"

@[simp] theorem coreDomain_name : ClockDomain.name CoreDomain = "tile_core_clk" := rfl
@[simp] theorem memoryDomain_name : ClockDomain.name MemoryDomain = "tile_memory_clk" := rfl
@[simp] theorem monitorDomain_name : ClockDomain.name MonitorDomain = "tile_core_clk" := rfl

abbrev coreClock : ClockHandle := .named "tile_core_clk"
abbrev memoryClock : ClockHandle := .named "tile_memory_clk"

abbrev requestInternal : Chan requestWidth :=
  { name := "tile_request_internal", depth := 8, policy := .exchange }
abbrev requestContract : Chan requestWidth :=
  { name := "tile_request_contract", depth := 8, policy := .exchange }
abbrev responseInternal : Chan responseWidth :=
  { name := "tile_response_internal", depth := 8, policy := .exchange }
abbrev responseContract : Chan responseWidth :=
  { name := "tile_response_contract", depth := 8, policy := .exchange }

/-! ## Plugin-configured core component graph -/

private abbrev sourcePorts : Stream.SourcePorts CoreDomain RequestBits :=
  Stream.sourcePorts "out" requestType
private abbrev runLimitPort : Port .input CoreDomain (BitVec 20) :=
  Port.bits .input 20 "run_limit"
private abbrev producerHoldPort : Port .input CoreDomain (BitVec 1) :=
  Port.bits .input 1 "producer_hold"
private abbrev sequenceOut : Port .output CoreDomain (BitVec 20) :=
  Port.bits .output 20 "sequence_count"
private abbrev acceptedOut : Port .output CoreDomain (BitVec 32) :=
  Port.bits .output 32 "accepted_count"
private abbrev sourceStallOut : Port .output CoreDomain (BitVec 32) :=
  Port.bits .output 32 "stall_count"

private abbrev sourceComponent (name : String) (clientId : BitVec 1) : Component :=
  let sequenceReg : Reg 20 := ⟨"sequence"⟩
  let acceptedReg : Reg 32 := ⟨"accepted"⟩
  let stallsReg : Reg 32 := ⟨"stalls"⟩
  let active := .and (.not producerHoldPort.bitReg.rd)
    (.ult sequenceReg.rd runLimitPort.bitReg.rd)
  let accepted := .and active sourcePorts.ready.bitReg.rd
  { name
    interface := ⟨sourcePorts.decls ++
        [runLimitPort.decl, producerHoldPort.decl, sequenceOut.decl,
          acceptedOut.decl, sourceStallOut.decl]⟩
    design :=
        { name
          regs := [sequenceReg.decl 0, acceptedReg.decl 0, stallsReg.decl 0]
          mems := []
          inputs := [sourcePorts.ready.bitReg.input, runLimitPort.bitReg.input,
            producerHoldPort.bitReg.input]
          rules :=
            [⟨"advance", .ite accepted
                (.seq (sequenceReg.set (.add sequenceReg.rd (.lit 1)))
                  (acceptedReg.set (.add acceptedReg.rd (.lit 1))))
                (.ite (.and active (.not sourcePorts.ready.bitReg.rd))
                  (stallsReg.set (.add stallsReg.rd (.lit 1))) .skip)⟩]
          outputs := []
          combOutputs :=
            [⟨sourcePorts.valid.name, 1, active⟩,
             ⟨sourcePorts.payload.name, requestWidth,
                Request.make clientId sequenceReg.rd⟩,
             ⟨sequenceOut.name, 20, sequenceReg.rd⟩,
             ⟨acceptedOut.name, 32, acceptedReg.rd⟩,
             ⟨sourceStallOut.name, 32, stallsReg.rd⟩] } }

private abbrev sourceAComponent : Component := sourceComponent "TileSourceA" 0#1
private abbrev sourceBComponent : Component := sourceComponent "TileSourceB" 1#1

private def sourceA : DomainComponent CoreDomain where
  implementation := DomainDesign.authored sourceAComponent.design
  sealed :=
    { component := sourceAComponent
      interfaceOk := by unfold sourceAComponent sourceComponent; decide
      readsOk := by unfold sourceAComponent sourceComponent; decide
      certified := CertifiedDesign.ofChecks
        (by unfold sourceAComponent sourceComponent; decide)
        (by unfold sourceAComponent sourceComponent; decide) }
  implementationEq := rfl
  domainOk := by decide

private def sourceB : DomainComponent CoreDomain where
  implementation := DomainDesign.authored sourceBComponent.design
  sealed :=
    { component := sourceBComponent
      interfaceOk := by unfold sourceBComponent sourceComponent; decide
      readsOk := by unfold sourceBComponent sourceComponent; decide
      certified := CertifiedDesign.ofChecks
        (by unfold sourceBComponent sourceComponent; decide)
        (by unfold sourceBComponent sourceComponent; decide) }
  implementationEq := rfl
  domainOk := by decide

private structure MergePorts where
  first : Stream.SinkPorts CoreDomain RequestBits
  second : Stream.SinkPorts CoreDomain RequestBits
  output : Stream.SourcePorts CoreDomain RequestBits

private abbrev mergePorts : MergePorts :=
  { first := Stream.sinkPorts "first" requestType
    second := Stream.sinkPorts "second" requestType
    output := Stream.sourcePorts "out" requestType }

private abbrev grantAOut : Port .output CoreDomain (BitVec 32) :=
  Port.bits .output 32 "grant_a_count"
private abbrev grantBOut : Port .output CoreDomain (BitVec 32) :=
  Port.bits .output 32 "grant_b_count"
private abbrev contentionOut : Port .output CoreDomain (BitVec 32) :=
  Port.bits .output 32 "contention_count"

private abbrev mergeComponent (roundRobin : Bool) : Component :=
  let turn : Reg 1 := ⟨"turn"⟩
  let grantACount : Reg 32 := ⟨"grant_a"⟩
  let grantBCount : Reg 32 := ⟨"grant_b"⟩
  let contentionCount : Reg 32 := ⟨"contention"⟩
  let requestA := mergePorts.first.valid.bitReg.rd
  let requestB := mergePorts.second.valid.bitReg.rd
  let (grantA, grantB, rotation) :=
    if roundRobin then
      let arbiter : Arbiter.TwoWayRoundRobin := ⟨turn⟩
      let result := arbiter.grants requestA requestB
      (result.grant0, result.grant1,
        arbiter.advance result mergePorts.output.ready.bitReg.rd)
    else
      (requestA, .and requestB (.not requestA), Act.skip)
  let transferA := .and grantA mergePorts.output.ready.bitReg.rd
  let transferB := .and grantB mergePorts.output.ready.bitReg.rd
  { name := if roundRobin then "TileRoundRobinArbiter" else "TileFixedArbiter"
    interface := ⟨mergePorts.first.decls ++ mergePorts.second.decls ++
        mergePorts.output.decls ++
        [grantAOut.decl, grantBOut.decl, contentionOut.decl]⟩
    design :=
        { name := if roundRobin then "tile_round_robin_arbiter" else
            "tile_fixed_arbiter"
          regs := [turn.decl 0, grantACount.decl 0, grantBCount.decl 0,
            contentionCount.decl 0]
          mems := []
          inputs := [mergePorts.first.valid.bitReg.input,
            mergePorts.first.payload.reg.input,
            mergePorts.second.valid.bitReg.input,
            mergePorts.second.payload.reg.input,
            mergePorts.output.ready.bitReg.input]
          rules :=
            [⟨"account", .seq rotation <|
                .seq (.ite transferA
                    (grantACount.set (.add grantACount.rd (.lit 1))) .skip) <|
                  .seq (.ite transferB
                      (grantBCount.set (.add grantBCount.rd (.lit 1))) .skip)
                    (.ite (.and requestA requestB)
                      (contentionCount.set (.add contentionCount.rd (.lit 1)))
                      .skip)⟩]
          outputs := []
          combOutputs :=
            [⟨mergePorts.first.ready.name, 1,
                .and mergePorts.output.ready.bitReg.rd grantA⟩,
             ⟨mergePorts.second.ready.name, 1,
                .and mergePorts.output.ready.bitReg.rd grantB⟩,
             ⟨mergePorts.output.valid.name, 1, .or grantA grantB⟩,
             ⟨mergePorts.output.payload.name, requestWidth,
                .mux grantA mergePorts.first.payload.reg.rd
                  mergePorts.second.payload.reg.rd⟩,
             ⟨grantAOut.name, 32, grantACount.rd⟩,
             ⟨grantBOut.name, 32, grantBCount.rd⟩,
             ⟨contentionOut.name, 32, contentionCount.rd⟩] } }

private abbrev roundRobinComponent : Component := mergeComponent true

private def roundRobinMerge : DomainComponent CoreDomain where
  implementation := DomainDesign.authored roundRobinComponent.design
  sealed :=
    { component := roundRobinComponent
      interfaceOk := by unfold roundRobinComponent mergeComponent; decide
      readsOk := by unfold roundRobinComponent mergeComponent; decide
      certified := CertifiedDesign.ofChecks
        (by unfold roundRobinComponent mergeComponent; decide)
        (by unfold roundRobinComponent mergeComponent; decide) }
  implementationEq := rfl
  domainOk := by decide

private abbrev endpointInput : Stream.SinkPorts CoreDomain RequestBits :=
  Stream.sinkPorts "in" requestType
private abbrev channelReadyPort : Port .input CoreDomain (BitVec 1) :=
  Port.bits .input 1 "channel_ready"
private abbrev endpointValidOut : Port .output CoreDomain (BitVec 1) :=
  Port.bits .output 1 "buffer_valid"
private abbrev endpointPayloadOut : Port .output CoreDomain RequestBits :=
  ⟨"buffer_payload", requestType⟩
private abbrev endpointSentOut : Port .output CoreDomain (BitVec 32) :=
  Port.bits .output 32 "sent_count"

private abbrev endpointComponent : Component :=
  let valid : Reg 1 := ⟨"valid"⟩
  let payload : Reg requestWidth := ⟨"payload"⟩
  let sent : Reg 32 := ⟨"sent"⟩
  let ready := .or (.not valid.rd) channelReadyPort.bitReg.rd
  { name := "TileRequestEndpoint"
    interface := ⟨endpointInput.decls ++ [channelReadyPort.decl,
        endpointValidOut.decl, endpointPayloadOut.decl, endpointSentOut.decl]⟩
    design :=
        { name := "tile_request_endpoint"
          regs := [valid.decl 0, payload.decl 0, sent.decl 0]
          mems := []
          inputs := [endpointInput.valid.bitReg.input,
            endpointInput.payload.reg.input, channelReadyPort.bitReg.input]
          rules :=
            [⟨"transfer", .seq
                (.ite (.and valid.rd channelReadyPort.bitReg.rd)
                  (sent.set (.add sent.rd (.lit 1))) .skip)
                (.ite ready
                  (.seq (valid.set endpointInput.valid.bitReg.rd)
                    (.ite endpointInput.valid.bitReg.rd
                      (payload.set endpointInput.payload.reg.rd) .skip)) .skip)⟩]
          outputs := []
          combOutputs :=
            [⟨endpointInput.ready.name, 1, ready⟩,
             ⟨endpointValidOut.name, 1, valid.rd⟩,
             ⟨endpointPayloadOut.name, requestWidth, payload.rd⟩,
             ⟨endpointSentOut.name, 32, sent.rd⟩] } }

private def endpoint : DomainComponent CoreDomain where
  implementation := DomainDesign.authored endpointComponent.design
  sealed :=
    { component := endpointComponent
      interfaceOk := by unfold endpointComponent; decide
      readsOk := by unfold endpointComponent; decide
      certified := CertifiedDesign.ofChecks
        (by unfold endpointComponent; decide)
        (by unfold endpointComponent; decide) }
  implementationEq := rfl
  domainOk := by decide

private structure Selection where
  depth : Nat
  selectedIndex : Nat
  flushable : Bool
  roundRobin : Bool
  deriving DecidableEq, BEq

private inductive TileService : Type → Type where
  | depth : TileService Nat
  | roundRobin : TileService Bool
  | flushable : TileService Bool
  | datapath : TileService Selection

private instance : ServiceCatalog TileService where
  name
    | .depth => "pipeline_depth"
    | .roundRobin => "arbitration_policy"
    | .flushable => "pipeline_flush_policy"
    | .datapath => "tile_datapath"
  matchKey
    | .depth, .depth => .same rfl
    | .roundRobin, .roundRobin => .same rfl
    | .flushable, .flushable => .same rfl
    | .datapath, .datapath => .same rfl
    | _, _ => .different
  matchKey_sound := by
    intro α β left right equal matched
    cases left <;> cases right <;> simp_all
  matchKey_refl := by intro α key; cases key <;> rfl

private abbrev configPlugin : Spec (κ := TileService) where
  name := "tile_configuration"
  providers :=
    [{ Value := Nat, name := "pipeline", key := .depth, requires := [],
       build := fun _ => .ok 3 },
     { Value := Bool, name := "arbiter", key := .roundRobin, requires := [],
       build := fun _ => .ok true },
     { Value := Bool, name := "flush", key := .flushable, requires := [],
       build := fun _ => .ok true }]

private abbrev datapathPlugin : Spec (κ := TileService) where
  name := "tile_datapath"
  providers :=
    [{ Value := Selection, name := "build", key := .datapath,
       requires := [Key.of .depth, Key.of .roundRobin, Key.of .flushable],
       build := fun requirements => do
         let depth ← requirements.getUnique? .depth
         let roundRobin ← requirements.getUnique? .roundRobin
         let flushable ← requirements.getUnique? .flushable
         if depth == 0 then throw "tile pipeline depth must be positive"
         let selectedIndex := depth / 2
         return ⟨depth, selectedIndex, flushable, roundRobin⟩ }]

private abbrev selected? : Except String Selection :=
  match Plugin.resolve? (κ := TileService) [configPlugin, datapathPlugin] with
  | .error message => .error message
  | .ok resolved => Plugin.Resolved.getUnique? resolved TileService.datapath

/-- The release profile is an ordinary small value. The evidence emitter
requires the plugin resolver to return this exact value before publishing
the corresponding artifact; keeping the value itself proof-free avoids
placing the plugin evaluator in the hardware theorem's reduction path. -/
private abbrev selection : Selection := ⟨3, 1, true, true⟩

def pluginSelectionMatches : Bool :=
  match selected? with
  | .ok resolved => resolved == selection
  | .error _ => false

private abbrev ordinaryPipelineComponent : Component :=
  Stream.registerSliceComponent (δ := CoreDomain) (α := RequestBits)
    "tile_pipeline_register" requestType

private def ordinaryPipeline : DomainComponent CoreDomain where
  implementation := DomainDesign.authored ordinaryPipelineComponent.design
  sealed :=
    { component := ordinaryPipelineComponent
      interfaceOk := by
        unfold ordinaryPipelineComponent Stream.registerSliceComponent
        decide
      readsOk := by
        unfold ordinaryPipelineComponent Stream.registerSliceComponent
        decide
      certified := CertifiedDesign.ofChecks
        (by unfold ordinaryPipelineComponent Stream.registerSliceComponent; decide)
        (by unfold ordinaryPipelineComponent Stream.registerSliceComponent; decide) }
  implementationEq := rfl
  domainOk := by decide

private abbrev flushablePipelineComponent : Component :=
  let ports := Pipeline.linkPorts (δ := CoreDomain) (α := RequestBits) requestType
  let flush := Pipeline.flushPort (δ := CoreDomain)
  let full : Reg 1 := ⟨"full"⟩
  let payload : Reg requestWidth := ⟨"payload"⟩
  let active := .not flush.bitReg.rd
  let canAccept := .and active (.or (.not full.rd) ports.output.ready.bitReg.rd)
  let outputValid := .and active full.rd
  let transfer := .ite canAccept
    (.seq (full.set ports.input.valid.bitReg.rd)
      (.ite ports.input.valid.bitReg.rd
        (payload.set ports.input.payload.reg.rd) .skip)) .skip
  { name := "tile_pipeline_flushable"
    interface := ⟨ports.input.decls ++ ports.output.decls ++ [flush.decl]⟩
    design :=
      { name := "tile_pipeline_flushable"
        regs := [full.decl 0, payload.decl 0]
        mems := []
        inputs := [ports.input.valid.bitReg.input, ports.input.payload.reg.input,
          ports.output.ready.bitReg.input, flush.bitReg.input]
        rules := [⟨"transfer_or_flush",
          .ite flush.bitReg.rd (full.set (.lit 0)) transfer⟩]
        outputs := []
        combOutputs :=
          [⟨ports.input.ready.name, 1, canAccept⟩,
           ⟨ports.output.valid.name, 1, outputValid⟩,
           ⟨ports.output.payload.name, requestWidth, payload.rd⟩] } }

private def flushablePipeline : DomainComponent CoreDomain where
  implementation := DomainDesign.authored flushablePipelineComponent.design
  sealed :=
    { component := flushablePipelineComponent
      interfaceOk := by unfold flushablePipelineComponent; decide
      readsOk := by unfold flushablePipelineComponent; decide
      certified := CertifiedDesign.ofChecks
        (by unfold flushablePipelineComponent; decide)
        (by unfold flushablePipelineComponent; decide) }
  implementationEq := rfl
  domainOk := by decide

@[simp] private theorem sourceA_component :
    sourceA.sealed.component = sourceAComponent := rfl
@[simp] private theorem sourceB_component :
    sourceB.sealed.component = sourceBComponent := rfl
@[simp] private theorem roundRobinMerge_component :
    roundRobinMerge.sealed.component = roundRobinComponent := rfl
@[simp] private theorem endpoint_component :
    endpoint.sealed.component = endpointComponent := rfl
@[simp] private theorem ordinaryPipeline_component :
    ordinaryPipeline.sealed.component = ordinaryPipelineComponent := rfl
@[simp] private theorem flushablePipeline_component :
    flushablePipeline.sealed.component = flushablePipelineComponent := rfl

private abbrev pipelineStages : List (DomainComponent CoreDomain) :=
  List.replicate selection.selectedIndex ordinaryPipeline ++
    [if selection.flushable then flushablePipeline else ordinaryPipeline] ++
    List.replicate (selection.depth - selection.selectedIndex - 1) ordinaryPipeline

private abbrev batch? : Except String (DomainComponentBatch CoreDomain) := do
  let sourceAInst : DomainComponentInstance CoreDomain := ⟨"source_a", sourceA⟩
  let sourceBInst : DomainComponentInstance CoreDomain := ⟨"source_b", sourceB⟩
  if !selection.roundRobin then
    throw "this tile profile requires round-robin arbitration"
  let mergeInst : DomainComponentInstance CoreDomain := ⟨"arbiter", roundRobinMerge⟩
  let pipeline0 : DomainComponentInstance CoreDomain :=
    ⟨"pipeline_0", ordinaryPipeline⟩
  let pipeline1 : DomainComponentInstance CoreDomain :=
    ⟨"pipeline_1", if selection.flushable then flushablePipeline else ordinaryPipeline⟩
  let pipeline2 : DomainComponentInstance CoreDomain :=
    ⟨"pipeline_2", ordinaryPipeline⟩
  let endpointInst : DomainComponentInstance CoreDomain :=
    ⟨"request_endpoint", endpoint⟩
  let mut batch := DomainComponentBatch.empty (δ := CoreDomain)
    "typed_soc_tile_core_graph"
  batch := batch.addInstance sourceAInst
  batch := batch.addInstance sourceBInst
  batch := batch.addInstance mergeInst
  batch := batch.addInstance pipeline0
  batch := batch.addInstance pipeline1
  batch := batch.addInstance pipeline2
  batch := batch.addInstance endpointInst
  let firstSource ← sourcePorts.resolve sourceAInst
  let secondSource ← sourcePorts.resolve sourceBInst
  let firstSink ← mergePorts.first.resolve mergeInst
  let secondSink ← mergePorts.second.resolve mergeInst
  batch ← Stream.connectBatch batch firstSource firstSink
  batch ← Stream.connectBatch batch secondSource secondSink
  let linkPorts := Pipeline.linkPorts (δ := CoreDomain) (α := RequestBits) requestType
  batch ← Stream.connectBatch batch (← mergePorts.output.resolve mergeInst)
    (← linkPorts.input.resolve pipeline0)
  batch ← Stream.connectBatch batch (← linkPorts.output.resolve pipeline0)
    (← linkPorts.input.resolve pipeline1)
  batch ← Stream.connectBatch batch (← linkPorts.output.resolve pipeline1)
    (← linkPorts.input.resolve pipeline2)
  batch ← Stream.connectBatch batch (← linkPorts.output.resolve pipeline2)
    (← endpointInput.resolve endpointInst)
  batch := batch.expose "source_a" sequenceOut.name
  batch := batch.expose "source_a" acceptedOut.name
  batch := batch.expose "source_a" sourceStallOut.name
  batch := batch.expose "source_b" sequenceOut.name
  batch := batch.expose "source_b" acceptedOut.name
  batch := batch.expose "source_b" sourceStallOut.name
  batch := batch.expose "arbiter" grantAOut.name
  batch := batch.expose "arbiter" grantBOut.name
  batch := batch.expose "arbiter" contentionOut.name
  batch := batch.expose "request_endpoint" endpointValidOut.name
  batch := batch.expose "request_endpoint" endpointPayloadOut.name
  batch := batch.expose "request_endpoint" endpointSentOut.name
  return batch

abbrev coreBatch : DomainComponentBatch CoreDomain :=
  (batch?.toOption).get (by
    simp [batch?, requestWidth, requestType, Request.make,
      sourceAComponent, sourceBComponent, sourceComponent,
      roundRobinComponent, mergeComponent,
      endpointComponent, ordinaryPipelineComponent,
      flushablePipelineComponent,
      sourcePorts, runLimitPort, producerHoldPort, sequenceOut, acceptedOut,
      sourceStallOut, grantAOut, grantBOut, contentionOut,
      endpointInput, channelReadyPort, endpointValidOut,
      endpointSentOut, Stream.sourcePorts, Stream.sinkPorts,
      Stream.SourcePorts.decls, Stream.SinkPorts.decls,
      Stream.registerSlicePorts, Stream.registerSliceComponent,
      Pipeline.linkPorts, Pipeline.flushPort,
      Port.bits, Port.decl, Port.bitReg, Port.reg,
      Stream.SourcePorts.resolve, Stream.SinkPorts.resolve,
      Stream.connectBatch, Connection.typed, DomainComponentInstance.output?,
      DomainComponentInstance.input?, DomainComponentInstance.erase,
      ComponentInterface.contains,
      Design.exportedRegs,
      ComponentInstance.output?,
      ComponentInstance.input?, ComponentInstance.outputExpr?, castExpr?,
      DomainComponentBatch.empty, DomainComponentBatch.addInstance,
      DomainComponentBatch.connect, DomainComponentBatch.expose]
    decide)

abbrev coreDomainGraph : DomainComponentGraph CoreDomain :=
  DomainComponentBatch.Expert.materialize coreBatch

private def coreTopologicalOrder : List String :=
  ["pipeline_2__out_payload", "request_endpoint__in_payload",
   "pipeline_2__out_valid", "request_endpoint__in_valid",
   "pipeline_1__out_payload", "pipeline_2__in_payload",
   "pipeline_0__out_payload", "pipeline_1__in_payload",
   "pipeline_0__out_valid", "pipeline_1__in_valid",
   "source_b__out_payload", "arbiter__second_payload",
   "source_a__out_payload", "arbiter__first_payload",
   "request_endpoint__channel_ready", "request_endpoint__in_ready",
   "pipeline_2__out_ready", "pipeline_2__in_ready",
   "pipeline_1__out_ready", "pipeline_1__flush", "pipeline_1__in_ready",
   "pipeline_0__out_ready", "pipeline_0__in_ready", "arbiter__out_ready",
   "pipeline_1__out_valid", "pipeline_2__in_valid",
   "source_b__run_limit", "source_b__producer_hold", "source_b__out_valid",
   "arbiter__second_valid", "source_a__run_limit", "source_a__producer_hold",
   "source_a__out_valid", "arbiter__first_valid", "arbiter__first_ready",
   "source_a__out_ready", "arbiter__second_ready", "source_b__out_ready",
   "arbiter__out_valid", "pipeline_0__in_valid", "arbiter__out_payload",
   "pipeline_0__in_payload"]

private def coreDependencyEdges : List (String × String) :=
  [("source_a__producer_hold", "source_a__out_valid"),
   ("source_a__run_limit", "source_a__out_valid"),
   ("source_b__producer_hold", "source_b__out_valid"),
   ("source_b__run_limit", "source_b__out_valid"),
   ("arbiter__out_ready", "arbiter__first_ready"),
   ("arbiter__first_valid", "arbiter__first_ready"),
   ("arbiter__second_valid", "arbiter__first_ready"),
   ("arbiter__out_ready", "arbiter__second_ready"),
   ("arbiter__second_valid", "arbiter__second_ready"),
   ("arbiter__first_valid", "arbiter__second_ready"),
   ("arbiter__first_valid", "arbiter__out_valid"),
   ("arbiter__second_valid", "arbiter__out_valid"),
   ("arbiter__first_valid", "arbiter__out_payload"),
   ("arbiter__second_valid", "arbiter__out_payload"),
   ("arbiter__first_payload", "arbiter__out_payload"),
   ("arbiter__second_payload", "arbiter__out_payload"),
   ("pipeline_0__out_ready", "pipeline_0__in_ready"),
   ("pipeline_1__flush", "pipeline_1__in_ready"),
   ("pipeline_1__out_ready", "pipeline_1__in_ready"),
   ("pipeline_1__flush", "pipeline_1__out_valid"),
   ("pipeline_2__out_ready", "pipeline_2__in_ready"),
   ("request_endpoint__channel_ready", "request_endpoint__in_ready"),
   ("source_a__out_valid", "arbiter__first_valid"),
   ("source_a__out_payload", "arbiter__first_payload"),
   ("arbiter__first_ready", "source_a__out_ready"),
   ("source_b__out_valid", "arbiter__second_valid"),
   ("source_b__out_payload", "arbiter__second_payload"),
   ("arbiter__second_ready", "source_b__out_ready"),
   ("arbiter__out_valid", "pipeline_0__in_valid"),
   ("arbiter__out_payload", "pipeline_0__in_payload"),
   ("pipeline_0__in_ready", "arbiter__out_ready"),
   ("pipeline_0__out_valid", "pipeline_1__in_valid"),
   ("pipeline_0__out_payload", "pipeline_1__in_payload"),
   ("pipeline_1__in_ready", "pipeline_0__out_ready"),
   ("pipeline_1__out_valid", "pipeline_2__in_valid"),
   ("pipeline_1__out_payload", "pipeline_2__in_payload"),
   ("pipeline_2__in_ready", "pipeline_1__out_ready"),
   ("pipeline_2__out_valid", "request_endpoint__in_valid"),
   ("pipeline_2__out_payload", "request_endpoint__in_payload"),
   ("request_endpoint__in_ready", "pipeline_2__out_ready")]

private theorem coreDependencyEdges_eq :
    coreDomainGraph.raw.dependencyEdges = coreDependencyEdges := by
  simp [coreDomainGraph, coreBatch, batch?, coreDependencyEdges,
    requestWidth, requestType, Request.make,
    sourceAComponent, sourceBComponent, sourceComponent,
    roundRobinComponent, mergeComponent, endpointComponent,
    ordinaryPipelineComponent, flushablePipelineComponent,
    sourcePorts, runLimitPort, producerHoldPort, sequenceOut, acceptedOut,
    sourceStallOut, grantAOut, grantBOut, contentionOut,
    endpointInput, channelReadyPort, endpointValidOut,
    endpointSentOut, Stream.sourcePorts, Stream.sinkPorts,
    Stream.SourcePorts.decls, Stream.SinkPorts.decls,
    Stream.registerSlicePorts, Stream.registerSliceComponent,
    Pipeline.linkPorts, Pipeline.flushPort, Port.bits, Port.decl,
    Port.bitReg, Port.reg, Stream.SourcePorts.resolve,
    Stream.SinkPorts.resolve, Stream.connectBatch, Connection.typed,
    DomainComponentInstance.output?, DomainComponentInstance.input?,
    DomainComponentInstance.erase, ComponentInterface.contains,
    Design.exportedRegs, ComponentInstance.output?, ComponentInstance.input?,
    ComponentInstance.outputExpr?, castExpr?, DomainComponentBatch.empty,
    DomainComponentBatch.addInstance, DomainComponentBatch.connect,
    DomainComponentBatch.expose, DomainComponentBatch.Expert.materialize,
    ComponentGraph.dependencyEdges, Component.combinationalDependencies]
  rfl

private theorem coreProposedOrder :
    ComponentGraph.proposeTopologicalOrder coreDomainGraph.raw.dependencyEdges =
      coreTopologicalOrder := by
  rw [coreDependencyEdges_eq]
  decide +kernel

private theorem coreTopology :
    ComponentGraph.topologicalOrderCheckB coreDomainGraph.raw.dependencyEdges
      coreTopologicalOrder = true := by
  rw [coreDependencyEdges_eq]
  decide +kernel

private def coreGraphCertificate :
    ComponentHierarchy.DomainCertificate coreDomainGraph where
  erased :=
    { nameValid := by decide
      pathsUnique := by decide
      connectionsValid := by decide
      exportBoundaryValid := by decide
      namespacesDisjoint := by decide
      order := coreTopologicalOrder
      order_eq := coreProposedOrder.symm
      topology := coreTopology }

abbrev coreGraph : ComponentHierarchy.CheckedBatch CoreDomain :=
  ⟨coreDomainGraph, coreGraphCertificate⟩

abbrev coreGraphDesign : Design := coreGraph.graph.raw.flatten

private def bothRequestChannelsReady : Expr 1 :=
  .and requestInternal.canEnq requestContract.canEnq

private def boundaryPayload : Expr requestWidth :=
  .reg requestWidth "request_endpoint__payload"

private def coreGraphConnected : Design :=
  coreGraphDesign.connect fun name width =>
    if _hName : name = "request_endpoint__channel_ready" then
      if hWidth : width = 1 then some (hWidth ▸ bothRequestChannelsReady)
      else none
    else none

private def requestBoundary : Design where
  name := "typed_soc_tile_request_boundary"
  regs := []
  mems := []
  inputs := []
  rules :=
    [⟨"broadcast_request", .ite
      (.and (.reg 1 "request_endpoint__valid") bothRequestChannelsReady)
      (.seq (requestInternal.enq boundaryPayload)
        (requestContract.enq boundaryPayload)) .skip⟩]
  outputs := []

abbrev coreBody : Design :=
  { coreGraphConnected.par requestBoundary with
    name := "typed_soc_tile_core"
    outputs := coreGraphConnected.outputs ++
      ["pipeline_0__full", "pipeline_1__full", "pipeline_2__full",
       "source_a__sequence", "source_a__accepted", "source_a__stalls",
       "source_b__sequence", "source_b__accepted", "source_b__stalls",
       "arbiter__grant_a", "arbiter__grant_b", "arbiter__contention",
       "request_endpoint__valid", "request_endpoint__payload",
       "request_endpoint__sent"] }

/-! ## Two identical logical memory services -/

private abbrev memoryBody (lane : String) (requests : Chan requestWidth)
    (responses : Chan responseWidth) : Design :=
  let memory : Mem 9 32 := ⟨lane ++ "_memory"⟩
  let requestReg : Reg requestWidth := ⟨"request"⟩
  let readData : Reg 32 := ⟨"read_data"⟩
  let pending : Reg 1 := ⟨"pending"⟩
  let commits : Reg 32 := ⟨"commits"⟩
  let requestStalls : Reg 32 := ⟨"request_stalls"⟩
  let responseStalls : Reg 32 := ⟨"response_stalls"⟩
  let merged := maskedWord readData.rd (Request.data requestReg.rd)
    (Request.mask requestReg.rd)
  let result := .mux (Request.write requestReg.rd) merged readData.rd
  { name := "typed_soc_tile_memory_" ++ lane
    regs := [requestReg.decl 0, readData.decl 0, pending.decl 0,
      commits.decl 0, requestStalls.decl 0, responseStalls.decl 0]
    mems := [memory.decl]
    inputs := [⟨"memory_hold", 1⟩]
    rules :=
      [⟨"service", .ite (.not (.reg 1 "memory_hold"))
        (.ite pending.rd
          (.ite responses.canEnq
            (.seq (.ite (Request.write requestReg.rd)
                (memory.write 0 (Request.memoryAddress requestReg.rd) merged) .skip)
              (.seq (responses.enq (Response.make requestReg.rd result))
                (.seq (pending.set (.lit 0))
                  (commits.set (.add commits.rd (.lit 1))))))
            (responseStalls.set (.add responseStalls.rd (.lit 1))))
          (.ite requests.canDeq
            (.seq (requestReg.set requests.deq)
              (.seq (readData.set (memory.rd (Request.memoryAddress requests.deq)))
                (.seq (pending.set (.lit 1)) requests.pop)))
            (requestStalls.set (.add requestStalls.rd (.lit 1))))) .skip⟩]
    outputs := ["pending", "commits", "request_stalls", "response_stalls"]
    syncReadMems := [memory.name] }

abbrev internalMemoryBody : Design :=
  memoryBody "internal" requestInternal responseInternal
abbrev contractMemoryBody : Design :=
  memoryBody "contract" requestContract responseContract

abbrev coreIsland : IslandHandle := .named "tile_core" coreBody coreClock
abbrev internalMemoryIsland : IslandHandle :=
  .named "tile_memory_internal" internalMemoryBody memoryClock
abbrev contractMemoryIsland : IslandHandle :=
  .named "tile_memory_contract" contractMemoryBody memoryClock

abbrev requestInternalRoute :=
  requestInternal.between coreIsland internalMemoryIsland
abbrev requestContractRoute :=
  requestContract.between coreIsland contractMemoryIsland

/-! ## Sibling checker and ledger fragment -/

private def shadowMemory : Mem 9 32 := ⟨"shadow_memory"⟩

private def expectedSequence (client : Expr 1) : Expr 20 :=
  .mux client (.reg 20 "expected_b") (.reg 20 "expected_a")

private def checkerConsume : Act :=
  let left := responseInternal.deq
  let right := responseContract.deq
  let client := Response.client left
  let sequence := Response.sequence left
  let expected := expectedSequence client
  let nextExpected := .add expected (.lit 1)
  let normal := .eq sequence expected
  let oneGap := .and (.eq sequence nextExpected)
    (.not (.reg 1 "flush_gap_seen"))
  let address : Expr 9 := Expr.concat client (Response.address left)
  let old := shadowMemory.rd address
  let data := .xor (.zext sequence 32)
    (.mux client (.lit 0x2468ace0) (.lit 0x13579bdf))
  let mask := .slice (.zext sequence 32) 0 4
  let expectedWrite := .slice (.zext sequence 32) 8 1
  let updated := maskedWord old data mask
  let expectedResult := .mux expectedWrite updated old
  let mismatch := .or (.not (.eq left right)) <|
    .or (.not (.or normal oneGap)) <|
    .or (.not (.eq (Response.address left) (.slice (.zext sequence 32) 0 8))) <|
    .or (.not (.eq (Response.write left) expectedWrite))
      (.not (.eq (Response.result left) expectedResult))
  .seq (.ite mismatch (.write 1 "sticky_error" (.lit 1)) .skip) <|
    .seq (.ite oneGap
      (.seq (.write 1 "flush_gap_seen" (.lit 1)) <|
        .seq (.write 1 "discarded_client" client) <|
        .seq (.write 20 "discarded_sequence" expected) <|
          .write 32 "discarded"
            (.add (.reg 32 "discarded") (.lit 1))) .skip) <|
    .seq (.ite expectedWrite
      (shadowMemory.write 0 address expectedResult) .skip) <|
    .seq (.ite client
      (.write 20 "expected_b" (.add sequence (.lit 1)))
      (.write 20 "expected_a" (.add sequence (.lit 1)))) <|
    .seq (.write 32 "digest"
      (.xor (.reg 32 "digest")
        (.xor (Response.result left) (.zext sequence 32)))) <|
    .seq (.write 32 "records" (.add (.reg 32 "records") (.lit 1))) <|
      .seq responseInternal.pop responseContract.pop

abbrev monitorBody : Design where
  name := "typed_soc_tile_monitor"
  regs := [⟨"expected_a", 20, 0⟩, ⟨"expected_b", 20, 0⟩,
    ⟨"records", 32, 0⟩, ⟨"discarded", 32, 0⟩, ⟨"digest", 32, 0⟩,
    ⟨"discarded_client", 1, 0⟩, ⟨"discarded_sequence", 20, 0⟩,
    ⟨"flush_gap_seen", 1, 0⟩, ⟨"sticky_error", 1, 0⟩,
    ⟨"pair_skew_ticks", 32, 0⟩, ⟨"response_hold_ticks", 32, 0⟩]
  mems := [shadowMemory.decl]
  inputs := [⟨"response_hold", 1⟩]
  rules :=
    [⟨"pair_skew", .ite
      (.xor responseInternal.canDeq responseContract.canDeq)
      (.write 32 "pair_skew_ticks"
        (.add (.reg 32 "pair_skew_ticks") (.lit 1))) .skip⟩,
     ⟨"hold_account", .ite (.reg 1 "response_hold")
      (.write 32 "response_hold_ticks"
        (.add (.reg 32 "response_hold_ticks") (.lit 1))) .skip⟩,
     ⟨"compare", .ite
      (.and (.not (.reg 1 "response_hold"))
        (.and responseInternal.canDeq responseContract.canDeq))
      checkerConsume .skip⟩]
  outputs := ["expected_a", "expected_b", "records", "discarded", "digest",
    "discarded_client", "discarded_sequence", "flush_gap_seen", "sticky_error",
    "pair_skew_ticks", "response_hold_ticks"]

abbrev monitorIsland : IslandHandle := .named "tile_monitor" monitorBody coreClock

/-! ## Reusable fragments and final parent -/

structure TileInterface (system : System) where
  internalResponse : DeclaredSource system responseInternal
  contractResponse : DeclaredSource system responseContract

abbrev tileBuilder : SystemBuilder :=
  System.empty
    |>.addErasedIsland coreIsland
    |>.addErasedIsland internalMemoryIsland
    |>.addErasedIsland contractMemoryIsland
    |>.addChannel requestInternalRoute
    |>.addChannel requestContractRoute
    |>.exportSource (responseInternal.exportSource internalMemoryIsland)
    |>.exportSource (responseContract.exportSource contractMemoryIsland)
    |>.withClockRel .asynchronous

private def declaredSource? (system : System) {width : Nat}
    (channel : Chan width) (owner : IslandHandle) :
    Except String (DeclaredSource system channel) :=
  if declared : system.openSources.any (fun endpoint =>
      System.openEndpointMatches endpoint channel owner.name) = true then
    pure { owner, declared }
  else
    throw s!"channel {channel.name}: assembled fragment lost its declared source endpoint"

/-- Assemble and certify the reusable tile fragment without asking the kernel
to normalize the large flattened component graph. `assemble` still executes
the exact fail-closed structural gate; the successful dependent branch carries
that proof into `System`, and the remaining compiler/realization checks are
likewise converted to certificates only in their `true` branches. -/
def buildTileFragment :
    Except String (System.SystemFragment TileInterface (fun _ _ => Unit)) := do
  let system ← tileBuilder.assemble
  let internalResponse ← declaredSource? system responseInternal internalMemoryIsland
  let contractResponse ← declaredSource? system responseContract contractMemoryIsland
  if islandsReady : system.islandsCheck = true then
    let block : System.SealedBlock TileInterface (fun _ _ => Unit) :=
      { system
        islands := system.certifyIslands islandsReady
        interface := { internalResponse, contractResponse }
        theorems := () }
    let plan : RealizationPlan := .portable
    if realizationReady : System.realizationCheck system plan = true then
      pure { block, plan, realizationReady }
    else
      throw (system.selectedReadinessReport plan)
  else
    throw (String.intercalate "\n"
      ((system.selectedReadinessIssues .portable).map fun issue =>
        issue.subject ++ ": " ++ issue.detail))

structure MonitorInterface (system : System) where
  internalResponse : DeclaredSink system responseInternal
  contractResponse : DeclaredSink system responseContract

abbrev monitorBuilder : SystemBuilder :=
  System.empty
    |>.addErasedIsland monitorIsland
    |>.exportSink (responseInternal.exportSink monitorIsland)
    |>.exportSink (responseContract.exportSink monitorIsland)
    |>.withClockRel .asynchronous

abbrev monitorSystem : System := monitorBuilder.certify (by decide)

abbrev monitorInterface : MonitorInterface monitorSystem :=
  { internalResponse := { owner := monitorIsland, declared := by decide }
    contractResponse := { owner := monitorIsland, declared := by decide } }

abbrev monitorBlock : System.SealedBlock MonitorInterface (fun _ _ => Unit) where
  system := monitorSystem
  islands := monitorSystem.certifyIslands (by decide)
  interface := monitorInterface
  theorems := ()

abbrev monitorFragment : System.SystemFragment MonitorInterface (fun _ _ => Unit) where
  block := monitorBlock
  plan := .portable
  realizationReady := by decide

abbrev BuiltTile := System.BuiltSystem

private def closeFragments
    (tileFragment : System.SystemFragment TileInterface (fun _ _ => Unit)) :
    Except String BuiltTile :=
  let tileInterface := System.SystemFragment.interface tileFragment
  let parentBuilder : SystemBuilder := System.empty
    |>.includeFragment tileFragment
    |>.includeFragment monitorFragment
    |>.connectDeclaredExports (TileInterface.internalResponse tileInterface)
      monitorInterface.internalResponse
    |>.connectDeclaredExports (TileInterface.contractResponse tileInterface)
      monitorInterface.contractResponse
    |>.withClockRel .asynchronous
  let plan : RealizationPlan := RealizationPlan.portable
    |>.includeFragment tileFragment
    |>.includeFragment monitorFragment
  let islandInventory : System.CertifiedIslands.Inventory parentBuilder.islands := by
    simpa [parentBuilder] using
      System.CertifiedIslands.includeFragment
        (System.CertifiedIslands.includeFragment
          (builder := System.empty) .empty tileFragment)
        monitorFragment
  match parentBuilder.buildWithCertifiedIslands islandInventory plan with
  | .error message => .error message
  | .ok built =>
          if (System.islands built.system).map (·.name) !=
              ["tile_core", "tile_memory_internal", "tile_memory_contract",
                "tile_monitor"] then
            .error "typed SoC tile parent island inventory changed"
          else if (System.connections built.system).map (·.chan.name) !=
              [requestInternal.name, requestContract.name,
                responseInternal.name, responseContract.name] then
            .error "typed SoC tile parent channel inventory changed"
          else if !(System.openSources built.system).isEmpty ||
              !(System.openSinks built.system).isEmpty then
            .error "typed SoC tile parent retained an open endpoint"
          else
            .ok built

/-- Exact end-to-end construction path used by simulation and emission.  It
retains both typed fragments until their declared endpoints are connected,
assembles the closed parent, then returns the dependent certified application.
No unchecked fallback artifact exists. -/
def buildCertifiedArtifact : Except String BuiltTile :=
  buildTileFragment.bind closeFragments

example : coreGraph.graph.instances.length = 7 := by decide
example : coreGraph.graph.connectionCount = 18 := by decide

end Machines.Multiclock.TypedSoCTile
