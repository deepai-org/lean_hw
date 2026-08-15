-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Multiclock

/-! # Typed component hierarchy regressions -/

namespace Tests.Component

open Loom.Hw

private inductive CoreClock
private inductive PeripheralClock

private instance : ClockDomain CoreClock where name := "core"
private instance : ClockDomain PeripheralClock where name := "peripheral"

private def producerOutput : Port .output CoreClock (BitVec 8) :=
  Port.bits .output 8 "data"

private def consumerInput : Port .input CoreClock (BitVec 8) :=
  Port.bits .input 8 "incoming"

private def consumerOutput : Port .output CoreClock (BitVec 8) :=
  Port.bits .output 8 "accepted"

private def wrongClockInput : Port .input PeripheralClock (BitVec 8) :=
  Port.bits .input 8 "incoming"

private def producerDesign : Design where
  name := "producer"
  regs := [producerOutput.reg.decl 37]
  mems := []
  rules := []
  outputs := [producerOutput.name]

private def consumerDesign : Design where
  name := "consumer"
  regs := [consumerOutput.reg.decl 0]
  mems := []
  inputs := [consumerInput.reg.input]
  rules := [⟨"accept", .write 8 consumerOutput.name consumerInput.reg.rd⟩]
  outputs := [consumerOutput.name]

private def producer : Component where
  name := "Producer"
  interface := ⟨[producerOutput.decl]⟩
  design := producerDesign

private def consumer : Component where
  name := "Consumer"
  interface := ⟨[consumerInput.decl, consumerOutput.decl]⟩
  design := consumerDesign

#guard producer.interfaceOkB
#guard consumer.interfaceOkB

/- The graph is assembled entirely through the checked API. -/
private def assembled : Except String Design := do
  let producerComponent ← producer.seal?
  let consumerComponent ← consumer.seal?
  let producerInstance : ComponentInstance := ⟨"produce", producerComponent⟩
  let consumerInstance : ComponentInstance := ⟨"consume", consumerComponent⟩
  let source ← producerInstance.output? producerOutput
  let sink ← consumerInstance.input? consumerInput
  let connection ← Connection.typed source sink
  let graph ← (ComponentGraph.empty "typed_top").addInstance producerInstance
  let graph ← graph.addInstance consumerInstance
  let graph ← graph.connect connection
  let graph ← graph.expose "consume" "accepted"
  graph.flatten?

#guard match assembled with
  | .error _ => false
  | .ok design =>
      design.inputs.isEmpty &&
      design.outputs == ["consume__accepted"] &&
      !(design.outputs.contains "produce__data") &&
      design.readsOkB && Compile.designWFCheck design

#guard match assembled with
  | .error _ => false
  | .ok design =>
      (design.cycle design.reset).regs "consume__accepted" 8 == 37

/- The ordinary hierarchy path retains `CoreClock` through flattening and
island placement; the erased Design appears only in the final System record. -/
private def domainIsland : Except String SystemIsland := do
  let producerSealed ← producer.seal?
  let consumerSealed ← consumer.seal?
  let producerComponent ← DomainComponent.check? (δ := CoreClock) producerSealed
  let consumerComponent ← DomainComponent.check? (δ := CoreClock) consumerSealed
  let p : DomainComponentInstance CoreClock := ⟨"produce", producerComponent⟩
  let c : DomainComponentInstance CoreClock := ⟨"consume", consumerComponent⟩
  let source ← p.output? producerOutput
  let sink ← c.input? consumerInput
  let connection ← Connection.typed source sink
  let graph := DomainComponentGraph.empty (δ := CoreClock) "typed_domain_top"
  let graph ← graph.addInstance p
  let graph ← graph.addInstance c
  let graph ← graph.connect connection
  let graph ← graph.expose "consume" "accepted"
  let design ← graph.flatten?
  let island : DomainIslandHandle CoreClock := .named "core" design
  return island.toSystemIsland

#guard match domainIsland with
  | .error _ => false
  | .ok island => island.clock == "core" && island.design.name == "typed_domain_top"

/- An erased/dynamic graph cannot bypass the same-domain check: the port's
domain name remains part of exact interface membership.  Ordinary typed code
is stronger—the call to `Connection.typed` cannot even be formed because the
phantom domain types differ. -/
#guard match do
    let consumerComponent ← consumer.seal?
    let inst : ComponentInstance := ⟨"consume", consumerComponent⟩
    inst.input? wrongClockInput with
  | .error _ => true
  | .ok _ => false

/- Duplicate drivers are rejected at the second connection rather than left
to source order. -/
#guard match do
    let producerComponent ← producer.seal?
    let consumerComponent ← consumer.seal?
    let p : ComponentInstance := ⟨"p", producerComponent⟩
    let c : ComponentInstance := ⟨"c", consumerComponent⟩
    let source ← p.output? producerOutput
    let sink ← c.input? consumerInput
    let connection ← Connection.typed source sink
    let graph ← (ComponentGraph.empty "duplicate").addInstance p
    let graph ← graph.addInstance c
    let graph ← graph.connect connection
    graph.connect connection with
  | .error _ => true
  | .ok _ => false

end Tests.Component
