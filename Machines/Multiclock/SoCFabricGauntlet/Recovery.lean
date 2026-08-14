-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Dsl
import Machines.Multiclock.SoCFabricGauntlet.Design

/-!
# SoC Fabric Gauntlet graceful-recovery realization

The coordinated-reset artifact remains the canonical production/evidence
artifact.  This second realization keeps the exact same application islands,
typed channel inventory, directions, widths, and depths, but selects Loom's
loss-explicit independent-flush contract and recovery-capable implementation
for every route.  The pretty `system` declaration is intentionally the source
of the topology and realization choice for this experiment.
-/

namespace Machines.Multiclock.SoCFabricGauntlet.Recovery

open Loom.Hw
open Loom.Hw.Dsl
open Machines.Multiclock.SoCFabricGauntlet

system recoveryFabric where
  clock cpu_fabric_clk
  clock dma_clk
  clock mem_clk
  clock mon_clk
  clocks Clock.asynchronous
  reset Reset.independentFlush

  channel cpu_request : Request depth 2
  channel cpu_response : Response depth 2
  channel dma_request : Request depth 4
  channel dma_response : Response depth 4
  channel target_request : Request depth 4
  channel target_response : Response depth 4
  channel audit : CommitRecord depth 4

  island cpu on cpu_fabric_clk :=
    clientBody "soc_fabric_cpu" 0#1 cpu_request cpu_response
  island dma on dma_clk :=
    clientBody "soc_fabric_dma" 1#1 dma_request dma_response
  island fabric on cpu_fabric_clk :=
    Machines.Multiclock.SoCFabricGauntlet.fabricBody
  island service on mem_clk :=
    Machines.Multiclock.SoCFabricGauntlet.serviceBody
  island monitor on mon_clk :=
    Machines.Multiclock.SoCFabricGauntlet.monitorBody

  connect cpu_request from cpu to fabric
  connect cpu_response from fabric to cpu
  connect dma_request from dma to fabric
  connect dma_response from fabric to dma
  connect target_request from fabric to service
  connect target_response from service to fabric
  connect audit from service to monitor

  realize cpu_request, cpu_response, dma_request, dma_response,
    target_request, target_response, audit with Cdc.recoverableGrayFifo

/-- The pretty source owns the recovery topology and selects the closed stock
recovery profile for every route. -/
example : recoveryFabric.connections.map (·.key) =
    SoCFabricGauntlet.system.connections.map (·.key) := by decide
example : recoveryFabric.resetPolicy = .independentFlush := by rfl
example : recoveryFabric.application.artifact.bindings.length = 7 := by
  decide
example : recoveryFabric.application.artifact.bindings.all
    System.CertifiedChannelBinding.recoveryCapable := by
  decide

end Machines.Multiclock.SoCFabricGauntlet.Recovery
