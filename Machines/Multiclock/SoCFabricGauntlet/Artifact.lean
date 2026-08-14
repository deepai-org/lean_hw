-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Certification

namespace Machines.Multiclock.SoCFabricGauntlet

open Loom.Hw

private def syncBinding (connection : SystemConnection)
    (positive : 0 < connection.chan.depth)
    (compiler : Compile.designWFCheck connection.chan.physicalAdapter = true)
    (fast : connection.chan.physicalAdapter.fastWFB = true) :
    System.CertifiedSyncBinding where
  connection := connection
  positiveDepth := positive
  adapter := .ofChecks compiler fast

private def portableBinding (connection : SystemConnection)
    (depthAtLeastTwo : 2 ≤ connection.chan.depth)
    (powerOfTwo : 2 ^ Nat.log2 connection.chan.depth = connection.chan.depth)
    (sourceCompiler : Compile.designWFCheck
      (Cdc.AsyncFifoDesign.sourceControl
        (System.CertifiedPortable.fifoParameters connection
          depthAtLeastTwo powerOfTwo)) = true)
    (sourceFast : (Cdc.AsyncFifoDesign.sourceControl
      (System.CertifiedPortable.fifoParameters connection
        depthAtLeastTwo powerOfTwo)).fastWFB = true)
    (sinkCompiler : Compile.designWFCheck
      (Cdc.AsyncFifoDesign.sinkControl
        (System.CertifiedPortable.fifoParameters connection
          depthAtLeastTwo powerOfTwo)) = true)
    (sinkFast : (Cdc.AsyncFifoDesign.sinkControl
      (System.CertifiedPortable.fifoParameters connection
        depthAtLeastTwo powerOfTwo)).fastWFB = true)
    (storageReady : Cdc.AsyncQueueStorage.Portable.compilerReady
      (System.CertifiedPortable.storageShape connection depthAtLeastTwo)) :
    System.CertifiedPortableBinding where
  connection := connection
  depthAtLeastTwo := depthAtLeastTwo
  powerOfTwo := powerOfTwo
  controls := Cdc.AsyncFifoDesign.certify _ sourceCompiler sourceFast
    sinkCompiler sinkFast
  storage := Cdc.AsyncQueueStorage.Portable.certify _ storageReady

def cpuRequestBinding : System.CertifiedSyncBinding :=
  syncBinding cpuRequestConnection (by decide) (by decide) (by decide)

def cpuResponseBinding : System.CertifiedSyncBinding :=
  syncBinding cpuResponseConnection (by decide) (by decide) (by decide)

def dmaRequestBinding : System.CertifiedPortableBinding :=
  portableBinding dmaRequestConnection (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by
      unfold Cdc.AsyncQueueStorage.Portable.compilerReady
      constructor; · decide
      constructor; · decide
      constructor <;> decide)

def dmaResponseBinding : System.CertifiedPortableBinding :=
  portableBinding dmaResponseConnection (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by
      unfold Cdc.AsyncQueueStorage.Portable.compilerReady
      constructor; · decide
      constructor; · decide
      constructor <;> decide)

def targetRequestBinding : System.CertifiedPortableBinding :=
  portableBinding targetRequestConnection (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by
      unfold Cdc.AsyncQueueStorage.Portable.compilerReady
      constructor; · decide
      constructor; · decide
      constructor <;> decide)

def targetResponseBinding : System.CertifiedPortableBinding :=
  portableBinding targetResponseConnection (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by
      unfold Cdc.AsyncQueueStorage.Portable.compilerReady
      constructor; · decide
      constructor; · decide
      constructor <;> decide)

def auditBinding : System.CertifiedPortableBinding :=
  portableBinding auditConnection (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by
      unfold Cdc.AsyncQueueStorage.Portable.compilerReady
      constructor; · decide
      constructor; · decide
      constructor <;> decide)

/-- The canonical mixed realization: same-clock FIFO on CPU/fabric routes and
portable Gray FIFOs on every unrelated-clock route, in inventory order. -/
def certifiedArtifact : System.CertifiedRealizedSystem system certified where
  bindings := [
    .synchronous cpuRequestBinding,
    .synchronous cpuResponseBinding,
    .portable dmaRequestBinding,
    .portable dmaResponseBinding,
    .portable targetRequestBinding,
    .portable targetResponseBinding,
    .portable auditBinding]
  coverage := by decide
  clockRules := by decide
  resetCompatibility := by decide

theorem artifactBytes : certifiedArtifact.renderedUTF8 =
    certifiedArtifact.renderedVerilog.toUTF8 :=
  certifiedArtifact.renderedUTF8_eq

theorem exactRealizationChoices :
    certifiedArtifact.bindings.map (fun binding =>
      match binding with
      | .synchronous _ => "synchronous"
      | .portable _ => "asynchronous"
      | .recoveryPortable _ => "recovery") =
    ["synchronous", "synchronous", "asynchronous", "asynchronous",
      "asynchronous", "asynchronous", "asynchronous"] := by
  rfl

end Machines.Multiclock.SoCFabricGauntlet
