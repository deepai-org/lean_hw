-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.ClockGauntlet.Proofs
import Machines.Multiclock.ClockGauntlet.Certification
import Loom.Hw.CertifiedSystemArtifact

namespace Machines.Multiclock.ClockGauntlet

open Loom.Hw

private def storageShape : Cdc.AsyncQueueStorage.Portable.Shape :=
  System.CertifiedPortable.storageShape firstConnection (by decide)

private theorem storageDesigns_ready :
    Cdc.AsyncQueueStorage.Portable.compilerReady storageShape := by
  unfold Cdc.AsyncQueueStorage.Portable.compilerReady
  constructor
  · decide
  constructor
  · decide
  constructor <;> decide

def compiledStorage : Cdc.AsyncQueueStorage.Portable.CertifiedDesigns storageShape :=
  Cdc.AsyncQueueStorage.Portable.certify storageShape storageDesigns_ready

def compiledControls : Cdc.AsyncFifoDesign.Controls fifoParameters :=
  Cdc.AsyncFifoDesign.certify fifoParameters
    (by decide) (by decide) (by decide) (by decide)

def firstBinding : System.CertifiedPortableBinding where
  connection := firstConnection
  depthAtLeastTwo := by decide
  powerOfTwo := by decide
  controls := compiledControls
  storage := compiledStorage

def secondBinding : System.CertifiedPortableBinding where
  connection := secondConnection
  depthAtLeastTwo := by decide
  powerOfTwo := by decide
  controls := compiledControls
  storage := by simpa [storageShape, firstConnection, secondConnection] using compiledStorage

/-- Exact compiler-only physical artifact.  The two crossing bindings are in
the same order as the checked connection inventory. -/
def certifiedArtifact : System.CertifiedRealizedSystem system certified where
  bindings := [.portable firstBinding, .portable secondBinding]
  coverage := by decide
  clockRules := by decide
  resetCompatibility := by decide

theorem certifiedArtifact_bytes :
    certifiedArtifact.renderedUTF8 = certifiedArtifact.renderedVerilog.toUTF8 :=
  certifiedArtifact.renderedUTF8_eq

/-- Publication-facing binding of arbitrary-schedule end-to-end safety to the
exact UTF-8 bytes carried by the certified artifact. -/
theorem certifiedArtifact_end_to_end (events : List NamedClockEvent) :
    certifiedArtifact.renderedUTF8 = certifiedArtifact.renderedVerilog.toUTF8 ∧
      TraceContract.mapPrefix transformValue
        (acceptedInputTrace events) (deliveredOutputTrace events) :=
  ⟨certifiedArtifact_bytes, end_to_end_contract events⟩

end Machines.Multiclock.ClockGauntlet
