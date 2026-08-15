-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SurfaceMatrix.Design
import Evidence.Targets.AsyncQueueStorage

/-!
# Minimal registered-BRAM multiclock qualification artifact

This keeps one ordinary width-32/depth-4 logical channel and substitutes only
its portable storage binding with an inferred Xilinx 7-series registered block
RAM leaf. The logical `System` and certified channel refinement are unchanged;
the target leaf's exact external contract assumption remains visible.
-/

namespace Machines.Multiclock.SurfaceMatrix.RegisteredBram

open Loom.Hw
open Machines.Multiclock.SurfaceMatrix
open Loom.Evidence.Targets.AsyncQueueStorage

def spec : LaneSpec := ⟨4, .ordinary, by decide, by decide⟩

def builder : SystemBuilder :=
  System.empty
    |>.addErasedIsland (producerIsland spec)
    |>.addErasedIsland (sinkIsland spec)
    |>.addChannel (route spec)
    |>.withClockRel .asynchronous

def system : System := builder.certify (by decide)
def application : System.Application system := system.realizePortable (by decide)

def connection : SystemConnection := (route spec).toSystemConnection

def portableBinding : System.CertifiedPortableBinding :=
  System.portableBindingFromCheck (system := system) connection (by decide)

def parameters : Cdc.AsyncQueueStorage.Parameters :=
  (System.CertifiedPortable.storageShape portableBinding.connection
    portableBinding.depthAtLeastTwo).parameters

def registeredBinding : System.CertifiedRegisteredStorageBinding where
  base := portableBinding
  leaf := xilinx7InferredBramLeaf parameters "surface_ordinary_d4"
  registered := rfl

def overlay : System.CertifiedBindingOverlay application.artifact.bindings where
  replacements := [.registeredStorage registeredBinding]
  distinct := by decide
  covered := by decide

def certifiedArtifact : System.CertifiedRealizedSystem system application.certified :=
  application.artifact.withOverlay overlay (by decide) (by decide)

example : certifiedArtifact.realized.system = application.artifact.realized.system := rfl
example : certifiedArtifact.realized.artifacts.externalAssumptions.length = 1 := by decide
example : parameters.width = 32 := rfl
example : parameters.depth = 4 := rfl
example : parameters.readLatency = 1 := rfl

end Machines.Multiclock.SurfaceMatrix.RegisteredBram
