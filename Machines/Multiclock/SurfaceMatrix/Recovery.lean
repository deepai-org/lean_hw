-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SurfaceMatrix.Design

/-!
# Recovery qualification for a generalized/full-rate lane

This companion artifact selects the independent-flush realization for the
depth-eight, full-rate surface.  The board campaign requests recovery of both
endpoint islands under load, holds the level through acknowledgement, and then
requires a clean checked epoch without applying common reset.
-/

namespace Machines.Multiclock.SurfaceMatrix.Recovery

open Loom.Hw
open Machines.Multiclock.SurfaceMatrix

def spec : LaneSpec := ⟨8, .fullRate, by decide, by decide⟩

def sourceIsland : IslandHandle := producerIsland spec
def destinationIsland : IslandHandle := sinkIsland spec
def recoveryRoute := spec.channel.between sourceIsland destinationIsland

def builder : SystemBuilder :=
  System.empty
    |>.addErasedIsland sourceIsland
    |>.addErasedIsland destinationIsland
    |>.addFullRateChannel recoveryRoute
    |>.withClockRel .asynchronous
    |>.withIndependentReset

def system : System := builder.certify (by decide)

def application : System.Application system :=
  system.realizeWith RealizationPlan.recoveryPortable (by decide)

def certifiedArtifact :
    System.CertifiedRealizedSystem system application.certified :=
  application.artifact

example : system.resetPolicy = .independentFlush := by decide
example : certifiedArtifact.bindings.all
    System.CertifiedChannelBinding.recoveryCapable := by decide

end Machines.Multiclock.SurfaceMatrix.Recovery
