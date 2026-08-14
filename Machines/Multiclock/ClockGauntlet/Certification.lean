-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.ClockGauntlet.Design
import Loom.Hw.CertifiedSystem
import Loom.Hw.AsyncFifoDesign

namespace Machines.Multiclock.ClockGauntlet

open Loom.Hw

def sourceCertificate : CertifiedDesign source := .ofChecks (by decide) (by decide)
def transformCertificate : CertifiedDesign transform := .ofChecks (by decide) (by decide)
def checkerCertificate : CertifiedDesign checker := .ofChecks (by decide) (by decide)

def fifoParameters : Cdc.AsyncFifoDesign.Parameters :=
  { width := 32, depth := 2, depthAtLeastTwo := by decide,
    powerOfTwo := by decide }

private def sourceIsland : SystemIsland := ⟨"source", "source_clk", source⟩
private def transformIsland : SystemIsland :=
  ⟨"transform", "transform_clk", transform⟩
private def checkerIsland : SystemIsland := ⟨"checker", "checker_clk", checker⟩

def certified : CertifiedSystem system where
  channelCertificate := by
    intro connection member
    by_cases firstName : connection.chan.name = sourceToTransform.name
    · have first : connection = firstConnection := by
        simp [system, builder, System.empty, SystemBuilder.island,
          SystemBuilder.connect, SystemBuilder.withClockRel,
          System.connections_certify] at member
        rcases member with first | second
        · exact first
        · subst connection
          simp [sourceToTransform, transformToChecker] at firstName
      subst connection
      exact Cdc.AsyncFifoDesign.Compiled.refinement fifoParameters
        sourceToTransform rfl (by decide)
        (Cdc.AsyncQueueStorage.DepthTwo.implementation 32)
    · have second : connection = secondConnection := by
        simp [system, builder, System.empty, SystemBuilder.island,
          SystemBuilder.connect, SystemBuilder.withClockRel,
          System.connections_certify] at member
        rcases member with first | second
        · subst connection
          simp [sourceToTransform] at firstName
        · exact second
      subst connection
      exact Cdc.AsyncFifoDesign.Compiled.refinement fifoParameters
        transformToChecker rfl (by decide)
        (Cdc.AsyncQueueStorage.DepthTwo.implementation 32)
  islandCertificate := by
    intro name island found
    by_cases sourceName : name = "source"
    · subst name
      have islandEq : island = sourceIsland := by
        simpa [system, builder, sourceIsland, System.empty,
          SystemBuilder.island, SystemBuilder.connect,
          SystemBuilder.withClockRel, SystemBuilder.findIsland?,
          System.findIsland?_certify] using found.symm
      subst island
      exact sourceCertificate
    · by_cases transformName : name = "transform"
      · subst name
        have islandEq : island = transformIsland := by
          simpa [system, builder, transformIsland, System.empty,
            SystemBuilder.island, SystemBuilder.connect,
            SystemBuilder.withClockRel, SystemBuilder.findIsland?,
            System.findIsland?_certify] using found.symm
        subst island
        exact transformCertificate
      · have checkerName : name = "checker" := by
          by_contra notChecker
          have impossible : system.findIsland? name = none := by
            simp [system, builder, System.empty, SystemBuilder.island,
              SystemBuilder.connect, SystemBuilder.withClockRel,
              SystemBuilder.findIsland?, System.findIsland?_certify]
            exact ⟨fun nameEq => sourceName nameEq.symm,
              fun nameEq => transformName nameEq.symm,
              fun nameEq => notChecker nameEq.symm⟩
          rw [impossible] at found
          contradiction
        subst name
        have islandEq : island = checkerIsland := by
          simpa [system, builder, checkerIsland, System.empty,
            SystemBuilder.island, SystemBuilder.connect,
            SystemBuilder.withClockRel, SystemBuilder.findIsland?,
            System.findIsland?_certify] using found.symm
        subst island
        exact checkerCertificate

end Machines.Multiclock.ClockGauntlet
