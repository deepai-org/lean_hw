-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.SoCFabricGauntlet.Design
import Loom.Hw.CertifiedSystemArtifact

namespace Machines.Multiclock.SoCFabricGauntlet

open Loom.Hw

def cpuCertificate : CertifiedDesign cpu := .ofChecks (by decide) (by decide)
def dmaCertificate : CertifiedDesign dma := .ofChecks (by decide) (by decide)
def fabricCertificate : CertifiedDesign fabric := .ofChecks (by decide) (by decide)
def serviceCertificate : CertifiedDesign service := .ofChecks (by decide) (by decide)
def monitorCertificate : CertifiedDesign monitor := .ofChecks (by decide) (by decide)

private def cpuIsland : SystemIsland := ⟨"cpu", "cpu_fabric_clk", cpu⟩
private def dmaIsland : SystemIsland := ⟨"dma", "dma_clk", dma⟩
private def fabricIsland : SystemIsland := ⟨"fabric", "cpu_fabric_clk", fabric⟩
private def serviceIsland : SystemIsland := ⟨"service", "mem_clk", service⟩
private def monitorIsland : SystemIsland := ⟨"monitor", "mon_clk", monitor⟩

def certified : CertifiedSystem system where
  channelCertificate := by
    intro connection member
    by_cases cpuReq : connection.chan.name = cpuRequest.bits.name
    · have eq : connection = cpuRequestConnection := by
        rw [connectionInventory] at member
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with eq | eq | eq | eq | eq | eq | eq
        · exact eq
        all_goals subst connection
        all_goals simp [PackedChan.named, cpuRequestConnection, cpuResponseConnection,
          dmaRequestConnection, dmaResponseConnection, targetRequestConnection,
          targetResponseConnection, auditConnection, cpuRequest, cpuResponse,
          dmaRequest, dmaResponse, targetRequest, targetResponse, audit] at cpuReq
      subst connection
      exact cpuRequest.bits.syncRefinement (by decide)
    · by_cases cpuResp : connection.chan.name = cpuResponse.bits.name
      · have eq : connection = cpuResponseConnection := by
          rw [connectionInventory] at member
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
          rcases member with eq | eq | eq | eq | eq | eq | eq
          · subst connection
            simp [PackedChan.named, cpuRequestConnection, cpuRequest, cpuResponse] at cpuResp
          · exact eq
          all_goals subst connection
          all_goals simp [PackedChan.named, dmaRequestConnection, dmaResponseConnection,
            targetRequestConnection, targetResponseConnection, auditConnection,
            cpuResponse, dmaRequest, dmaResponse, targetRequest, targetResponse,
            audit] at cpuResp
        subst connection
        exact cpuResponse.bits.syncRefinement (by decide)
      · by_cases dmaReq : connection.chan.name = dmaRequest.bits.name
        · have eq : connection = dmaRequestConnection := by
            rw [connectionInventory] at member
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
            rcases member with eq | eq | eq | eq | eq | eq | eq
            · subst connection
              simp [PackedChan.named, cpuRequestConnection, cpuRequest, dmaRequest] at dmaReq
            · subst connection
              simp [PackedChan.named, cpuResponseConnection, cpuResponse, dmaRequest] at dmaReq
            · exact eq
            all_goals subst connection
            all_goals simp [PackedChan.named, dmaResponseConnection, targetRequestConnection,
              targetResponseConnection, auditConnection, dmaRequest, dmaResponse,
              targetRequest, targetResponse, audit] at dmaReq
          subst connection
          exact dmaRequest.bits.syncRefinement (by decide)
        · by_cases dmaResp : connection.chan.name = dmaResponse.bits.name
          · have eq : connection = dmaResponseConnection := by
              rw [connectionInventory] at member
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
              rcases member with eq | eq | eq | eq | eq | eq | eq
              · subst connection
                simp [PackedChan.named, cpuRequestConnection, cpuRequest, dmaResponse] at dmaResp
              · subst connection
                simp [PackedChan.named, cpuResponseConnection, cpuResponse, dmaResponse] at dmaResp
              · subst connection
                simp [PackedChan.named, dmaRequestConnection, dmaRequest, dmaResponse] at dmaResp
              · exact eq
              all_goals subst connection
              all_goals simp [PackedChan.named, targetRequestConnection, targetResponseConnection,
                auditConnection, dmaResponse, targetRequest, targetResponse, audit]
                at dmaResp
            subst connection
            exact dmaResponse.bits.syncRefinement (by decide)
          · by_cases targetReq : connection.chan.name = targetRequest.bits.name
            · have eq : connection = targetRequestConnection := by
                rw [connectionInventory] at member
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
                rcases member with eq | eq | eq | eq | eq | eq | eq
                · subst connection
                  simp [PackedChan.named, cpuRequestConnection, cpuRequest, targetRequest] at targetReq
                · subst connection
                  simp [PackedChan.named, cpuResponseConnection, cpuResponse, targetRequest] at targetReq
                · subst connection
                  simp [PackedChan.named, dmaRequestConnection, dmaRequest, targetRequest] at targetReq
                · subst connection
                  simp [PackedChan.named, dmaResponseConnection, dmaResponse, targetRequest] at targetReq
                · exact eq
                all_goals subst connection
                all_goals simp [PackedChan.named, targetResponseConnection, auditConnection,
                  targetRequest, targetResponse, audit] at targetReq
              subst connection
              exact targetRequest.bits.syncRefinement (by decide)
            · by_cases targetResp : connection.chan.name = targetResponse.bits.name
              · have eq : connection = targetResponseConnection := by
                  rw [connectionInventory] at member
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
                  rcases member with eq | eq | eq | eq | eq | eq | eq
                  · subst connection
                    simp [PackedChan.named, cpuRequestConnection, cpuRequest, targetResponse] at targetResp
                  · subst connection
                    simp [PackedChan.named, cpuResponseConnection, cpuResponse, targetResponse] at targetResp
                  · subst connection
                    simp [PackedChan.named, dmaRequestConnection, dmaRequest, targetResponse] at targetResp
                  · subst connection
                    simp [PackedChan.named, dmaResponseConnection, dmaResponse, targetResponse] at targetResp
                  · subst connection
                    simp [PackedChan.named, targetRequestConnection, targetRequest, targetResponse] at targetResp
                  · exact eq
                  · subst connection
                    simp [PackedChan.named, auditConnection, targetResponse, audit] at targetResp
                subst connection
                exact targetResponse.bits.syncRefinement (by decide)
              · have auditEq : connection = auditConnection := by
                  rw [connectionInventory] at member
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
                  rcases member with eq | eq | eq | eq | eq | eq | eq
                  · subst connection
                    simp [PackedChan.named, cpuRequestConnection, cpuRequest, audit] at cpuReq
                  · subst connection
                    simp [PackedChan.named, cpuResponseConnection, cpuResponse, audit] at cpuResp
                  · subst connection
                    simp [PackedChan.named, dmaRequestConnection, dmaRequest, audit] at dmaReq
                  · subst connection
                    simp [PackedChan.named, dmaResponseConnection, dmaResponse, audit] at dmaResp
                  · subst connection
                    simp [PackedChan.named, targetRequestConnection, targetRequest, audit] at targetReq
                  · subst connection
                    simp [PackedChan.named, targetResponseConnection, targetResponse, audit] at targetResp
                  · exact eq
                subst connection
                exact audit.bits.syncRefinement (by decide)
  islandCertificate := by
    intro name island found
    by_cases cpuName : name = "cpu"
    · subst name
      have islandEq : island = cpuIsland := by
        simpa [system, builder, cpuIsland, System.empty,
          SystemBuilder.addErasedDesignIsland, SystemBuilder.connect,
          SystemBuilder.withClockRel, SystemBuilder.findIsland?,
          System.findIsland?_certify] using found.symm
      subst island
      exact cpuCertificate
    · by_cases dmaName : name = "dma"
      · subst name
        have islandEq : island = dmaIsland := by
          simpa [system, builder, dmaIsland, System.empty,
            SystemBuilder.addErasedDesignIsland, SystemBuilder.connect,
            SystemBuilder.withClockRel, SystemBuilder.findIsland?,
            System.findIsland?_certify] using found.symm
        subst island
        exact dmaCertificate
      · by_cases fabricName : name = "fabric"
        · subst name
          have islandEq : island = fabricIsland := by
            simpa [system, builder, fabricIsland, System.empty,
              SystemBuilder.addErasedDesignIsland, SystemBuilder.connect,
              SystemBuilder.withClockRel, SystemBuilder.findIsland?,
              System.findIsland?_certify] using found.symm
          subst island
          exact fabricCertificate
        · by_cases serviceName : name = "service"
          · subst name
            have islandEq : island = serviceIsland := by
              simpa [system, builder, serviceIsland, System.empty,
                SystemBuilder.addErasedDesignIsland, SystemBuilder.connect,
                SystemBuilder.withClockRel, SystemBuilder.findIsland?,
                System.findIsland?_certify] using found.symm
            subst island
            exact serviceCertificate
          · have monitorName : name = "monitor" := by
              by_contra notMonitor
              have impossible : system.findIsland? name = none := by
                simp [system, builder, System.empty, SystemBuilder.addErasedDesignIsland,
                  SystemBuilder.connect, SystemBuilder.withClockRel,
                  SystemBuilder.findIsland?, System.findIsland?_certify]
                exact ⟨fun eq => cpuName eq.symm, fun eq => dmaName eq.symm,
                  fun eq => fabricName eq.symm, fun eq => serviceName eq.symm,
                  fun eq => notMonitor eq.symm⟩
              rw [impossible] at found
              contradiction
            subst name
            have islandEq : island = monitorIsland := by
              simpa [system, builder, monitorIsland, System.empty,
                SystemBuilder.addErasedDesignIsland, SystemBuilder.connect,
                SystemBuilder.withClockRel, SystemBuilder.findIsland?,
                System.findIsland?_certify] using found.symm
            subst island
            exact monitorCertificate

end Machines.Multiclock.SoCFabricGauntlet
