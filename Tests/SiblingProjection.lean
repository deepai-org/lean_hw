-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tests.SystemProjection

/-!
# Order-independent sibling fragment projection

Two reusable fragments are included in both orders. Builder-produced placement
evidence gives each sibling an execution projection regardless of inventory
position, preserving exact island/channel lookup and dispatch semantics.
-/

namespace Tests.SiblingProjection

open Loom.Hw
open Tests.SystemProjection

/-! The first sibling is the closed, channel-bearing service system from the
main projection gate. -/

structure ServiceInterface (_system : System) where
  serviceName : String

def serviceInterface : ServiceInterface asynchronousParent := ⟨"service"⟩

def serviceBlock : System.SealedBlock ServiceInterface (fun _ _ => Unit) where
  system := asynchronousParent
  islands := asynchronousParent.certifyIslands (by decide)
  interface := serviceInterface
  theorems := ()

def serviceFragment : System.SystemFragment ServiceInterface (fun _ _ => Unit) where
  block := serviceBlock
  plan := .portable
  realizationReady := by decide

/-! The second sibling is deliberately independent and has no channels. It
still carries a reusable trace theorem, so both sides of each assembly order
exercise theorem transport rather than inventory lookup alone. -/

def observerBuilder : SystemBuilder :=
  System.empty
    |>.addErasedIsland monitorIsland
    |>.withClockRel .asynchronous

def observerSystem : System := observerBuilder.certify (by decide)

structure ObserverInterface (_system : System) where
  observerName : String

def observerInterface : ObserverInterface observerSystem := ⟨"observer"⟩

def observerBlock : System.SealedBlock ObserverInterface (fun _ _ => Unit) where
  system := observerSystem
  islands := observerSystem.certifyIslands (by decide)
  interface := observerInterface
  theorems := ()

def observerFragment :
    System.SystemFragment ObserverInterface (fun _ _ => Unit) where
  block := observerBlock
  plan := .portable
  realizationReady := by decide

def observerProperty (_steps : List System.ObservedRecoveryEvent)
    (_final : observerSystem.State) : Prop := True

theorem observerTheorem :
    System.FiniteTraceTheorem observerSystem observerProperty := by
  intro _steps _valid
  trivial

/-! ## Service then observer -/

def serviceFirst := System.empty.includeFragmentPlaced serviceFragment
def observerAfterService :=
  serviceFirst.builder.includeFragmentPlaced observerFragment

def servicePlacementInServiceObserver :=
  serviceFirst.placement.afterIncludeFragment observerFragment

def serviceObserverBuilder : SystemBuilder := observerAfterService.builder
def serviceObserverReady : serviceObserverBuilder.check.isOk := by decide
def serviceObserver : System :=
  serviceObserverBuilder.certify serviceObserverReady

def serviceObserverIslandInventory :
    System.CertifiedIslands.Inventory serviceObserverBuilder.islands := by
  simpa [serviceObserverBuilder, observerAfterService, serviceFirst] using
    System.CertifiedIslands.includeFragment
      (System.CertifiedIslands.includeFragment
        (builder := System.empty) .empty serviceFragment)
      observerFragment

def serviceObserverIslandCache : System.CertifiedIslands serviceObserver :=
  System.CertifiedIslands.ofInventory serviceObserver
    serviceObserverIslandInventory

def serviceEmbeddingInServiceObserver :
    System.StandardEmbedding serviceObserver asynchronousParent :=
  servicePlacementInServiceObserver.toStandardEmbedding
    serviceObserverReady (by decide) (by decide) (by decide) (by decide)
      (by decide) rfl rfl (by intros; rfl)

def observerEmbeddingInServiceObserver :
    System.StandardEmbedding serviceObserver observerSystem :=
  observerAfterService.placement.toStandardEmbedding
    serviceObserverReady (by decide) (by decide) (by decide) (by decide)
      (by decide) rfl rfl (by intros; rfl)

def serviceProjectionInServiceObserver :=
  serviceFragment.standardProjection serviceEmbeddingInServiceObserver

def observerProjectionInServiceObserver :=
  observerFragment.standardProjection observerEmbeddingInServiceObserver

def serviceTheoremInServiceObserver :=
  serviceFragment.liftFragmentTheorem serviceProjectionInServiceObserver
    asynchronousOrderingNoLoss

def observerTheoremInServiceObserver :=
  observerFragment.liftFragmentTheorem observerProjectionInServiceObserver
    observerTheorem

/-! ## Observer then service -/

def observerFirst := System.empty.includeFragmentPlaced observerFragment
def serviceAfterObserver :=
  observerFirst.builder.includeFragmentPlaced serviceFragment

def observerPlacementInObserverService :=
  observerFirst.placement.afterIncludeFragment serviceFragment

def observerServiceBuilder : SystemBuilder := serviceAfterObserver.builder
def observerServiceReady : observerServiceBuilder.check.isOk := by decide
def observerService : System :=
  observerServiceBuilder.certify observerServiceReady

def observerServiceIslandInventory :
    System.CertifiedIslands.Inventory observerServiceBuilder.islands := by
  simpa [observerServiceBuilder, serviceAfterObserver, observerFirst] using
    System.CertifiedIslands.includeFragment
      (System.CertifiedIslands.includeFragment
        (builder := System.empty) .empty observerFragment)
      serviceFragment

def observerServiceIslandCache : System.CertifiedIslands observerService :=
  System.CertifiedIslands.ofInventory observerService
    observerServiceIslandInventory

def observerEmbeddingInObserverService :
    System.StandardEmbedding observerService observerSystem :=
  observerPlacementInObserverService.toStandardEmbedding
    observerServiceReady (by decide) (by decide) (by decide) (by decide)
      (by decide) rfl rfl (by intros; rfl)

def serviceEmbeddingInObserverService :
    System.StandardEmbedding observerService asynchronousParent :=
  serviceAfterObserver.placement.toStandardEmbedding
    observerServiceReady (by decide) (by decide) (by decide) (by decide)
      (by decide) rfl rfl (by intros; rfl)

def observerProjectionInObserverService :=
  observerFragment.standardProjection observerEmbeddingInObserverService

def serviceProjectionInObserverService :=
  serviceFragment.standardProjection serviceEmbeddingInObserverService

def observerTheoremInObserverService :=
  observerFragment.liftFragmentTheorem observerProjectionInObserverService
    observerTheorem

def serviceTheoremInObserverService :=
  serviceFragment.liftFragmentTheorem serviceProjectionInObserverService
    asynchronousOrderingNoLoss

/-! Inventory position really differs, while both projection families remain
available. The service owns internal channels; the observer does not acquire
them merely by preceding or following it. -/

example : serviceObserver.islands.map (·.name) =
    asynchronousParent.islands.map (·.name) ++ [monitorIsland.name] := by
  decide

example : observerService.islands.map (·.name) =
    [monitorIsland.name] ++ asynchronousParent.islands.map (·.name) := by
  decide

example : serviceObserver.connections.map (·.chan.name) =
    asynchronousParent.connections.map (·.chan.name) := by
  decide

example : observerService.connections.map (·.chan.name) =
    asynchronousParent.connections.map (·.chan.name) := by
  decide

/-! Duplicate sibling inclusion is rejected at assembly, preserving the
negative collision gate independently of placement construction. -/

def duplicateServiceBuilder : SystemBuilder :=
  serviceFirst.builder.includeFragment serviceFragment

def duplicateServiceRejected : Bool :=
  match duplicateServiceBuilder.check with
  | .error _ => true
  | .ok _ => false

example : duplicateServiceRejected = true := by decide

end Tests.SiblingProjection
