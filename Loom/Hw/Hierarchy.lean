-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
namespace Loom.Hw
universe u v
abbrev InstancePath := String
inductive PortDirection where
  | input
  | output
  deriving Repr, DecidableEq, BEq

namespace Inventory
def uniqueB {α : Type u} [BEq α] (items : List α) : Bool := items.eraseDups.length == items.length
def disjointB {α : Type u} [BEq α] (left right : List α) : Bool := !left.any right.contains
def ensureUnique {α : Type u} [BEq α] (items : List α)
    (message : String) : Except String Unit := if uniqueB items then pure () else throw message
end Inventory
namespace Backend
structure ModuleArtifact where
  name : String
  text : String
structure PortPlan where
  port : String
  net : String
  direction : PortDirection
  width : Nat
  deriving Repr, DecidableEq, BEq
structure InstancePlan where
  path : InstancePath
  moduleName : String
  parameters : List (String × String)
  ports : List PortPlan
  external : Bool
  deriving Repr, DecidableEq, BEq
structure Plan (ExternalArtifact Assumption : Type v) where
  topName : String
  instances : List InstancePlan
  modules : List ModuleArtifact
  externalArtifacts : List ExternalArtifact
  assumptions : List Assumption
end Backend
end Loom.Hw
