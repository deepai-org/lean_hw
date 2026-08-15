-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component

/-!
# Typed plugin services

Plugins are deterministic construction-time programs, not hardware
semantics. A service key is a GADT indexed by the Lean type of the value it
names. The type is therefore carried by the key itself: an address service
cannot be accidentally populated with an equal-width decoder or bus endpoint.
-/

namespace Loom.Hw

universe u

inductive ServiceMultiplicity where
  | unique
  | many
  deriving Repr, DecidableEq, BEq

/-- Constructive result of comparing two typed service keys. -/
inductive ServiceMatch (α β : Type u) where
  | same (equal : α = β)
  | different

/-- Operations for a project's typed key GADT. `sameType?` returns a type
equality exactly when its two values denote the same service. This witness,
not an erased string or width, is the authority used to recover values. -/
class ServiceCatalog (κ : Type u → Type u) where
  name : {α : Type u} → κ α → String
  matchKey : {α β : Type u} → κ α → κ β → ServiceMatch α β
  matchKey_sound : {α β : Type u} → (left : κ α) → (right : κ β) →
    (equal : α = β) → matchKey left right = .same equal → HEq left right
  matchKey_refl : {α : Type u} → (key : κ α) →
    matchKey key key = .same rfl
  multiplicity : {α : Type u} → κ α → ServiceMultiplicity := fun _ => .unique

namespace Plugin

variable {κ : Type u → Type u} [ServiceCatalog κ]

/-- A heterogeneous service key with its result type retained. -/
structure Key where
  Value : Type u
  key : κ Value

namespace Key

def of {α : Type u} (key : κ α) : Key (κ := κ) := ⟨α, key⟩

def sameB (left right : Key (κ := κ)) : Bool :=
  match ServiceCatalog.matchKey left.key right.key with
  | .same _ => true
  | .different => false

def name (key : Key (κ := κ)) : String := ServiceCatalog.name key.key

end Key

/-- One resolved value, existential only in its typed key. -/
structure Binding where
  Value : Type u
  key : κ Value
  provider : String
  value : Value

abbrev Registry := List (Binding (κ := κ))

namespace Registry

def values {α : Type u} (registry : Registry (κ := κ)) (key : κ α) : List α :=
  registry.filterMap fun binding =>
    match ServiceCatalog.matchKey binding.key key with
    | .same equal => some (equal ▸ binding.value)
    | .different => none

def getUnique? {α : Type u} (registry : Registry (κ := κ)) (key : κ α) :
    Except String α :=
  match registry.values key with
  | [value] => .ok value
  | [] => .error s!"service '{ServiceCatalog.name key}' is unresolved"
  | values => .error s!"unique service '{ServiceCatalog.name key}' has {values.length} providers"

end Registry

/-- The only view passed to a provider builder. Access is dynamically checked
against the provider's declared requirement list and remains statically typed
by the requested GADT key. -/
structure Requirements (required : List (Key (κ := κ))) where
  private registry : Registry (κ := κ)

namespace Requirements

private def declaredB {α : Type u} {required : List (Key (κ := κ))}
    (key : κ α) : Bool :=
  required.any fun requirement => requirement.sameB (Key.of key)

def getUnique? {α : Type u} {required : List (Key (κ := κ))}
    (requirements : Requirements (κ := κ) required) (key : κ α) :
    Except String α := do
  unless declaredB (required := required) key do
    throw s!"provider attempted undeclared service read '{ServiceCatalog.name key}'"
  requirements.registry.getUnique? key

def getAll {α : Type u} {required : List (Key (κ := κ))}
    (requirements : Requirements (κ := κ) required) (key : κ α) :
    Except String (List α) := do
  unless declaredB (required := required) key do
    throw s!"provider attempted undeclared service read '{ServiceCatalog.name key}'"
  return requirements.registry.values key

end Requirements

/-- One typed provider. Its key fixes the type its builder must return. -/
structure Provider where
  Value : Type u
  name : String
  key : κ Value
  requires : List (Key (κ := κ))
  build : Requirements (κ := κ) requires → Except String Value

structure ResourceClaim where
  kind : String
  name : String
  exclusive : Bool := true
  deriving Repr, DecidableEq, BEq

structure Spec where
  name : String
  providers : List (Provider (κ := κ)) := []
  resources : List ResourceClaim := []

private structure Pending where
  pluginName : String
  provider : Provider (κ := κ)

namespace Pending

def fullName (pending : Pending (κ := κ)) : String :=
  pending.pluginName ++ "." ++ pending.provider.name

def key (pending : Pending (κ := κ)) : Key (κ := κ) :=
  Key.of pending.provider.key

end Pending

private def insertPending (pending : Pending (κ := κ)) :
    List (Pending (κ := κ)) → List (Pending (κ := κ))
  | [] => [pending]
  | first :: rest =>
      if pending.fullName < first.fullName then pending :: first :: rest
      else first :: insertPending pending rest

private def sortPending (providers : List (Pending (κ := κ))) :
    List (Pending (κ := κ)) :=
  providers.foldr insertPending []

private def declaredProviders (plugins : List (Spec (κ := κ))) :
    List (Pending (κ := κ)) :=
  sortPending <| plugins.flatMap fun plugin =>
    plugin.providers.map fun provider => ⟨plugin.name, provider⟩

private def countProviders (providers : List (Pending (κ := κ)))
    (key : Key (κ := κ)) : Nat :=
  (providers.filter fun provider => provider.key.sameB key).length

private def allNamesUniqueB (names : List String) : Bool :=
  names.eraseDups.length == names.length

private def resourcesCompatibleB (plugins : List (Spec (κ := κ))) : Bool :=
  let claims := plugins.flatMap (·.resources)
  claims.all fun claim =>
    !claim.exclusive ||
      (claims.filter fun other =>
        other.kind == claim.kind && other.name == claim.name).length == 1

private def declarationsValidB (plugins : List (Spec (κ := κ))) : Bool :=
  let providers := declaredProviders plugins
  !plugins.isEmpty &&
    plugins.all (fun plugin => !plugin.name.isEmpty) &&
    allNamesUniqueB (plugins.map (·.name)) &&
    providers.all (fun pending =>
      !pending.provider.name.isEmpty && !pending.key.name.isEmpty) &&
    allNamesUniqueB (providers.map Pending.fullName) &&
    resourcesCompatibleB plugins

private def negotiatedB (providers : List (Pending (κ := κ))) : Bool :=
  providers.all fun pending =>
    let providerCount := countProviders providers pending.key
    let ownMultiplicityOk :=
      match ServiceCatalog.multiplicity pending.provider.key with
      | .unique => providerCount == 1
      | .many => providerCount > 0
    ownMultiplicityOk && pending.provider.requires.all (fun requirement =>
      let count := countProviders providers requirement
      match ServiceCatalog.multiplicity requirement.key with
      | .unique => count == 1
      | .many => count > 0)

private def countResolved (registry : Registry (κ := κ))
    (key : Key (κ := κ)) : Nat :=
  (registry.filter fun binding =>
    (Key.of binding.key).sameB key).length

private def requirementReadyB (all : List (Pending (κ := κ)))
    (registry : Registry (κ := κ)) (key : Key (κ := κ)) : Bool :=
  countResolved registry key == countProviders all key

private def readyB (all : List (Pending (κ := κ)))
    (registry : Registry (κ := κ)) (pending : Pending (κ := κ)) : Bool :=
  pending.provider.requires.all (requirementReadyB all registry)

private def removeFullName (name : String) :
    List (Pending (κ := κ)) → List (Pending (κ := κ))
  | [] => []
  | pending :: rest =>
      if pending.fullName == name then rest
      else pending :: removeFullName name rest

private def buildProviders (all : List (Pending (κ := κ))) :
    Nat → List (Pending (κ := κ)) → Registry (κ := κ) →
      Except String (Registry (κ := κ))
  | _, [], registry => .ok registry
  | 0, pending, _ =>
      .error s!"service dependency resolution exhausted with {pending.length} provider(s) pending"
  | fuel + 1, pending, registry => do
      let some next := pending.find? (readyB all registry)
        | throw (s!"service dependency cycle: " ++
            String.intercalate ", " (pending.map Pending.fullName))
      let requirements : Requirements (κ := κ) next.provider.requires :=
        ⟨registry⟩
      match next.provider.build requirements with
      | .error message => .error message
      | .ok value =>
          let binding : Binding (κ := κ) :=
            ⟨next.provider.Value, next.provider.key, next.fullName, value⟩
          buildProviders all fuel (removeFullName next.fullName pending)
            (registry ++ [binding])

structure ManifestEntry where
  provider : String
  service : String
  deriving Repr, DecidableEq, BEq

structure Resolved where
  private registry : Registry (κ := κ)
  manifest : List ManifestEntry
  resources : List (String × ResourceClaim)

namespace Resolved

def getUnique? {α : Type u} (resolved : Resolved (κ := κ)) (key : κ α) :
    Except String α := resolved.registry.getUnique? key

def getAll {α : Type u} (resolved : Resolved (κ := κ)) (key : κ α) : List α :=
  resolved.registry.values key

end Resolved

/-- Declare, negotiate, build, and seal a plugin set. Input order is erased by
canonical provider-name sorting before any builder runs. -/
def resolve? (plugins : List (Spec (κ := κ))) :
    Except String (Resolved (κ := κ)) := do
  unless declarationsValidB plugins do
    throw "plugin declarations have empty/duplicate names or conflicting exclusive resources"
  let providers := declaredProviders plugins
  unless negotiatedB providers do
    throw "plugin service negotiation found a missing or duplicate unique provider"
  let registry ← buildProviders providers providers.length providers []
  return {
    registry := registry
    manifest := registry.map fun binding =>
      ⟨binding.provider, ServiceCatalog.name binding.key⟩
    resources := plugins.flatMap fun plugin =>
      plugin.resources.map fun claim => (plugin.name, claim)
  }

end Plugin

end Loom.Hw
