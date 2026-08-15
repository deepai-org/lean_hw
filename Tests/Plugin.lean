-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Plugin

/-! # Typed deterministic plugin regressions -/

namespace Tests.Plugin

open Loom.Hw
open Loom.Hw.Plugin

private inductive CpuService : Type → Type where
  | config : CpuService Nat
  | addressWidth : CpuService Nat
  | resetVector : CpuService (BitVec 64)
  | observer : CpuService String

private instance : ServiceCatalog CpuService where
  name
    | .config => "config"
    | .addressWidth => "address_width"
    | .resetVector => "reset_vector"
    | .observer => "observer"
  matchKey
    | .config, .config => .same rfl
    | .addressWidth, .addressWidth => .same rfl
    | .resetVector, .resetVector => .same rfl
    | .observer, .observer => .same rfl
    | _, _ => .different
  matchKey_sound := by
    intro α β left right equal matched
    cases left <;> cases right <;> simp_all
  matchKey_refl := by
    intro α key
    cases key <;> rfl
  multiplicity
    | .observer => .many
    | _ => .unique

private def configProvider : Provider (κ := CpuService) where
  Value := Nat
  name := "provide"
  key := .config
  requires := []
  build := fun _ => .ok 64

private def widthProvider : Provider (κ := CpuService) where
  Value := Nat
  name := "derive"
  key := .addressWidth
  requires := [Key.of .config]
  build := fun requirements => requirements.getUnique? .config

private def resetProvider : Provider (κ := CpuService) where
  Value := BitVec 64
  name := "reset"
  key := .resetVector
  requires := [Key.of .addressWidth]
  build := fun requirements => do
    let width ← requirements.getUnique? .addressWidth
    if width == 64 then return 0x80000000#64
    throw "unsupported address width"

private def observerProvider (name value : String) : Provider (κ := CpuService) where
  Value := String
  name
  key := .observer
  requires := []
  build := fun _ => .ok value

private def base : Spec (κ := CpuService) where
  name := "base"
  providers := [configProvider]
  resources := [⟨"address-space", "boot", true⟩]

private def derived : Spec (κ := CpuService) where
  name := "derived"
  providers := [widthProvider, resetProvider]

private def tracing : Spec (κ := CpuService) where
  name := "tracing"
  providers := [observerProvider "trace" "trace"]

private def metrics : Spec (κ := CpuService) where
  name := "metrics"
  providers := [observerProvider "metrics" "metrics"]

private def resolved : Except String (Resolved (κ := CpuService)) :=
  resolve? [derived, metrics, base, tracing]

#guard match resolved with
  | .error _ => false
  | .ok services =>
      match services.getUnique? .config, services.getUnique? .resetVector with
      | .ok config, .ok reset =>
          config == 64 && reset == 0x80000000#64 &&
          services.getAll .observer == ["metrics", "trace"] &&
          services.manifest.map (·.provider) ==
            ["base.provide", "derived.derive", "derived.reset",
             "metrics.metrics", "tracing.trace"]
      | _, _ => false

/- Reordering plugins does not change the canonical build or manifest. -/
#guard match resolved, resolve? [tracing, base, metrics, derived] with
  | .ok left, .ok right =>
      left.manifest == right.manifest && left.getAll .observer == right.getAll .observer &&
      match left.getUnique? .resetVector, right.getUnique? .resetVector with
      | .ok leftReset, .ok rightReset => leftReset == rightReset
      | _, _ => false
  | _, _ => false

private def alternativeBase : Spec (κ := CpuService) where
  name := "alternative"
  providers := [{ configProvider with name := "config" }]

/- A provider can be replaced without changing consumers or weakening the
service type. -/
#guard match resolve? [derived, alternativeBase] with
  | .ok services =>
      match services.getUnique? .resetVector with
      | .ok reset => reset == 0x80000000#64
      | .error _ => false
  | .error _ => false

private def duplicateConfig : Spec (κ := CpuService) where
  name := "duplicate"
  providers := [{ configProvider with name := "other" }]

#guard match resolve? [base, duplicateConfig] with
  | .error _ => true
  | .ok _ => false

private def cyclicWidth : Provider (κ := CpuService) where
  Value := Nat
  name := "width"
  key := .addressWidth
  requires := [Key.of .resetVector]
  build := fun requirements => do
    let _ ← requirements.getUnique? .resetVector
    return 64

private def cyclicReset : Provider (κ := CpuService) where
  Value := BitVec 64
  name := "reset"
  key := .resetVector
  requires := [Key.of .addressWidth]
  build := fun requirements => do
    let _ ← requirements.getUnique? .addressWidth
    return 0#64

private def cyclePlugin : Spec (κ := CpuService) where
  name := "cycle"
  providers := [cyclicWidth, cyclicReset]

#guard match resolve? [cyclePlugin] with
  | .error _ => true
  | .ok _ => false

private def conflictingResource : Spec (κ := CpuService) where
  name := "conflict"
  resources := [⟨"address-space", "boot", true⟩]

#guard match resolve? [base, conflictingResource] with
  | .error _ => true
  | .ok _ => false

end Tests.Plugin
