-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Core.Ts

/-! # Simulation-chain regressions -/

namespace Tests.SimulationComp

open Loom

example {A B C : TSys} (σ₁ : StutterSimulation A B)
    (σ₂ : StutterSimulation B C) (s : C.S) :
    (σ₁.comp σ₂).abs s = σ₁.abs (σ₂.abs s) := rfl

example {A B C : TSys} (σ₁ : Simulation A B)
    (σ₂ : StutterSimulation B C) {P : A.S → Prop}
    (hP : A.Invariant P) :
    C.Invariant (fun s => P (σ₁.abs (σ₂.abs s))) :=
  (StutterSimulation.ofSimulationComp σ₁ σ₂).invariant_pullback hP

example (A : TSys) {P : A.S → Prop} (hP : A.Invariant P) :
    A.Invariant (fun s => P ((StutterSimulation.refl A).abs s)) :=
  (StutterSimulation.refl A).invariant_pullback hP

end Tests.SimulationComp
