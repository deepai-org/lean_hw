-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
/-!
# The transition-system spine (P2/P3)

One `TSys` abstraction through which the spec machine (L0), the hardware
semantics (L3), the µVerilog semantics (L4), and the decision procedures (L2)
speak to each other. Refinement, invariance, BMC, k-induction, and the
emission theorem are all stated against this type.

Deliberately minimal: a state type, initial states, and a step *relation*.
Deterministic systems (the spec, µVerilog) package their step function into
the relation and recover determinism as a lemma, not a representation
constraint.

`BitSys` is the bit-level face for the L2 engines: `BitVec` state, decidable
init/step. `BitSys.toTSys` embeds it so engine results transport to the
`Prop`-level systems via proved correspondences (Spec/BitLevel.lean).
-/

namespace Loom

/-- A transition system: the spine type of the whole stack. -/
structure TSys where
  /-- The state space. -/
  S : Type
  /-- Initial states. -/
  init : S → Prop
  /-- The step relation. -/
  step : S → S → Prop

namespace TSys

variable (M : TSys)

/-- Reachability from an initial state. -/
inductive Reachable : M.S → Prop
  | init {s : M.S} : M.init s → Reachable s
  | step {s s' : M.S} : Reachable s → M.step s s' → Reachable s'

/-- `P` holds in every reachable state. -/
def Invariant (P : M.S → Prop) : Prop :=
  ∀ s, M.Reachable s → P s

/-- `P` is inductive: it holds initially and is preserved by steps. -/
structure Inductive (P : M.S → Prop) : Prop where
  init : ∀ s, M.init s → P s
  step : ∀ s s', P s → M.step s s' → P s'

/-- Invariant induction: an inductive predicate is an invariant. -/
theorem Inductive.invariant {M : TSys} {P : M.S → Prop}
    (h : M.Inductive P) : M.Invariant P := by
  intro s hr
  induction hr with
  | init h0 => exact h.init _ h0
  | step _ hstep ih => exact h.step _ _ ih hstep

/-- Strengthening: an invariant may be established via a stronger inductive
predicate. The standard shape every L2 engine result lands in. -/
theorem invariant_of_inductive_of_imp {M : TSys} {P Q : M.S → Prop}
    (hind : M.Inductive Q) (himp : ∀ s, Q s → P s) : M.Invariant P :=
  fun s hr => himp s (hind.invariant s hr)

/-- The deterministic-system package: a total step function presented as a
`TSys`. The spec machine and µVerilog semantics are built with this. -/
def ofFun (S : Type) (init : S → Prop) (f : S → S) : TSys :=
  { S := S, init := init, step := fun s s' => f s = s' }

@[simp] theorem ofFun_step {S : Type} {init : S → Prop} {f : S → S}
    {s s' : S} : (ofFun S init f).step s s' ↔ f s = s' := Iff.rfl

/-- Determinism of a transition system. Holds definitionally for `ofFun`. -/
def Deterministic : Prop :=
  ∀ s s₁ s₂, M.step s s₁ → M.step s s₂ → s₁ = s₂

theorem ofFun_deterministic (S : Type) (init : S → Prop) (f : S → S) :
    (ofFun S init f).Deterministic := by
  intro s s₁ s₂ h₁ h₂
  simp only [ofFun_step] at h₁ h₂
  exact h₁ ▸ h₂

end TSys

/-- Forward simulation via an abstraction *function*: the refinement currency
of the stack ("abstraction function in, commuting squares out"). If the
pipeline's Burch–Dill proof needs a relation, `SimulationRel` is added beside
this without disturbing its users (open decision D3). -/
structure Simulation (A C : TSys) where
  /-- The abstraction function from concrete to abstract states. -/
  abs : C.S → A.S
  /-- Initial concrete states abstract to initial abstract states. -/
  init_ok : ∀ s, C.init s → A.init (abs s)
  /-- The commuting square. -/
  square : ∀ s s', C.step s s' → A.step (abs s) (abs s')

namespace Simulation

/-- Reachable concrete states abstract to reachable abstract states. -/
theorem reachable {A C : TSys} (σ : Simulation A C) :
    ∀ s, C.Reachable s → A.Reachable (σ.abs s) := by
  intro s hr
  induction hr with
  | init h0 => exact .init (σ.init_ok _ h0)
  | step _ hstep ih => exact .step ih (σ.square _ _ hstep)

/-- Invariants transport down a simulation: a property proved of the abstract
system holds of the concrete one through the abstraction function. -/
theorem invariant_pullback {A C : TSys} (σ : Simulation A C)
    {P : A.S → Prop} (h : A.Invariant P) :
    C.Invariant (fun s => P (σ.abs s)) :=
  fun s hr => h _ (σ.reachable s hr)

/-- Simulations compose. -/
def comp {A B C : TSys} (σ₁ : Simulation A B) (σ₂ : Simulation B C) :
    Simulation A C where
  abs := σ₁.abs ∘ σ₂.abs
  init_ok := fun s h => σ₁.init_ok _ (σ₂.init_ok s h)
  square := fun s s' h => σ₁.square _ _ (σ₂.square s s' h)

end Simulation

/-- A stuttering forward simulation: one concrete step corresponds to zero or
one abstract steps. The multicycle core takes several cycles per instruction,
so its refinement (R-MC) lives here. -/
structure StutterSimulation (A C : TSys) where
  /-- The abstraction function from concrete to abstract states. -/
  abs : C.S → A.S
  /-- Initial concrete states abstract to initial abstract states. -/
  init_ok : ∀ s, C.init s → A.init (abs s)
  /-- Each concrete step either stutters (same abstract state) or commutes. -/
  square : ∀ s s', C.step s s' → abs s' = abs s ∨ A.step (abs s) (abs s')

namespace StutterSimulation

theorem reachable {A C : TSys} (σ : StutterSimulation A C) :
    ∀ s, C.Reachable s → A.Reachable (σ.abs s) := by
  intro s hr
  induction hr with
  | init h0 => exact .init (σ.init_ok _ h0)
  | step _ hstep ih =>
    rcases σ.square _ _ hstep with heq | hstep'
    · exact heq ▸ ih
    · exact .step ih hstep'

/-- Invariants transport down a stuttering simulation. -/
theorem invariant_pullback {A C : TSys} (σ : StutterSimulation A C)
    {P : A.S → Prop} (h : A.Invariant P) :
    C.Invariant (fun s => P (σ.abs s)) :=
  fun s hr => h _ (σ.reachable s hr)

end StutterSimulation

/-- The bit-level face of a transition system (P3): fixed-width `BitVec`
state with `Bool`-valued (hence decidable) init and step. The L2 engines
(BMC, k-induction, PDR) operate exclusively on this type. -/
structure BitSys where
  /-- State width in bits. -/
  width : Nat
  /-- Decidable initial-state predicate. -/
  init : BitVec width → Bool
  /-- Decidable step relation. -/
  step : BitVec width → BitVec width → Bool

namespace BitSys

/-- Embed a bit-level system as a `TSys` so correspondence proofs and
transported results are stated in one vocabulary. -/
def toTSys (B : BitSys) : TSys where
  S := BitVec B.width
  init := fun s => B.init s = true
  step := fun s s' => B.step s s' = true

end BitSys
end Loom
