-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

/-!
# Relational trace contracts

This is the small, schedule-free algebra used to connect application-level
stream facts. A contract relates a consumed input trace to a produced output
trace. It says nothing about clocks, buffering, latency, or a particular
pipeline shape; those facts are established separately by islands and `Chan`.
-/

namespace Loom.Hw

universe u v w x

/-- A relation between finite input and output traces. This deliberately
permits nondeterministic components, filters, merges, and protocol adapters;
deterministic element-wise transforms are the common special case below. -/
abbrev TraceContract (α : Type u) (β : Type v) := List α → List β → Prop

namespace TraceContract

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-- Relational composition hides the intermediate trace. -/
def comp (left : TraceContract α β) (right : TraceContract β γ) :
    TraceContract α γ :=
  fun input output => ∃ middle, left input middle ∧ right middle output

/-- The identity trace contract. -/
def id : TraceContract α α := Eq

@[simp] theorem id_comp (contract : TraceContract α β) :
    comp id contract = contract := by
  funext input output
  apply propext
  constructor
  · rintro ⟨middle, rfl, holds⟩
    exact holds
  · intro holds
    exact ⟨input, rfl, holds⟩

@[simp] theorem comp_id (contract : TraceContract α β) :
    comp contract id = contract := by
  funext input output
  apply propext
  constructor
  · rintro ⟨middle, holds, rfl⟩
    exact holds
  · intro holds
    exact ⟨output, holds, rfl⟩

theorem comp_assoc (first : TraceContract α β) (second : TraceContract β γ)
    (third : TraceContract γ δ) :
    comp (comp first second) third = comp first (comp second third) := by
  funext input output
  apply propext
  constructor
  · rintro ⟨right, ⟨middle, firstHolds, secondHolds⟩, thirdHolds⟩
    exact ⟨middle, firstHolds, right, secondHolds, thirdHolds⟩
  · rintro ⟨middle, firstHolds, right, secondHolds, thirdHolds⟩
    exact ⟨right, ⟨middle, firstHolds, secondHolds⟩, thirdHolds⟩

/-- The observed output is an ordered prefix of applying `transform` to all
accepted inputs. The existential suffix is exactly the still-buffered or
otherwise in-flight work. -/
def mapPrefix (transform : α → β) : TraceContract α β :=
  fun input output => ∃ pending, input.map transform = output ++ pending

theorem mapPrefix_id (input output : List α) :
    mapPrefix (fun value : α => value) input output ↔
      ∃ pending, input = output ++ pending := by
  simp [mapPrefix]

/-- Prefix-preserving deterministic transforms compose without exposing
buffer placement, latency, clocks, or schedules. -/
theorem mapPrefix_comp {first : α → β} {second : β → γ}
    {input : List α} {middle : List β} {output : List γ}
    (left : mapPrefix first input middle)
    (right : mapPrefix second middle output) :
    mapPrefix (second ∘ first) input output := by
  rcases left with ⟨leftPending, leftEq⟩
  rcases right with ⟨rightPending, rightEq⟩
  refine ⟨rightPending ++ leftPending.map second, ?_⟩
  rw [← List.map_map, leftEq, List.map_append, rightEq, List.append_assoc]

/-- Contract-level form of `mapPrefix_comp`. -/
theorem comp_mapPrefix (first : α → β) (second : β → γ) :
    ∀ input output,
      comp (mapPrefix first) (mapPrefix second) input output →
        mapPrefix (second ∘ first) input output := by
  intro input output composed
  rcases composed with ⟨middle, left, right⟩
  exact mapPrefix_comp left right

/-! ## Bounded service

Bounded delivery needs a notion of observation time, but it does not need to
mention clocks or a `System` schedule.  Applications project their execution
to cumulative accepted/delivered counts indexed by whichever service unit is
appropriate (destination ticks, grants, or protocol rounds), then discharge
the explicit premise below.  In particular, Loom never infers liveness from
the existence of a channel alone.
-/

/-- Cumulative number of events observed at each application-defined service
index.  Monotonicity is requested explicitly by lemmas that need it rather
than hidden in this lightweight type. -/
abbrev CountTrace := Nat → Nat

/-- Every item accepted by service index `time` has been delivered by
`time + bound`.  The caller chooses and documents the service index; the
relation itself is schedule- and technology-neutral. -/
def deliveredWithin (bound : Nat) (accepted delivered : CountTrace) : Prop :=
  ∀ time, accepted time ≤ delivered (time + bound)

/-- Serial bounded-service contracts compose by adding their bounds.  This is
the generic liveness counterpart of `mapPrefix_comp`; it exposes neither a
pipeline topology nor any finite-search certificate. -/
theorem deliveredWithin_comp {input middle output : CountTrace}
    {firstBound secondBound : Nat}
    (first : deliveredWithin firstBound input middle)
    (second : deliveredWithin secondBound middle output) :
    deliveredWithin (firstBound + secondBound) input output := by
  intro time
  calc
    input time ≤ middle (time + firstBound) := first time
    _ ≤ output ((time + firstBound) + secondBound) := second (time + firstBound)
    _ = output (time + (firstBound + secondBound)) := by rw [Nat.add_assoc]

/-- A proved service bound remains valid when weakened, provided the delivered
count is cumulative.  The monotonicity premise is deliberately visible. -/
theorem deliveredWithin_mono {accepted delivered : CountTrace}
    {tight loose : Nat}
    (deliveryMonotone : ∀ first second, first ≤ second →
      delivered first ≤ delivered second)
    (bound : deliveredWithin tight accepted delivered) (weaker : tight ≤ loose) :
    deliveredWithin loose accepted delivered := by
  intro time
  calc
    accepted time ≤ delivered (time + tight) := bound time
    _ ≤ delivered (time + loose) :=
      deliveryMonotone _ _ (Nat.add_le_add_left weaker time)

end TraceContract
end Loom.Hw
