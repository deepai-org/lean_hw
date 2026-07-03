import Loom.Logic.Sep.Bi
import Machines.Lnp64u.Logic.Defs

/-!
# µLog: the LNP64-µ resource algebra (L1, PLAN §5 "L1 µLog")

The machine instance of the generic BI core: a µ **resource** is a bundle of
ownership claims over exactly the sorts T9 conserves — memory words,
capability slots, lineage cells, and per-domain budget time. Claims on the
set-like sorts compose by disjoint union; budget composes additively (time
is a quantity, not a location). `interp` says a resource is *realized* by a
machine state: claimed slots/cells are occupied, claimed budget is covered.
One set of terms — `cellCount`/`derivedCount` (T9) count the very cells the
`cell` claims own (charter L1 discipline, no parallel formalization).
-/

namespace Machines.Lnp64u.Logic

open Loom.Logic Machines.Lnp64u

/-- A µ resource: ownership claims over T9's conserved sorts. -/
structure Res where
  /-- Claimed memory words. -/
  mem : Addr → Prop
  /-- Claimed capability slots. -/
  slot : DomainId → Slot → Prop
  /-- Claimed lineage cells. -/
  cell : DomainId → LineageId → Prop
  /-- Claimed budget time, per domain (additive). -/
  budget : DomainId → Nat

namespace Res

/-- Two resources are disjoint when their location-like claims never
overlap (budget, being a quantity, always composes). -/
def Disj (a b : Res) : Prop :=
  (∀ w, ¬ (a.mem w ∧ b.mem w)) ∧
  (∀ d s, ¬ (a.slot d s ∧ b.slot d s)) ∧
  (∀ d l, ¬ (a.cell d l ∧ b.cell d l))

/-- Join of two (disjoint) resources. -/
def op (a b : Res) : Res where
  mem := fun w => a.mem w ∨ b.mem w
  slot := fun d s => a.slot d s ∨ b.slot d s
  cell := fun d l => a.cell d l ∨ b.cell d l
  budget := fun d => a.budget d + b.budget d

/-- The empty resource. -/
def unit : Res where
  mem := fun _ => False
  slot := fun _ _ => False
  cell := fun _ _ => False
  budget := fun _ => 0

theorem ext' {a b : Res} (hm : ∀ w, a.mem w ↔ b.mem w)
    (hs : ∀ d s, a.slot d s ↔ b.slot d s)
    (hc : ∀ d l, a.cell d l ↔ b.cell d l)
    (hb : ∀ d, a.budget d = b.budget d) : a = b := by
  cases a; cases b
  simp only [Res.mk.injEq]
  refine ⟨funext fun w => propext (hm w),
          funext fun d => funext fun s => propext (hs d s),
          funext fun d => funext fun l => propext (hc d l),
          funext hb⟩

end Res

/-- The µ resource algebra: the machine instance of the generic PCM. -/
def resPcm : Pcm Res where
  disj := Res.Disj
  op := Res.op
  unit := Res.unit
  disj_comm := by
    rintro a b ⟨hm, hs, hc⟩
    exact ⟨fun w h => hm w ⟨h.2, h.1⟩, fun d s h => hs d s ⟨h.2, h.1⟩,
           fun d l h => hc d l ⟨h.2, h.1⟩⟩
  op_comm := by
    rintro a b _
    exact Res.ext' (fun w => Or.comm) (fun d s => Or.comm) (fun d l => Or.comm)
      (fun d => Nat.add_comm _ _)
  unit_disj := fun a =>
    ⟨fun w h => h.1, fun d s h => h.1, fun d l h => h.1⟩
  unit_op := fun a =>
    Res.ext' (fun w => by simp [Res.op, Res.unit]) (fun d s => by simp [Res.op, Res.unit])
      (fun d l => by simp [Res.op, Res.unit]) (fun d => Nat.zero_add _)
  disj_assoc := by
    rintro a b c ⟨_, _, _⟩ ⟨hm₂, hs₂, hc₂⟩
    exact ⟨fun w h => hm₂ w ⟨Or.inr h.1, h.2⟩,
           fun d s h => hs₂ d s ⟨Or.inr h.1, h.2⟩,
           fun d l h => hc₂ d l ⟨Or.inr h.1, h.2⟩⟩
  disj_assoc' := by
    rintro a b c ⟨hm₁, hs₁, hc₁⟩ ⟨hm₂, hs₂, hc₂⟩
    refine ⟨fun w h => ?_, fun d s h => ?_, fun d l h => ?_⟩
    · rcases h.2 with hb | hcm
      · exact hm₁ w ⟨h.1, hb⟩
      · exact hm₂ w ⟨Or.inl h.1, hcm⟩
    · rcases h.2 with hb | hcm
      · exact hs₁ d s ⟨h.1, hb⟩
      · exact hs₂ d s ⟨Or.inl h.1, hcm⟩
    · rcases h.2 with hb | hcm
      · exact hc₁ d l ⟨h.1, hb⟩
      · exact hc₂ d l ⟨Or.inl h.1, hcm⟩
  op_assoc := by
    rintro a b c _ _
    exact Res.ext' (fun w => or_assoc) (fun d s => or_assoc) (fun d l => or_assoc)
      (fun d => Nat.add_assoc _ _ _)

/-- Realization: machine state `σ` covers resource `r` — every claimed slot
holds a capability, every claimed cell is occupied, and claimed budget does
not exceed the domain's actual budget. (Memory-word claims are pure
ownership marks at this layer; the points-to refinement arrives with the
logical relation.) -/
def interp (σ : MachineState) (r : Res) : Prop :=
  (∀ d s, r.slot d s → ((σ.doms d).caps s).isSome) ∧
  (∀ d l, r.cell d l → ((σ.doms d).lineage l).isSome) ∧
  (∀ d, r.budget d ≤ (σ.doms d).budget)

/-- Primitive assertions, in the generic `Prp` over the µ PCM. -/
def ownsSlot (d : DomainId) (s : Slot) : Pcm.Prp resPcm :=
  fun r => r.slot d s

def ownsCell (d : DomainId) (l : LineageId) : Pcm.Prp resPcm :=
  fun r => r.cell d l

def budgetAtLeast (d : DomainId) (n : Nat) : Pcm.Prp resPcm :=
  fun r => n ≤ r.budget d

/-- **The T9 bridge**: in a realized resource, the claimed cells of each
domain number at most `cellCount` — separation's disjointness *is* the
counting argument. Stated over a decidable claim set. -/
theorem claimed_le_cellCount (σ : MachineState) (r : Res) (h : interp σ r)
    (d : DomainId) [DecidablePred (r.cell d)] :
    (Finset.univ.filter (r.cell d)).card ≤ cellCount (σ.doms d) := by
  unfold cellCount
  apply Finset.card_le_card
  intro l hl
  rw [Finset.mem_filter] at hl ⊢
  exact ⟨hl.1, h.2.1 d l hl.2⟩

/-- Budget claims sum within the quota once `budget_bounded` holds: the
resource-level form of T9's budget conservation. -/
theorem budget_claim_le (σ : MachineState) (r : Res) (h : interp σ r)
    (m : Manifest) (hb : ∀ d, (σ.doms d).budget ≤ (m.doms d).budgetQ)
    (d : DomainId) : r.budget d ≤ (m.doms d).budgetQ :=
  Nat.le_trans (h.2.2 d) (hb d)

end Machines.Lnp64u.Logic
