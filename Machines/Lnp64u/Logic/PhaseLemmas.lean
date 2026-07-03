import Machines.Lnp64u.Step
import Machines.Lnp64u.Logic.Wf

/-!
# Phase-structure lemmas (L1 support for `step_wf`)

`step` is `refillPhase` then `corePhase` then `moverPhase`. The refill and
Mover phases touch only budgets and memory/Mover state — never capability
tables, lineage, regions, or gate records — so all of `Wf`'s structural
obligations reduce to the core phase (which reduces further to instruction
retirement). These lemmas isolate that, turning the `step_wf` proof into a
per-instruction argument rather than a whole-cycle one.
-/

namespace Machines.Lnp64u

open Loom

/-! ## refillPhase preserves everything structural -/

@[simp] theorem refillPhase_caps (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).caps = (σ.doms d).caps := by
  unfold refillPhase; split <;> [rfl; (simp only; split <;> rfl)]

@[simp] theorem refillPhase_lineage (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).lineage = (σ.doms d).lineage := by
  unfold refillPhase; split <;> [rfl; (simp only; split <;> rfl)]

@[simp] theorem refillPhase_slotGen (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).slotGen = (σ.doms d).slotGen := by
  unfold refillPhase; split <;> [rfl; (simp only; split <;> rfl)]

@[simp] theorem refillPhase_regions (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).regions = (σ.doms d).regions := by
  unfold refillPhase; split <;> [rfl; (simp only; split <;> rfl)]

@[simp] theorem refillPhase_run (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).run = (σ.doms d).run := by
  unfold refillPhase; split <;> [rfl; (simp only; split <;> rfl)]

@[simp] theorem refillPhase_serving (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).serving = (σ.doms d).serving := by
  unfold refillPhase; split <;> [rfl; (simp only; split <;> rfl)]

@[simp] theorem refillPhase_gates (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).gates = σ.gates := by
  unfold refillPhase; split <;> rfl

@[simp] theorem refillPhase_mover (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).mover = σ.mover := by
  unfold refillPhase; split <;> rfl

/-- The Mover reference-liveness test only reads caps/slotGen, which refill
preserves, so `liveRef` is unchanged. -/
@[simp] theorem refillPhase_liveRef (m : Manifest) (σ : MachineState) (r : CapRef) :
    (refillPhase m σ).liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap
  rw [refillPhase_caps, refillPhase_slotGen]

/-- Consequently refill preserves the whole structural invariant. Only the
budget bound (T9) — not part of `Wf` — is affected by refill, and it is
re-established because budgets are reset to the manifest quota. -/
theorem refillPhase_preserves_wf (m : Manifest) (σ : MachineState) (h : Wf σ) :
    Wf (refillPhase m σ) := by
  constructor
  · intro d
    have hd := h.doms d
    constructor
    · intro s; rw [refillPhase_slotGen]; exact hd.gen_pos s
    · intro s e l; rw [refillPhase_caps, refillPhase_lineage]; exact hd.cell_backed s e l
    · intro s s' e e' l; rw [refillPhase_caps]
      exact hd.ptr_inj s s' e e' l
    · intro l; rw [refillPhase_lineage]
      intro hl; obtain ⟨s, e, hc, he⟩ := hd.cell_used l hl
      exact ⟨s, e, by rw [refillPhase_caps]; exact hc, he⟩
    · intro s base len p; rw [refillPhase_caps]; exact hd.wx s base len p
    · intro s e base len p; rw [refillPhase_caps]; exact hd.bounds s e base len p
  · intro d s p
    rw [show (refillPhase m σ).parentOf d s = σ.parentOf d s from by
      unfold MachineState.parentOf; rw [refillPhase_caps, refillPhase_lineage]]
    rw [refillPhase_liveRef]; exact h.parent_live d s p
  · intro d r rg; rw [refillPhase_regions]
    intro hrg
    obtain ⟨e, hlive, hle⟩ := h.region_backed d r rg hrg
    exact ⟨e, by rw [show ((refillPhase m σ).doms rg.backing.dom).liveCap
      rg.backing.slot rg.backing.gen = (σ.doms rg.backing.dom).liveCap
      rg.backing.slot rg.backing.gen from by
        unfold DomainState.liveCap; rw [refillPhase_caps, refillPhase_slotGen]]; exact hlive, hle⟩
  · intro job; rw [refillPhase_mover]; intro hj
    obtain ⟨h1, h2, h3, h4⟩ := h.mover_wf job hj
    exact ⟨h1, h2, by rw [refillPhase_liveRef]; exact h3, by rw [refillPhase_liveRef]; exact h4⟩
  · intro g a; rw [refillPhase_gates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    refine ⟨?_, ?_, s3, s4⟩
    · rw [refillPhase_serving]; exact s1
    · rw [refillPhase_run]; exact s2
  · intro d g; rw [refillPhase_serving, refillPhase_gates]; intro hs
    exact h.serving_gate d g hs
  · intro d g; rw [refillPhase_run, refillPhase_gates]; intro hb
    exact h.blocked_gate d g hb
  · intro fl; rw [show (refillPhase m σ).inflight = σ.inflight from by
      unfold refillPhase; split <;> rfl]
    intro hfl; rw [refillPhase_run]; exact h.inflight_running fl hfl

end Machines.Lnp64u
