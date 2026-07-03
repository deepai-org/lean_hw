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


/-! ## moverPhase preserves everything structural

The Mover phase writes only memory and the `mover` field; it never touches
any domain's caps/lineage/regions, the gate records, or the in-flight
instruction. So every `Wf` obligation except `mover_wf` is immediate, and
`mover_wf` survives because a continued job keeps the same source and
destination references. -/

private theorem write_doms (σ : MachineState) (a : Addr) (v : Loom.Word32) :
    (σ.write a v).doms = σ.doms := rfl

@[simp] theorem moverStatus_doms (σ : MachineState) (job : MoverJob) (v : Loom.Word32) :
    (moverStatus σ job v).doms = σ.doms := by
  unfold moverStatus; split <;> rfl

@[simp] theorem moverStatus_gates (σ : MachineState) (job : MoverJob) (v : Loom.Word32) :
    (moverStatus σ job v).gates = σ.gates := by
  unfold moverStatus; split <;> rfl

@[simp] theorem moverStatus_inflight (σ : MachineState) (job : MoverJob) (v : Loom.Word32) :
    (moverStatus σ job v).inflight = σ.inflight := by
  unfold moverStatus; split <;> rfl

@[simp] theorem moverStatus_mover (σ : MachineState) (job : MoverJob) (v : Loom.Word32) :
    (moverStatus σ job v).mover = σ.mover := by
  unfold moverStatus; split <;> rfl

@[simp] theorem moverPhase_doms (σ : MachineState) : (moverPhase σ).doms = σ.doms := by
  unfold moverPhase
  cases σ.mover with
  | none => rfl
  | some job =>
      by_cases h0 : job.remaining = 0
      · simp [h0, moverStatus_doms]
      · by_cases hc : moverCheck σ job.src job.srcCur { r := true, w := false, x := false } &&
                      moverCheck σ job.dst job.dstCur { r := false, w := true, x := false }
        · simp only [h0, if_false, hc, if_true]
          by_cases h1 : (job.remaining - 1) = 0
          · simp [h1, moverStatus_doms, write_doms, MachineState.write]
          · simp [h1, MachineState.write]
        · simp [h0, hc, moverStatus_doms]

@[simp] theorem moverPhase_gates (σ : MachineState) : (moverPhase σ).gates = σ.gates := by
  unfold moverPhase
  cases σ.mover with
  | none => rfl
  | some job =>
      by_cases h0 : job.remaining = 0
      · simp [h0, moverStatus_gates]
      · by_cases hc : moverCheck σ job.src job.srcCur { r := true, w := false, x := false } &&
                      moverCheck σ job.dst job.dstCur { r := false, w := true, x := false }
        · simp only [h0, if_false, hc, if_true]
          by_cases h1 : (job.remaining - 1) = 0
          · simp [h1, moverStatus_gates, MachineState.write]
          · simp [h1, MachineState.write]
        · simp [h0, hc, moverStatus_gates]

@[simp] theorem moverPhase_inflight (σ : MachineState) :
    (moverPhase σ).inflight = σ.inflight := by
  unfold moverPhase
  cases σ.mover with
  | none => rfl
  | some job =>
      by_cases h0 : job.remaining = 0
      · simp [h0, moverStatus_inflight]
      · by_cases hc : moverCheck σ job.src job.srcCur { r := true, w := false, x := false } &&
                      moverCheck σ job.dst job.dstCur { r := false, w := true, x := false }
        · simp only [h0, if_false, hc, if_true]
          by_cases h1 : (job.remaining - 1) = 0
          · simp [h1, moverStatus_inflight, MachineState.write]
          · simp [h1, MachineState.write]
        · simp [h0, hc, moverStatus_inflight]

@[simp] theorem moverPhase_liveRef (σ : MachineState) (r : CapRef) :
    (moverPhase σ).liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap; rw [moverPhase_doms]

/-- The Mover phase leaves the `mover` field either empty or holding a job
with the same owner, source, and destination references as before. -/
theorem moverPhase_mover (σ : MachineState) :
    (moverPhase σ).mover = none ∨
    ∃ job job', σ.mover = some job ∧ (moverPhase σ).mover = some job' ∧
      job'.owner = job.owner ∧ job'.src = job.src ∧ job'.dst = job.dst := by
  unfold moverPhase
  cases hm : σ.mover with
  | none => left; simp [hm]
  | some job =>
      by_cases h0 : job.remaining = 0
      · left; simp [h0]
      · by_cases hchk : moverCheck σ job.src job.srcCur { r := true, w := false, x := false } &&
                        moverCheck σ job.dst job.dstCur { r := false, w := true, x := false }
        · simp only [h0, if_false, hchk, if_true]
          by_cases h1 : (job.remaining - 1) = 0
          · left; simp [h1]
          · right
            exact ⟨job,
              { owner := job.owner, src := job.src, dst := job.dst
                srcCur := job.srcCur + 1, dstCur := job.dstCur + 1
                remaining := job.remaining - 1, statusAddr := job.statusAddr },
              rfl, by simp [h1], rfl, rfl, rfl⟩
        · left; simp [h0, hchk]

/-- The Mover phase preserves the structural invariant. -/
theorem moverPhase_preserves_wf (σ : MachineState) (h : Wf σ) :
    Wf (moverPhase σ) := by
  have hd := moverPhase_doms σ
  constructor
  · intro d; rw [hd]; exact h.doms d
  · intro d s p
    rw [show (moverPhase σ).parentOf d s = σ.parentOf d s from by
      unfold MachineState.parentOf; rw [hd]]
    rw [moverPhase_liveRef]; exact h.parent_live d s p
  · intro d r rg; rw [hd]; intro hrg
    obtain ⟨e, hlive, hle⟩ := h.region_backed d r rg hrg
    exact ⟨e, hlive, hle⟩
  · intro job hj
    rcases moverPhase_mover σ with hnone | ⟨job0, job', hm0, hm', ho, hs, hdst⟩
    · rw [hnone] at hj; exact absurd hj (by simp)
    · rw [hm'] at hj; cases hj
      obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job0 hm0
      refine ⟨by rw [hs, ho]; exact o1, by rw [hdst, ho]; exact o2, ?_, ?_⟩
      · rw [hs, moverPhase_liveRef]; exact o3
      · rw [hdst, moverPhase_liveRef]; exact o4
  · intro g a; rw [moverPhase_gates, hd]; exact h.gate_serving g a
  · intro d g; rw [hd, moverPhase_gates]; exact h.serving_gate d g
  · intro d g; rw [hd, moverPhase_gates]; exact h.blocked_gate d g
  · intro fl; rw [moverPhase_inflight, hd]; exact h.inflight_running fl


/-- `Wf` does not mention the cycle counter, so bumping it is transparent. -/
theorem wf_setCycle (σ : MachineState) (c : Nat) (h : Wf σ) :
    Wf { σ with cycle := c } := by
  -- doms, gates, mover, inflight are unchanged; every field of Wf reads only these
  obtain ⟨hdoms, hpl, hrb, hmw, hgs, hsg, hbg, hir⟩ := h
  exact ⟨hdoms, hpl, hrb, hmw, hgs, hsg, hbg, hir⟩

/-- The remaining `step_wf` obligation: the core phase (fetch, decode, budget
charge, and — on retirement — the instruction's effect via the kernel
functions) preserves the structural invariant. This is the per-instruction
argument (25 opcodes × the kernel operations), the core of the Phase-1 proof
effort; the two surrounding phases are already discharged
(`refillPhase_preserves_wf`, `moverPhase_preserves_wf`). -/
theorem corePhase_preserves_wf (m : Manifest) (hwf : m.WF) (σ : MachineState)
    (h : Wf σ) : Wf (corePhase m σ) := by
  sorry

end Machines.Lnp64u
