-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Step
import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Logic.KernelLemmas

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
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_lineage (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).lineage = (σ.doms d).lineage := by
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_slotGen (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).slotGen = (σ.doms d).slotGen := by
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_regions (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).regions = (σ.doms d).regions := by
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_run (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).run = (σ.doms d).run := by
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_serving (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).serving = (σ.doms d).serving := by
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_gates (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).gates = σ.gates := by
  rfl

@[simp] theorem refillPhase_mover (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).mover = σ.mover := by
  rfl

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
      rfl]
    intro hfl; rw [refillPhase_run]; exact h.inflight_running fl hfl
  · intro g a; rw [refillPhase_gates]; exact h.gate_saved_none g a


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
  · intro g a; rw [moverPhase_gates]; exact h.gate_saved_none g a



/-- `Wf` does not mention the cycle counter, so bumping it is transparent. -/
theorem wf_setCycle (σ : MachineState) (c : BitVec 32) (h : Wf σ) :
    Wf { σ with cycle := c } := by
  obtain ⟨hdoms, hpl, hrb, hmw, hgs, hsg, hbg, hir, hgsn⟩ := h
  exact ⟨hdoms, hpl, hrb, hmw, hgs, hsg, hbg, hir, hgsn⟩

/-! ## A congruence lemma for `Wf`

`Wf` reads only a *skeleton* of the state: each domain's caps, lineage, slot
generations, regions, run-state, and serving mark; the gates' configs and
activation caller/depth; the mover; and inflight. A modification that
preserves the skeleton — charging budget, decrementing a donation counter,
or advancing an in-flight instruction's cycle count — preserves `Wf`. -/
theorem wf_of_skeleton (σ σ' : MachineState)
    (hcaps : ∀ d, (σ'.doms d).caps = (σ.doms d).caps)
    (hlin : ∀ d, (σ'.doms d).lineage = (σ.doms d).lineage)
    (hgen : ∀ d, (σ'.doms d).slotGen = (σ.doms d).slotGen)
    (hreg : ∀ d, (σ'.doms d).regions = (σ.doms d).regions)
    (hrun : ∀ d, (σ'.doms d).run = (σ.doms d).run)
    (hserv : ∀ d, (σ'.doms d).serving = (σ.doms d).serving)
    (hcfg : ∀ g, (σ'.gates g).config = (σ.gates g).config)
    (hact : ∀ g a', (σ'.gates g).act = some a' →
      ∃ a, (σ.gates g).act = some a ∧ a'.caller = a.caller ∧ a'.depth = a.depth ∧
           a'.savedServing = a.savedServing)
    (hactSome : ∀ g, ((σ.gates g).act).isSome → ((σ'.gates g).act).isSome)
    (hmover : σ'.mover = σ.mover)
    (hinf : ∀ fl, σ'.inflight = some fl → (σ'.doms fl.dom).run = .running)
    (h : Wf σ) : Wf σ' := by
  have hlive : ∀ r, σ'.liveRef r = σ.liveRef r := by
    intro r; unfold MachineState.liveRef DomainState.liveCap; rw [hcaps, hgen]
  have hparent : ∀ d s, σ'.parentOf d s = σ.parentOf d s := by
    intro d s; unfold MachineState.parentOf; rw [hcaps, hlin]
  constructor
  · intro d
    have hd := h.doms d
    exact ⟨fun s => hgen d ▸ hd.gen_pos s,
      fun s e l => by rw [hcaps, hlin]; exact hd.cell_backed s e l,
      fun s s' e e' l => by rw [hcaps]; exact hd.ptr_inj s s' e e' l,
      fun l => by rw [hlin, hcaps]; exact hd.cell_used l,
      fun s base len p => by rw [hcaps]; exact hd.wx s base len p,
      fun s e base len p => by rw [hcaps]; exact hd.bounds s e base len p⟩
  · intro d s p; rw [hparent, hlive]; exact h.parent_live d s p
  · intro d r rg; rw [hreg]; intro hrg
    obtain ⟨e, hl, hle⟩ := h.region_backed d r rg hrg
    refine ⟨e, ?_, hle⟩; unfold DomainState.liveCap; rw [hcaps, hgen]; exact hl
  · intro job; rw [hmover]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, by rw [hlive]; exact o3, by rw [hlive]; exact o4⟩
  · intro g a' ha'
    obtain ⟨a, ha, hcaller, hdepth, _⟩ := hact g a' ha'
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    exact ⟨by rw [hcfg, hserv]; exact s1, by rw [hcaller, hrun]; exact s2,
      hdepth ▸ s3, hdepth ▸ s4⟩
  · intro d g; rw [hserv]; intro hs
    obtain ⟨c1, c2⟩ := h.serving_gate d g hs
    exact ⟨by rw [hcfg]; exact c1, hactSome g c2⟩
  · intro d g; rw [hrun]; intro hb
    obtain ⟨a, ha, hc⟩ := h.blocked_gate d g hb
    have hsome : ((σ'.gates g).act).isSome := hactSome g (by rw [ha]; rfl)
    obtain ⟨a'', ha''⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨a0, ha0, hcaller0, _, _⟩ := hact g a'' ha''
    rw [ha0] at ha; cases ha
    exact ⟨a'', ha'', by rw [hcaller0]; exact hc⟩
  · exact hinf
  · intro g a' ha'
    obtain ⟨a, ha, _, _, hsaved⟩ := hact g a' ha'
    rw [hsaved]; exact h.gate_saved_none g a ha

/-- The `hact`/`hactSome` obligations of `wf_of_skeleton` when the gate map is
literally unchanged. -/
theorem wf_of_skeleton_sameGates (σ σ' : MachineState)
    (hcaps : ∀ d, (σ'.doms d).caps = (σ.doms d).caps)
    (hlin : ∀ d, (σ'.doms d).lineage = (σ.doms d).lineage)
    (hgen : ∀ d, (σ'.doms d).slotGen = (σ.doms d).slotGen)
    (hreg : ∀ d, (σ'.doms d).regions = (σ.doms d).regions)
    (hrun : ∀ d, (σ'.doms d).run = (σ.doms d).run)
    (hserv : ∀ d, (σ'.doms d).serving = (σ.doms d).serving)
    (hgates : σ'.gates = σ.gates) (hmover : σ'.mover = σ.mover)
    (hinf : ∀ fl, σ'.inflight = some fl → (σ'.doms fl.dom).run = .running)
    (h : Wf σ) : Wf σ' :=
  wf_of_skeleton σ σ' hcaps hlin hgen hreg hrun hserv
    (fun g => by rw [hgates]) (fun g a' hh => ⟨a', by rw [hgates] at hh; exact hh, rfl, rfl, rfl⟩)
    (fun g hh => by rw [hgates]; exact hh) hmover hinf h

/-- `haltBase` (halt a *running* domain, no unwind) preserves `Wf`: a running
domain is neither a gate's blocked caller nor another serving domain, so
setting its run to halted and clearing its (empty) serving mark is consistent.
Requires `inflight = none` (holds at every `haltWith` call site). -/
theorem haltBase_preserves_wf (σ : MachineState) (d : DomainId) (c : Loom.Word32)
    (h : Wf σ) (hrun : (σ.doms d).run = .running) (hserv : (σ.doms d).serving = none)
    (hinf : σ.inflight = none) : Wf (σ.haltBase d c) := by
  constructor
  · intro d'
    have hd := h.doms d'
    exact ⟨fun s => by rw [haltBase_slotGen]; exact hd.gen_pos s,
      fun s e l => by rw [haltBase_caps, haltBase_lineage]; exact hd.cell_backed s e l,
      fun s s' e e' l => by rw [haltBase_caps]; exact hd.ptr_inj s s' e e' l,
      fun l => by rw [haltBase_lineage, haltBase_caps]; exact hd.cell_used l,
      fun s base len p => by rw [haltBase_caps]; exact hd.wx s base len p,
      fun s e base len p => by rw [haltBase_caps]; exact hd.bounds s e base len p⟩
  · intro d' s p
    rw [show (σ.haltBase d c).parentOf d' s = σ.parentOf d' s from by
      unfold MachineState.parentOf; rw [haltBase_caps, haltBase_lineage]]
    rw [haltBase_liveRef]; exact h.parent_live d' s p
  · intro d' r rg; rw [haltBase_regions]; intro hrg
    obtain ⟨e, hl, hle⟩ := h.region_backed d' r rg hrg
    refine ⟨e, ?_, hle⟩; unfold DomainState.liveCap; rw [haltBase_caps, haltBase_slotGen]; exact hl
  · intro job; rw [haltBase_mover]; intro hj
    obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
    exact ⟨o1, o2, by rw [haltBase_liveRef]; exact o3, by rw [haltBase_liveRef]; exact o4⟩
  · intro g a; rw [haltBase_gates]; intro ha
    obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g a ha
    refine ⟨?_, ?_, s3, s4⟩
    · rw [haltBase_serving]
      -- callee of g is running (serving g); it is not d unless d serves g, but
      -- d.serving = none, so callee ≠ d
      have hne : (σ.gates g).config.callee ≠ d := by
        intro he; rw [he] at s1; rw [s1] at hserv; exact absurd hserv (by simp)
      simp [hne, s1]
    · rw [haltBase_run]
      -- a.caller is blocked g; d is running, so a.caller ≠ d
      have hne : a.caller ≠ d := by
        intro he; rw [he] at s2; rw [hrun] at s2; exact absurd s2 (by simp)
      simp [hne, s2]
  · intro d' g; rw [haltBase_serving]; intro hs
    by_cases hd : d' = d
    · rw [hd] at hs; simp at hs
    · rw [if_neg hd] at hs
      obtain ⟨c1, c2⟩ := h.serving_gate d' g hs
      rw [haltBase_gates]; exact ⟨c1, c2⟩
  · intro d' g; rw [haltBase_run]; intro hb
    by_cases hd : d' = d
    · rw [hd] at hb; simp at hb
    · rw [if_neg hd] at hb
      obtain ⟨a, ha, hc⟩ := h.blocked_gate d' g hb
      rw [haltBase_gates]; exact ⟨a, ha, hc⟩
  · intro fl; rw [haltBase_inflight, hinf]; simp
  · intro g a; rw [haltBase_gates]; exact h.gate_saved_none g a

/-- Halting a *running* domain (with the gate-activation unwind) preserves
the invariant, for any cause word. -/
theorem haltDom_preserves_wf (σ : MachineState) (d : DomainId) (c : Loom.Word32)
    (h : Wf σ) (hrun : (σ.doms d).run = .running) (hinf : σ.inflight = none) :
    Wf (σ.haltDom d c) := by
  cases hserv : (σ.doms d).serving with
  | none =>
      rw [haltDom_base σ d _ hserv]
      exact haltBase_preserves_wf σ d _ h hrun hserv hinf
  | some g =>
      cases hact : (σ.gates g).act with
      | none =>
          exact absurd (h.serving_gate d g hserv).2 (by rw [hact]; simp)
      | some a =>
          rw [haltDom_unwind σ d _ g a hserv hact]
          -- unwind: free gate g, resume a.caller. Facts from Wf:
          have hcallee : (σ.gates g).config.callee = d := (h.serving_gate d g hserv).1
          have hgs := h.gate_serving g a hact
          have hcaller_blk : (σ.doms a.caller).run = .blocked g := hgs.2.1
          have hcaller_ne_d : a.caller ≠ d := by
            intro he; rw [he, hrun] at hcaller_blk; exact absurd hcaller_blk (by simp)
          -- structural projections of the result state
          set σ' := (σ.haltBase d (c)).unwindGate g a.caller a.callerRd
            with hσ'
          have hcaps : ∀ d', (σ'.doms d').caps = (σ.doms d').caps := by
            intro d'; rw [hσ']; simp
          have hlin : ∀ d', (σ'.doms d').lineage = (σ.doms d').lineage := by
            intro d'; rw [hσ']; simp
          have hgen : ∀ d', (σ'.doms d').slotGen = (σ.doms d').slotGen := by
            intro d'; rw [hσ']; simp
          have hreg : ∀ d', (σ'.doms d').regions = (σ.doms d').regions := by
            intro d'; rw [hσ']; simp
          have hlive : ∀ r, σ'.liveRef r = σ.liveRef r := by intro r; rw [hσ']; simp
          have hmov : σ'.mover = σ.mover := by rw [hσ']; simp
          have hcfg : ∀ g', (σ'.gates g').config = (σ.gates g').config := by
            intro g'; rw [hσ']; simp
          have hrunv : ∀ d', (σ'.doms d').run =
              if d' = a.caller then .running else if d' = d then .halted else (σ.doms d').run := by
            intro d'; rw [hσ']; simp
          have hservv : ∀ d', (σ'.doms d').serving =
              if d' = d then none else (σ.doms d').serving := by
            intro d'; rw [hσ']; simp
          have hactv : ∀ g', (σ'.gates g').act =
              if g' = g then none else (σ.gates g').act := by intro g'; rw [hσ']; simp
          have hinfv : σ'.inflight = none := by rw [hσ']; simp [hinf]
          -- now assemble Wf σ'
          constructor
          · intro d'
            have hd := h.doms d'
            exact ⟨fun s => by rw [hgen]; exact hd.gen_pos s,
              fun s e l => by rw [hcaps, hlin]; exact hd.cell_backed s e l,
              fun s s' e e' l => by rw [hcaps]; exact hd.ptr_inj s s' e e' l,
              fun l => by rw [hlin, hcaps]; exact hd.cell_used l,
              fun s base len p => by rw [hcaps]; exact hd.wx s base len p,
              fun s e base len p => by rw [hcaps]; exact hd.bounds s e base len p⟩
          · intro d' s p
            rw [show σ'.parentOf d' s = σ.parentOf d' s from by
              unfold MachineState.parentOf; rw [hcaps, hlin]]
            rw [hlive]; exact h.parent_live d' s p
          · intro d' r rg; rw [hreg]; intro hrg
            obtain ⟨e, hl, hle⟩ := h.region_backed d' r rg hrg
            refine ⟨e, ?_, hle⟩; unfold DomainState.liveCap; rw [hcaps, hgen]; exact hl
          · intro job; rw [hmov]; intro hj
            obtain ⟨o1, o2, o3, o4⟩ := h.mover_wf job hj
            exact ⟨o1, o2, by rw [hlive]; exact o3, by rw [hlive]; exact o4⟩
          · intro g' a' ha'
            rw [hactv] at ha'
            by_cases hgg : g' = g
            · rw [if_pos hgg] at ha'; exact absurd ha' (by simp)
            · rw [if_neg hgg] at ha'
              obtain ⟨s1, s2, s3, s4⟩ := h.gate_serving g' a' ha'
              refine ⟨?_, ?_, s3, s4⟩
              · rw [hcfg, hservv]
                have hne : (σ.gates g').config.callee ≠ d := by
                  intro he; rw [he] at s1; rw [hserv] at s1
                  exact hgg (by injection s1 with hh; exact hh.symm)
                rw [if_neg hne]; exact s1
              · rw [hrunv]
                have hne1 : a'.caller ≠ a.caller := by
                  intro he; rw [he, hcaller_blk] at s2
                  exact hgg (by injection s2 with hh; exact hh.symm)
                have hne2 : a'.caller ≠ d := by
                  intro he; rw [he, hrun] at s2; exact absurd s2 (by simp)
                rw [if_neg hne1, if_neg hne2]; exact s2
          · intro d' g'; rw [hservv]; intro hs
            by_cases hd : d' = d
            · rw [if_pos hd] at hs; exact absurd hs (by simp)
            · rw [if_neg hd] at hs
              obtain ⟨c1, c2⟩ := h.serving_gate d' g' hs
              rw [hcfg, hactv]
              have hne : g' ≠ g := by
                intro he; subst he; rw [hcallee] at c1; exact hd c1.symm
              rw [if_neg hne]; exact ⟨c1, c2⟩
          · intro d' g'; rw [hrunv]; intro hb
            by_cases h1 : d' = a.caller
            · rw [if_pos h1] at hb; exact absurd hb (by simp)
            · rw [if_neg h1] at hb
              by_cases h2 : d' = d
              · rw [if_pos h2] at hb; exact absurd hb (by simp)
              · rw [if_neg h2] at hb
                obtain ⟨a0, ha0, hc0⟩ := h.blocked_gate d' g' hb
                rw [hactv]
                have hne : g' ≠ g := by
                  intro he; subst he; rw [hact] at ha0
                  injection ha0 with hh; rw [← hh] at hc0; exact h1 hc0.symm
                rw [if_neg hne]; exact ⟨a0, ha0, hc0⟩
          · intro fl; rw [hinfv]; simp
          · intro g' a' ha'; rw [hactv] at ha'
            by_cases hgg : g' = g
            · rw [if_pos hgg] at ha'; simp at ha'
            · rw [if_neg hgg] at ha'; exact h.gate_saved_none g' a' ha'


/-- Halting a domain with a fault preserves the invariant (the `step_wf`
fault-path corollary of `haltDom_preserves_wf`). -/
theorem haltWith_preserves_wf (σ : MachineState) (d : DomainId) (f : Fault)
    (h : Wf σ) (hrun : (σ.doms d).run = .running) (hinf : σ.inflight = none) :
    Wf (haltWith σ d f) :=
  haltDom_preserves_wf σ d (BitVec.ofNat 32 f.code) h hrun hinf
/-- Updating a domain's registers preserves `Wf` — `regs` is not read by `Wf`. -/
theorem wf_setReg (σ : MachineState) (d : DomainId) (r : RegId) (v : Loom.Word32)
    (h : Wf σ) :
    Wf (σ.setDom d (fun ds => ds.setReg r v)) := by
  have hproj : ∀ (d' : DomainId),
      (((σ.setDom d (fun ds => ds.setReg r v)).doms d').caps = (σ.doms d').caps) ∧
      (((σ.setDom d (fun ds => ds.setReg r v)).doms d').lineage = (σ.doms d').lineage) ∧
      (((σ.setDom d (fun ds => ds.setReg r v)).doms d').slotGen = (σ.doms d').slotGen) ∧
      (((σ.setDom d (fun ds => ds.setReg r v)).doms d').regions = (σ.doms d').regions) ∧
      (((σ.setDom d (fun ds => ds.setReg r v)).doms d').run = (σ.doms d').run) ∧
      (((σ.setDom d (fun ds => ds.setReg r v)).doms d').serving = (σ.doms d').serving) := by
    intro d'; unfold MachineState.setDom
    by_cases hp : d' = d
    · subst hp; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ hp]
  refine wf_of_skeleton_sameGates σ _
    (fun d' => (hproj d').1) (fun d' => (hproj d').2.1) (fun d' => (hproj d').2.2.1)
    (fun d' => (hproj d').2.2.2.1) (fun d' => (hproj d').2.2.2.2.1) (fun d' => (hproj d').2.2.2.2.2)
    rfl rfl ?_ h
  intro fl' hfl'
  have hinfeq : (σ.setDom d (fun ds => ds.setReg r v)).inflight = σ.inflight := rfl
  rw [hinfeq] at hfl'
  rw [(hproj fl'.dom).2.2.2.2.1]; exact h.inflight_running fl' hfl'

/-- The single remaining Phase-1 obligation, stated cleanly: every
instruction's semantics preserves the machine invariant. This is the
per-opcode security argument (25 ops × the capability-kernel operations) —
the irreducible core. Once proved, `retire_preserves_wf`, `wf_invariant`, and
the crown-jewel theorems that rest on the invariant all close. -/
def ExecPreservesWf : Prop :=
  ∀ (instr : Instr), instr ∈ isa → ∀ (c : Ctx) (σ : MachineState),
    Wf σ → (σ.doms c.d).run = .running → σ.inflight = none →
    (∀ a σ', instr.sem.exec c σ = .ok a σ' → Wf σ') ∧
    (∀ e σ', instr.sem.exec c σ = .err e σ' → Wf σ')

/-- `retire` preserves `Wf`, reduced to `ExecPreservesWf`. The decode-failure
and fault paths go through the proved `haltWith_preserves_wf`; the pc bump and
errno write preserve the skeleton; the instruction effect is `ExecPreservesWf`.
Requires `d` running (true at the call site: retirement acts on the domain that
was scheduled and in flight). -/
theorem retire_preserves_wf (hexec : ExecPreservesWf) (σ : MachineState)
    (d : DomainId) (w : Loom.Word32) (h : Wf σ) (hdrun : (σ.doms d).run = .running)
    (hinf : σ.inflight = none) : Wf (retire σ d w) := by
  unfold retire
  split
  · exact haltWith_preserves_wf σ d .illegalInstruction h hdrun hinf
  · rename_i instr hdec
    -- σ₁ = advance pc; preserves Wf, d still running, inflight none
    have hpcproj : ∀ (d' : DomainId),
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').caps = (σ.doms d').caps) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').lineage = (σ.doms d').lineage) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').slotGen = (σ.doms d').slotGen) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').regions = (σ.doms d').regions) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').run = (σ.doms d').run) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').serving = (σ.doms d').serving) := by
      intro d'; unfold MachineState.setDom
      by_cases hp : d' = d
      · subst hp; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hp]
    set σ1 := σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }) with hσ1
    have hσ1wf : Wf σ1 := by
      refine wf_of_skeleton_sameGates σ σ1
        (fun d' => (hpcproj d').1) (fun d' => (hpcproj d').2.1) (fun d' => (hpcproj d').2.2.1)
        (fun d' => (hpcproj d').2.2.2.1) (fun d' => (hpcproj d').2.2.2.2.1)
        (fun d' => (hpcproj d').2.2.2.2.2) rfl rfl ?_ h
      intro fl' hfl'; rw [show σ1.inflight = σ.inflight from rfl, hinf] at hfl'
      exact absurd hfl' (by simp)
    have hσ1run : (σ1.doms d).run = .running := by rw [(hpcproj d).2.2.2.2.1]; exact hdrun
    have hσ1inf : σ1.inflight = none := hinf
    have hmem : instr ∈ isa := Loom.Isa.decode_mem isa hdec
    obtain ⟨hok, herr⟩ := hexec instr hmem { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      σ1 hσ1wf hσ1run hσ1inf
    show Wf (match instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
      | .ok _ σ' => σ'
      | .err e σ' => σ'.setDom d (fun ds => ds.setReg (operandsOf w).rd e.toWord)
      | .fault f => haltWith σ d f)
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
    | ok a σ' => simp only [hexr]; exact hok a σ' hexr
    | err e σ' => simp only [hexr]; exact wf_setReg σ' d (operandsOf w).rd e.toWord (herr e σ' hexr)
    | fault f => simp only [hexr]; exact haltWith_preserves_wf σ d f h hdrun hinf

/-- The scheduler returns a running domain. -/
theorem schedule_running (m : Manifest) (σ : MachineState) (d : DomainId)
    (h : schedule m σ = some d) : (σ.doms d).run = .running := by
  unfold schedule at h
  set L := (List.finRange numDomains).filter (fun d =>
    decide ((σ.doms d).run = .running) && decide (0 < (σ.doms (σ.payer d)).budget)) with hL
  have hmem : ∀ (l : List DomainId) (init : Option DomainId),
      (l.foldl (fun best d => match best with
        | none => some d
        | some b => if (m.doms b).priority < (m.doms d).priority then some d else some b) init)
        = some d → d ∈ l ∨ init = some d := by
    intro l
    induction l with
    | nil => intro init hh; exact Or.inr hh
    | cons x rest ih =>
        intro init hh
        rcases ih _ hh with hin | hinit
        · exact Or.inl (List.mem_cons_of_mem _ hin)
        · cases init with
          | none =>
              simp only [Option.some.injEq] at hinit
              exact Or.inl (hinit ▸ List.mem_cons_self ..)
          | some b =>
              by_cases hp : (m.doms b).priority < (m.doms x).priority
              · simp only [hp, if_true, Option.some.injEq] at hinit
                exact Or.inl (hinit ▸ List.mem_cons_self ..)
              · simp only [hp, if_false] at hinit
                exact Or.inr hinit
  rcases hmem L none h with hin | hcontra
  · rw [hL, List.mem_filter] at hin
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    exact hin.2.1
  · exact absurd hcontra (by simp)

/-- Charging a domain's budget preserves every skeleton projection. -/
theorem setBudget_proj (σ : MachineState) (p : DomainId) (bf : DomainState → Nat) :
    let σ0 := σ.setDom p (fun ds => { ds with budget := bf ds })
    (∀ d, (σ0.doms d).caps = (σ.doms d).caps) ∧
    (∀ d, (σ0.doms d).lineage = (σ.doms d).lineage) ∧
    (∀ d, (σ0.doms d).slotGen = (σ.doms d).slotGen) ∧
    (∀ d, (σ0.doms d).regions = (σ.doms d).regions) ∧
    (∀ d, (σ0.doms d).run = (σ.doms d).run) ∧
    (∀ d, (σ0.doms d).serving = (σ.doms d).serving) ∧
    (σ0.gates = σ.gates) ∧ (σ0.mover = σ.mover) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;>
    (intro d; unfold MachineState.setDom
     by_cases hp : d = p
     · subst hp; simp [Loom.Fun.update_same]
     · simp [Loom.Fun.update_ne _ _ _ _ hp])

/-- Setting an in-flight instruction whose domain is running, on a state that
otherwise preserves the skeleton, preserves `Wf`. Used by the issue path. -/
theorem wf_setInflight (σ σ0 : MachineState) (fl : InFlight)
    (hcaps : ∀ d, (σ0.doms d).caps = (σ.doms d).caps)
    (hlin : ∀ d, (σ0.doms d).lineage = (σ.doms d).lineage)
    (hgen : ∀ d, (σ0.doms d).slotGen = (σ.doms d).slotGen)
    (hreg : ∀ d, (σ0.doms d).regions = (σ.doms d).regions)
    (hrun : ∀ d, (σ0.doms d).run = (σ.doms d).run)
    (hserv : ∀ d, (σ0.doms d).serving = (σ.doms d).serving)
    (hcfg : ∀ g, (σ0.gates g).config = (σ.gates g).config)
    (hact : ∀ g a', (σ0.gates g).act = some a' →
      ∃ a, (σ.gates g).act = some a ∧ a'.caller = a.caller ∧ a'.depth = a.depth ∧
           a'.savedServing = a.savedServing)
    (hactSome : ∀ g, ((σ.gates g).act).isSome → ((σ0.gates g).act).isSome)
    (hmover : σ0.mover = σ.mover)
    (hflrun : (σ0.doms fl.dom).run = .running)
    (h : Wf σ) : Wf { σ0 with inflight := some fl } := by
  refine wf_of_skeleton σ { σ0 with inflight := some fl }
    hcaps hlin hgen hreg hrun hserv hcfg hact hactSome hmover ?_ h
  intro fl' hfl'
  have hfe : fl' = fl := (by simpa using hfl' : fl = fl').symm
  subst hfe; exact hflrun

/-- The core phase preserves `Wf`. The countdown, budget-charge, and stall
paths preserve the skeleton (via `wf_of_skeleton`); the fault paths delegate
to `haltWith_preserves_wf`, and retirement to `retire_preserves_wf`. The
inflight-countdown and stall paths are discharged here; the full assembly of
the issue path's donation sub-cases is in progress. -/
theorem corePhase_preserves_wf (hexec : ExecPreservesWf) (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (h : Wf σ) : Wf (corePhase m σ) := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · simp only [hc, if_true]
        refine retire_preserves_wf hexec { σ with inflight := none } fl.dom fl.word ?_ ?_ rfl
        · exact wf_of_skeleton_sameGates σ { σ with inflight := none }
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) rfl rfl (by simp) h
        · show (σ.doms fl.dom).run = .running
          exact h.inflight_running fl hinf
      · simp only [hc, if_false]
        refine wf_of_skeleton_sameGates σ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl ?_ h
        intro fl' hfl'
        have hdom : fl'.dom = fl.dom := by
          simp only [Option.some.injEq] at hfl'; exact hfl' ▸ rfl
        rw [hdom]; exact h.inflight_running fl hinf
  | none =>
      simp only []
      split
      · exact h
      · rename_i d hsched
        have hdrun : (σ.doms d).run = .running := schedule_running m σ d hsched
        split
        · exact haltWith_preserves_wf σ d .memoryAuthority h hdrun hinf
        · rename_i w hfetch
          split
          · exact haltWith_preserves_wf σ d .illegalInstruction h hdrun hinf
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              obtain ⟨pc, pl, pg, pr, pru, ps, pgates, pmov⟩ :=
                setBudget_proj σ (σ.payer d) (fun ds => ds.budget - instr.cost.cost)
              cases hserv : (σ.doms d).serving with
              | none =>
                  simp only [hserv]
                  refine wf_setInflight σ (σ.setDom (σ.payer d) (fun ds => { ds with budget := ds.budget - instr.cost.cost }))
                    (⟨d, w, instr.cost.cost⟩ : InFlight) pc pl pg pr pru ps
                    (fun g => by rw [pgates]) (fun g a' ha' => ⟨a', by rw [pgates] at ha'; exact ha', rfl, rfl, rfl⟩)
                    (fun g hh => by rw [pgates]; exact hh) pmov ?_ h
                  rw [pru]; exact hdrun
              | some g =>
                  simp only [hserv]
                  cases hact : (σ.gates g).act with
                  | none => exact haltWith_preserves_wf σ d .protocol h hdrun hinf
                  | some a =>
                      simp only [hact]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        set sb := σ.setDom (σ.payer d)
                          (fun ds => { ds with budget := ds.budget - instr.cost.cost }) with hsb
                        have hg0 : sb.gates = σ.gates := pgates
                        set gv : GateState :=
                          { (sb.gates g) with act := some { a with donated := a.donated - instr.cost.cost } }
                          with hgv
                        refine wf_setInflight σ
                          { sb with gates := Loom.Fun.update sb.gates g gv }
                          (⟨d, w, instr.cost.cost⟩ : InFlight) pc pl pg pr pru ps ?_ ?_ ?_ pmov ?_ h
                        · intro g'
                          show (Loom.Fun.update sb.gates g gv g').config = (σ.gates g').config
                          by_cases hg : g' = g
                          · subst hg; simp only [Loom.Fun.update_same, hgv, hg0]
                          · simp only [Loom.Fun.update_ne _ _ _ _ hg, hg0]
                        · intro g' a' ha'
                          simp only at ha'
                          show ∃ a0, (σ.gates g').act = some a0 ∧ _ ∧ _
                          by_cases hg : g' = g
                          · subst hg
                            rw [Loom.Fun.update_same, hgv] at ha'
                            injection ha' with haa; subst haa
                            exact ⟨a, hact, rfl, rfl, rfl⟩
                          · rw [Loom.Fun.update_ne _ _ _ _ hg, hg0] at ha'
                            exact ⟨a', ha', rfl, rfl, rfl⟩
                        · intro g' hh
                          show ((Loom.Fun.update sb.gates g gv g').act).isSome
                          by_cases hg : g' = g
                          · subst hg; simp only [Loom.Fun.update_same, hgv, Option.isSome_some]
                          · rw [Loom.Fun.update_ne _ _ _ _ hg, hg0]; exact hh
                        · rw [pru]; exact hdrun
                      · simp only [hdon, if_false]
                        exact haltWith_preserves_wf σ d .budget h hdrun hinf
            · simp only [hbud, if_false]; exact h
end Machines.Lnp64u
