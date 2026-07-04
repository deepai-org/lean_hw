-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Logic.SlotGen
import Machines.Lnp64u.Logic.Tombstone

/-!
# T3 — Temporal safety, machine-wide (spec level)

The crown jewel: after `cap_revoke` retires, no agent — core via any region
register, Mover mid-transfer — accesses under any descendant; and
generation retirement is permanent (no resurrection). The RTL cycle-bound
form (T3′) lands in Phase 3 through the refinement.
-/

namespace Machines.Lnp64u.Theorems.T3

open Machines.Lnp64u Loom

/-- Slot generations never decrease (saturating bump only). -/
theorem gen_monotone (m : Manifest) (σ : MachineState) (d : DomainId) (s : Slot) :
    ((σ.doms d).slotGen s).toNat ≤ (((step m σ).doms d).slotGen s).toNat :=
  Wip.step_slotGen_ge m σ d s

/-- Generation monotonicity extends to any number of cycles. -/
theorem gen_monotone_n (m : Manifest) (σ : MachineState) (d : DomainId) (s : Slot) :
    ∀ n, ((σ.doms d).slotGen s).toNat ≤ (((stepN m n σ).doms d).slotGen s).toNat := by
  intro n
  induction n generalizing σ with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      calc ((σ.doms d).slotGen s).toNat
          ≤ (((step m σ).doms d).slotGen s).toNat := gen_monotone m σ d s
        _ ≤ (((stepN m k (step m σ)).doms d).slotGen s).toNat := ih (step m σ)

/-- **No resurrection.** A dead reference stays dead: once a slot's
generation has moved strictly past a reference's, no future state revives
it. Follows from generation monotonicity: `liveRef` requires the slot's
current generation to equal the reference's, which monotonicity forbids
once it has advanced. -/
theorem no_resurrection (m : Manifest) (σ : MachineState) (r : CapRef)
    (h : r.gen.toNat < ((σ.doms r.dom).slotGen r.slot).toNat) :
    ∀ n, (stepN m n σ).liveRef r = false := by
  intro n
  have hmono := gen_monotone_n m σ r.dom r.slot n
  have hne : ((stepN m n σ).doms r.dom).slotGen r.slot ≠ r.gen := by
    intro heq
    rw [heq] at hmono
    omega
  unfold MachineState.liveRef DomainState.liveCap
  cases hc : ((stepN m n σ).doms r.dom).caps r.slot with
  | none => simp [hc]
  | some e =>
      simp only [hc]
      rw [if_neg]
      · rfl
      · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro heq; exact absurd heq hne

/-- **T3.** If `cap_revoke` retires this cycle — the in-flight instruction
is `cap_revoke` on its last cycle, its handle naming the live memory
capability `(s, g)` of the executing domain — then from the next cycle on,
forever, no agent writes any address under any descendant of the revoked
capability (`marks` is the descendant set the sweep destroys). -/
theorem revoke_temporal_safety (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (fl : InFlight) (hfl : σ.inflight = some fl) (hlast : fl.cyclesLeft ≤ 1)
    (i : Instr) (hdec : Loom.Isa.decode isa fl.word = some i)
    (hrev : i.mnemonic = "cap_revoke")
    (s : Slot) (g : Gen) (e : CapEntry)
    (hlive : (σ.doms fl.dom).liveCap s g = some e)
    (hhandle : Handle.decode ((σ.doms fl.dom).reg (operandsOf fl.word).rs1)
               = ⟨s, g, .mem⟩) :
    ∀ n, 1 ≤ n → ∀ (d' : DomainId) (s' : Slot),
      σ.marks ⟨fl.dom, s, g⟩ d' s' = true →
      ∀ a : Addr,
        ¬ WritesUnder (stepN m n σ) ⟨d', s', (σ.doms d').slotGen s'⟩ a := by
  intro n hn d' s' hmark a hwu
  set r : CapRef := ⟨d', s', (σ.doms d').slotGen s'⟩ with hr
  -- invariants at the future state
  have hreachτ : (machine m).Reachable (stepN m n σ) := reachable_stepN m σ hreach n
  obtain ⟨hwfτ, hacτ, hclτ⟩ := wfacl_invariant m hwf _ hreachτ
  have hmlτ : MoverLiveMem (stepN m n σ) := moverLiveMem_invariant m _ hreachτ
  obtain ⟨hwfσ, hacσ, hclσ⟩ := wfacl_invariant m hwf σ hreach
  -- either way, `WritesUnder` needs `r` live at the future state, with a
  -- memory-class entry; case on the revoked capability's class
  cases hclseq : e.kind.cls with
  | mem =>
      -- the retirement destroys every marked slot: `r` is dead forever
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨hcaps, hgen⟩ := revoke_step_projections m σ fl hfl hlast i hdec hrev
        s g e hlive hhandle hclseq d' s' hmark
      have hstepN : stepN m (k + 1) σ = stepN m k (step m σ) := rfl
      have hdead : (stepN m (k + 1) σ).liveRef r = false := by
        rw [hstepN]
        by_cases hret : (σ.doms d').slotGen s' = genRetired
        · -- saturated generation: the slot is tombstoned forever
          have hts : Tombstoned d' s' (step m σ) :=
            ⟨hcaps, by rw [hgen, hret]; exact bumpGen_retired⟩
          have htsτ := (stepN_evo m k (step m σ)).2.2.1 d' s' hts
          unfold MachineState.liveRef DomainState.liveCap
          rw [htsτ.1]
          rfl
        · -- strict bump: no resurrection
          have h1 : ((σ.doms d').slotGen s').toNat
              < (((step m σ).doms d').slotGen s').toNat := by
            rw [hgen]; exact bumpGen_gt _ hret
          have h2 := (stepN_evo m k (step m σ)).1 d' s'
          have hne : ((stepN m k (step m σ)).doms d').slotGen s' ≠ r.gen := by
            intro heq
            rw [heq] at h2
            show False
            have : r.gen = (σ.doms d').slotGen s' := rfl
            rw [this] at h2
            omega
          unfold MachineState.liveRef DomainState.liveCap
          cases hc : ((stepN m k (step m σ)).doms d').caps r.slot with
          | none => simp
          | some e0 =>
              simp only [hc]
              simp
              intro heq
              exact absurd heq hne
      -- but a write under `r` requires `r` live (Mover job or region backing)
      rcases hwu with ⟨job, hjob, hdst, _, _⟩ | ⟨fl2, rg, reg2, hfl2, _, hrg, hback, _⟩
      · have hl := (hwfτ.mover_wf job hjob).2.2.2
        rw [hdst] at hl
        rw [hl] at hdead
        cases hdead
      · obtain ⟨e4, hlive4, _⟩ := hwfτ.region_backed _ reg2 rg hrg
        rw [hback] at hlive4
        unfold MachineState.liveRef at hdead
        rw [hlive4] at hdead
        cases hdead
  | gate =>
      -- gate-class root: every marked descendant is gate-class, and its kind
      -- is pinned while it lives — it can never back a region or Mover job
      obtain ⟨e', hce', hcls'⟩ := marked_cls σ hwfσ hclσ ⟨fl.dom, s, g⟩ e hlive d' s' hmark
      have hfate : RefFate r e'.kind σ := Or.inl ⟨rfl, e', hce', rfl⟩
      have hfateτ := (stepN_evo m n σ).2.1 r e'.kind hfate
      have hclsgate : e'.kind.cls = .gate := by rw [hcls', hclseq]
      rcases hwu with ⟨job, hjob, hdst, _, _⟩ | ⟨fl2, rg, reg2, hfl2, _, hrg, hback, _⟩
      · -- Mover destination: always live memory-class
        obtain ⟨e4, hlive4, hcls4⟩ := hmlτ job hjob
        rw [hdst] at hlive4
        obtain ⟨hc4, hg4, _⟩ := (liveCap_eq_some _ _ _ _).mp hlive4
        rcases hfateτ with ⟨hgt, e5, hce5, hk5⟩ | hlt | ⟨hnone, _, _⟩
        · rw [hce5] at hc4
          injection hc4 with h4; subst h4
          rw [hk5, hclsgate] at hcls4
          cases hcls4
        · rw [hg4] at hlt
          exact absurd hlt (lt_irrefl _)
        · rw [hnone] at hc4
          cases hc4
      · -- region backing: must be dominated by a memory kind
        obtain ⟨e4, hlive4, hle⟩ := hwfτ.region_backed _ reg2 rg hrg
        rw [hback] at hlive4
        obtain ⟨hc4, hg4, _⟩ := (liveCap_eq_some _ _ _ _).mp hlive4
        rcases hfateτ with ⟨hgt, e5, hce5, hk5⟩ | hlt | ⟨hnone, _, _⟩
        · rw [hce5] at hc4
          injection hc4 with h4; subst h4
          cases hk4 : e5.kind with
          | mem b4 l4 p4 =>
              rw [hk4] at hk5
              rw [← hk5] at hclsgate
              cases hclsgate
          | gate g4 =>
              rw [hk4] at hle
              exact absurd hle (by simp [CapKind.le])
        · rw [hg4] at hlt
          exact absurd hlt (lt_irrefl _)
        · rw [hnone] at hc4
          cases hc4

end Machines.Lnp64u.Theorems.T3
