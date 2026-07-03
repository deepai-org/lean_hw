import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Logic.KernelLemmas
import Machines.Lnp64u.Logic.PhaseLemmas

/-!
# The workhorse: machine well-formedness is invariant

Everything in the Phase-1 ladder either strengthens `Wf` or is its
corollary. Proof strategy (µLog DESIGN.md): show `Wf` inductive over
`step`'s phases, then per-instruction preservation lemmas, one kernel
function at a time.
-/

namespace Machines.Lnp64u.Theorems.Inv

open Machines.Lnp64u Loom

/-- Boot capabilities are all roots: their lineage field is `none`. -/
private theorem boot_lineage_none (m : Manifest) (d : DomainId) (s : Slot)
    (e : CapEntry) (h : (m.initState.doms d).caps s = some e) : e.lineage = none := by
  simp only [Manifest.initState, Manifest.bootDom, Option.map_eq_some_iff] at h
  obtain ⟨k, _, hk⟩ := h; simp [← hk]

/-- At boot every domain's bookkeeping is well-formed. Most obligations are
vacuous (no derived caps, no lineage cells); `gen_pos`, `wx`, and `bounds`
come from the manifest's well-formedness. -/
private theorem init_domWf (m : Manifest) (hwf : m.WF) (d : DomainId) :
    DomWf (m.initState.doms d) := by
  constructor
  · intro s; show 1 ≤ (genFirst).toNat; decide
  · intro s e l h hl; rw [boot_lineage_none m d s e h] at hl; exact absurd hl (by simp)
  · intro s s' e e' l h _ hl _; rw [boot_lineage_none m d s e h] at hl; exact absurd hl (by simp)
  · intro l hl; exact absurd hl (by simp [Manifest.initState, Manifest.bootDom])
  · intro s base len p hcase
    have hget : (m.doms d).initCaps s = some (.mem base len p) := by
      rcases hcase with h | ⟨l, h⟩ <;>
      · simp only [Manifest.initState, Manifest.bootDom, Option.map_eq_some_iff] at h
        obtain ⟨k, hk, he⟩ := h
        have : k = CapKind.mem base len p := by
          have := congrArg CapEntry.kind he; simpa using this
        rw [← this]; exact hk
    exact (hwf.caps_wx d s base len p hget).1
  · intro s e base len p h hk
    have hget : (m.doms d).initCaps s = some (.mem base len p) := by
      simp only [Manifest.initState, Manifest.bootDom, Option.map_eq_some_iff] at h
      obtain ⟨k, hk', he⟩ := h
      have hke : k = e.kind := by have := congrArg CapEntry.kind he; simpa using this
      rw [hke, hk] at hk'; exact hk'
    exact (hwf.caps_wx d s base len p hget).2

/-- Boot states are well-formed. -/
theorem init_wf (m : Manifest) (hwf : m.WF) : Wf m.initState := by
  constructor
  · exact init_domWf m hwf
  · -- parent_live: no lineage cells at boot, so parentOf is always none
    intro d s p hp
    simp only [MachineState.parentOf, Manifest.initState, Manifest.bootDom,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
    obtain ⟨e, _, l, _, cell, hcell, _⟩ := hp
    exact absurd hcell (by simp)
  · -- region_backed: a boot region is backed by its own live root capability,
    -- and its authority equals that capability's
    intro d r rg hrg
    simp only [Manifest.initState, Manifest.bootDom] at hrg
    revert hrg
    cases hinit : (m.doms d).initRegions r with
    | none => intro h; simp at h
    | some s =>
        cases hcap : (m.doms d).initCaps s with
        | none => intro h; simp [hcap] at h
        | some k =>
            cases k with
            | gate g => intro h; simp [hcap] at h
            | mem base len perms =>
                intro h
                simp only [hcap, Option.some.injEq] at h
                refine ⟨⟨.mem base len perms, none⟩, ?_, ?_⟩
                · subst h
                  show (m.initState.doms d).liveCap s genFirst = some _
                  simp only [Manifest.initState, Manifest.bootDom,
                    DomainState.liveCap, hcap, Option.map_some]
                  rfl
                · subst h
                  exact CapKind.le_refl (.mem base len perms)
  · intro job h; exact absurd h (by simp [Manifest.initState])
  · intro g a h; exact absurd h (by simp [Manifest.initState])
  · intro d g h; exact absurd h (by simp [Manifest.initState, Manifest.bootDom])
  · intro d g h; exact absurd h (by simp [Manifest.initState, Manifest.bootDom])
  · intro fl h; exact absurd h (by simp [Manifest.initState])
  · intro g a h; exact absurd h (by simp [Manifest.initState])

/-- `Wf` is preserved by one cycle. Decomposed across the three phases:
refill and the Mover are fully discharged (`refillPhase_preserves_wf`,
`moverPhase_preserves_wf`); the cycle bump is transparent (`wf_setCycle`);
the one remaining obligation is `corePhase_preserves_wf`. -/
theorem step_wf (hexec : ExecPreservesWf) (m : Manifest) (hwf : m.WF) (σ : MachineState)
    (h : Wf σ) : Wf (step m σ) := by
  unfold step
  exact wf_setCycle _ _
    (moverPhase_preserves_wf _
      (corePhase_preserves_wf hexec m hwf _
        (refillPhase_preserves_wf m σ h)))

/-- The invariant. -/
theorem wf_invariant (hexec : ExecPreservesWf) (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant Wf :=
  (TSys.Inductive.invariant
    { init := fun σ h => h ▸ init_wf m hwf
      step := fun σ σ' hσ hstep => by
        have : step m σ = σ' := hstep
        exact this ▸ step_wf hexec m hwf σ hσ })

end Machines.Lnp64u.Theorems.Inv
