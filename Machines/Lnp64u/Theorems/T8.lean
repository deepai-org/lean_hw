import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Theorems.Inv

/-!
# T8 — Whole-machine memory safety as ownership transfer

Grant–revoke–regrant: once authority is revoked and regranted, the prior
holder and its Mover traffic never touch the range; machine-wide W^X;
status-word writes only under the owner's live authority.
-/

namespace Machines.Lnp64u.Theorems.T8

open Machines.Lnp64u Loom

/-- Machine-wide W^X: no live memory capability and no region register
carries write and execute together, in any reachable state. -/
theorem wx_machine_wide (hexec : ExecPreservesWf) (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant (fun σ =>
      (∀ d s base len p l, (σ.doms d).caps s = some ⟨.mem base len p, l⟩ →
        p.wx = true) ∧
      (∀ d r rg, (σ.doms d).regions r = some rg → rg.perms.wx = true)) := by
  intro σ hreach
  have hwfσ : Wf σ := Inv.wf_invariant hexec m hwf σ hreach
  refine ⟨?_, ?_⟩
  · -- capabilities: from DomWf.wx
    intro d s base len p l hcap
    cases l with
    | none => exact (hwfσ.doms d).wx s base len p (Or.inl hcap)
    | some l' => exact (hwfσ.doms d).wx s base len p (Or.inr ⟨l', hcap⟩)
  · -- regions: a region's authority is dominated by a live memory capability,
    -- which is W^X; permission narrowing preserves W^X
    intro d r rg hrg
    obtain ⟨e, hlive, hle⟩ := hwfσ.region_backed d r rg hrg
    -- e.kind is a memory capability (regions cache memory), and it is W^X
    cases hk : e.kind with
    | gate g => rw [hk] at hle; exact absurd hle (by simp [CapKind.le])
    | mem base len p =>
        rw [hk] at hle
        obtain ⟨_, _, hperm⟩ := hle
        -- the backing capability is W^X (it is a live memory cap)
        have hbwx : p.wx = true := by
          have hbcap : (σ.doms rg.backing.dom).caps rg.backing.slot = some e := by
            unfold DomainState.liveCap at hlive
            revert hlive
            cases hc : (σ.doms rg.backing.dom).caps rg.backing.slot with
            | none => intro h; simp at h
            | some e' => intro h; split at h <;> simp_all
          have : e = ⟨.mem base len p, e.lineage⟩ := by
            cases e; simp_all
          rw [this] at hbcap
          exact (hwfσ.doms rg.backing.dom).wx rg.backing.slot base len p
            (by cases hel : e.lineage with
                | none => exact Or.inl (by rw [hel] at hbcap; exact hbcap)
                | some l' => exact Or.inr ⟨l', by rw [hel] at hbcap; exact hbcap⟩)
        -- narrowing: rg.perms.le p, and p is W^X, so rg.perms is W^X
        cases hrp : rg.perms with
        | mk rr rw rx =>
            cases hp : p with
            | mk pr pw px =>
                simp only [Perms.wx, hrp, Bool.not_eq_true'] at *
                simp only [Perms.le, hrp, hp, Bool.and_eq_true, Bool.or_eq_true,
                  Bool.not_eq_true'] at hperm
                rw [hp] at hbwx
                simp only [Perms.wx, Bool.not_eq_true', Bool.and_eq_false_iff] at hbwx
                rcases hbwx with hw | hx
                · rcases hperm.1.2 with h | h
                  · simp [h]
                  · rw [hw] at h; simp at h
                · rcases hperm.2 with h | h
                  · simp [h]
                  · rw [hx] at h; simp at h

/-- **Ownership transfer.** After the prior holder's capability over a
range is destroyed (its reference dead), the prior holder never again
writes that range under that reference — for all future states. The
grant–revoke–regrant scenario instantiates this with the regrant on the
other side. -/
theorem prior_holder_excluded (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (r : CapRef) (hdead : σ.liveRef r = false) :
    ∀ n a, ¬ WritesUnder (stepN m n σ) r a := by
  sorry

/-- **Status-word safety.** Whenever the machine writes a Mover status
word, the job's owner holds current write authority over it (the write is
dropped otherwise) — completion reporting can never become an unauthorized
write channel. Stated as: the Mover phase changes memory only at addresses
the owner covers writable, or at the job's current destination under the
re-checked destination capability. -/
theorem status_word_safety (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (job : MoverJob) (hjob : σ.mover = some job)
    (a : Addr) (hchg : (moverPhase σ).mem a ≠ σ.mem a) :
    (a = job.dstCur ∧
      moverCheck σ job.dst a { r := false, w := true, x := false } = true) ∨
    (a = job.statusAddr ∧
      σ.domCovers job.owner a { r := false, w := true, x := false } = true) := by
  sorry

end Machines.Lnp64u.Theorems.T8
