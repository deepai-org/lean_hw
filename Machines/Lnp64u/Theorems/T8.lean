import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Theorems.Inv
import Machines.Lnp64u.Logic.AcyclicWfa
import Machines.Lnp64u.Theorems.T3

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
theorem wx_machine_wide (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant (fun σ =>
      (∀ d s base len p l, (σ.doms d).caps s = some ⟨.mem base len p, l⟩ →
        p.wx = true) ∧
      (∀ d r rg, (σ.doms d).regions r = some rg → rg.perms.wx = true)) := by
  intro σ hreach
  have hwfσ : Wf σ := (Machines.Lnp64u.wfa_invariant m hwf σ hreach).1
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

/-- Reachability is closed under any number of machine cycles. -/
private theorem reachable_stepN (m : Manifest) (σ : MachineState)
    (hreach : (machine m).Reachable σ) :
    ∀ n, (machine m).Reachable (stepN m n σ) := by
  intro n
  induction n generalizing σ with
  | zero => exact hreach
  | succ k ih => exact ih (step m σ) (Loom.TSys.Reachable.step hreach rfl)

/-- **Ownership transfer.** After the prior holder's capability over a
range is destroyed, its reference is *retired* — the slot's generation has
strictly advanced past the reference's (the state every destruction leaves
behind: `clearSlot`/`destroyMarked` bump the generation, `freeSlot`
tombstones). From then on the prior holder never again writes that range
under that reference — for all future states. The grant–revoke–regrant
scenario instantiates this with the regrant on the other side. -/
theorem prior_holder_excluded (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (r : CapRef)
    (hdead : r.gen.toNat < ((σ.doms r.dom).slotGen r.slot).toNat) :
    ∀ n a, ¬ WritesUnder (stepN m n σ) r a := by
  intro n a hw
  have hwfτ : Wf (stepN m n σ) :=
    (Machines.Lnp64u.wfa_invariant m hwf (stepN m n σ)
      (reachable_stepN m σ hreach n)).1
  have hlive : (stepN m n σ).liveRef r = false :=
    Machines.Lnp64u.Theorems.T3.no_resurrection m σ r hdead n
  rcases hw with ⟨job, hjob, hdst, _, _⟩ | ⟨fl, rg, reg, hfl, _, hrg, hback, _⟩
  · -- Mover channel: the job's destination is live (Wf), but r is dead
    have hl := (hwfτ.mover_wf job hjob).2.2.2
    rw [hdst, hlive] at hl
    exact Bool.false_ne_true hl
  · -- Core channel: the region's backing is live (Wf), but r is dead
    obtain ⟨e, he, _⟩ := hwfτ.region_backed fl.dom reg rg hrg
    rw [hback] at he
    have hl : (stepN m n σ).liveRef r = true := by
      unfold MachineState.liveRef
      rw [he]
      rfl
    rw [hlive] at hl
    exact Bool.false_ne_true hl

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
  -- A status write changes memory only at the status address, and only
  -- under the owner's current write authority (otherwise it is dropped).
  have hstat : ∀ (τ : MachineState) (j : MoverJob) (v : Loom.Word32) (b : Addr),
      (moverStatus τ j v).mem b ≠ τ.mem b →
      b = j.statusAddr ∧
        τ.domCovers j.owner j.statusAddr { r := false, w := true, x := false }
          = true := by
    intro τ j v b hne
    unfold moverStatus at hne
    by_cases hcov :
        τ.domCovers j.owner j.statusAddr { r := false, w := true, x := false }
          = true
    · rw [if_pos hcov] at hne
      refine ⟨?_, hcov⟩
      by_contra hb
      exact hne (Loom.Fun.update_ne τ.mem j.statusAddr b v hb)
    · rw [if_neg hcov] at hne
      exact absurd rfl hne
  -- Reduce the Mover phase on `some job` to its three explicit branches.
  have hred : moverPhase σ =
      if job.remaining = 0 then
        moverStatus { σ with mover := none } job 1
      else if moverCheck σ job.src job.srcCur { r := true, w := false, x := false } &&
              moverCheck σ job.dst job.dstCur { r := false, w := true, x := false } then
        if job.remaining - 1 = 0 then
          moverStatus { σ.write job.dstCur (σ.read job.srcCur) with mover := none }
            { job with srcCur := job.srcCur + 1, dstCur := job.dstCur + 1
                       remaining := job.remaining - 1 } 1
        else
          { σ.write job.dstCur (σ.read job.srcCur) with mover := some { job with
              srcCur := job.srcCur + 1, dstCur := job.dstCur + 1,
              remaining := job.remaining - 1 } }
      else
        moverStatus { σ with mover := none } job Errno.staleHandle.toWord := by
    unfold moverPhase
    rw [hjob]
  rw [hred] at hchg
  by_cases h0 : job.remaining = 0
  · -- Completion report: only the status write can change memory
    rw [if_pos h0] at hchg
    obtain ⟨hb, hcov⟩ := hstat { σ with mover := none } job 1 a hchg
    exact Or.inr ⟨hb, by rw [hb]; exact hcov⟩
  · rw [if_neg h0] at hchg
    by_cases hchk :
        (moverCheck σ job.src job.srcCur { r := true, w := false, x := false } &&
         moverCheck σ job.dst job.dstCur { r := false, w := true, x := false })
          = true
    · -- Checks passed: the word write lands at dstCur; completion may
      -- additionally write the status word
      rw [if_pos hchk] at hchg
      by_cases ha : a = job.dstCur
      · exact Or.inl ⟨ha, by rw [ha]; exact ((Bool.and_eq_true _ _).mp hchk).2⟩
      · have hmem : (σ.write job.dstCur (σ.read job.srcCur)).mem a = σ.mem a :=
          Loom.Fun.update_ne σ.mem job.dstCur a (σ.read job.srcCur) ha
        by_cases h1 : job.remaining - 1 = 0
        · rw [if_pos h1, ← hmem] at hchg
          obtain ⟨hb, hcov⟩ := hstat
            { σ.write job.dstCur (σ.read job.srcCur) with mover := none }
            { job with srcCur := job.srcCur + 1, dstCur := job.dstCur + 1
                       remaining := job.remaining - 1 } 1 a hchg
          exact Or.inr ⟨hb, by rw [hb]; exact hcov⟩
        · rw [if_neg h1] at hchg
          exact absurd hmem hchg
    · -- Checks failed: abort report — same shape as completion
      rw [if_neg hchk] at hchg
      obtain ⟨hb, hcov⟩ :=
        hstat { σ with mover := none } job Errno.staleHandle.toWord a hchg
      exact Or.inr ⟨hb, by rw [hb]; exact hcov⟩

end Machines.Lnp64u.Theorems.T8
