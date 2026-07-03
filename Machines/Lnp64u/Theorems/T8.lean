import Machines.Lnp64u.Logic.Wf

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
  sorry

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
