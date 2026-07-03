import Machines.Lnp64u.Logic.Wf

/-!
# T6 — Totality and no-hostage

The outcome set is closed — {retire, `-errno`, domain-halt} — and a blocked
gate caller resumes within a manifest-computable bound, quantified over all
callees *including adversarial ones*: the donation bound plus forced unwind
(the design change this theorem forced, 2026-07-03) makes the statement one
only a proof can make.
-/

namespace Machines.Lnp64u.Theorems.T6

open Machines.Lnp64u Loom

/-- **Totality.** The machine is deterministic and total: every state has
exactly one successor. (By construction — `step` is a Lean function — but
stated because the claim is about the *machine*, not the formalization:
there is no state, adversarial or otherwise, without a defined next
cycle.) -/
theorem totality (m : Manifest) (σ : MachineState) :
    ∃! σ', (machine m).step σ σ' :=
  ⟨step m σ, rfl, fun _ h => h.symm⟩

/-- The caller-side resume bound: donation for every chain level below the
caller, each level's instructions issued at worst one per period of the
payer, plus the Mover word and sweep slack. Coarse and manifest-computable
— tightened per target as T6′ in Phase 3. -/
def resumeBound (m : Manifest) (d : DomainId) : Nat :=
  ((m.doms d).maxDonation + 1) * maxChainDepth * (m.doms d).periodP +
    2 * (m.doms d).periodP

/-- **No-hostage.** A domain blocked on a gate call resumes (or halts)
within `resumeBound` cycles, whatever the callee does: return, fault,
halt, loop (donation exhaustion unwinds it), or call deeper (depth ≤ 4,
each level donation-bounded). -/
theorem no_hostage (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (d : DomainId) (g : GateId) (hblocked : (σ.doms d).run = .blocked g) :
    ∃ n ≤ resumeBound m d, ((stepN m n σ).doms d).run ≠ .blocked g := by
  sorry

end Machines.Lnp64u.Theorems.T6
