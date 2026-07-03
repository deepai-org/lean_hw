import Machines.Lnp64u.Logic.Wf

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
    ((σ.doms d).slotGen s).toNat ≤ (((step m σ).doms d).slotGen s).toNat := by
  sorry

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
  sorry

end Machines.Lnp64u.Theorems.T3
