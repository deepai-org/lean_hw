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

/-- **No resurrection.** A dead reference stays dead: once a slot's
generation has moved past a reference's, no future state revives it. -/
theorem no_resurrection (m : Manifest) (σ : MachineState) (r : CapRef)
    (h : r.gen.toNat < ((σ.doms r.dom).slotGen r.slot).toNat) :
    ∀ n, (stepN m n σ).liveRef r = false := by
  sorry

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
