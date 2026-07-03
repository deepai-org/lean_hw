import Machines.Lnp64u.Logic.AcyclicExec
import Machines.Lnp64u.Logic.SystemOpsWf

/-!
# `cap_drop` preserves `Wf ∧ Acyclic` (the `capLive → dropCore` thread)

Wires `cap_drop`'s `exec` to `dropCore_preserves`: after a read-only `reg` and
`capLive` (which pins the dropped slot's live generation), the dispatch +
`clearSlot` + sweeps is exactly `dropCore`, which preserves both invariants; the
final `setReg` preserves them too. Because `cap_drop`'s *Wf* clause itself needs
`Acyclic` (via `dropCore`'s reparent branch), this is proved against the combined
`Wf ∧ Acyclic` — the first revocation opcode fully discharged.
-/

namespace Machines.Lnp64u

open Loom.Isa SpecM Machines.Lnp64u.Isa Machines.Lnp64u.Isa.Wip

/-- `cap_drop` preserves `Wf ∧ Acyclic`. -/
theorem capdrop_preserves_wfa (c : Ctx) (σ : MachineState) (hwf : Wf σ) (hac : Acyclic σ) :
    (∀ x σ',
      ((do let hw ← reg c.d c.op.rs1
           let (s, g, _) ← capLive c.d hw
           let ref : CapRef := ⟨c.d, s, g⟩
           let σ0 ← SpecM.get
           let σ' :=
             match σ0.parentOf c.d s with
             | some p => σ0.reparent ref p
             | none => σ0.orphanChildren ref
           SpecM.set (((σ'.clearSlot c.d s).sweepRegions).sweepMover)
           setReg c.d c.op.rd 0) : SpecM Unit) σ = .ok x σ' → Wf σ' ∧ Acyclic σ') ∧
    (∀ e σ',
      ((do let hw ← reg c.d c.op.rs1
           let (s, g, _) ← capLive c.d hw
           let ref : CapRef := ⟨c.d, s, g⟩
           let σ0 ← SpecM.get
           let σ' :=
             match σ0.parentOf c.d s with
             | some p => σ0.reparent ref p
             | none => σ0.orphanChildren ref
           SpecM.set (((σ'.clearSlot c.d s).sweepRegions).sweepMover)
           setReg c.d c.op.rd 0) : SpecM Unit) σ = .err e σ' → Wf σ' ∧ Acyclic σ') := by
  constructor
  · intro x σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 => rw [hcl] at he; simp at he
    | fault f => rw [hcl] at he; simp at he
    | ok r σ0 =>
        obtain ⟨hσeq, hlive⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, e⟩ := r; simp only at he hlive
        have hg : (σ.doms c.d).slotGen s = g := by
          unfold DomainState.liveCap at hlive
          cases hc : (σ.doms c.d).caps s with
          | none => simp [hc] at hlive
          | some e0 =>
              simp only [hc] at hlive
              split at hlive
              · rename_i hgc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgc; exact hgc.1
              · simp at hlive
        subst g
        simp only [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he
        injection he with _ h2; subst h2
        obtain ⟨hwfd, hacd⟩ := dropCore_preserves σ c.d s hwf hac
        exact ⟨wf_setReg _ c.d c.op.rd 0 hwfd, acyclic_setReg_dom _ c.d c.op.rd 0 hacd⟩
  · intro e σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := capLive_err_state c.d _ σ hcl; rw [hcl] at he
        injection he with _ h2; subst h2; subst hs; exact ⟨hwf, hac⟩
    | fault f => rw [hcl] at he; simp at he
    | ok r σ0 =>
        obtain ⟨hσeq, hlive⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, e0⟩ := r
        simp [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he

namespace Isa.Wip

open Machines.Lnp64u

/-- Per-opcode dispatch of `SystemOpsPreserveAcyclic`. `cap_drop` (via
`capdrop_preserves_wfa`), `unmap`/`yield` (region/budget update + `setReg`), and
`halt` (`haltDom`) are proved; the derivation/revoke/gate/Mover ops remain. -/
theorem system_preserves_acyclic : SystemOpsPreserveAcyclic := by
  intro instr hmem c σ hwf hac hrun hinf
  fin_cases hmem
  case _ => sorry  -- cap_dup   (installDerived)
  case _ => exact ⟨fun a σ' he => ((capdrop_preserves_wfa c σ hwf hac).1 a σ' he).2,
                   fun e σ' he => ((capdrop_preserves_wfa c σ hwf hac).2 e σ' he).2⟩
  case _ => sorry  -- cap_revoke (destroyMarked + sweeps)
  case _ => sorry  -- mem_grant (installDerived)
  case _ =>
    constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨s, g, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate gid => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he
              simp only [specM_bind, SpecM.updDom, SpecM.modify, SpecM.set, SpecM.setReg] at he
              injection he with _ h2; subst h2
              exact acyclic_setReg_dom _ c.d _ _
                (acyclic_setDom σ c.d _ (fun _ => ⟨rfl, rfl⟩) hac)
    · intro er σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
          rw [hcl] at he; injection he with _ h2; subst h2; subst hs; exact hac
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨s, g, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate gid => rw [hk] at he; simp only [SpecM.raise] at he
                        injection he with _ h2; subst h2; exact hac
          | mem base len perms =>
              rw [hk] at he
              simp [specM_bind, SpecM.updDom, SpecM.modify, SpecM.set, SpecM.setReg] at he
  case _ =>
    exact ⟨fun a σ' he => (PreservesAcyclic.bind (PreservesAcyclic.clearRegion _ _)
        (fun _ => PreservesAcyclic.setReg _ _ _) σ hac).1 a σ' he,
      fun e σ' he => (PreservesAcyclic.bind (PreservesAcyclic.clearRegion _ _)
        (fun _ => PreservesAcyclic.setReg _ _ _) σ hac).2 e σ' he⟩
  case _ => sorry  -- gate_call
  case _ => sorry  -- gate_return
  case _ => sorry  -- move
  case _ =>
    exact ⟨fun a σ' he => (PreservesAcyclic.bind (PreservesAcyclic.updDomBudget _ _)
        (fun _ => PreservesAcyclic.setReg _ _ _) σ hac).1 a σ' he,
      fun e σ' he => (PreservesAcyclic.bind (PreservesAcyclic.updDomBudget _ _)
        (fun _ => PreservesAcyclic.setReg _ _ _) σ hac).2 e σ' he⟩
  case _ =>
    refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
    · simp only [SpecM.modify] at he; injection he with h1 h2; subst h2
      exact acyclic_haltDom σ c.d 0 hac
    · simp [SpecM.modify] at he

end Isa.Wip

end Machines.Lnp64u
