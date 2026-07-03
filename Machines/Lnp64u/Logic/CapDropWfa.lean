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
theorem move_acyclic_ok (c : Ctx) (σ : MachineState) (hac : Acyclic σ) :
    (∀ x σ', (moveExec c) σ = .ok x σ' → Acyclic σ') := by
  intro x σ' he
  simp only [moveExec, SpecM.get, specM_bind] at he
  cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
  | err e0 σ0 => rw [hr0] at he; simp at he
  | fault f => rw [hr0] at he; simp at he
  | ok u0 σ0 =>
      have hh0 := require_ok _ _ σ hr0; subst σ0
      rw [hr0] at he; simp only [SpecM.reg] at he
      set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
      cases hl1 : load c.d B σ with
      | err e σe => rw [hl1] at he; simp at he
      | fault f => rw [hl1] at he; simp at he
      | ok srcH σ1 =>
          have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
          cases hl2 : load c.d (B + 1) σ with
          | err e σe => rw [hl2] at he; simp at he
          | fault f => rw [hl2] at he; simp at he
          | ok dstH σ2 =>
              have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
              cases hl3 : load c.d (B + 2) σ with
              | err e σe => rw [hl3] at he; simp at he
              | fault f => rw [hl3] at he; simp at he
              | ok lenW σ3 =>
                  have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                  cases hl4 : load c.d (B + 3) σ with
                  | err e σe => rw [hl4] at he; simp at he
                  | fault f => rw [hl4] at he; simp at he
                  | ok stW σ4 =>
                      have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                      cases hc1 : capLive c.d srcH σ with
                      | err e σe => rw [hc1] at he; simp at he
                      | fault f => rw [hc1] at he; simp at he
                      | ok rs σ5 =>
                          have hcs := capLive_ok c.d _ σ hc1; obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                          rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                          cases hc2 : capLive c.d dstH σ with
                          | err e σe => rw [hc2] at he; simp at he
                          | fault f => rw [hc2] at he; simp at he
                          | ok rdd σ6 =>
                              have hcd := capLive_ok c.d _ σ hc2; obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                              rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                              cases hks : es.kind with
                              | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                          | gate _ => rw [hkd] at he; simp [SpecM.raise] at he
                                          | mem _ _ _ => rw [hkd] at he; simp [SpecM.raise] at he
                              | mem sb sl sp =>
                                  cases hkd : ed.kind with
                                  | gate _ => rw [hks, hkd] at he; simp [SpecM.raise] at he
                                  | mem db dl dp =>
                                      rw [hks, hkd] at he; simp only [specM_bind] at he
                                      cases hq1 : SpecM.require sp.r .permDenied σ with
                                      | err e σe => rw [hq1] at he; simp at he
                                      | fault f => rw [hq1] at he; simp at he
                                      | ok _ σq1 =>
                                          have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                          cases hq2 : SpecM.require dp.w .permDenied σ with
                                          | err e σe => rw [hq2] at he; simp at he
                                          | fault f => rw [hq2] at he; simp at he
                                          | ok _ σq2 =>
                                              have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                              cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                              | err e σe => rw [hq3] at he; simp at he
                                              | fault f => rw [hq3] at he; simp at he
                                              | ok _ σq3 =>
                                                  have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                  cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                  | err e σe => rw [hd] at he; simp at he
                                                  | fault f => rw [hd] at he; simp at he
                                                  | ok _ σdd =>
                                                      have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                      simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
                                                      injection he with _ h2; subst h2
                                                      exact acyclic_setReg_dom _ c.d _ 0 (acyclic_setMover σ _ hac)


theorem move_acyclic_err (c : Ctx) (σ : MachineState) (hac : Acyclic σ) :
    (∀ x σ', (moveExec c) σ = .err x σ' → Acyclic σ') := by
  intro x σ' he
  simp only [moveExec, SpecM.get, specM_bind] at he
  cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
  | err e0 σ0 => have hq := require_err_state _ _ σ hr0; rw [hr0] at he; injection he with _ h2; subst h2; subst hq; exact hac
  | fault f => rw [hr0] at he; simp at he
  | ok u0 σ0 =>
      have hh0 := require_ok _ _ σ hr0; subst σ0
      rw [hr0] at he; simp only [SpecM.reg] at he
      set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
      cases hl1 : load c.d B σ with
      | err e σe => have hq := load_err_state _ _ σ hl1; rw [hl1] at he; injection he with _ h2; subst h2; subst hq; exact hac
      | fault f => rw [hl1] at he; simp at he
      | ok srcH σ1 =>
          have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
          cases hl2 : load c.d (B + 1) σ with
          | err e σe => have hq := load_err_state _ _ σ hl2; rw [hl2] at he; injection he with _ h2; subst h2; subst hq; exact hac
          | fault f => rw [hl2] at he; simp at he
          | ok dstH σ2 =>
              have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
              cases hl3 : load c.d (B + 2) σ with
              | err e σe => have hq := load_err_state _ _ σ hl3; rw [hl3] at he; injection he with _ h2; subst h2; subst hq; exact hac
              | fault f => rw [hl3] at he; simp at he
              | ok lenW σ3 =>
                  have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                  cases hl4 : load c.d (B + 3) σ with
                  | err e σe => have hq := load_err_state _ _ σ hl4; rw [hl4] at he; injection he with _ h2; subst h2; subst hq; exact hac
                  | fault f => rw [hl4] at he; simp at he
                  | ok stW σ4 =>
                      have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                      cases hc1 : capLive c.d srcH σ with
                      | err e σe => have hq := capLive_err_state c.d _ σ hc1; rw [hc1] at he; injection he with _ h2; subst h2; subst hq; exact hac
                      | fault f => rw [hc1] at he; simp at he
                      | ok rs σ5 =>
                          have hcs := capLive_ok c.d _ σ hc1; obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                          rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                          cases hc2 : capLive c.d dstH σ with
                          | err e σe => have hq := capLive_err_state c.d _ σ hc2; rw [hc2] at he; injection he with _ h2; subst h2; subst hq; exact hac
                          | fault f => rw [hc2] at he; simp at he
                          | ok rdd σ6 =>
                              have hcd := capLive_ok c.d _ σ hc2; obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                              rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                              cases hks : es.kind with
                              | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                          | gate _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact hac
                                          | mem _ _ _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact hac
                              | mem sb sl sp =>
                                  cases hkd : ed.kind with
                                  | gate _ => rw [hks, hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact hac
                                  | mem db dl dp =>
                                      rw [hks, hkd] at he; simp only [specM_bind] at he
                                      cases hq1 : SpecM.require sp.r .permDenied σ with
                                      | err e σe => have hq := require_err_state _ _ σ hq1; rw [hq1] at he; injection he with _ h2; subst h2; subst hq; exact hac
                                      | fault f => rw [hq1] at he; simp at he
                                      | ok _ σq1 =>
                                          have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                          cases hq2 : SpecM.require dp.w .permDenied σ with
                                          | err e σe => have hq := require_err_state _ _ σ hq2; rw [hq2] at he; injection he with _ h2; subst h2; subst hq; exact hac
                                          | fault f => rw [hq2] at he; simp at he
                                          | ok _ σq2 =>
                                              have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                              cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                              | err e σe => have hq := require_err_state _ _ σ hq3; rw [hq3] at he; injection he with _ h2; subst h2; subst hq; exact hac
                                              | fault f => rw [hq3] at he; simp at he
                                              | ok _ σq3 =>
                                                  have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                  cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                  | err e σe => exact absurd hd (by simp [SpecM.demand]; split <;> simp [SpecM.fatal])
                                                  | fault f => rw [hd] at he; simp at he
                                                  | ok _ σdd =>
                                                      have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                      simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he


/-- Dispatch. -/
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
  case _ => exact ⟨move_acyclic_ok c σ hac, move_acyclic_err c σ hac⟩
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
