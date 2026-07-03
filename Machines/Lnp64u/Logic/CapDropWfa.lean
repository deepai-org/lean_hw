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


theorem capdup_acyclic (c : Ctx) (σ : MachineState) (hwf : Wf σ) (hac : Acyclic σ) :
    (∀ x σ',
      ((do let hw ← reg c.d c.op.rs1
           let dw ← reg c.d c.op.rs2
           let (s, g, e) ← capLive c.d hw
           let kind ← match e.kind with
             | .mem base len perms => narrow base len perms dw
             | .gate gid => (Pure.pure (.gate gid) : SpecM _)
           let h ← allocDerived c.d kind ⟨c.d, s, g⟩
           setReg c.d c.op.rd h) : SpecM Unit) σ = .ok x σ' → Acyclic σ') := by
  intro x σ' he
  simp only [SpecM.reg, specM_bind] at he
  cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
  | err e0 σ0 => rw [hcl] at he; simp at he
  | fault f => rw [hcl] at he; simp at he
  | ok rr σ0 =>
      obtain ⟨hσeq, hlive⟩ := capLive_ok c.d _ σ hcl; subst σ0
      rw [hcl] at he
      obtain ⟨s, g, en⟩ := rr
      simp only at he hlive
      -- the parent ⟨c.d, s, g⟩ is live
      have hpar : σ.liveRef ⟨c.d, s, g⟩ = true := by
        unfold MachineState.liveRef; rw [hlive]; rfl
      -- compute the kind, then allocDerived
      cases hk : en.kind with
      | gate gid =>
          rw [hk] at he; simp only [specM_pure, specM_bind] at he
          cases ha : allocDerived c.d (.gate gid) ⟨c.d, s, g⟩ σ with
          | err e1 σ1 => rw [ha] at he; simp at he
          | fault f => rw [ha] at he; simp at he
          | ok hh σ1 =>
              rw [ha] at he
              simp only [specM_bind, SpecM.setReg, SpecM.modify] at he
              injection he with _ h2; subst h2
              exact acyclic_setReg_dom σ1 c.d _ hh
                (acyclic_allocDerived c.d (.gate gid) _ σ hpar hwf hac ha)
      | mem base len perms =>
          rw [hk] at he; simp only [specM_bind] at he
          cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
          | err e1 σ1 => rw [hn] at he; simp at he
          | fault f => rw [hn] at he; simp at he
          | ok kind σ1 =>
              obtain ⟨hσn, off, nlen, np, hkind, hwx, hin⟩ := narrow_ok base len perms _ σ hn
              subst σ1; rw [hn] at he
              simp only [specM_bind] at he
              cases ha : allocDerived c.d kind ⟨c.d, s, g⟩ σ with
              | err e2 σ2 => rw [ha] at he; simp at he
              | fault f => rw [ha] at he; simp at he
              | ok hh σ2 =>
                  rw [ha] at he
                  simp only [specM_bind, SpecM.setReg, SpecM.modify] at he
                  injection he with _ h2; subst h2
                  exact acyclic_setReg_dom σ2 c.d _ hh
                    (acyclic_allocDerived c.d kind _ σ hpar hwf hac ha)


theorem capdup_acyclic_err (c : Ctx) (σ : MachineState) (hac : Acyclic σ) :
    (∀ e σ',
      ((do let hw ← reg c.d c.op.rs1
           let dw ← reg c.d c.op.rs2
           let (s, g, en) ← capLive c.d hw
           let kind ← match en.kind with
             | .mem base len perms => narrow base len perms dw
             | .gate gid => (Pure.pure (.gate gid) : SpecM _)
           let h ← allocDerived c.d kind ⟨c.d, s, g⟩
           setReg c.d c.op.rd h) : SpecM Unit) σ = .err e σ' → Acyclic σ') := by
  intro e σ' he
  simp only [SpecM.reg, specM_bind] at he
  cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
  | err e0 σ0 =>
      have := capLive_err_state c.d _ σ hcl; rw [hcl] at he
      injection he with _ h2; subst h2; subst this; exact hac
  | fault f => rw [hcl] at he; simp at he
  | ok rr σ0 =>
      obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
      rw [hcl] at he; obtain ⟨s, g, en⟩ := rr; simp only at he
      have halloc : ∀ (kind : CapKind),
          ((allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h => setReg c.d c.op.rd h) : SpecM Unit) σ
            = .err e σ' → Acyclic σ' := by
        intro kind hh
        simp only [specM_bind] at hh
        cases haD : allocDerived c.d kind ⟨c.d, s, g⟩ σ with
        | err e1 σ1 =>
            have hs := allocDerived_err_state c.d kind _ σ haD; rw [haD] at hh
            injection hh with _ h2; subst h2; subst hs; exact hac
        | fault f => rw [haD] at hh; simp at hh
        | ok hval σ1 => rw [haD] at hh; simp [SpecM.setReg, SpecM.modify] at hh
      cases hk : en.kind with
      | gate gid =>
          rw [hk] at he; simp only [specM_pure, specM_bind] at he
          exact halloc (.gate gid) he
      | mem base len perms =>
          rw [hk] at he; simp only [specM_bind] at he
          cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
          | err e1 σ1 =>
              have hs := narrow_err_state base len perms _ σ hn; rw [hn] at he
              injection he with _ h2; subst h2; subst hs; exact hac
          | fault f => rw [hn] at he; simp at he
          | ok kind σ1 =>
              have hσn := narrow_ok base len perms _ σ hn |>.1; subst σ1
              rw [hn] at he; simp only [specM_bind] at he
              exact halloc kind he

theorem memgrant_acyclic (c : Ctx) (σ : MachineState) (hwf : Wf σ) (hac : Acyclic σ) :
    (∀ x σ',
      ((do let hw ← reg c.d c.op.rs1
           let dw ← reg c.d c.op.rs2
           let (s, g, e) ← capLive c.d hw
           match e.kind with
           | .gate _ => raise .badCap
           | .mem base len perms => do
               let kind ← narrow base len perms dw
               let h ← allocDerived (descDom dw) kind ⟨c.d, s, g⟩
               setReg c.d c.op.rd h) : SpecM Unit) σ = .ok x σ' → Acyclic σ') ∧
    (∀ e σ',
      ((do let hw ← reg c.d c.op.rs1
           let dw ← reg c.d c.op.rs2
           let (s, g, e) ← capLive c.d hw
           match e.kind with
           | .gate _ => raise .badCap
           | .mem base len perms => do
               let kind ← narrow base len perms dw
               let h ← allocDerived (descDom dw) kind ⟨c.d, s, g⟩
               setReg c.d c.op.rd h) : SpecM Unit) σ = .err e σ' → Acyclic σ') := by
  constructor
  · intro x σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 => rw [hcl] at he; simp at he
    | fault f => rw [hcl] at he; simp at he
    | ok rr σ0 =>
        obtain ⟨hσeq, hlive⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, en⟩ := rr; simp only at he hlive
        have hpar : σ.liveRef ⟨c.d, s, g⟩ = true := by
          unfold MachineState.liveRef; rw [hlive]; rfl
        cases hk : en.kind with
        | gate gid => rw [hk] at he; simp [SpecM.raise] at he
        | mem base len perms =>
            rw [hk] at he; simp only [specM_bind] at he
            cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
            | err e1 σ1 => rw [hn] at he; simp at he
            | fault f => rw [hn] at he; simp at he
            | ok kind σ1 =>
                obtain ⟨hσn, off, nlen, np, hkind, hwx, hin⟩ := narrow_ok base len perms _ σ hn
                subst σ1; rw [hn] at he; simp only [specM_bind] at he
                cases haD : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kind ⟨c.d, s, g⟩ σ with
                | err e2 σ2 => rw [haD] at he; simp at he
                | fault f => rw [haD] at he; simp at he
                | ok hh σ2 =>
                    rw [haD] at he
                    simp only [specM_bind, SpecM.setReg, SpecM.modify] at he
                    injection he with _ h2; subst h2
                    exact acyclic_setReg_dom σ2 c.d _ hh
                      (acyclic_allocDerived (descDom _) kind _ σ hpar hwf hac haD)
  · intro e σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := capLive_err_state c.d _ σ hcl; rw [hcl] at he
        injection he with _ h2; subst h2; subst hs; exact hac
    | fault f => rw [hcl] at he; simp at he
    | ok rr σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, en⟩ := rr; simp only at he
        cases hk : en.kind with
        | gate gid =>
            rw [hk] at he; simp only [SpecM.raise] at he
            injection he with _ h2; subst h2; exact hac
        | mem base len perms =>
            rw [hk] at he; simp only [specM_bind] at he
            cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
            | err e1 σ1 =>
                have hs := narrow_err_state base len perms _ σ hn; rw [hn] at he
                injection he with _ h2; subst h2; subst hs; exact hac
            | fault f => rw [hn] at he; simp at he
            | ok kind σ1 =>
                have hσn := narrow_ok base len perms _ σ hn |>.1; subst σ1
                rw [hn] at he; simp only [specM_bind] at he
                cases haD : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kind ⟨c.d, s, g⟩ σ with
                | err e2 σ2 =>
                    have hs := allocDerived_err_state (descDom _) kind _ σ haD; rw [haD] at he
                    injection he with _ h2; subst h2; subst hs; exact hac
                | fault f => rw [haD] at he; simp at he
                | ok hh σ2 => rw [haD] at he; simp [SpecM.setReg, SpecM.modify] at he

theorem caprevoke_acyclic (c : Ctx) (σ : MachineState) (hac : Acyclic σ) :
    (∀ a σ',
      ((do let hw ← reg c.d c.op.rs1
           let (s, g, e) ← capLive c.d hw
           require (e.kind.cls = .mem) .badCap
           let σ0 ← SpecM.get
           let m := σ0.marks ⟨c.d, s, g⟩
           SpecM.set (((σ0.destroyMarked m).sweepRegions).sweepMover)
           setReg c.d c.op.rd 0) : SpecM Unit) σ = .ok a σ' → Acyclic σ') ∧
    (∀ e σ',
      ((do let hw ← reg c.d c.op.rs1
           let (s, g, e) ← capLive c.d hw
           require (e.kind.cls = .mem) .badCap
           let σ0 ← SpecM.get
           let m := σ0.marks ⟨c.d, s, g⟩
           SpecM.set (((σ0.destroyMarked m).sweepRegions).sweepMover)
           setReg c.d c.op.rd 0) : SpecM Unit) σ = .err e σ' → Acyclic σ') := by
  constructor
  · intro a σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 => rw [hcl] at he; simp at he
    | fault f => rw [hcl] at he; simp at he
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, e⟩ := r; simp only at he
        cases hrq : SpecM.require (e.kind.cls = .mem) .badCap σ with
        | err e1 σ1 => rw [hrq] at he; simp at he
        | fault f => rw [hrq] at he; simp at he
        | ok u σ1 =>
            have := require_ok _ _ σ hrq; subst σ1; rw [hrq] at he
            simp only [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            exact acyclic_setReg_dom _ c.d _ _
              (acyclic_sweepMover _ (acyclic_sweepRegions _
                (acyclic_destroyMarked σ _ hac)))
  · intro e σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := capLive_err_state c.d _ σ hcl; rw [hcl] at he
        injection he with _ h2; subst h2; subst hs; exact hac
    | fault f => rw [hcl] at he; simp at he
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, e⟩ := r; simp only at he
        cases hrq : SpecM.require (e.kind.cls = .mem) .badCap σ with
        | err e1 σ1 =>
            have hs := require_err_state _ _ σ hrq; rw [hrq] at he
            injection he with _ h2; subst h2; subst hs; exact hac
        | fault f => rw [hrq] at he; simp at he
        | ok u σ1 =>
            have := require_ok _ _ σ hrq; subst σ1; rw [hrq] at he
            simp [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he


/-- The combined system-op obligation: every system opcode preserves `Wf ∧ Acyclic`
given `Wf ∧ Acyclic`. This is the shape the revocation ops need (`cap_drop`'s Wf
clause itself uses `Acyclic`). -/
def SystemOpsPreserveWfA : Prop :=
  ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ (c : Ctx) (σ : MachineState),
    Wf σ → Acyclic σ → (σ.doms c.d).run = .running → σ.inflight = none →
    (∀ a σ', instr.sem.exec c σ = .ok a σ' → Wf σ' ∧ Acyclic σ') ∧
    (∀ e σ', instr.sem.exec c σ = .err e σ' → Wf σ' ∧ Acyclic σ')

/-- `transferByHandle` preserves `run`/`serving`/`gates` (the `hw = 0` and error
paths are no-ops; the transfer path is `transferCap_frame`). -/
theorem transferByHandle_frame (d to_ : DomainId) (hw : Loom.Word32)
    (σ : MachineState) (a : Loom.Word32) (σ' : MachineState)
    (he : Machines.Lnp64u.Isa.transferByHandle d to_ hw σ = .ok a σ') :
    (∀ d', (σ'.doms d').run = (σ.doms d').run) ∧
    (∀ d', (σ'.doms d').serving = (σ.doms d').serving) ∧ σ'.gates = σ.gates ∧
    σ'.inflight = σ.inflight := by
  unfold Machines.Lnp64u.Isa.transferByHandle at he
  by_cases hz : hw = 0
  · rw [if_pos hz] at he; simp only [specM_pure] at he; obtain ⟨_, rfl⟩ := he
    exact ⟨fun _ => rfl, fun _ => rfl, rfl, rfl⟩
  · simp only [if_neg hz, specM_bind] at he
    cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
    | err e0 σ0 => rw [hcl] at he; simp at he
    | fault f => rw [hcl] at he; simp at he
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
        simp only [SpecM.get, specM_bind] at he
        cases htc : σ.transferCap d sslot to_ with
        | none => rw [htc] at he; simp [SpecM.raise] at he
        | some pr =>
            obtain ⟨σ2, ref⟩ := pr
            rw [htc] at he; simp only [SpecM.set, specM_bind, specM_pure] at he
            injection he with _ h2; subst h2
            exact transferCap_frame σ d sslot to_ σ2 ref htc

/-- `transferByHandle` preserves `Wf ∧ Acyclic`: the `hw = 0` and error paths
leave the state unchanged; the transfer path is `wf_transferCap` /
`acyclic_transferCap`. -/
theorem transferByHandle_preserves (d to_ : DomainId) (hw : Loom.Word32)
    (σ : MachineState) (hwf : Wf σ) (hac : Acyclic σ) :
    (∀ a σ', Machines.Lnp64u.Isa.transferByHandle d to_ hw σ = .ok a σ' → Wf σ' ∧ Acyclic σ') ∧
    (∀ e σ', Machines.Lnp64u.Isa.transferByHandle d to_ hw σ = .err e σ' → Wf σ' ∧ Acyclic σ') := by
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    exact ⟨fun a σ' he => by simp only [specM_pure] at he; obtain ⟨_, rfl⟩ := he; exact ⟨hwf, hac⟩,
           fun e σ' he => by simp [specM_pure] at he⟩
  · simp only [if_neg hz, specM_bind]
    constructor
    · intro a σ' he
      cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none => rw [htc] at he; simp [SpecM.raise] at he
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp only [SpecM.set, specM_bind, specM_pure] at he
              injection he with _ h2; subst h2
              exact ⟨wf_transferCap σ d sslot to_ σ2 ref hwf htc,
                     acyclic_transferCap σ d sslot to_ σ2 ref hwf hac htc⟩
    · intro er σ' he
      cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state d _ σ hcl; rw [hcl] at he
          injection he with _ h2; subst h2; subst hs; exact ⟨hwf, hac⟩
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none =>
              rw [htc] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2; exact ⟨hwf, hac⟩
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- `cap_revoke` preserves `Wf ∧ Acyclic`. -/
theorem caprevoke_preserves_wfa (c : Ctx) (σ : MachineState) (hwf : Wf σ) (hac : Acyclic σ) :
    (∀ a σ',
      ((do let hw ← reg c.d c.op.rs1
           let (s, g, e) ← capLive c.d hw
           require (e.kind.cls = .mem) .badCap
           let σ0 ← SpecM.get
           let m := σ0.marks ⟨c.d, s, g⟩
           SpecM.set (((σ0.destroyMarked m).sweepRegions).sweepMover)
           setReg c.d c.op.rd 0) : SpecM Unit) σ = .ok a σ' → Wf σ' ∧ Acyclic σ') ∧
    (∀ e σ',
      ((do let hw ← reg c.d c.op.rs1
           let (s, g, e) ← capLive c.d hw
           require (e.kind.cls = .mem) .badCap
           let σ0 ← SpecM.get
           let m := σ0.marks ⟨c.d, s, g⟩
           SpecM.set (((σ0.destroyMarked m).sweepRegions).sweepMover)
           setReg c.d c.op.rd 0) : SpecM Unit) σ = .err e σ' → Wf σ' ∧ Acyclic σ') := by
  constructor
  · intro a σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 => rw [hcl] at he; simp at he
    | fault f => rw [hcl] at he; simp at he
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, e⟩ := r; simp only at he
        cases hrq : SpecM.require (e.kind.cls = .mem) .badCap σ with
        | err e1 σ1 => rw [hrq] at he; simp at he
        | fault f => rw [hrq] at he; simp at he
        | ok u σ1 =>
            have := require_ok _ _ σ hrq; subst σ1; rw [hrq] at he
            simp only [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            exact ⟨wf_setReg _ c.d _ _ (wf_destroyMarked_sweep σ ⟨c.d, s, g⟩ hwf),
              acyclic_setReg_dom _ c.d _ _
                (acyclic_sweepMover _ (acyclic_sweepRegions _ (acyclic_destroyMarked σ _ hac)))⟩
  · intro e σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := capLive_err_state c.d _ σ hcl; rw [hcl] at he
        injection he with _ h2; subst h2; subst hs; exact ⟨hwf, hac⟩
    | fault f => rw [hcl] at he; simp at he
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, e⟩ := r; simp only at he
        cases hrq : SpecM.require (e.kind.cls = .mem) .badCap σ with
        | err e1 σ1 =>
            have hs := require_err_state _ _ σ hrq; rw [hrq] at he
            injection he with _ h2; subst h2; subst hs; exact ⟨hwf, hac⟩
        | fault f => rw [hrq] at he; simp at he
        | ok u σ1 =>
            have := require_ok _ _ σ hrq; subst σ1; rw [hrq] at he
            simp [SpecM.get, specM_bind, SpecM.set, SpecM.setReg, SpecM.modify] at he



/-- `gate_call` preserves `Wf ∧ Acyclic`. -/
theorem gatecall_preserves_wfa (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hac : Acyclic σ) (hrun : (σ.doms c.d).run = .running) (hinf : σ.inflight = none) :
    (∀ a σ', (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = .ok a σ' → Wf σ' ∧ Acyclic σ') ∧
    (∀ e σ', (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = .err e σ' → Wf σ' ∧ Acyclic σ') := by
  have body : ∀ (out : Res Unit),
      (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = out →
      (∀ a σ', out = .ok a σ' → Wf σ' ∧ Acyclic σ') ∧
      (∀ e σ', out = .err e σ' → Wf σ' ∧ Acyclic σ') := by
    intro out hout
    unfold Machines.Lnp64u.Isa.Wip.gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl; rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hs; exact ⟨hwf, hac⟩⟩
    | fault f => rw [hcl] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r; simp only at hout
        cases hk : e.kind with
        | mem base len perms => rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
                                exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨hwf, hac⟩⟩
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 => have hst := require_err_state _ _ σ hr1; rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact ⟨hwf, hac⟩⟩
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | ok u1 σ1 =>
                have hc1 := require_cond _ _ σ hr1; have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 => have hst := require_err_state _ _ σ hr2; rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                               exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                 simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact ⟨hwf, hac⟩⟩
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                | ok u2 σ2 =>
                    have hc2 := require_cond _ _ σ hr2; have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 => have hst := require_err_state _ _ σ hr3; rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                   exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                     simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact ⟨hwf, hac⟩⟩
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                    | ok u3 σ3 =>
                        have hc3 := require_cond _ _ σ hr3; have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 => have hst := require_err_state _ _ σ hr4; rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                       exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                         simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact ⟨hwf, hac⟩⟩
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                        | ok u4 σ4 =>
                            have hc4 := require_cond _ _ σ hr4; have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (Machines.Lnp64u.Isa.Wip.gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 => have hst := require_err_state _ _ σ hr5; rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; exact ⟨hwf, hac⟩⟩
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                            | ok u5 σ5 =>
                                have hc5 := require_cond _ _ σ hr5; have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                                | err e6 τ =>
                                    rw [htbh] at hout; subst hout
                                    have hτ := (transferByHandle_preserves c.d cal _ σ hwf hac).2 e6 τ htbh
                                    exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    obtain ⟨hwfτ, hacτ⟩ := (transferByHandle_preserves c.d cal _ σ hwf hac).1 argHandle τ htbh
                                    obtain ⟨hfrun, hfserv, hfgates, hfinf⟩ := transferByHandle_frame c.d cal _ σ argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify] at hout
                                    subst hout
                                    have hgsnoneσ : (σ.gates gid).act = none := by
                                      rw [Option.isNone_iff_eq_none] at hc1; exact hc1
                                    have hcalne : cal ≠ c.d := of_decide_eq_true hc2
                                    have hcalrunσ : (σ.doms cal).run = .running := of_decide_eq_true hc3
                                    have hcalservσ : (σ.doms cal).serving = none := by
                                      rw [Option.isNone_iff_eq_none] at hc4; exact hc4
                                    have hdepthmax : Machines.Lnp64u.Isa.Wip.gateDepth c σ ≤ maxChainDepth := of_decide_eq_true hc5
                                    have hdepth1 : 1 ≤ Machines.Lnp64u.Isa.Wip.gateDepth c σ := by
                                      unfold Machines.Lnp64u.Isa.Wip.gateDepth
                                      split
                                      · split
                                        · omega
                                        · omega
                                      · omega
                                    have hgsnoneτ : (τ.gates gid).act = none := by rw [hfgates]; exact hgsnoneσ
                                    have hcalleeτ : (τ.gates gid).config.callee = cal := by rw [hfgates]
                                    have hcalrunτ : (τ.doms cal).run = .running := by rw [hfrun]; exact hcalrunσ
                                    have hcalservτ : (τ.doms cal).serving = none := by rw [hfserv]; exact hcalservσ
                                    have hcallerrunτ : (τ.doms c.d).run = .running := by rw [hfrun]; exact hrun
                                    have hinfτ : τ.inflight = none := by rw [hfinf]; exact hinf
                                    have hgseqτ : (σ.gates gid) = (τ.gates gid) := by rw [hfgates]
                                    obtain ⟨hw', ha'⟩ := wf_acyclic_gateCall τ c.d cal gid
                                      { caller := c.d, callerRd := c.op.rd, savedRegs := (τ.doms cal).regs,
                                        savedPc := (τ.doms cal).pc, savedServing := (τ.doms cal).serving,
                                        depth := Machines.Lnp64u.Isa.Wip.gateDepth c σ, donated := (τ.doms c.d).maxDonation }
                                      (fun r => if r = (1 : Fin numRegs) then argHandle else 0)
                                      (τ.gates gid).config.entry
                                      hgsnoneτ hcalleeτ hcalne hcalrunτ hcalservτ rfl hcalservτ hdepth1 hdepthmax
                                      hcallerrunτ hinfτ hwfτ hacτ
                                    refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    rw [hgseqτ]; exact ⟨hw', ha'⟩
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩


/-- `gate_return` preserves `Wf ∧ Acyclic`. -/
theorem gatereturn_preserves_wfa (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hac : Acyclic σ) (hrun : (σ.doms c.d).run = .running) (hinf : σ.inflight = none) :
    (∀ a σ',
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = .ok a σ' →
        Wf σ' ∧ Acyclic σ') ∧
    (∀ e σ',
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = .err e σ' →
        Wf σ' ∧ Acyclic σ') := by
  have body : ∀ (out : Res Unit),
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = out →
      (∀ a σ', out = .ok a σ' → Wf σ' ∧ Acyclic σ') ∧
      (∀ e σ', out = .err e σ' → Wf σ' ∧ Acyclic σ') := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none => rw [hserv] at hout; simp [SpecM.fatal] at hout; subst hout
              exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none => simp only [hgact] at hout; simp [SpecM.fatal] at hout; subst hout
                  exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
        | some act =>
            simp only [hgact] at hout; simp only [SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f => rw [htbh] at hout; subst hout
                         exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | err e0 τ =>
                rw [htbh] at hout; subst hout
                have hτ := (transferByHandle_preserves c.d act.caller _ σ hwf hac).2 e0 τ htbh
                exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
            | ok reply τ =>
                rw [htbh] at hout
                obtain ⟨hwfτ, hacτ⟩ := (transferByHandle_preserves c.d act.caller _ σ hwf hac).1 reply τ htbh
                obtain ⟨hfrun, hfserv, hfgates, hfinf⟩ := transferByHandle_frame c.d act.caller _ σ reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                  SpecM.setReg] at hout
                subst hout
                have hservτ : (τ.doms c.d).serving = some gid := by rw [hfserv]; exact hserv
                have hgactτ : (τ.gates gid).act = some act := by rw [hfgates]; exact hgact
                have hrunτ : (τ.doms c.d).run = .running := by rw [hfrun]; exact hrun
                have hinfτ : τ.inflight = none := by rw [hfinf]; exact hinf
                obtain ⟨hw', ha'⟩ := wf_acyclic_gateReturn τ c.d gid act reply hservτ hgactτ hrunτ hinfτ hwfτ hacτ
                exact ⟨fun a σ' h => by
                  simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨hw', ha'⟩,
                  fun e σ' h => by simp at h⟩
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩


/-- Dispatch. -/
theorem system_preserves_acyclic : SystemOpsPreserveAcyclic := by
  intro instr hmem c σ hwf hac hrun hinf
  fin_cases hmem
  case _ => exact ⟨capdup_acyclic c σ hwf hac, capdup_acyclic_err c σ hac⟩
  case _ => exact ⟨fun a σ' he => ((capdrop_preserves_wfa c σ hwf hac).1 a σ' he).2,
                   fun e σ' he => ((capdrop_preserves_wfa c σ hwf hac).2 e σ' he).2⟩
  case _ => exact caprevoke_acyclic c σ hac
  case _ => exact memgrant_acyclic c σ hwf hac
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
  case _ => exact ⟨fun a σ' he => ((gatecall_preserves_wfa c σ hwf hac hrun hinf).1 a σ' he).2,
      fun e σ' he => ((gatecall_preserves_wfa c σ hwf hac hrun hinf).2 e σ' he).2⟩
  case _ => exact ⟨fun a σ' he => ((gatereturn_preserves_wfa c σ hwf hac hrun hinf).1 a σ' he).2,
      fun e σ' he => ((gatereturn_preserves_wfa c σ hwf hac hrun hinf).2 e σ' he).2⟩
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

/-- **The combined dispatch.** 10 of 11 ops discharged: `cap_drop` via
`capdrop_preserves_wfa`; the other 7 by pairing each op's `Wf` proof with its
`system_preserves_acyclic` clause. Only `cap_revoke` and the 2 gate ops remain. -/
theorem system_preserves_wfa : SystemOpsPreserveWfA := by
  intro instr hmem c σ hwf hac hrun hinf
  have hA := system_preserves_acyclic instr hmem c σ hwf hac hrun hinf
  fin_cases hmem
  case _ => -- cap_dup
    exact ⟨fun a σ' he => ⟨capdup_preserves c σ hwf hinf a σ' he, hA.1 a σ' he⟩,
           fun e σ' he => ⟨capdup_err c σ hwf e σ' he, hA.2 e σ' he⟩⟩
  case _ => exact capdrop_preserves_wfa c σ hwf hac  -- cap_drop
  case _ => exact caprevoke_preserves_wfa c σ hwf hac
  case _ => -- mem_grant
    exact ⟨fun a σ' he => ⟨(memgrant_preserves c σ hwf).1 a σ' he, hA.1 a σ' he⟩,
           fun e σ' he => ⟨(memgrant_preserves c σ hwf).2 e σ' he, hA.2 e σ' he⟩⟩
  case _ => -- map
    exact ⟨fun a σ' he => ⟨(map_preserves c σ hwf hinf).1 a σ' he, hA.1 a σ' he⟩,
           fun e σ' he => ⟨(map_preserves c σ hwf hinf).2 e σ' he, hA.2 e σ' he⟩⟩
  case _ => -- unmap
    refine ⟨fun a σ' he => ⟨?_, hA.1 a σ' he⟩, fun e σ' he => ⟨?_, hA.2 e σ' he⟩⟩
    · exact ((PreservesWf.bind (PreservesWf.clearRegion _ _)
        (fun _ => PreservesWf.setReg _ _ _)) σ hwf hinf).1 a σ' he |>.1
    · exact ((PreservesWf.bind (PreservesWf.clearRegion _ _)
        (fun _ => PreservesWf.setReg _ _ _)) σ hwf hinf).2 e σ' he |>.1
  case _ => exact gatecall_preserves_wfa c σ hwf hac hrun hinf
  case _ => exact gatereturn_preserves_wfa c σ hwf hac hrun hinf
  case _ => -- move
    exact ⟨fun a σ' he => ⟨move_ok c σ hwf a σ' he, hA.1 a σ' he⟩,
           fun e σ' he => ⟨move_err c σ hwf e σ' he, hA.2 e σ' he⟩⟩
  case _ => -- yield
    refine ⟨fun a σ' he => ⟨?_, hA.1 a σ' he⟩, fun e σ' he => ⟨?_, hA.2 e σ' he⟩⟩
    · exact ((PreservesWf.bind (PreservesWf.updDomBudget _ _)
        (fun _ => PreservesWf.setReg _ _ _)) σ hwf hinf).1 a σ' he |>.1
    · exact ((PreservesWf.bind (PreservesWf.updDomBudget _ _)
        (fun _ => PreservesWf.setReg _ _ _)) σ hwf hinf).2 e σ' he |>.1
  case _ => -- halt
    refine ⟨fun a σ' he => ⟨?_, hA.1 a σ' he⟩, fun e σ' he => ⟨?_, hA.2 e σ' he⟩⟩
    · simp only [SpecM.modify] at he; injection he with h1 h2; subst h2
      exact haltDom_preserves_wf σ c.d 0 hwf hrun hinf
    · simp [SpecM.modify] at he

end Isa.Wip

end Machines.Lnp64u