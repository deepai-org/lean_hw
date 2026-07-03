import Machines.Lnp64u.Logic.ExecWf
import Machines.Lnp64u.Logic.BaseOpsWf
import Machines.Lnp64u.Isa.System

/-!
# System opcodes preserve the invariant (work in progress)

`SystemOpsPreserveWf` (the sole remaining Phase-1 obligation) requires all 11
system opcodes to preserve `Wf`. The scheduling/mapping ops (`yield`, `unmap`)
touch only budget/region state and are **proved** here via the `PreservesWf`
toolkit. The nine capability/gate/Mover ops call the capability-kernel
operations (`installDerived`, `clearSlot`, `destroyMarked`, `transferCap`, the
sweeps, gate call/return, the Mover programming) — proving those is exactly
T2/T3/T8/T9's kernel content, and they remain (each isolated as its own
`sorry` below, in the `Wip` namespace so the audit's sorry policy permits it).
-/

namespace Machines.Lnp64u.Isa.Wip

open Machines.Lnp64u Loom.Isa SpecM

/-- On success, `capLive` leaves the state unchanged and its result names a
live capability of the queried domain. Infrastructure for the capability
system-op proofs (`cap_dup`/`cap_drop`/`cap_revoke`/`mem_grant`/`map`). -/
theorem capLive_ok (d : DomainId) (w : Loom.Word32) (σ : MachineState)
    {r : Slot × Gen × CapEntry} {σ0 : MachineState} (he : capLive d w σ = .ok r σ0) :
    σ0 = σ ∧ (σ.doms d).liveCap r.1 r.2.1 = some r.2.2 := by
  have hred : capLive d w σ =
      (match (σ.doms d).liveCap (Handle.decode w).slot (Handle.decode w).gen with
        | none => SpecM.raise .staleHandle
        | some e => (SpecM.require ((Handle.decode w).cls = e.kind.cls) .badCap >>=
            fun _ => (Pure.pure ((Handle.decode w).slot, (Handle.decode w).gen, e) : SpecM _))) σ :=
    rfl
  rw [hred] at he
  cases hlc : (σ.doms d).liveCap (Handle.decode w).slot (Handle.decode w).gen with
  | none => rw [hlc] at he; simp [SpecM.raise] at he
  | some e =>
      rw [hlc] at he
      by_cases hcls : (Handle.decode w).cls = e.kind.cls
      · simp only [SpecM.require, hcls, if_true, specM_bind, specM_pure] at he
        injection he with h1 h2; subst h2
        refine ⟨rfl, ?_⟩; rw [← h1]; exact hlc
      · simp [SpecM.require, hcls, specM_bind, SpecM.raise] at he

/-- On an `err` outcome, `capLive` leaves the state unchanged. -/
theorem capLive_err_state (d : DomainId) (w : Loom.Word32) (σ : MachineState)
    {e : Errno} {σ0 : MachineState} (he : capLive d w σ = .err e σ0) : σ0 = σ := by
  have hred : capLive d w σ =
      (match (σ.doms d).liveCap (Handle.decode w).slot (Handle.decode w).gen with
        | none => SpecM.raise .staleHandle
        | some en => (SpecM.require ((Handle.decode w).cls = en.kind.cls) .badCap >>=
            fun _ => (Pure.pure ((Handle.decode w).slot, (Handle.decode w).gen, en) : SpecM _))) σ :=
    rfl
  rw [hred] at he
  cases hlc : (σ.doms d).liveCap (Handle.decode w).slot (Handle.decode w).gen with
  | none => rw [hlc] at he; simp only [SpecM.raise] at he; injection he with _ h2; exact h2.symm
  | some en =>
      rw [hlc] at he
      by_cases hcls : (Handle.decode w).cls = en.kind.cls
      · simp [SpecM.require, hcls, specM_bind, specM_pure] at he
      · simp only [SpecM.require, hcls, if_false, specM_bind, SpecM.raise] at he
        injection he with _ h2; exact h2.symm

/-- `map` preserves the invariant: it installs a region caching a *live* memory
capability's authority (dominated reflexively), via `wf_installRegion`; all
error paths (`capLive` failing, or a gate handle) leave the state unchanged. -/
theorem map_preserves (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hinf : σ.inflight = none) :
    (∀ x σ',
      ((do let hw ← reg c.d c.op.rs1
           let (s, g, e) ← capLive c.d hw
           match e.kind with
           | .gate _ => raise .badCap
           | .mem base len perms => do
               let ri : RegionId :=
                 ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
               let rgn : Region := { base := base, len := len, perms := perms
                                     backing := ⟨c.d, s, g⟩ }
               updDom c.d fun ds =>
                 { ds with regions := Loom.Fun.update ds.regions ri (some rgn) }
               setReg c.d c.op.rd 0) : SpecM Unit) σ = .ok x σ' → Wf σ') ∧
    (∀ e σ',
      ((do let hw ← reg c.d c.op.rs1
           let (s, g, e) ← capLive c.d hw
           match e.kind with
           | .gate _ => raise .badCap
           | .mem base len perms => do
               let ri : RegionId :=
                 ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
               let rgn : Region := { base := base, len := len, perms := perms
                                     backing := ⟨c.d, s, g⟩ }
               updDom c.d fun ds =>
                 { ds with regions := Loom.Fun.update ds.regions ri (some rgn) }
               setReg c.d c.op.rd 0) : SpecM Unit) σ = .err e σ' → Wf σ') := by
  refine ⟨?_, ?_⟩
  · intro x σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 => rw [hcl] at he; simp at he
    | fault f => rw [hcl] at he; simp at he
    | ok rr σ0 =>
        obtain ⟨hσeq, hlive⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he
        obtain ⟨s, g, en⟩ := rr
        simp only at he hlive
        cases hk : en.kind with
        | gate gi => rw [hk] at he; simp [SpecM.raise] at he
        | mem base len perms =>
            rw [hk] at he
            simp only [specM_bind, SpecM.updDom, SpecM.modify, SpecM.setReg] at he
            injection he with _ h2; subst h2
            have hb : ∃ e', ((σ.doms c.d).liveCap s g) = some e' ∧
                (CapKind.mem base len perms).le e'.kind :=
              ⟨en, hlive, by rw [hk]; exact CapKind.le_refl _⟩
            exact wf_setReg _ c.d _ 0 (wf_installRegion σ c.d _ _ hb hwf)
  · intro e σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hσ : σ0 = σ := capLive_err_state c.d _ σ hcl
        rw [hcl] at he; injection he with _ h2; subst h2; subst hσ; exact hwf
    | fault f => rw [hcl] at he; simp at he
    | ok rr σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he
        obtain ⟨s, g, en⟩ := rr
        simp only at he
        cases hk : en.kind with
        | gate gi => rw [hk] at he; simp only [SpecM.raise] at he
                     injection he with _ h2; subst h2; exact hwf
        | mem base len perms =>
            rw [hk] at he
            simp only [specM_bind, SpecM.updDom, SpecM.modify, SpecM.setReg] at he
            simp at he

/-- The per-opcode dispatch of `SystemOpsPreserveWf`. Two of eleven ops proved
(`unmap`, `yield`); the nine capability/gate/Mover ops are the remaining
kernel-level core. -/
theorem system_preserves : SystemOpsPreserveWf := by
  intro instr hmem c σ hwf hrun hinf
  fin_cases hmem
  case _ => sorry  -- cap_dup    (installDerived)
  case _ => sorry  -- cap_drop   (reparent/orphan + clearSlot + sweeps)
  case _ => sorry  -- cap_revoke (destroyMarked + sweeps)
  case _ => sorry  -- mem_grant  (installDerived, cross-domain)
  case _ => exact map_preserves c σ hwf hinf
  -- unmap: clear a region register — proved
  case _ =>
    refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
    · exact (PreservesWf.bind (PreservesWf.clearRegion _ _)
        (fun _ => PreservesWf.setReg _ _ _) σ hwf hinf).1 a σ' he |>.1
    · exact (PreservesWf.bind (PreservesWf.clearRegion _ _)
        (fun _ => PreservesWf.setReg _ _ _) σ hwf hinf).2 e σ' he |>.1
  case _ => sorry  -- gate_call
  case _ => sorry  -- gate_return
  case _ => sorry  -- move
  -- yield: zero the budget — proved
  case _ =>
    refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
    · exact (PreservesWf.bind (PreservesWf.updDomBudget _ _)
        (fun _ => PreservesWf.setReg _ _ _) σ hwf hinf).1 a σ' he |>.1
    · exact (PreservesWf.bind (PreservesWf.updDomBudget _ _)
        (fun _ => PreservesWf.setReg _ _ _) σ hwf hinf).2 e σ' he |>.1
  -- halt: voluntary domain-fatal — haltDom on the running caller
  case _ =>
    refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
    · simp only [SpecM.modify] at he; injection he with h1 h2; subst h2
      exact haltDom_preserves_wf σ c.d 0 hwf hrun hinf
    · simp [SpecM.modify] at he

end Machines.Lnp64u.Isa.Wip
