import Machines.Lnp64u.Logic.ExecWf
import Mathlib.Tactic.FinCases
import Machines.Lnp64u.Logic.SystemOpsWf

/-!
# Inflight-preservation of the exec semantics (T7 support)

No instruction's `exec` ever writes the core's `inflight` latch: every state
primitive touches `doms`/`gates`/`mover`/`mem` only. `InflightEq` is the
`SpecM`-level combinator (mirroring `SlotGenLe`) carrying this through the
exec semantics of all 25 opcodes; `retire_inflight` lifts it to the retire
glue, and the `step`-level countdown/retire characterization at the end is
what T7's `wcet_retirement` inducts on.
-/

namespace Machines.Lnp64u

open Loom.Isa SpecM Machines.Lnp64u.Isa

/-- A `SpecM` computation leaves `inflight` untouched on every `ok`/`err`
outcome (`fault` carries no state). -/
def InflightEq {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', mm σ = .ok a σ' → σ'.inflight = σ.inflight) ∧
       (∀ e σ', mm σ = .err e σ' → σ'.inflight = σ.inflight)

theorem InflightEq.of_preserves {α : Type} (mm : SpecM α)
    (hok : ∀ σ a σ', mm σ = .ok a σ' → σ'.inflight = σ.inflight)
    (herr : ∀ σ e σ', mm σ = .err e σ' → σ'.inflight = σ.inflight) :
    InflightEq mm :=
  fun σ => ⟨hok σ, herr σ⟩

theorem InflightEq.pure {α : Type} (a : α) : InflightEq (Pure.pure a : SpecM α) :=
  InflightEq.of_preserves _
    (fun σ a' σ' he => by rw [specM_pure] at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he => by rw [specM_pure] at he; simp at he)

theorem InflightEq.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : InflightEq m) (hf : ∀ a, InflightEq (f a)) : InflightEq (m >>= f) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 rw [(hf a σ1).1 b σ' he, (hm σ).1 a σ1 hmσ]
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 rw [(hf a σ1).2 e σ' he, (hm σ).1 a σ1 hmσ]
    | err e1 σ1 => rw [hmσ] at he; injection he with h1 h2; subst h2; exact (hm σ).2 e1 σ1 hmσ
    | fault g => rw [hmσ] at he; simp at he

theorem InflightEq.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : InflightEq m1) (h2 : InflightEq m2) : InflightEq (if b then m1 else m2) := by
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact h2
  · exact h1

theorem InflightEq.reg (d : DomainId) (r : RegId) : InflightEq (SpecM.reg d r) :=
  InflightEq.of_preserves _
    (fun σ a σ' he => by unfold SpecM.reg at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he => by unfold SpecM.reg at he; simp at he)

theorem InflightEq.raise {α : Type} (e : Errno) : InflightEq (SpecM.raise e : SpecM α) :=
  InflightEq.of_preserves _
    (fun σ a σ' he => by unfold SpecM.raise at he; simp at he)
    (fun σ e' σ' he => by unfold SpecM.raise at he; injection he with _ h2; subst h2; rfl)

theorem InflightEq.require (cond : Bool) (e : Errno) : InflightEq (SpecM.require cond e) :=
  InflightEq.of_preserves _
    (fun σ a σ' he => by rw [require_ok cond e σ he])
    (fun σ e' σ' he => by rw [require_err_state cond e σ he])

theorem InflightEq.demand (cond : Bool) (f : Fault) : InflightEq (SpecM.demand cond f) :=
  InflightEq.of_preserves _
    (fun σ a σ' he => by rw [demand_ok cond f σ he])
    (fun σ e σ' he => by
      unfold SpecM.demand at he; split at he
      · simp [specM_pure] at he
      · simp [SpecM.fatal] at he)

theorem InflightEq.load (d : DomainId) (a : Addr) : InflightEq (SpecM.load d a) :=
  InflightEq.of_preserves _
    (fun σ v σ' he => by rw [load_ok d a σ he])
    (fun σ e σ' he => by rw [load_err_state d a σ he])

theorem InflightEq.get : InflightEq SpecM.get :=
  InflightEq.of_preserves _
    (fun σ a σ' he => by unfold SpecM.get at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he => by unfold SpecM.get at he; simp at he)

/-- A `modify` whose function preserves `inflight` is `InflightEq`. -/
theorem InflightEq.modifyPres (f : MachineState → MachineState)
    (hf : ∀ σ, (f σ).inflight = σ.inflight) : InflightEq (SpecM.modify f) :=
  InflightEq.of_preserves _
    (fun σ a σ' he => by
      unfold SpecM.modify at he; injection he with _ h2; subst h2; exact hf σ)
    (fun σ e σ' he => by unfold SpecM.modify at he; simp at he)

@[simp] theorem setDom_inflight (σ : MachineState) (d : DomainId)
    (f : DomainState → DomainState) : (σ.setDom d f).inflight = σ.inflight := rfl

@[simp] theorem write_inflight (σ : MachineState) (a : Addr) (v : Loom.Word32) :
    (σ.write a v).inflight = σ.inflight := rfl

@[simp] theorem reparent_inflight (σ : MachineState) (old new : CapRef) :
    (σ.reparent old new).inflight = σ.inflight := rfl

theorem InflightEq.setReg (d : DomainId) (r : RegId) (v : Loom.Word32) :
    InflightEq (SpecM.setReg d r v) :=
  InflightEq.modifyPres _ (fun _ => rfl)

theorem InflightEq.updDom (d : DomainId) (f : DomainState → DomainState) :
    InflightEq (SpecM.updDom d f) :=
  InflightEq.modifyPres _ (fun _ => rfl)

theorem InflightEq.store (d : DomainId) (a : Addr) (v : Loom.Word32) :
    InflightEq (SpecM.store d a v) := by
  intro σ; unfold SpecM.store; refine ⟨?_, ?_⟩
  · intro x σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2; subst h2; rfl
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

/-- `haltDom` never touches `inflight`: `haltBase` is a `setDom`, and the gate
unwind is a gates-record update plus a `setDom`. -/
theorem haltDom_inflight (σ : MachineState) (d : DomainId) (c : Loom.Word32) :
    (σ.haltDom d c).inflight = σ.inflight := by
  unfold MachineState.haltDom
  split
  · rfl
  · split
    · rfl
    · rfl

theorem InflightEq.halt (c : Ctx) :
    InflightEq (SpecM.modify (fun σ => σ.haltDom c.d 0)) :=
  InflightEq.modifyPres _ (fun σ => haltDom_inflight σ c.d 0)

theorem InflightEq.capLive (d : DomainId) (hw : Loom.Word32) :
    InflightEq (Machines.Lnp64u.Isa.capLive d hw) :=
  InflightEq.of_preserves _
    (fun σ r σ' he => by rw [(Machines.Lnp64u.Isa.Wip.capLive_ok d hw σ he).1])
    (fun σ e σ' he => by rw [Machines.Lnp64u.Isa.Wip.capLive_err_state d hw σ he])

theorem InflightEq.narrow (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32) :
    InflightEq (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  InflightEq.of_preserves _
    (fun σ k σ' he => by rw [(Machines.Lnp64u.Isa.Wip.narrow_ok base len perms dw σ he).1])
    (fun σ e σ' he => by rw [Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms dw σ he])

theorem InflightEq.allocDerived (owner : DomainId) (kind : CapKind) (parent : CapRef) :
    InflightEq (Machines.Lnp64u.Isa.allocDerived owner kind parent) := by
  intro σ; refine ⟨?_, ?_⟩
  · intro hw σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp [SpecM.raise] at he
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp [SpecM.raise] at he
        | some lc =>
            rw [hfc] at he
            simp only [SpecM.set, specM_bind, specM_pure] at he
            injection he with _ h2
            rw [← h2]; rfl
  · intro e σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
        | some lc => rw [hfc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- **The base opcodes never touch `inflight`.** Their `exec` only writes
regs/pc/memory. -/
theorem base_inflight_eq : ∀ instr ∈ base, ∀ c : Ctx, InflightEq (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.setReg _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.setReg _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.setReg _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.setReg _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.setReg _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.setReg _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.setReg _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.setReg _ _ _)
  · exact InflightEq.setReg _ _ _
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.load _ _) (fun _ => InflightEq.setReg _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.store _ _ _))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.iteBool _ (InflightEq.updDom _ _) (InflightEq.pure ())))
  · exact InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.bind (InflightEq.reg _ _) (fun _ => InflightEq.iteBool _ (InflightEq.updDom _ _) (InflightEq.pure ())))
  · exact InflightEq.bind (InflightEq.reg _ _)
      (fun _ => InflightEq.bind (InflightEq.setReg _ _ _) (fun _ => InflightEq.updDom _ _))

namespace Wip
open Machines.Lnp64u.Isa Machines.Lnp64u.Isa.Wip

/-- **`transferCap` never touches `inflight`**: install-at-recipient, reparent,
`clearSlot`, and both sweeps are `doms`/`mover`/`mem`-level only. -/
theorem transferCap_inflight (σ : MachineState) (from_ : DomainId) (s : Slot) (to_ : DomainId)
    (τ : MachineState) (ref : CapRef) (h : σ.transferCap from_ s to_ = some (τ, ref)) :
    τ.inflight = σ.inflight := by
  unfold MachineState.transferCap at h
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hfs : σ.freeSlot to_ with
      | none => rw [hfs] at h; simp at h
      | some s2 =>
          rw [hfs] at h; simp only [Option.bind_some] at h
          have key : ∀ (σ₁ : MachineState), σ₁.inflight = σ.inflight →
              some (((((σ₁.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
                ⟨to_, s2, (σ.doms to_).slotGen s2⟩).clearSlot from_ s).sweepRegions).sweepMover),
                (⟨to_, s2, (σ.doms to_).slotGen s2⟩ : CapRef))
                = some (τ, ref) →
              τ.inflight = σ.inflight := by
            intro σ₁ hpre heq
            injection heq with heq; injection heq with hτ _; subst hτ
            rw [sweepMover_inflight, sweepRegions_inflight, clearSlot_inflight,
                reparent_inflight]
            exact hpre
          cases hl : e.lineage with
          | none =>
              rw [hl] at h; simp only [Option.pure_def, Option.bind_some] at h
              exact key (σ.setDom to_ (fun ds =>
                  { ds with caps := Loom.Fun.update ds.caps s2 (some { kind := e.kind, lineage := none }) }))
                rfl h
          | some l =>
              rw [hl] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
              cases hc : (σ.doms from_).lineage l with
              | none => rw [hc] at h; simp at h
              | some cell =>
                  rw [hc] at h; simp only [Option.bind_some] at h
                  cases hfc : σ.freeCell to_ with
                  | none => rw [hfc] at h; simp at h
                  | some l' =>
                      rw [hfc] at h; simp only [Option.pure_def, Option.bind_some] at h
                      exact key (σ.setDom to_ (fun ds =>
                          { ds with
                            caps := Loom.Fun.update ds.caps s2 (some { kind := e.kind, lineage := some l' })
                            lineage := Loom.Fun.update ds.lineage l' (some cell) }))
                        rfl h

theorem transferByHandle_inflight_eq (d to_ : DomainId) (hw : Loom.Word32) :
    InflightEq (transferByHandle d to_ hw) := by
  intro σ
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    exact ⟨fun a σ' he => by
        simp only [specM_pure] at he; obtain ⟨_, rfl⟩ := he; rfl,
      fun e σ' he => by simp [specM_pure] at he⟩
  · simp only [if_neg hz, specM_bind]
    constructor
    · intro a σ' he
      cases hcl : capLive d hw σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none => rw [htc] at he; simp [SpecM.raise] at he
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp only [SpecM.set, specM_bind, specM_pure] at he
              injection he with _ h2; subst h2
              exact transferCap_inflight σ d sslot to_ σ2 ref htc
    · intro er σ' he
      cases hcl : capLive d hw σ with
      | err e0 σ0 =>
          have hs := capLive_err_state d _ σ hcl; rw [hcl] at he
          injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none =>
              rw [htc] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2; rfl
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- `gate_call` never touches `inflight`: the capability transfer preserves it
and the activation / serving / run bookkeeping is `gates`/`doms`-level. -/
theorem gatecall_inflight_eq (c : Ctx) : InflightEq (gateCallExec c) := by
  intro σ
  have body : ∀ (out : Res Unit), gateCallExec c σ = out →
      (∀ a σ', out = .ok a σ' → σ'.inflight = σ.inflight) ∧
      (∀ e σ', out = .err e σ' → σ'.inflight = σ.inflight) := by
    intro out hout
    unfold gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := capLive_err_state c.d _ σ hcl; rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hs; rfl⟩
    | fault f => rw [hcl] at hout; subst hout
                 exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r; simp only at hout
        cases hk : e.kind with
        | mem base len perms =>
            rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
              simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; rfl⟩
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 => have hst := require_err_state _ _ σ hr1; rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | ok u1 σ1 =>
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 => have hst := require_err_state _ _ σ hr2; rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                               exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                 simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                | ok u2 σ2 =>
                    have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 => have hst := require_err_state _ _ σ hr3; rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                   exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                     simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                    | ok u3 σ3 =>
                        have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 => have hst := require_err_state _ _ σ hr4; rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                       exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                         simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                        | ok u4 σ4 =>
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 => have hst := require_err_state _ _ σ hr5; rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                            | ok u5 σ5 =>
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                                | err e6 τ =>
                                    rw [htbh] at hout; subst hout
                                    have hτ := (transferByHandle_inflight_eq c.d cal _ σ).2 e6 τ htbh
                                    exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    have hτ := (transferByHandle_inflight_eq c.d cal _ σ).1 argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify] at hout
                                    subst hout
                                    refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    exact hτ
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩

/-- `gate_return` never touches `inflight`: the reply transfer preserves it and
the context restore is `gates`/`doms`-level. -/
theorem gatereturn_inflight_eq (c : Ctx) :
    InflightEq ((do
      let σ0 ← SpecM.get
      match (σ0.doms c.d).serving with
      | none => SpecM.fatal .protocol
      | some gid =>
          match (σ0.gates gid).act with
          | none => SpecM.fatal .protocol
          | some act => do
              let rw ← SpecM.reg c.d c.op.rs1
              let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
              let σ1 ← SpecM.get
              SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
              SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
              SpecM.updDom act.caller (fun ds => { ds with run := .running })
              SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) := by
  intro σ
  have body : ∀ (out : Res Unit),
      ((do
        let σ0 ← SpecM.get
        match (σ0.doms c.d).serving with
        | none => SpecM.fatal .protocol
        | some gid =>
            match (σ0.gates gid).act with
            | none => SpecM.fatal .protocol
            | some act => do
                let rw ← SpecM.reg c.d c.op.rs1
                let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                let σ1 ← SpecM.get
                SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                SpecM.updDom act.caller (fun ds => { ds with run := .running })
                SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = out →
      (∀ a σ', out = .ok a σ' → σ'.inflight = σ.inflight) ∧
      (∀ e σ', out = .err e σ' → σ'.inflight = σ.inflight) := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none => rw [hserv] at hout; simp only [SpecM.fatal] at hout; subst hout
              exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none => simp only [hgact] at hout; simp only [SpecM.fatal] at hout; subst hout
                  exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
        | some act =>
            simp only [hgact, SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f => rw [htbh] at hout; subst hout
                         exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | err e1 τ =>
                rw [htbh] at hout; subst hout
                have hτ := (transferByHandle_inflight_eq c.d act.caller _ σ).2 e1 τ htbh
                exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
            | ok reply τ =>
                rw [htbh] at hout
                have hτ := (transferByHandle_inflight_eq c.d act.caller _ σ).1 reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                           SpecM.setReg] at hout
                subst hout
                refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                exact hτ
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩

/-- `move` never touches `inflight`: a read-only prefix, then a `mover`-record
write plus the `rd` write-back. -/
theorem move_inflight_eq (c : Ctx) : InflightEq (moveExec c) := by
  intro σ; refine ⟨fun x σ' he => ?_, fun x σ' he => ?_⟩
  ·
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
                                                        rfl
  ·
    simp only [moveExec, SpecM.get, specM_bind] at he
    cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
    | err e0 σ0 => have hq := require_err_state _ _ σ hr0; rw [hr0] at he; injection he with _ h2; subst h2; subst hq; rfl
    | fault f => rw [hr0] at he; simp at he
    | ok u0 σ0 =>
        have hh0 := require_ok _ _ σ hr0; subst σ0
        rw [hr0] at he; simp only [SpecM.reg] at he
        set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
        cases hl1 : load c.d B σ with
        | err e σe => have hq := load_err_state _ _ σ hl1; rw [hl1] at he; injection he with _ h2; subst h2; subst hq; rfl
        | fault f => rw [hl1] at he; simp at he
        | ok srcH σ1 =>
            have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
            cases hl2 : load c.d (B + 1) σ with
            | err e σe => have hq := load_err_state _ _ σ hl2; rw [hl2] at he; injection he with _ h2; subst h2; subst hq; rfl
            | fault f => rw [hl2] at he; simp at he
            | ok dstH σ2 =>
                have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
                cases hl3 : load c.d (B + 2) σ with
                | err e σe => have hq := load_err_state _ _ σ hl3; rw [hl3] at he; injection he with _ h2; subst h2; subst hq; rfl
                | fault f => rw [hl3] at he; simp at he
                | ok lenW σ3 =>
                    have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                    cases hl4 : load c.d (B + 3) σ with
                    | err e σe => have hq := load_err_state _ _ σ hl4; rw [hl4] at he; injection he with _ h2; subst h2; subst hq; rfl
                    | fault f => rw [hl4] at he; simp at he
                    | ok stW σ4 =>
                        have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                        cases hc1 : capLive c.d srcH σ with
                        | err e σe => have hq := capLive_err_state c.d _ σ hc1; rw [hc1] at he; injection he with _ h2; subst h2; subst hq; rfl
                        | fault f => rw [hc1] at he; simp at he
                        | ok rs σ5 =>
                            have hcs := capLive_ok c.d _ σ hc1; obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                            rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                            cases hc2 : capLive c.d dstH σ with
                            | err e σe => have hq := capLive_err_state c.d _ σ hc2; rw [hc2] at he; injection he with _ h2; subst h2; subst hq; rfl
                            | fault f => rw [hc2] at he; simp at he
                            | ok rdd σ6 =>
                                have hcd := capLive_ok c.d _ σ hc2; obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                                rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                                cases hks : es.kind with
                                | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                            | gate _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
                                            | mem _ _ _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
                                | mem sb sl sp =>
                                    cases hkd : ed.kind with
                                    | gate _ => rw [hks, hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
                                    | mem db dl dp =>
                                        rw [hks, hkd] at he; simp only [specM_bind] at he
                                        cases hq1 : SpecM.require sp.r .permDenied σ with
                                        | err e σe => have hq := require_err_state _ _ σ hq1; rw [hq1] at he; injection he with _ h2; subst h2; subst hq; rfl
                                        | fault f => rw [hq1] at he; simp at he
                                        | ok _ σq1 =>
                                            have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                            cases hq2 : SpecM.require dp.w .permDenied σ with
                                            | err e σe => have hq := require_err_state _ _ σ hq2; rw [hq2] at he; injection he with _ h2; subst h2; subst hq; rfl
                                            | fault f => rw [hq2] at he; simp at he
                                            | ok _ σq2 =>
                                                have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                                cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                                | err e σe => have hq := require_err_state _ _ σ hq3; rw [hq3] at he; injection he with _ h2; subst h2; subst hq; rfl
                                                | fault f => rw [hq3] at he; simp at he
                                                | ok _ σq3 =>
                                                    have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                    cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                    | err e σe => exact absurd hd (by simp [SpecM.demand]; split <;> simp [SpecM.fatal])
                                                    | fault f => rw [hd] at he; simp at he
                                                    | ok _ σdd =>
                                                        have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                        simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he

/-- **The system opcodes never touch `inflight`** — the capability/gate/Mover
kernel operations are `doms`/`gates`/`mover`/`mem`-level only. -/
theorem system_inflight_eq : ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ c : Ctx,
    InflightEq (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  case _ => -- cap_dup
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          have hstep : ∀ (kd : CapKind) (hh : Loom.Word32) (τ : MachineState),
              allocDerived c.d kd ⟨c.d, sl, gg⟩ σ = .ok hh τ →
              (SpecM.setReg c.d c.op.rd hh) τ = .ok a σ' →
              σ'.inflight = σ.inflight := by
            intro kd hh τ hal hsr
            have h1 := (InflightEq.allocDerived c.d kd ⟨c.d, sl, gg⟩ σ).1 hh τ hal
            have h2 := (InflightEq.setReg c.d c.op.rd hh τ).1 a σ' hsr
            exact h2.trans h1
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => rw [hal] at he; simp at he
              | fault f => rw [hal] at he; simp at he
              | ok hh τ => rw [hal] at he; exact hstep _ hh τ hal he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived c.d kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => rw [hal] at he; simp at he
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; exact hstep _ hh τ hal he
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state c.d _ _ σ hal
                             rw [hal] at he; injection he with _ h2; subst h2; subst hs; rfl
              | fault f => rw [hal] at he; simp at he
              | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms _ σ hn
                             rw [hn] at he; injection he with _ h2; subst h2; subst hs; rfl
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived c.d kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state c.d _ _ σ hal
                                 rw [hal] at he; injection he with _ h2; subst h2; subst hs; rfl
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_drop
    intro σ; constructor
    · intro a σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, _⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind] at he
          have key : ∀ (σ' : MachineState), σ'.inflight = σ.inflight →
              (SpecM.set (((σ'.clearSlot c.d sl).sweepRegions).sweepMover) >>=
                fun _ => SpecM.setReg c.d c.op.rd 0) σ = .ok a σ'' →
              σ''.inflight = σ.inflight := by
            intro σ' hpre hset
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at hset
            injection hset with _ h2; subst h2
            rw [setDom_inflight, sweepMover_inflight, sweepRegions_inflight, clearSlot_inflight]
            exact hpre
          cases hp : σ.parentOf c.d sl with
          | some p => rw [hp] at he
                      exact key _ (reparent_inflight σ _ _) he
          | none => rw [hp] at he
                    exact key _ (orphanChildren_inflight σ _) he
    · intro e σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, _⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind] at he
          cases hp : σ.parentOf c.d sl with
          | some p => rw [hp] at he; simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          | none => rw [hp] at he; simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_revoke
    intro σ; constructor
    · intro a σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.require] at he
          by_cases hcls : decide (e.kind.cls = .mem) = true
          · simp only [hcls, if_true, specM_pure, specM_bind, SpecM.get] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            rw [setDom_inflight, sweepMover_inflight, sweepRegions_inflight,
                destroyMarked_inflight]
          · rw [if_neg hcls] at he; simp [SpecM.raise, specM_bind] at he
    · intro e σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.require] at he
          by_cases hcls : decide (e.kind.cls = .mem) = true
          · simp only [hcls, if_true, specM_pure, specM_bind, SpecM.get] at he
            simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          · rw [if_neg hcls] at he; simp only [SpecM.raise, specM_bind] at he
            injection he with _ h2; subst h2; rfl
  case _ => -- mem_grant
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => rw [hal] at he; simp at he
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ =>
                      rw [hal] at he
                      have h1 := (InflightEq.allocDerived (descDom _) kd ⟨c.d, sl, gg⟩ σ).1 hh τ hal
                      have h2 := (InflightEq.setReg c.d c.op.rd hh τ).1 a σ' he
                      exact h2.trans h1
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms _ σ hn
                             rw [hn] at he; injection he with _ h2; subst h2; subst hs; rfl
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state (descDom _) _ _ σ hal
                                 rw [hal] at he; injection he with _ h2; subst h2; subst hs; rfl
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
  case _ => -- map
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he
              simp only [SpecM.updDom, SpecM.modify, SpecM.setReg, specM_bind, SpecM.set] at he
              injection he with _ h2; subst h2
              rfl
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
          | mem base len perms =>
              rw [hk] at he
              simp [SpecM.updDom, SpecM.modify, SpecM.setReg, specM_bind, SpecM.set] at he
  case _ => -- unmap
    exact InflightEq.bind (InflightEq.updDom _ _) (fun _ => InflightEq.setReg _ _ _)
  case _ => exact gatecall_inflight_eq c
  case _ => exact gatereturn_inflight_eq c
  case _ => exact move_inflight_eq c
  case _ => -- yield
    exact InflightEq.bind (InflightEq.updDom _ _) (fun _ => InflightEq.setReg _ _ _)
  case _ => exact InflightEq.halt c

/-- **No instruction's exec ever touches `inflight`.** -/
theorem exec_inflight_eq : ∀ instr ∈ isa, ∀ c : Ctx, InflightEq (instr.sem.exec c) := by
  intro instr hmem c
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · exact base_inflight_eq instr hb c
  · exact system_inflight_eq instr hs c

/-- **`retire` never sets `inflight`**: the pc bump, exec effect, errno
write-back, and halts all preserve it. -/
theorem retire_inflight (σ : MachineState) (d : DomainId) (w : Loom.Word32) :
    (retire σ d w).inflight = σ.inflight := by
  unfold retire
  split
  · exact haltDom_inflight σ d _
  · rename_i instr hdec
    have hex := exec_inflight_eq instr (Loom.Isa.decode_mem isa hdec)
      { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }))
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w }
        (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })) with
    | ok a σ' =>
        simp only [hexr]
        exact hex.1 a σ' hexr
    | err e σ' =>
        simp only [hexr]
        exact hex.2 e σ' hexr
    | fault f =>
        simp only [hexr]
        exact haltDom_inflight σ d _

/-! ### The `step`-level countdown/retire characterization (T7 core) -/

theorem refillPhase_inflight (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).inflight = σ.inflight := by
  unfold refillPhase; split <;> rfl

/-- `step`'s `inflight` equals `corePhase`'s (refill, mover, and the cycle
bump leave it untouched). -/
theorem step_inflight_reduce (m : Manifest) (σ : MachineState) :
    (step m σ).inflight = (corePhase m (refillPhase m σ)).inflight := by
  unfold step; simp only [moverPhase_inflight]

/-- One cycle with more than one cycle left: the countdown decrements and the
latched instruction is unchanged. -/
theorem step_inflight_countdown (m : Manifest) (σ : MachineState) (fl : InFlight)
    (hfl : σ.inflight = some fl) (h1 : 1 < fl.cyclesLeft) :
    (step m σ).inflight = some { fl with cyclesLeft := fl.cyclesLeft - 1 } := by
  have hrf : (refillPhase m σ).inflight = some fl := by
    rw [refillPhase_inflight, hfl]
  rw [step_inflight_reduce]
  unfold corePhase
  simp only [hrf]
  rw [if_neg (by omega : ¬ fl.cyclesLeft ≤ 1)]

/-- One cycle on the last in-flight cycle: the instruction retires and the
core frees. -/
theorem step_inflight_retire (m : Manifest) (σ : MachineState) (fl : InFlight)
    (hfl : σ.inflight = some fl) (h1 : fl.cyclesLeft ≤ 1) :
    (step m σ).inflight = none := by
  have hrf : (refillPhase m σ).inflight = some fl := by
    rw [refillPhase_inflight, hfl]
  rw [step_inflight_reduce]
  unfold corePhase
  simp only [hrf]
  rw [if_pos h1, retire_inflight]

/-- `stepN`'s successor on the right (its definition recurses on the left). -/
theorem stepN_succ (m : Manifest) : ∀ (n : Nat) (σ : MachineState),
    stepN m (n + 1) σ = step m (stepN m n σ) := by
  intro n
  induction n with
  | zero => intro σ; rfl
  | succ k ih =>
      intro σ
      show stepN m (k + 1) (step m σ) = step m (stepN m (k + 1) σ)
      rw [ih (step m σ)]
      rfl

/-- The countdown, iterated: as long as cycles remain, the latched
instruction survives with `cyclesLeft` decremented `k` times. -/
theorem stepN_inflight_countdown (m : Manifest) :
    ∀ (k : Nat) (σ : MachineState) (fl : InFlight), σ.inflight = some fl →
      k < fl.cyclesLeft →
      (stepN m k σ).inflight = some ⟨fl.dom, fl.word, fl.cyclesLeft - k⟩ := by
  intro k
  induction k with
  | zero =>
      intro σ fl hfl _
      show σ.inflight = some ⟨fl.dom, fl.word, fl.cyclesLeft - 0⟩
      exact hfl
  | succ n ih =>
      intro σ fl hfl hk
      have hstep := step_inflight_countdown m σ fl hfl (by omega)
      have hrec : (stepN m n (step m σ)).inflight =
          some ⟨fl.dom, fl.word, fl.cyclesLeft - 1 - n⟩ :=
        ih (step m σ) ⟨fl.dom, fl.word, fl.cyclesLeft - 1⟩ hstep
          (show n < fl.cyclesLeft - 1 by omega)
      have harith : fl.cyclesLeft - 1 - n = fl.cyclesLeft - (n + 1) := by omega
      show (stepN m n (step m σ)).inflight = some ⟨fl.dom, fl.word, fl.cyclesLeft - (n + 1)⟩
      rw [hrec, harith]

end Wip

end Machines.Lnp64u
