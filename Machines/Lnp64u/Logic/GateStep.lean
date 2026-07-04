import Machines.Lnp64u.Logic.AcyclicWfa
import Mathlib.Tactic.FinCases

/-!
# Gate-step characterization (T4 support)

Characterizes what one cycle may do to any single domain's control state
(`serving`/`run`) and register file (`regs`/`pc`/`cause`):

* the only `serving` flip `none → some g` is `gate_call`'s callee
  activation, which scrubs the register file (`r1 := argHandle`, all else
  0) and enters at the gate's configured entry point;
* the only `run` flip `blocked g → running` is the caller resumption of
  `gate_return` (reply write) or of a forced unwind (`-ECALLEEFAULT`), and
  in both cases the register file is the saved (in-place) file plus exactly
  the recorded reply register;
* a domain that is not executing and sees no gate transition keeps its
  `regs`/`pc`/`cause` — there is no fifth channel.

`Touch` packages the three clauses; `step_touch` proves them for the whole
cycle. T4's three theorems are corollaries.
-/

namespace Machines.Lnp64u

open Loom.Isa SpecM Machines.Lnp64u.Isa

/-! ## Projection helpers -/

theorem setDom_doms_same (σ : MachineState) (d : DomainId) (f : DomainState → DomainState) :
    ((σ.setDom d f).doms d) = f (σ.doms d) := by
  unfold MachineState.setDom; simp [Loom.Fun.update_same]

theorem setDom_doms_ne (σ : MachineState) (d : DomainId) (f : DomainState → DomainState)
    (e : DomainId) (he : e ≠ d) : ((σ.setDom d f).doms e) = σ.doms e := by
  unfold MachineState.setDom; simp [Loom.Fun.update_ne _ _ _ _ he]

@[simp] theorem refillPhase_regs (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).regs = (σ.doms d).regs := by
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_pc (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).pc = (σ.doms d).pc := by
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_cause (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).cause = (σ.doms d).cause := by
  unfold refillPhase; dsimp only; split <;> rfl

@[simp] theorem refillPhase_inflight (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).inflight = σ.inflight := by
  rfl

/-- `step`'s domain table equals `corePhase`'s over the refilled state (the
Mover phase and the cycle bump never touch `doms`). -/
theorem step_doms (m : Manifest) (σ : MachineState) :
    (step m σ).doms = (corePhase m (refillPhase m σ)).doms := by
  show (moverPhase (corePhase m (refillPhase m σ))).doms = _
  exact funext (fun d => congrFun (moverPhase_doms _) d)

/-- Architectural register read after a register write: the zero-guarded
update formula (writes to `r0` are discarded, reads of `r0` are 0). -/
theorem DomainState.setReg_reg (ds : DomainState) (rd : RegId) (v : Loom.Word32) (r : RegId) :
    (ds.setReg rd v).reg r = if r = rd ∧ r ≠ (0 : Fin numRegs) then v else ds.reg r := by
  unfold DomainState.setReg DomainState.reg
  by_cases hr0 : r = (0 : Fin numRegs)
  · simp [hr0]
  · by_cases hrd0 : rd = (0 : Fin numRegs)
    · simp [hrd0, hr0]
    · by_cases hrrd : r = rd
      · subst hrrd; simp [hr0, hrd0]
      · simp [hr0, hrd0, hrrd]

/-- `reg` reads only `regs`. -/
theorem reg_of_regs_eq {ds1 ds2 : DomainState} (h : ds1.regs = ds2.regs) (r : RegId) :
    ds1.reg r = ds2.reg r := by
  unfold DomainState.reg; rw [h]

/-! ## Extra kernel projections (regs/pc/cause are never touched by the
capability kernel: it writes caps/lineage/slotGen/regions/mover only) -/

@[simp] theorem reparent_regs (σ : MachineState) (old new : CapRef) (d : DomainId) :
    ((σ.reparent old new).doms d).regs = (σ.doms d).regs := rfl
@[simp] theorem reparent_pc (σ : MachineState) (old new : CapRef) (d : DomainId) :
    ((σ.reparent old new).doms d).pc = (σ.doms d).pc := rfl
@[simp] theorem reparent_cause (σ : MachineState) (old new : CapRef) (d : DomainId) :
    ((σ.reparent old new).doms d).cause = (σ.doms d).cause := rfl

@[simp] theorem orphanChildren_regs (σ : MachineState) (old : CapRef) (d : DomainId) :
    ((σ.orphanChildren old).doms d).regs = (σ.doms d).regs := rfl
@[simp] theorem orphanChildren_pc (σ : MachineState) (old : CapRef) (d : DomainId) :
    ((σ.orphanChildren old).doms d).pc = (σ.doms d).pc := rfl
@[simp] theorem orphanChildren_cause (σ : MachineState) (old : CapRef) (d : DomainId) :
    ((σ.orphanChildren old).doms d).cause = (σ.doms d).cause := rfl

@[simp] theorem destroyMarked_regs (σ : MachineState) (mk : DomainId → Slot → Bool) (d : DomainId) :
    ((σ.destroyMarked mk).doms d).regs = (σ.doms d).regs := rfl
@[simp] theorem destroyMarked_pc (σ : MachineState) (mk : DomainId → Slot → Bool) (d : DomainId) :
    ((σ.destroyMarked mk).doms d).pc = (σ.doms d).pc := rfl
@[simp] theorem destroyMarked_cause (σ : MachineState) (mk : DomainId → Slot → Bool) (d : DomainId) :
    ((σ.destroyMarked mk).doms d).cause = (σ.doms d).cause := rfl

@[simp] theorem sweepRegions_regs (σ : MachineState) (d : DomainId) :
    (σ.sweepRegions.doms d).regs = (σ.doms d).regs := rfl
@[simp] theorem sweepRegions_pc (σ : MachineState) (d : DomainId) :
    (σ.sweepRegions.doms d).pc = (σ.doms d).pc := rfl
@[simp] theorem sweepRegions_cause (σ : MachineState) (d : DomainId) :
    (σ.sweepRegions.doms d).cause = (σ.doms d).cause := rfl

@[simp] theorem clearSlot_regs (σ : MachineState) (d : DomainId) (s : Slot) (d' : DomainId) :
    ((σ.clearSlot d s).doms d').regs = (σ.doms d').regs := by
  unfold MachineState.clearSlot
  by_cases hd : d' = d
  · subst hd; rw [setDom_doms_same]
  · rw [setDom_doms_ne _ _ _ _ hd]
@[simp] theorem clearSlot_pc (σ : MachineState) (d : DomainId) (s : Slot) (d' : DomainId) :
    ((σ.clearSlot d s).doms d').pc = (σ.doms d').pc := by
  unfold MachineState.clearSlot
  by_cases hd : d' = d
  · subst hd; rw [setDom_doms_same]
  · rw [setDom_doms_ne _ _ _ _ hd]
@[simp] theorem clearSlot_cause (σ : MachineState) (d : DomainId) (s : Slot) (d' : DomainId) :
    ((σ.clearSlot d s).doms d').cause = (σ.doms d').cause := by
  unfold MachineState.clearSlot
  by_cases hd : d' = d
  · subst hd; rw [setDom_doms_same]
  · rw [setDom_doms_ne _ _ _ _ hd]

@[simp] theorem haltBase_regs (σ : MachineState) (d : DomainId) (c : Loom.Word32) (d' : DomainId) :
    ((σ.haltBase d c).doms d').regs = (σ.doms d').regs := by
  unfold MachineState.haltBase
  by_cases hd : d' = d
  · subst hd; rw [setDom_doms_same]
  · rw [setDom_doms_ne _ _ _ _ hd]
@[simp] theorem haltBase_pc (σ : MachineState) (d : DomainId) (c : Loom.Word32) (d' : DomainId) :
    ((σ.haltBase d c).doms d').pc = (σ.doms d').pc := by
  unfold MachineState.haltBase
  by_cases hd : d' = d
  · subst hd; rw [setDom_doms_same]
  · rw [setDom_doms_ne _ _ _ _ hd]

theorem haltBase_doms_ne (σ : MachineState) (d : DomainId) (c : Loom.Word32) (d' : DomainId)
    (hd : d' ≠ d) : ((σ.haltBase d c).doms d') = σ.doms d' := by
  unfold MachineState.haltBase; rw [setDom_doms_ne _ _ _ _ hd]

theorem unwindGate_doms_ne (σ : MachineState) (g : GateId) (cl : DomainId) (rd : RegId)
    (d' : DomainId) (hd : d' ≠ cl) : ((σ.unwindGate g cl rd).doms d') = σ.doms d' := by
  unfold MachineState.unwindGate; rw [setDom_doms_ne _ _ _ _ hd]

theorem unwindGate_doms_same (σ : MachineState) (g : GateId) (cl : DomainId) (rd : RegId) :
    ((σ.unwindGate g cl rd).doms cl) =
      (({ (σ.doms cl) with run := .running } : DomainState).setReg rd Errno.calleeFault.toWord) := by
  unfold MachineState.unwindGate; rw [setDom_doms_same]

/-! ## The touch predicate

`Touch σ σ' P e` records the T4 channel structure of one transition
`σ → σ'` at domain `e`. `P` guards the frame clause (instantiated with
"`e` is not the executing domain"). -/

def Touch (σ σ' : MachineState) (P : Prop) (e : DomainId) : Prop :=
  -- activation entry: a `none → some g` serving flip scrubs the file
  (∀ g : GateId, (σ.doms e).serving = none → (σ'.doms e).serving = some g →
     (∀ r : RegId, r ≠ (1 : Fin numRegs) → (σ'.doms e).reg r = 0) ∧
     (σ'.doms e).pc = (σ.gates g).config.entry) ∧
  -- caller resumption: a `blocked g → running` run flip writes one reply register
  (∀ g : GateId, (σ.doms e).run = .blocked g → (σ'.doms e).run = .running →
     ∃ a reply, (σ.gates g).act = some a ∧ a.caller = e ∧
       ∀ r : RegId, (σ'.doms e).reg r =
         if r = a.callerRd ∧ r ≠ (0 : Fin numRegs) then reply else (σ.doms e).reg r) ∧
  -- frame: no gate transition and not executing ⇒ regs/pc/cause unchanged
  (P → (σ'.doms e).serving = (σ.doms e).serving → (σ'.doms e).run = (σ.doms e).run →
     (σ'.doms e).regs = (σ.doms e).regs ∧ (σ'.doms e).pc = (σ.doms e).pc ∧
     (σ'.doms e).cause = (σ.doms e).cause)

theorem Touch.mono {σ σ' : MachineState} {P : Prop} {e : DomainId}
    (h : Touch σ σ' P e) {Q : Prop} (hqp : Q → P) : Touch σ σ' Q e :=
  ⟨h.1, h.2.1, fun hq => h.2.2 (hqp hq)⟩

/-- A transition that changes no domain's serving/run marks, and no
non-excluded domain's regs/pc/cause, satisfies `Touch`. -/
theorem Touch.of_calm {σ σ' : MachineState} {P : Prop} {e : DomainId}
    (hss : (σ'.doms e).serving = (σ.doms e).serving)
    (hrr : (σ'.doms e).run = (σ.doms e).run)
    (hq : P → (σ'.doms e).regs = (σ.doms e).regs ∧ (σ'.doms e).pc = (σ.doms e).pc ∧
          (σ'.doms e).cause = (σ.doms e).cause) : Touch σ σ' P e := by
  refine ⟨?_, ?_, fun hp _ _ => hq hp⟩
  · intro g hpre hpost; rw [hss, hpre] at hpost; exact absurd hpost (by simp)
  · intro g hpre hpost; rw [hrr, hpre] at hpost; exact absurd hpost (by simp)

theorem Touch.refl (σ : MachineState) (P : Prop) (e : DomainId) : Touch σ σ P e :=
  Touch.of_calm rfl rfl (fun _ => ⟨rfl, rfl, rfl⟩)

theorem Touch.of_eq {σ σ' : MachineState} (h : σ' = σ) (P : Prop) (e : DomainId) :
    Touch σ σ' P e := h ▸ Touch.refl σ P e

/-- Transport a `Touch` across state decorations: a pre-state with the same
observables at `e` (and the same gates), and a post-state with the same
domain table at `e`. -/
theorem Touch.transport {σ0 σ σ2 σ' : MachineState} {P : Prop} {e : DomainId}
    (h : Touch σ σ2 P e)
    (hserv : (σ.doms e).serving = (σ0.doms e).serving)
    (hrun : (σ.doms e).run = (σ0.doms e).run)
    (hregs : (σ.doms e).regs = (σ0.doms e).regs)
    (hpc : P → (σ.doms e).pc = (σ0.doms e).pc)
    (hcause : (σ.doms e).cause = (σ0.doms e).cause)
    (hgates : σ.gates = σ0.gates)
    (hpost : σ'.doms e = σ2.doms e) : Touch σ0 σ' P e := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hpre hpo
    obtain ⟨hz, hp⟩ := h.1 g (hserv.trans hpre) (by rw [hpost] at hpo; exact hpo)
    exact ⟨fun r hr => by rw [hpost]; exact hz r hr, by rw [hpost, hp, hgates]⟩
  · intro g hpre hpo
    obtain ⟨a, reply, ha, hcal, hform⟩ := h.2.1 g (hrun.trans hpre)
      (by rw [hpost] at hpo; exact hpo)
    refine ⟨a, reply, by rw [← hgates]; exact ha, hcal, fun r => ?_⟩
    rw [hpost, hform r, reg_of_regs_eq hregs r]
  · intro hp hs hr
    obtain ⟨h1, h2, h3⟩ := h.2.2 hp (by rw [hpost] at hs; rw [hs, ← hserv])
      (by rw [hpost] at hr; rw [hr, ← hrun])
    exact ⟨by rw [hpost, h1, hregs], by rw [hpost, h2, hpc hp],
           by rw [hpost, h3, hcause]⟩

/-! ## Calm computations

A `SpecM` fragment is *calm* (relative to the executing domain `cd`) when
it changes no domain's serving/run and no other domain's regs/pc/cause —
every instruction except the two gate ops and `halt` is calm. -/

def CalmOut (cd : DomainId) (σ σ' : MachineState) : Prop :=
  (∀ e, (σ'.doms e).serving = (σ.doms e).serving) ∧
  (∀ e, (σ'.doms e).run = (σ.doms e).run) ∧
  (∀ e, e ≠ cd → (σ'.doms e).regs = (σ.doms e).regs ∧
        (σ'.doms e).pc = (σ.doms e).pc ∧ (σ'.doms e).cause = (σ.doms e).cause)

theorem CalmOut.refl (cd : DomainId) (σ : MachineState) : CalmOut cd σ σ :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem CalmOut.of_eq {cd : DomainId} {σ σ' : MachineState} (h : σ' = σ) : CalmOut cd σ σ' :=
  h ▸ CalmOut.refl cd σ

theorem CalmOut.trans {cd : DomainId} {σ σ1 σ2 : MachineState}
    (h1 : CalmOut cd σ σ1) (h2 : CalmOut cd σ1 σ2) : CalmOut cd σ σ2 :=
  ⟨fun e => (h2.1 e).trans (h1.1 e), fun e => (h2.2.1 e).trans (h1.2.1 e),
   fun e he =>
     ⟨((h2.2.2 e he).1).trans ((h1.2.2 e he).1),
      ((h2.2.2 e he).2.1).trans ((h1.2.2 e he).2.1),
      ((h2.2.2 e he).2.2).trans ((h1.2.2 e he).2.2)⟩⟩

theorem CalmOut.touch {cd : DomainId} {σ σ' : MachineState} (h : CalmOut cd σ σ')
    (e : DomainId) : Touch σ σ' (e ≠ cd) e :=
  Touch.of_calm (h.1 e) (h.2.1 e) (fun hne => h.2.2 e hne)

/-- `setDom` at the executing domain with a run/serving-preserving update is calm. -/
theorem CalmOut.setDomExec (σ : MachineState) (cd : DomainId) (f : DomainState → DomainState)
    (hs : (f (σ.doms cd)).serving = (σ.doms cd).serving)
    (hr : (f (σ.doms cd)).run = (σ.doms cd).run) : CalmOut cd σ (σ.setDom cd f) := by
  refine ⟨fun e => ?_, fun e => ?_, fun e he => ?_⟩
  · by_cases he : e = cd
    · subst he; rw [setDom_doms_same]; exact hs
    · rw [setDom_doms_ne _ _ _ _ he]
  · by_cases he : e = cd
    · subst he; rw [setDom_doms_same]; exact hr
    · rw [setDom_doms_ne _ _ _ _ he]
  · rw [setDom_doms_ne _ _ _ _ he]; exact ⟨rfl, rfl, rfl⟩

/-- `setDom` anywhere with an update preserving all five observables is calm. -/
theorem CalmOut.setDomAny (σ : MachineState) (cd d : DomainId) (f : DomainState → DomainState)
    (hs : (f (σ.doms d)).serving = (σ.doms d).serving)
    (hr : (f (σ.doms d)).run = (σ.doms d).run)
    (hregs : (f (σ.doms d)).regs = (σ.doms d).regs)
    (hpc : (f (σ.doms d)).pc = (σ.doms d).pc)
    (hcause : (f (σ.doms d)).cause = (σ.doms d).cause) : CalmOut cd σ (σ.setDom d f) := by
  refine ⟨fun e => ?_, fun e => ?_, fun e _ => ?_⟩
  · by_cases he : e = d
    · subst he; rw [setDom_doms_same]; exact hs
    · rw [setDom_doms_ne _ _ _ _ he]
  · by_cases he : e = d
    · subst he; rw [setDom_doms_same]; exact hr
    · rw [setDom_doms_ne _ _ _ _ he]
  · by_cases he : e = d
    · subst he; rw [setDom_doms_same]; exact ⟨hregs, hpc, hcause⟩
    · rw [setDom_doms_ne _ _ _ _ he]; exact ⟨rfl, rfl, rfl⟩

theorem CalmOut.of_doms_eq {cd : DomainId} {σ σ' : MachineState}
    (h : ∀ e, σ'.doms e = σ.doms e) : CalmOut cd σ σ' :=
  ⟨fun e => by rw [h e], fun e => by rw [h e], fun e _ => by rw [h e]; exact ⟨rfl, rfl, rfl⟩⟩

/-- The `SpecM`-level calm combinator: every `ok`/`err` outcome is calm. -/
def CalmLe (cd : DomainId) {α : Type} (m : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', m σ = .ok a σ' → CalmOut cd σ σ') ∧
       (∀ er σ', m σ = .err er σ' → CalmOut cd σ σ')

theorem CalmLe.of_state_eq {cd : DomainId} {α : Type} {m : SpecM α}
    (hok : ∀ σ a σ', m σ = .ok a σ' → σ' = σ)
    (herr : ∀ σ e σ', m σ = .err e σ' → σ' = σ) : CalmLe cd m :=
  fun σ => ⟨fun a σ' he => CalmOut.of_eq (hok σ a σ' he),
            fun e σ' he => CalmOut.of_eq (herr σ e σ' he)⟩

theorem CalmLe.pure {cd : DomainId} {α : Type} (a : α) : CalmLe cd (Pure.pure a : SpecM α) :=
  CalmLe.of_state_eq
    (fun σ a' σ' he => by rw [specM_pure] at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by rw [specM_pure] at he; simp at he)

theorem CalmLe.bind {cd : DomainId} {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : CalmLe cd m) (hf : ∀ a, CalmLe cd (f a)) : CalmLe cd (m >>= f) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact CalmOut.trans ((hm σ).1 a σ1 hmσ) ((hf a σ1).1 b σ' he)
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 exact CalmOut.trans ((hm σ).1 a σ1 hmσ) ((hf a σ1).2 e σ' he)
    | err e1 σ1 => rw [hmσ] at he; injection he with _ h2; subst h2
                   exact (hm σ).2 e1 σ1 hmσ
    | fault g => rw [hmσ] at he; simp at he

theorem CalmLe.iteBool {cd : DomainId} {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : CalmLe cd m1) (h2 : CalmLe cd m2) : CalmLe cd (if b then m1 else m2) := by
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact h2
  · exact h1

theorem CalmLe.reg {cd : DomainId} (d : DomainId) (r : RegId) : CalmLe cd (SpecM.reg d r) :=
  CalmLe.of_state_eq
    (fun σ a σ' he => by unfold SpecM.reg at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by unfold SpecM.reg at he; simp at he)

theorem CalmLe.get {cd : DomainId} : CalmLe cd SpecM.get :=
  CalmLe.of_state_eq
    (fun σ a σ' he => by unfold SpecM.get at he; injection he with _ h2; exact h2.symm)
    (fun σ e σ' he => by unfold SpecM.get at he; simp at he)

theorem CalmLe.raise {cd : DomainId} {α : Type} (e : Errno) :
    CalmLe cd (SpecM.raise e : SpecM α) :=
  CalmLe.of_state_eq
    (fun σ a σ' he => by unfold SpecM.raise at he; simp at he)
    (fun σ e' σ' he => by unfold SpecM.raise at he; injection he with _ h2; exact h2.symm)

theorem CalmLe.require {cd : DomainId} (cond : Bool) (e : Errno) :
    CalmLe cd (SpecM.require cond e) :=
  CalmLe.of_state_eq
    (fun σ a σ' he => by cases a; exact require_ok cond e σ he)
    (fun σ e' σ' he => require_err_state cond e σ he)

theorem CalmLe.demand {cd : DomainId} (cond : Bool) (f : Fault) :
    CalmLe cd (SpecM.demand cond f) :=
  CalmLe.of_state_eq
    (fun σ a σ' he => by cases a; exact demand_ok cond f σ he)
    (fun σ e σ' he => by
      unfold SpecM.demand at he; split at he
      · simp [specM_pure] at he
      · simp [SpecM.fatal] at he)

theorem CalmLe.load {cd : DomainId} (d : DomainId) (a : Addr) : CalmLe cd (SpecM.load d a) :=
  CalmLe.of_state_eq
    (fun σ v σ' he => load_ok d a σ he)
    (fun σ e σ' he => load_err_state d a σ he)

theorem CalmLe.capLive {cd : DomainId} (d : DomainId) (hw : Loom.Word32) :
    CalmLe cd (Machines.Lnp64u.Isa.capLive d hw) :=
  CalmLe.of_state_eq
    (fun σ r σ' he => (Machines.Lnp64u.Isa.Wip.capLive_ok d hw σ he).1)
    (fun σ e σ' he => Machines.Lnp64u.Isa.Wip.capLive_err_state d hw σ he)

theorem CalmLe.narrow {cd : DomainId} (base : Addr) (len : BitVec 13) (perms : Perms)
    (dw : Loom.Word32) : CalmLe cd (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  CalmLe.of_state_eq
    (fun σ k σ' he => (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms dw σ he).1)
    (fun σ e σ' he => Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms dw σ he)

theorem CalmLe.setReg (cd : DomainId) (r : RegId) (v : Loom.Word32) :
    CalmLe cd (SpecM.setReg cd r v) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro a σ' he
    unfold SpecM.setReg SpecM.modify at he; injection he with _ h2; subst h2
    exact CalmOut.setDomExec σ cd _ (setReg_serving _ _ _) (setReg_run _ _ _)
  · intro e σ' he; unfold SpecM.setReg SpecM.modify at he; simp at he

theorem CalmLe.updDomExec (cd : DomainId) (f : DomainState → DomainState)
    (hs : ∀ ds, (f ds).serving = ds.serving) (hr : ∀ ds, (f ds).run = ds.run) :
    CalmLe cd (SpecM.updDom cd f) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro a σ' he
    unfold SpecM.updDom SpecM.modify at he; injection he with _ h2; subst h2
    exact CalmOut.setDomExec σ cd f (hs _) (hr _)
  · intro e σ' he; unfold SpecM.updDom SpecM.modify at he; simp at he

theorem CalmLe.store {cd : DomainId} (d : DomainId) (a : Addr) (v : Loom.Word32) :
    CalmLe cd (SpecM.store d a v) := by
  intro σ; unfold SpecM.store
  refine ⟨?_, ?_⟩
  · intro x σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2; subst h2
      exact CalmOut.of_doms_eq (fun e => rfl)
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

theorem CalmLe.allocDerived {cd : DomainId} (owner : DomainId) (kind : CapKind)
    (parent : CapRef) : CalmLe cd (Machines.Lnp64u.Isa.allocDerived owner kind parent) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro hw σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp [SpecM.raise] at he
    | some s =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp [SpecM.raise] at he
        | some l =>
            rw [hfc] at he
            simp only [SpecM.set, specM_bind, specM_pure] at he
            injection he with _ h2
            rw [show σ' = (σ.installDerived owner s l kind parent).1 from by rw [← h2]]
            refine CalmOut.setDomAny σ cd owner (fun ds =>
              { ds with
                caps := Loom.Fun.update ds.caps s (some { kind := kind, lineage := some l })
                lineage := Loom.Fun.update ds.lineage l (some { parent := parent }) })
              rfl rfl rfl rfl rfl
  · intro e σ' he
    exact CalmOut.of_eq (Machines.Lnp64u.Isa.Wip.allocDerived_err_state owner kind parent σ he)

/-- Bind after `get`, where the continuation only needs to be safe from the
state `get` observed (the diagonal — required for `set` of state-derived
values). -/
theorem CalmLe.getD {cd : DomainId} {α : Type} (f : MachineState → SpecM α)
    (hf : ∀ σ0, (∀ a σ', f σ0 σ0 = .ok a σ' → CalmOut cd σ0 σ') ∧
                (∀ er σ', f σ0 σ0 = .err er σ' → CalmOut cd σ0 σ')) :
    CalmLe cd (SpecM.get >>= f) := by
  intro σ
  have hred : (SpecM.get >>= f) σ = f σ σ := rfl
  rw [hred]
  exact hf σ

/-! ## Capability transfer never touches regs/pc/cause -/

/-- `transferCap` only writes caps/lineage/slotGen/regions/mover: every
domain's `regs`, `pc`, and `cause` are preserved (the strengthened frame
T4 needs on top of `transferCap_frame`). -/
theorem transferCap_calm (σ : MachineState) (from_ : DomainId) (s : Slot) (to_ : DomainId)
    (σ' : MachineState) (ref : CapRef)
    (ht : σ.transferCap from_ s to_ = some (σ', ref)) :
    ∀ d, (σ'.doms d).regs = (σ.doms d).regs ∧ (σ'.doms d).pc = (σ.doms d).pc ∧
         (σ'.doms d).cause = (σ.doms d).cause := by
  unfold MachineState.transferCap at ht
  simp only [Option.bind_eq_bind] at ht
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at ht; simp at ht
  | some e =>
    rw [he] at ht; simp only [Option.bind_some] at ht
    cases hfs : σ.freeSlot to_ with
    | none => rw [hfs] at ht; simp at ht
    | some s' =>
      rw [hfs] at ht; simp only [Option.bind_some] at ht
      cases hle : e.lineage with
      | some l =>
        cases hcell : (σ.doms from_).lineage l with
        | none => simp [hle, hcell] at ht
        | some cell =>
          cases hfc : σ.freeCell to_ with
          | none => simp [hle, hcell, hfc] at ht
          | some l' =>
            simp only [hle, hcell, hfc, Option.bind_some, Option.some.injEq,
              Prod.mk.injEq] at ht
            obtain ⟨rfl, _⟩ := ht
            intro d
            refine ⟨?_, ?_, ?_⟩ <;>
            · simp only [sweepMover_doms, sweepRegions_regs, sweepRegions_pc,
                sweepRegions_cause, clearSlot_regs, clearSlot_pc, clearSlot_cause,
                reparent_regs, reparent_pc, reparent_cause]
              by_cases hd : d = to_
              · subst hd; rw [setDom_doms_same]
              · rw [setDom_doms_ne _ _ _ _ hd]
      | none =>
        simp only [hle, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        intro d
        refine ⟨?_, ?_, ?_⟩ <;>
        · simp only [sweepMover_doms, sweepRegions_regs, sweepRegions_pc,
            sweepRegions_cause, clearSlot_regs, clearSlot_pc, clearSlot_cause,
            reparent_regs, reparent_pc, reparent_cause]
          by_cases hd : d = to_
          · subst hd; rw [setDom_doms_same]
          · rw [setDom_doms_ne _ _ _ _ hd]

/-- `transferByHandle` preserves every domain's `regs`/`pc`/`cause` on success. -/
theorem transferByHandle_calm (d to_ : DomainId) (hw : Loom.Word32)
    (σ : MachineState) (a : Loom.Word32) (σ' : MachineState)
    (he : Machines.Lnp64u.Isa.transferByHandle d to_ hw σ = .ok a σ') :
    ∀ d', (σ'.doms d').regs = (σ.doms d').regs ∧ (σ'.doms d').pc = (σ.doms d').pc ∧
          (σ'.doms d').cause = (σ.doms d').cause := by
  unfold Machines.Lnp64u.Isa.transferByHandle at he
  by_cases hz : hw = 0
  · rw [if_pos hz] at he; simp only [specM_pure] at he; obtain ⟨_, rfl⟩ := he
    exact fun d' => ⟨rfl, rfl, rfl⟩
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
            exact transferCap_calm σ d sslot to_ σ2 ref htc

/-- `transferByHandle` has no effect on an `err` outcome (every failure is a
pre-mutation errno raise). -/
theorem transferByHandle_err_state (d to_ : DomainId) (hw : Loom.Word32)
    (σ : MachineState) (er : Errno) (σ' : MachineState)
    (he : Machines.Lnp64u.Isa.transferByHandle d to_ hw σ = .err er σ') : σ' = σ := by
  unfold Machines.Lnp64u.Isa.transferByHandle at he
  by_cases hz : hw = 0
  · rw [if_pos hz] at he; simp [specM_pure] at he
  · simp only [if_neg hz, specM_bind] at he
    cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
    | err e0 σ0 =>
        have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state d _ σ hcl
        rw [hcl] at he; injection he with _ h2; subst h2; exact hs
    | fault f => rw [hcl] at he; simp at he
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
        simp only [SpecM.get, specM_bind] at he
        cases htc : σ.transferCap d sslot to_ with
        | none =>
            rw [htc] at he; simp only [SpecM.raise] at he
            injection he with _ h2; exact h2.symm
        | some pr =>
            obtain ⟨σ2, ref⟩ := pr
            rw [htc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-! ## Halting a domain: the unwind is a caller resumption -/

theorem haltBase_touch (σ : MachineState) (d : DomainId) (cv : Loom.Word32)
    (hrun : (σ.doms d).run = .running) (e : DomainId) :
    Touch σ (σ.haltBase d cv) True e := by
  by_cases hed : e = d
  · subst hed
    refine ⟨?_, ?_, ?_⟩
    · intro g hpre hpost
      rw [haltBase_serving, if_pos rfl] at hpost; exact absurd hpost (by simp)
    · intro g hpre hpost
      rw [hrun] at hpre; exact absurd hpre (by simp)
    · intro _ _ hrr
      rw [haltBase_run, if_pos rfl, hrun] at hrr; exact absurd hrr (by simp)
  · have hde : (σ.haltBase d cv).doms e = σ.doms e := haltBase_doms_ne σ d cv e hed
    exact Touch.of_calm (by rw [hde]) (by rw [hde]) (fun _ => by rw [hde]; exact ⟨rfl, rfl, rfl⟩)

/-- Halting a running domain `d`: the only visible effects are `d`'s own
halt (run/serving/cause) and — when `d` was serving an activation — the
caller resumption with `-ECALLEEFAULT`, exactly the T4 reply channel. -/
theorem haltDom_touch (σ : MachineState) (d : DomainId) (cv : Loom.Word32)
    (hwf : Wf σ) (hrun : (σ.doms d).run = .running) (e : DomainId) :
    Touch σ (σ.haltDom d cv) True e := by
  cases hserv : (σ.doms d).serving with
  | none => rw [haltDom_base σ d cv hserv]; exact haltBase_touch σ d cv hrun e
  | some g0 =>
      cases hact : (σ.gates g0).act with
      | none => rw [haltDom_base' σ d cv g0 hserv hact]; exact haltBase_touch σ d cv hrun e
      | some a =>
          rw [haltDom_unwind σ d cv g0 a hserv hact]
          have hcallerblk : (σ.doms a.caller).run = .blocked g0 :=
            (hwf.gate_serving g0 a hact).2.1
          have hcne : a.caller ≠ d := by
            intro h; rw [h, hrun] at hcallerblk; exact absurd hcallerblk (by simp)
          by_cases hec : e = a.caller
          · subst hec
            refine ⟨?_, ?_, ?_⟩
            · intro g hpre hpost
              rw [unwindGate_serving, haltBase_serving, if_neg hcne, hpre] at hpost
              exact absurd hpost (by simp)
            · intro g hpre hpost
              have hgg : g = g0 := by
                rw [hpre] at hcallerblk
                exact RunState.blocked.inj hcallerblk
              subst hgg
              refine ⟨a, Errno.calleeFault.toWord, hact, rfl, fun r => ?_⟩
              rw [unwindGate_doms_same, haltBase_doms_ne σ d cv a.caller hcne,
                DomainState.setReg_reg]
              by_cases hcond : r = a.callerRd ∧ r ≠ (0 : Fin numRegs)
              · rw [if_pos hcond, if_pos hcond]
              · rw [if_neg hcond, if_neg hcond]
                exact reg_of_regs_eq rfl r
            · intro _ _ hrr
              rw [unwindGate_run, if_pos rfl, hcallerblk] at hrr
              exact absurd hrr (by simp)
          · have hde : ((σ.haltBase d cv).unwindGate g0 a.caller a.callerRd).doms e
                = (σ.haltBase d cv).doms e := unwindGate_doms_ne _ _ _ _ e hec
            by_cases hed : e = d
            · subst hed
              refine ⟨?_, ?_, ?_⟩
              · intro g hpre hpost
                rw [hde, haltBase_serving, if_pos rfl] at hpost; exact absurd hpost (by simp)
              · intro g hpre hpost
                rw [hrun] at hpre; exact absurd hpre (by simp)
              · intro _ _ hrr
                rw [hde, haltBase_run, if_pos rfl, hrun] at hrr; exact absurd hrr (by simp)
            · have hde2 : ((σ.haltBase d cv).unwindGate g0 a.caller a.callerRd).doms e
                  = σ.doms e := by rw [hde, haltBase_doms_ne σ d cv e hed]
              exact Touch.of_calm (by rw [hde2]) (by rw [hde2])
                (fun _ => by rw [hde2]; exact ⟨rfl, rfl, rfl⟩)

/-! ## The per-instruction obligation -/

/-- Every `ok` outcome of an instruction satisfies the touch
characterization; every `err` outcome is calm (pre-mutation raises plus the
uniform `rd` write, which the retire glue accounts for). -/
def TouchExec (c : Ctx) (m : SpecM Unit) : Prop :=
  ∀ σ, Wf σ → (σ.doms c.d).run = .running →
    (∀ a σ', m σ = .ok a σ' → ∀ e, Touch σ σ' (e ≠ c.d) e) ∧
    (∀ er σ', m σ = .err er σ' → CalmOut c.d σ σ')

theorem TouchExec.of_calm {c : Ctx} {m : SpecM Unit} (h : CalmLe c.d m) : TouchExec c m :=
  fun σ _ _ => ⟨fun a σ' he e => ((h σ).1 a σ' he).touch e, fun er σ' he => (h σ).2 er σ' he⟩

/-! ## `gate_call`: the activation-entry channel -/

/-- The `gate_call` endgame state update satisfies the touch
characterization: the callee's file is scrubbed (`r1 := argHandle`) and its
pc set to the gate's entry; the caller is merely blocked; nobody else moves.
`τ` is the post-transfer state, framed back to `σ0` by the hypotheses. -/
theorem gateCall_end_touch (τ σ0 : MachineState) (caller cal : DomainId) (gid : GateId)
    (G : GateState) (argHandle : Loom.Word32) (entry : Addr)
    (hcalne : cal ≠ caller)
    (hfrun : ∀ d', (τ.doms d').run = (σ0.doms d').run)
    (hfserv : ∀ d', (τ.doms d').serving = (σ0.doms d').serving)
    (hcalm : ∀ d', (τ.doms d').regs = (σ0.doms d').regs ∧
             (τ.doms d').pc = (σ0.doms d').pc ∧ (τ.doms d').cause = (σ0.doms d').cause)
    (hcallerrun : (σ0.doms caller).run = .running)
    (hcalrun : (σ0.doms cal).run = .running)
    (hcalserv : (σ0.doms cal).serving = none)
    (hentry : entry = (σ0.gates gid).config.entry)
    (e : DomainId) :
    Touch σ0 ((({ τ with gates := Loom.Fun.update τ.gates gid G }).setDom cal
        (fun ds => { ds with
          regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
          pc := entry, serving := some gid })).setDom caller
        (fun ds => { ds with run := .blocked gid })) (e ≠ caller) e := by
  have hXd : ({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).doms
      = τ.doms := rfl
  by_cases hecal : e = cal
  · subst hecal
    have hdcal : (((({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).setDom e
        (fun ds => { ds with
          regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
          pc := entry, serving := some gid })).setDom caller
        (fun ds => { ds with run := .blocked gid })).doms e)
        = { τ.doms e with
            regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
            pc := entry, serving := some gid } := by
      rw [setDom_doms_ne _ _ _ _ hcalne, setDom_doms_same, hXd]
    refine ⟨?_, ?_, ?_⟩
    · intro g hpre hpost
      rw [hdcal] at hpost
      have hg : gid = g := by simpa using hpost
      subst hg
      constructor
      · intro r hr1
        rw [hdcal]
        unfold DomainState.reg
        split
        · rfl
        · exact if_neg hr1
      · rw [hdcal]; exact hentry
    · intro g hpre hpost
      rw [hcalrun] at hpre; exact absurd hpre (by simp)
    · intro _ hss _
      rw [hdcal] at hss
      have hss' : some gid = (σ0.doms e).serving := hss
      rw [hcalserv] at hss'; exact absurd hss' (by simp)
  · by_cases hecd : e = caller
    · subst hecd
      have hdcaller : (((({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).setDom cal
          (fun ds => { ds with
            regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
            pc := entry, serving := some gid })).setDom e
          (fun ds => { ds with run := .blocked gid })).doms e)
          = { τ.doms e with run := .blocked gid } := by
        rw [setDom_doms_same, setDom_doms_ne _ _ _ _ hecal, hXd]
      refine ⟨?_, ?_, fun hp => absurd rfl hp⟩
      · intro g hpre hpost
        rw [hdcaller] at hpost
        have hpost' : (τ.doms e).serving = some g := hpost
        rw [hfserv, hpre] at hpost'
        exact absurd hpost' (by simp)
      · intro g hpre hpost
        rw [hcallerrun] at hpre; exact absurd hpre (by simp)
    · have hde : (((({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).setDom cal
          (fun ds => { ds with
            regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
            pc := entry, serving := some gid })).setDom caller
          (fun ds => { ds with run := .blocked gid })).doms e) = τ.doms e := by
        rw [setDom_doms_ne _ _ _ _ hecd, setDom_doms_ne _ _ _ _ hecal, hXd]
      exact Touch.of_calm (by rw [hde]; exact hfserv e) (by rw [hde]; exact hfrun e)
        (fun _ => by rw [hde]; exact hcalm e)

/-- `gate_call` satisfies the touch obligation: the ok path is
`gateCall_end_touch` behind the require chain and the capability transfer;
every err path leaves the state unchanged. -/
theorem gatecall_touch (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hrun : (σ.doms c.d).run = .running) :
    (∀ a σ', (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = .ok a σ' →
       ∀ e, Touch σ σ' (e ≠ c.d) e) ∧
    (∀ er σ', (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = .err er σ' → σ' = σ) := by
  have body : ∀ (out : Res Unit),
      (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = out →
      (∀ a σ', out = .ok a σ' → ∀ e, Touch σ σ' (e ≠ c.d) e) ∧
      (∀ er σ', out = .err er σ' → σ' = σ) := by
    intro out hout
    unfold Machines.Lnp64u.Isa.Wip.gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
        rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hs⟩
    | fault f => rw [hcl] at hout; subst hout
                 exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r; simp only at hout
        cases hk : e.kind with
        | mem base len perms =>
            rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
              simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; rfl⟩
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 =>
                have hst := require_err_state _ _ σ hr1
                rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                         exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
            | ok u1 σ1 =>
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 =>
                    have hst := require_err_state _ _ σ hr2
                    rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                    exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                             exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                | ok u2 σ2 =>
                    have hc2 := require_cond _ _ σ hr2
                    have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 =>
                        have hst := require_err_state _ _ σ hr3
                        rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                 exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                    | ok u3 σ3 =>
                        have hc3 := require_cond _ _ σ hr3
                        have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 =>
                            have hst := require_err_state _ _ σ hr4
                            rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                              simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                     exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                        | ok u4 σ4 =>
                            have hc4 := require_cond _ _ σ hr4
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (Machines.Lnp64u.Isa.Wip.gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 =>
                                have hst := require_err_state _ _ σ hr5
                                rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                         exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                            | ok u5 σ5 =>
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                                | err e6 τ =>
                                    rw [htbh] at hout; subst hout
                                    have hτ := transferByHandle_err_state c.d cal _ σ e6 τ htbh
                                    exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    obtain ⟨hfrun, hfserv, hfgates, hfinf⟩ :=
                                      Machines.Lnp64u.Isa.Wip.transferByHandle_frame c.d cal _ σ argHandle τ htbh
                                    have hcalm := transferByHandle_calm c.d cal _ σ argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom,
                                      SpecM.modify] at hout
                                    subst hout
                                    refine ⟨fun a σ' h => ?_, fun er σ' h => by simp at h⟩
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    have hcalne : cal ≠ c.d := of_decide_eq_true hc2
                                    have hcalrunσ : (σ.doms cal).run = .running := of_decide_eq_true hc3
                                    have hcalservσ : (σ.doms cal).serving = none := by
                                      rw [Option.isNone_iff_eq_none] at hc4; exact hc4
                                    intro e0
                                    exact gateCall_end_touch τ σ c.d cal gid _ argHandle _
                                      hcalne hfrun hfserv hcalm hrun hcalrunσ hcalservσ rfl e0
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun er σ' h => (body _ h).2 er σ' rfl⟩

/-! ## `gate_return`: the caller-resumption channel -/

/-- The `gate_return` endgame state update satisfies the touch
characterization: the serving domain restores its saved context; the
caller flips `blocked gid → running` with exactly `rd := reply`. -/
theorem gateReturn_end_touch (τ σ0 : MachineState) (cd : DomainId) (gid : GateId)
    (act : Activation) (reply : Loom.Word32) (G : GateState)
    (hfrun : ∀ d', (τ.doms d').run = (σ0.doms d').run)
    (hfserv : ∀ d', (τ.doms d').serving = (σ0.doms d').serving)
    (hcalm : ∀ d', (τ.doms d').regs = (σ0.doms d').regs ∧
             (τ.doms d').pc = (σ0.doms d').pc ∧ (τ.doms d').cause = (σ0.doms d').cause)
    (hrun : (σ0.doms cd).run = .running)
    (hserv : (σ0.doms cd).serving = some gid)
    (hgact : (σ0.gates gid).act = some act)
    (hwf : Wf σ0) (e : DomainId) :
    Touch σ0 (((({ τ with gates := Loom.Fun.update τ.gates gid G }).setDom cd
        (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc
                             serving := act.savedServing })).setDom act.caller
        (fun ds => { ds with run := .running })).setDom act.caller
        (fun ds => ds.setReg act.callerRd reply)) (e ≠ cd) e := by
  have hXd : ({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).doms
      = τ.doms := rfl
  have hcallerblk : (σ0.doms act.caller).run = .blocked gid :=
    (hwf.gate_serving gid act hgact).2.1
  have hcne : act.caller ≠ cd := by
    intro h; rw [h, hrun] at hcallerblk; exact absurd hcallerblk (by simp)
  by_cases hecd : e = cd
  · subst hecd
    refine ⟨?_, ?_, fun hp => absurd rfl hp⟩
    · intro g hpre hpost
      rw [hserv] at hpre; exact absurd hpre (by simp)
    · intro g hpre hpost
      rw [hrun] at hpre; exact absurd hpre (by simp)
  · by_cases hecl : e = act.caller
    · subst hecl
      have hdcaller : ((((({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).setDom cd
          (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc
                               serving := act.savedServing })).setDom act.caller
          (fun ds => { ds with run := .running })).setDom act.caller
          (fun ds => ds.setReg act.callerRd reply)).doms act.caller)
          = ({ τ.doms act.caller with run := .running } : DomainState).setReg act.callerRd reply := by
        rw [setDom_doms_same, setDom_doms_same, setDom_doms_ne _ _ _ _ hcne, hXd]
      refine ⟨?_, ?_, ?_⟩
      · intro g hpre hpost
        rw [hdcaller] at hpost
        have hpost' : (τ.doms act.caller).serving = some g := by
          rw [setReg_serving] at hpost; exact hpost
        rw [hfserv, hpre] at hpost'
        exact absurd hpost' (by simp)
      · intro g hpre hpost
        have hgg : g = gid := by
          rw [hpre] at hcallerblk
          exact RunState.blocked.inj hcallerblk
        subst hgg
        refine ⟨act, reply, hgact, rfl, fun r => ?_⟩
        rw [hdcaller, DomainState.setReg_reg]
        by_cases hcond : r = act.callerRd ∧ r ≠ (0 : Fin numRegs)
        · rw [if_pos hcond, if_pos hcond]
        · rw [if_neg hcond, if_neg hcond]
          exact (reg_of_regs_eq (show ({ τ.doms act.caller with run := .running } : DomainState).regs
            = (σ0.doms act.caller).regs from (hcalm act.caller).1) r)
      · intro _ _ hrr
        rw [hdcaller] at hrr
        have hrr' : RunState.running = (σ0.doms act.caller).run := by
          rw [setReg_run] at hrr; exact hrr
        rw [hcallerblk] at hrr'
        exact absurd hrr' (by simp)
    · have hde : ((((({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).setDom cd
          (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc
                               serving := act.savedServing })).setDom act.caller
          (fun ds => { ds with run := .running })).setDom act.caller
          (fun ds => ds.setReg act.callerRd reply)).doms e) = τ.doms e := by
        rw [setDom_doms_ne _ _ _ _ hecl, setDom_doms_ne _ _ _ _ hecl,
          setDom_doms_ne _ _ _ _ hecd, hXd]
      exact Touch.of_calm (by rw [hde]; exact hfserv e) (by rw [hde]; exact hfrun e)
        (fun _ => by rw [hde]; exact hcalm e)

/-- `gate_return` satisfies the touch obligation. -/
theorem gatereturn_touch (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hrun : (σ.doms c.d).run = .running) :
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
        ∀ e, Touch σ σ' (e ≠ c.d) e) ∧
    (∀ er σ',
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
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = .err er σ' →
        σ' = σ) := by
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
      (∀ a σ', out = .ok a σ' → ∀ e, Touch σ σ' (e ≠ c.d) e) ∧
      (∀ er σ', out = .err er σ' → σ' = σ) := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none =>
        rw [hserv] at hout; simp only [SpecM.fatal] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none =>
            simp only [hgact] at hout; simp only [SpecM.fatal] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
        | some act =>
            simp only [hgact] at hout; simp only [SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f => rw [htbh] at hout; subst hout
                         exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
            | err e0 τ =>
                rw [htbh] at hout; subst hout
                have hτ := transferByHandle_err_state c.d act.caller _ σ e0 τ htbh
                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
            | ok reply τ =>
                rw [htbh] at hout
                obtain ⟨hfrun, hfserv, hfgates, hfinf⟩ :=
                  Machines.Lnp64u.Isa.Wip.transferByHandle_frame c.d act.caller _ σ reply τ htbh
                have hcalm := transferByHandle_calm c.d act.caller _ σ reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                  SpecM.setReg] at hout
                subst hout
                refine ⟨fun a σ' h => ?_, fun er σ' h => by simp at h⟩
                simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                intro e
                exact gateReturn_end_touch τ σ c.d gid act reply _
                  hfrun hfserv hcalm hrun hserv hgact hwf e
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun er σ' h => (body _ h).2 er σ' rfl⟩

/-! ## The per-opcode sweeps -/

/-- Every base opcode is calm: register/ALU/memory/branch work touches only
the executing domain's regs/pc and memory. -/
theorem base_calm : ∀ instr ∈ Machines.Lnp64u.Isa.base, ∀ c : Ctx,
    CalmLe c.d (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.setReg _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.setReg _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.setReg _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.setReg _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.setReg _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.setReg _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.setReg _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.setReg _ _ _)
  · exact CalmLe.setReg _ _ _
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.load _ _)
      (fun _ => CalmLe.setReg _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.store _ _ _))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.iteBool _ (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
        (CalmLe.pure ())))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.reg _ _)
      (fun _ => CalmLe.iteBool _ (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
        (CalmLe.pure ())))
  · exact CalmLe.bind (CalmLe.reg _ _) (fun _ => CalmLe.bind (CalmLe.setReg _ _ _)
      (fun _ => CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl)))

/-- Every system opcode satisfies the touch obligation: eight are calm; the
two gate ops and `halt` carry exactly the T4 channels. -/
theorem system_touch : ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ c : Ctx,
    TouchExec c (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  case _ => -- cap_dup
    refine TouchExec.of_calm ?_
    refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
    refine CalmLe.bind (CalmLe.reg _ _) fun dw => ?_
    refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
    obtain ⟨s, g, e⟩ := r
    show CalmLe c.d (match e.kind with
      | .mem base len perms =>
          Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
          Machines.Lnp64u.Isa.allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h =>
          SpecM.setReg c.d c.op.rd h
      | .gate gid =>
          (Pure.pure (CapKind.gate gid) : SpecM CapKind) >>= fun kind =>
          Machines.Lnp64u.Isa.allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h =>
          SpecM.setReg c.d c.op.rd h)
    cases e.kind with
    | mem b l p =>
        exact CalmLe.bind (CalmLe.narrow _ _ _ _) fun kind =>
          CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
    | gate i =>
        exact CalmLe.bind (CalmLe.pure _) fun kind =>
          CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
  case _ => -- cap_drop
    refine TouchExec.of_calm ?_
    refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
    refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
    obtain ⟨s, g, e⟩ := r
    show CalmLe c.d (SpecM.get >>= fun σ0 =>
      SpecM.set ((((match σ0.parentOf c.d s with
          | some p => σ0.reparent ⟨c.d, s, g⟩ p
          | none => σ0.orphanChildren ⟨c.d, s, g⟩).clearSlot c.d s).sweepRegions).sweepMover) >>=
        fun _ => SpecM.setReg c.d c.op.rd 0)
    refine CalmLe.getD _ fun σ0 => ?_
    constructor
    · intro a σ' he
      cases hp : σ0.parentOf c.d s with
      | some p =>
          rw [hp] at he
          simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          injection he with _ h2; subst h2
          refine CalmOut.trans ?_
            (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
          exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
      | none =>
          rw [hp] at he
          simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          injection he with _ h2; subst h2
          refine CalmOut.trans ?_
            (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
          exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
    · intro er σ' he
      cases hp : σ0.parentOf c.d s with
      | some p => rw [hp] at he
                  simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
      | none => rw [hp] at he
                simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_revoke
    refine TouchExec.of_calm ?_
    refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
    refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
    obtain ⟨s, g, e⟩ := r
    show CalmLe c.d (SpecM.require (decide (e.kind.cls = .mem)) .badCap >>= fun _ =>
      SpecM.get >>= fun σ0 =>
      SpecM.set (((σ0.destroyMarked (σ0.marks ⟨c.d, s, g⟩)).sweepRegions).sweepMover) >>=
      fun _ => SpecM.setReg c.d c.op.rd 0)
    refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
    refine CalmLe.getD _ fun σ0 => ?_
    constructor
    · intro a σ' he
      simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
      injection he with _ h2; subst h2
      refine CalmOut.trans ?_
        (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
      exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
    · intro er σ' he
      simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
  case _ => -- mem_grant
    refine TouchExec.of_calm ?_
    refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
    refine CalmLe.bind (CalmLe.reg _ _) fun dw => ?_
    refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
    obtain ⟨s, g, e⟩ := r
    show CalmLe c.d (match e.kind with
      | .gate _ => (SpecM.raise .badCap : SpecM Unit)
      | .mem base len perms =>
          Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
          Machines.Lnp64u.Isa.allocDerived (descDom dw) kind ⟨c.d, s, g⟩ >>= fun h =>
          SpecM.setReg c.d c.op.rd h)
    cases e.kind with
    | gate gid => exact CalmLe.raise _
    | mem base len perms =>
        exact CalmLe.bind (CalmLe.narrow _ _ _ _) fun kind =>
          CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
  case _ => -- map
    refine TouchExec.of_calm ?_
    refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
    refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
    obtain ⟨s, g, e⟩ := r
    show CalmLe c.d (match e.kind with
      | .gate _ => (SpecM.raise .badCap : SpecM Unit)
      | .mem base len perms =>
          SpecM.updDom c.d (fun ds =>
            { ds with regions :=
                (Loom.Fun.update ds.regions
                  ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
                  (some { base := base, len := len, perms := perms
                          backing := ⟨c.d, s, g⟩ })) }) >>= fun _ =>
          SpecM.setReg c.d c.op.rd 0)
    cases e.kind with
    | gate gid => exact CalmLe.raise _
    | mem base len perms =>
        exact CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
          fun _ => CalmLe.setReg _ _ _
  case _ => -- unmap
    exact TouchExec.of_calm (CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
      fun _ => CalmLe.setReg _ _ _)
  case _ => -- gate_call
    intro σ hwf hrun
    obtain ⟨hok, herr⟩ := gatecall_touch c σ hwf hrun
    exact ⟨hok, fun er σ' he => CalmOut.of_eq (herr er σ' he)⟩
  case _ => -- gate_return
    intro σ hwf hrun
    obtain ⟨hok, herr⟩ := gatereturn_touch c σ hwf hrun
    exact ⟨hok, fun er σ' he => CalmOut.of_eq (herr er σ' he)⟩
  case _ => -- move
    refine TouchExec.of_calm ?_
    refine CalmLe.getD _ fun σg => (?_ : CalmLe c.d _) σg
    refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
    refine CalmLe.bind (CalmLe.reg _ _) fun aw => ?_
    refine CalmLe.bind (CalmLe.load _ _) fun srcH => ?_
    refine CalmLe.bind (CalmLe.load _ _) fun dstH => ?_
    refine CalmLe.bind (CalmLe.load _ _) fun lenW => ?_
    refine CalmLe.bind (CalmLe.load _ _) fun stW => ?_
    refine CalmLe.bind (CalmLe.capLive _ _) fun rs => ?_
    obtain ⟨ss, gs_, es⟩ := rs
    refine CalmLe.bind (CalmLe.capLive _ _) fun rd_ => ?_
    obtain ⟨sd, gd, ed⟩ := rd_
    show CalmLe c.d (match es.kind, ed.kind with
      | .mem sb sl sp, .mem db dl dp =>
          SpecM.require sp.r .permDenied >>= fun _ =>
          SpecM.require dp.w .permDenied >>= fun _ =>
          SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat))
            .outOfRange >>= fun _ =>
          SpecM.get >>= fun σ1 =>
          SpecM.demand (σ1.domCovers c.d (stW.setWidth 12)
            { r := false, w := true, x := false }) .memoryAuthority >>= fun _ =>
          SpecM.set ({ σ1 with mover :=
            (some { owner := c.d, src := ⟨c.d, ss, gs_⟩, dst := ⟨c.d, sd, gd⟩
                    srcCur := sb, dstCur := db, remaining := lenW.toNat
                    statusAddr := stW.setWidth 12 }) }) >>= fun _ =>
          SpecM.setReg c.d c.op.rd 0
      | _, _ => (SpecM.raise .badCap : SpecM Unit))
    cases es.kind with
    | gate gi =>
        cases ed.kind with
        | gate _ => exact CalmLe.raise _
        | mem db dl dp => exact CalmLe.raise _
    | mem sb sl sp =>
        cases ed.kind with
        | gate _ => exact CalmLe.raise _
        | mem db dl dp =>
            refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
            refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
            refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
            refine CalmLe.getD _ fun σ1 => ?_
            constructor
            · intro a σ' he
              by_cases hcov : σ1.domCovers c.d (stW.setWidth 12)
                  { r := false, w := true, x := false }
              · simp only [SpecM.demand, hcov, if_true, specM_pure, specM_bind, SpecM.set,
                  SpecM.setReg, SpecM.modify] at he
                injection he with _ h2; subst h2
                refine CalmOut.trans ?_
                  (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
                exact CalmOut.of_doms_eq (fun e' => rfl)
              · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
            · intro er σ' he
              by_cases hcov : σ1.domCovers c.d (stW.setWidth 12)
                  { r := false, w := true, x := false }
              · simp [SpecM.demand, hcov, specM_pure, specM_bind, SpecM.set,
                  SpecM.setReg, SpecM.modify] at he
              · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
  case _ => -- yield
    exact TouchExec.of_calm (CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
      fun _ => CalmLe.setReg _ _ _)
  case _ => -- halt
    intro σ hwf hrun
    refine ⟨fun a σ' he => ?_, fun er σ' he => ?_⟩
    · simp only [SpecM.modify] at he; injection he with _ h2; subst h2
      intro e; exact (haltDom_touch σ c.d 0 hwf hrun e).mono (fun _ => trivial)
    · simp [SpecM.modify] at he

/-- **Every instruction satisfies the touch obligation.** -/
theorem exec_touch : ∀ instr ∈ isa, ∀ c : Ctx, TouchExec c (instr.sem.exec c) := by
  intro instr hmem c
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · exact TouchExec.of_calm (base_calm instr hb c)
  · exact system_touch instr hs c

/-! ## Lifting to retirement, the core phase, and the whole cycle -/

/-- `retire` satisfies the touch characterization: the pc bump and errno
write hit only the retiring domain; the instruction effect is `exec_touch`;
decode failure and faults are `haltDom_touch`. -/
theorem retire_touch (σ : MachineState) (d : DomainId) (w : Loom.Word32)
    (hwf : Wf σ) (hrun : (σ.doms d).run = .running) (hinf : σ.inflight = none)
    (e : DomainId) : Touch σ (retire σ d w) (e ≠ d) e := by
  unfold retire
  split
  · exact (haltDom_touch σ d _ hwf hrun e).mono (fun _ => trivial)
  · rename_i instr hdec
    set σ1 := σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }) with hσ1
    have hne : ∀ e', e' ≠ d → σ1.doms e' = σ.doms e' :=
      fun e' he' => setDom_doms_ne _ _ _ _ he'
    have hall : ∀ (d' : DomainId),
        ((σ1.doms d').caps = (σ.doms d').caps) ∧
        ((σ1.doms d').lineage = (σ.doms d').lineage) ∧
        ((σ1.doms d').slotGen = (σ.doms d').slotGen) ∧
        ((σ1.doms d').regions = (σ.doms d').regions) ∧
        ((σ1.doms d').run = (σ.doms d').run) ∧
        ((σ1.doms d').serving = (σ.doms d').serving) ∧
        ((σ1.doms d').regs = (σ.doms d').regs) ∧
        ((σ1.doms d').cause = (σ.doms d').cause) := by
      intro d'; rw [hσ1]; unfold MachineState.setDom
      by_cases hp : d' = d
      · subst hp; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hp]
    have hwf1 : Wf σ1 := by
      refine wf_of_skeleton_sameGates σ σ1
        (fun d' => (hall d').1) (fun d' => (hall d').2.1) (fun d' => (hall d').2.2.1)
        (fun d' => (hall d').2.2.2.1) (fun d' => (hall d').2.2.2.2.1)
        (fun d' => (hall d').2.2.2.2.2.1) rfl rfl ?_ hwf
      intro fl' hfl'; rw [show σ1.inflight = σ.inflight from rfl, hinf] at hfl'
      exact absurd hfl' (by simp)
    have hrun1 : (σ1.doms d).run = .running := by
      rw [(hall d).2.2.2.2.1]; exact hrun
    obtain ⟨hok, herr⟩ := exec_touch instr (Loom.Isa.decode_mem isa hdec)
      { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 hwf1 hrun1
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
    | ok a σ' =>
        simp only [hexr]
        exact Touch.transport (hok a σ' hexr e) ((hall e).2.2.2.2.2.1) ((hall e).2.2.2.2.1)
          ((hall e).2.2.2.2.2.2.1) (fun hp => by rw [hne e hp])
          ((hall e).2.2.2.2.2.2.2) rfl rfl
    | err er σ' =>
        simp only [hexr]
        have hcal : CalmOut d σ1 (σ'.setDom d (fun ds => ds.setReg (operandsOf w).rd er.toWord)) :=
          CalmOut.trans (herr er σ' hexr)
            (CalmOut.setDomExec σ' d _ (setReg_serving _ _ _) (setReg_run _ _ _))
        refine Touch.of_calm ?_ ?_ (fun hp => ?_)
        · rw [hcal.1 e, (hall e).2.2.2.2.2.1]
        · rw [hcal.2.1 e, (hall e).2.2.2.2.1]
        · obtain ⟨h1, h2, h3⟩ := hcal.2.2 e hp
          exact ⟨by rw [h1, hne e hp], by rw [h2, hne e hp], by rw [h3, hne e hp]⟩
    | fault f =>
        simp only [hexr]
        exact (haltDom_touch σ d (BitVec.ofNat 32 f.code) hwf hrun e).mono (fun _ => trivial)

/-- Charging a payer's budget (with or without the gate-donation decrement
and the in-flight latch) touches nothing T4 observes. -/
theorem touch_setBudget (σ : MachineState) (p : DomainId) (n : Nat) (P : Prop) (e : DomainId)
    (S : MachineState)
    (hS : S.doms = (σ.setDom p (fun ds => { ds with budget := ds.budget - n })).doms) :
    Touch σ S P e := by
  have hproj : S.doms e = (σ.setDom p (fun ds => { ds with budget := ds.budget - n })).doms e :=
    congrFun hS e
  by_cases hep : e = p
  · subst hep
    rw [setDom_doms_same] at hproj
    exact Touch.of_calm (by rw [hproj]) (by rw [hproj]) (fun _ => by rw [hproj]; exact ⟨rfl, rfl, rfl⟩)
  · rw [setDom_doms_ne _ _ _ _ hep] at hproj
    exact Touch.of_calm (by rw [hproj]) (by rw [hproj]) (fun _ => by rw [hproj]; exact ⟨rfl, rfl, rfl⟩)

/-- The core phase satisfies the touch characterization. -/
theorem corePhase_touch (m : Manifest) (σ : MachineState) (hwf : Wf σ) (e : DomainId) :
    Touch σ (corePhase m σ) (∀ fl, σ.inflight = some fl → fl.dom ≠ e) e := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · simp only [hc, if_true]
        have hwfI : Wf { σ with inflight := none } :=
          wf_of_skeleton_sameGates σ { σ with inflight := none }
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) rfl rfl (by simp) hwf
        have hrunI : (({ σ with inflight := none } : MachineState).doms fl.dom).run = .running :=
          hwf.inflight_running fl hinf
        have ht := retire_touch { σ with inflight := none } fl.dom fl.word hwfI hrunI rfl e
        exact (Touch.transport ht rfl rfl rfl (fun _ => rfl) rfl rfl rfl).mono
          (fun hp => (hp fl rfl).symm)
      · simp only [hc, if_false]
        exact Touch.of_calm rfl rfl (fun _ => ⟨rfl, rfl, rfl⟩)
  | none =>
      simp only []
      split
      · exact Touch.refl σ _ e
      · rename_i d hsched
        have hdrun : (σ.doms d).run = .running := schedule_running m σ d hsched
        split
        · exact (haltDom_touch σ d _ hwf hdrun e).mono (fun _ => trivial)
        · rename_i w hfetch
          split
          · exact (haltDom_touch σ d _ hwf hdrun e).mono (fun _ => trivial)
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              cases hservd : (σ.doms d).serving with
              | none =>
                  simp only [hservd]
                  exact touch_setBudget σ (σ.payer d) instr.cost.cost _ e _ rfl
              | some g =>
                  simp only [hservd]
                  cases hactg : (σ.gates g).act with
                  | none => exact (haltDom_touch σ d _ hwf hdrun e).mono (fun _ => trivial)
                  | some a =>
                      simp only [hactg]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        exact touch_setBudget σ (σ.payer d) instr.cost.cost _ e _ rfl
                      · simp only [hdon, if_false]
                        exact (haltDom_touch σ d _ hwf hdrun e).mono (fun _ => trivial)
            · simp only [hbud, if_false]
              exact Touch.refl σ _ e

/-- **The whole-cycle touch characterization** (T4's engine): in one `step`,
a domain's serving mark flips `none → some g` only through the scrubbed
`gate_call` activation entry; its run state flips `blocked g → running` only
through the recorded reply write; and if it is not in flight and sees no
gate transition, its regs/pc/cause are untouched. -/
theorem step_touch (m : Manifest) (σ : MachineState) (hwf : Wf σ) (e : DomainId) :
    Touch σ (step m σ) (∀ fl, σ.inflight = some fl → fl.dom ≠ e) e := by
  have hR := corePhase_touch m (refillPhase m σ) (refillPhase_preserves_wf m σ hwf) e
  have ht := Touch.transport hR (refillPhase_serving m σ e) (refillPhase_run m σ e)
    (refillPhase_regs m σ e) (fun _ => refillPhase_pc m σ e) (refillPhase_cause m σ e)
    (refillPhase_gates m σ) (congrFun (step_doms m σ) e)
  exact ht.mono (fun hp fl hfl => hp fl (by rw [← refillPhase_inflight m σ]; exact hfl))
