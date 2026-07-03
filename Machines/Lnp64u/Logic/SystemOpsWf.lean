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

/-- `narrow` is read-only and, on success, yields a W^X memory kind whose range
sits within the parent's. -/
theorem narrow_ok (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32)
    (σ : MachineState) {kind : CapKind} {σ' : MachineState}
    (he : narrow base len perms dw σ = .ok kind σ') :
    σ' = σ ∧ ∃ off nlen np, kind = .mem (base + off) nlen np ∧ np.wx = true ∧
      off.toNat + nlen.toNat ≤ len.toNat := by
  unfold narrow at he
  simp only [SpecM.require, specM_bind, specM_pure] at he
  split_ifs at he with h1 h2 h3
  · injection he with hk hσ; subst hσ
    refine ⟨rfl, descOff dw, descLen dw, descPerms dw, hk.symm, h3, ?_⟩
    simpa using h1
  all_goals simp [SpecM.raise] at he

/-- Bounds for a narrowed range: it sits within the parent's window. -/
theorem narrow_bounds (base : Addr) (len : BitVec 13) (off : BitVec 12) (nlen : BitVec 13)
    (hin : off.toNat + nlen.toNat ≤ len.toNat) (hpar : base.toNat + len.toNat ≤ memWords) :
    (base + off).toNat + nlen.toNat ≤ memWords := by
  have hle : (base + off).toNat ≤ base.toNat + off.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_le _ _
  omega

/-- `narrow` leaves the state unchanged on error (pre-mutation errno raises). -/
theorem narrow_err_state (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32)
    (σ : MachineState) {e : Errno} {σ' : MachineState}
    (he : narrow base len perms dw σ = .err e σ') : σ' = σ := by
  unfold narrow at he
  simp only [SpecM.require, specM_bind, specM_pure] at he
  split_ifs at he with h1 h2 h3 <;>
    simp only [SpecM.raise] at he <;>
    (try (injection he with _ h2; exact h2.symm)) <;> simp at he

/-- `allocDerived` leaves the state unchanged on error. -/
theorem allocDerived_err_state (owner : DomainId) (kind : CapKind) (parent : CapRef)
    (σ : MachineState) {e : Errno} {σ' : MachineState}
    (he : allocDerived owner kind parent σ = .err e σ') : σ' = σ := by
  unfold allocDerived at he
  simp only [SpecM.get, specM_bind] at he
  cases hfs : σ.freeSlot owner with
  | none => rw [hfs] at he; simp only [SpecM.raise] at he; injection he with _ h2; exact h2.symm
  | some s =>
      rw [hfs] at he
      cases hfc : σ.freeCell owner with
      | none => rw [hfc] at he; simp only [SpecM.raise] at he; injection he with _ h2; exact h2.symm
      | some l => rw [hfc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- `cap_dup` preserves the invariant: it derives a new capability from a live
one (narrowed if memory), installed via `allocDerived`. All error paths leave
the state unchanged (they are pre-mutation errno raises). -/
theorem capdup_preserves (c : Ctx) (σ : MachineState) (hwf : Wf σ) (hinf : σ.inflight = none) :
    (∀ x σ',
      ((do let hw ← reg c.d c.op.rs1
           let dw ← reg c.d c.op.rs2
           let (s, g, e) ← capLive c.d hw
           let kind ← match e.kind with
             | .mem base len perms => narrow base len perms dw
             | .gate gid => (Pure.pure (.gate gid) : SpecM _)
           let h ← allocDerived c.d kind ⟨c.d, s, g⟩
           setReg c.d c.op.rd h) : SpecM Unit) σ = .ok x σ' → Wf σ') := by
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
              have hσ1 : Wf σ1 := allocDerived_ok c.d (.gate gid) _ σ (by simp) hpar hwf ha
              exact wf_setReg σ1 c.d _ hh hσ1
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
                  -- the narrowed kind is W^X and in-bounds
                  have hbnd : base.toNat + len.toNat ≤ memWords := by
                    have := (hwf.doms c.d).bounds s en base len perms
                      (by unfold DomainState.liveCap at hlive
                          revert hlive; cases hcc : (σ.doms c.d).caps s with
                          | none => intro hh0; simp at hh0
                          | some ee => intro hh0; split at hh0 <;> simp_all) hk
                    exact this
                  have hwx' : ∀ b' l' p', kind = .mem b' l' p' →
                      p'.wx = true ∧ b'.toNat + l'.toNat ≤ memWords := by
                    intro b' l' p' hkeq; rw [hkind] at hkeq; injection hkeq with hb hl hp
                    subst hb; subst hl; subst hp
                    exact ⟨hwx, narrow_bounds base len off nlen hin hbnd⟩
                  have hσ2 : Wf σ2 := allocDerived_ok c.d kind _ σ hwx' hpar hwf ha
                  exact wf_setReg σ2 c.d _ hh hσ2


/-- `cap_dup`'s error clause: every failure path is a pre-mutation errno raise,
so the state is unchanged and `Wf` transfers. -/
theorem capdup_err (c : Ctx) (σ : MachineState) (hwf : Wf σ) :
    (∀ e σ',
      ((do let hw ← reg c.d c.op.rs1
           let dw ← reg c.d c.op.rs2
           let (s, g, en) ← capLive c.d hw
           let kind ← match en.kind with
             | .mem base len perms => narrow base len perms dw
             | .gate gid => (Pure.pure (.gate gid) : SpecM _)
           let h ← allocDerived c.d kind ⟨c.d, s, g⟩
           setReg c.d c.op.rd h) : SpecM Unit) σ = .err e σ' → Wf σ') := by
  intro e σ' he
  simp only [SpecM.reg, specM_bind] at he
  cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
  | err e0 σ0 =>
      have := capLive_err_state c.d _ σ hcl; rw [hcl] at he
      injection he with _ h2; subst h2; subst this; exact hwf
  | fault f => rw [hcl] at he; simp at he
  | ok rr σ0 =>
      obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
      rw [hcl] at he; obtain ⟨s, g, en⟩ := rr; simp only at he
      have halloc : ∀ (kind : CapKind),
          ((allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h => setReg c.d c.op.rd h) : SpecM Unit) σ
            = .err e σ' → Wf σ' := by
        intro kind hh
        simp only [specM_bind] at hh
        cases hac : allocDerived c.d kind ⟨c.d, s, g⟩ σ with
        | err e1 σ1 =>
            have hs := allocDerived_err_state c.d kind _ σ hac; rw [hac] at hh
            injection hh with _ h2; subst h2; subst hs; exact hwf
        | fault f => rw [hac] at hh; simp at hh
        | ok hval σ1 => rw [hac] at hh; simp [SpecM.setReg, SpecM.modify] at hh
      cases hk : en.kind with
      | gate gid =>
          rw [hk] at he; simp only [specM_pure, specM_bind] at he
          exact halloc (.gate gid) he
      | mem base len perms =>
          rw [hk] at he; simp only [specM_bind] at he
          cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
          | err e1 σ1 =>
              have hs := narrow_err_state base len perms _ σ hn; rw [hn] at he
              injection he with _ h2; subst h2; subst hs; exact hwf
          | fault f => rw [hn] at he; simp at he
          | ok kind σ1 =>
              have hσn := narrow_ok base len perms _ σ hn |>.1; subst σ1
              rw [hn] at he; simp only [specM_bind] at he
              exact halloc kind he

/-- `mem_grant` preserves the invariant: it narrows a live memory capability and
installs it in another domain via `allocDerived`. Same structure as `cap_dup`
(the recipient domain is `descDom dw`, and gate handles error out). -/
theorem memgrant_preserves (c : Ctx) (σ : MachineState) (hwf : Wf σ) :
    (∀ x σ',
      ((do let hw ← reg c.d c.op.rs1
           let dw ← reg c.d c.op.rs2
           let (s, g, e) ← capLive c.d hw
           match e.kind with
           | .gate _ => raise .badCap
           | .mem base len perms => do
               let kind ← narrow base len perms dw
               let h ← allocDerived (descDom dw) kind ⟨c.d, s, g⟩
               setReg c.d c.op.rd h) : SpecM Unit) σ = .ok x σ' → Wf σ') ∧
    (∀ e σ',
      ((do let hw ← reg c.d c.op.rs1
           let dw ← reg c.d c.op.rs2
           let (s, g, e) ← capLive c.d hw
           match e.kind with
           | .gate _ => raise .badCap
           | .mem base len perms => do
               let kind ← narrow base len perms dw
               let h ← allocDerived (descDom dw) kind ⟨c.d, s, g⟩
               setReg c.d c.op.rd h) : SpecM Unit) σ = .err e σ' → Wf σ') := by
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
                cases ha : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kind ⟨c.d, s, g⟩ σ with
                | err e2 σ2 => rw [ha] at he; simp at he
                | fault f => rw [ha] at he; simp at he
                | ok hh σ2 =>
                    rw [ha] at he
                    simp only [specM_bind, SpecM.setReg, SpecM.modify] at he
                    injection he with _ h2; subst h2
                    have hbnd : base.toNat + len.toNat ≤ memWords :=
                      (hwf.doms c.d).bounds s en base len perms
                        (by unfold DomainState.liveCap at hlive
                            revert hlive; cases hcc : (σ.doms c.d).caps s with
                            | none => intro hh0; simp at hh0
                            | some ee => intro hh0; split at hh0 <;> simp_all) hk
                    have hwx' : ∀ b' l' p', kind = .mem b' l' p' →
                        p'.wx = true ∧ b'.toNat + l'.toNat ≤ memWords := by
                      intro b' l' p' hkeq; rw [hkind] at hkeq; injection hkeq with hb hl hp
                      subst hb; subst hl; subst hp
                      exact ⟨hwx, narrow_bounds base len off nlen hin hbnd⟩
                    exact wf_setReg σ2 c.d _ hh
                      (allocDerived_ok (descDom _) kind _ σ hwx' hpar hwf ha)
  · intro e σ' he
    simp only [SpecM.reg, specM_bind] at he
    cases hcl : capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := capLive_err_state c.d _ σ hcl; rw [hcl] at he
        injection he with _ h2; subst h2; subst hs; exact hwf
    | fault f => rw [hcl] at he; simp at he
    | ok rr σ0 =>
        obtain ⟨hσeq, _⟩ := capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at he; obtain ⟨s, g, en⟩ := rr; simp only at he
        cases hk : en.kind with
        | gate gid =>
            rw [hk] at he; simp only [SpecM.raise] at he
            injection he with _ h2; subst h2; exact hwf
        | mem base len perms =>
            rw [hk] at he; simp only [specM_bind] at he
            cases hn : narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
            | err e1 σ1 =>
                have hs := narrow_err_state base len perms _ σ hn; rw [hn] at he
                injection he with _ h2; subst h2; subst hs; exact hwf
            | fault f => rw [hn] at he; simp at he
            | ok kind σ1 =>
                have hσn := narrow_ok base len perms _ σ hn |>.1; subst σ1
                rw [hn] at he; simp only [specM_bind] at he
                cases ha : allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kind ⟨c.d, s, g⟩ σ with
                | err e2 σ2 =>
                    have hs := allocDerived_err_state (descDom _) kind _ σ ha; rw [ha] at he
                    injection he with _ h2; subst h2; subst hs; exact hwf
                | fault f => rw [ha] at he; simp at he
                | ok hh σ2 => rw [ha] at he; simp [SpecM.setReg, SpecM.modify] at he

/-- The `move` opcode's operational semantics (matches `Isa.system`'s `move`). -/
def moveExec (c : Ctx) : SpecM Unit := do
  let σ0 ← SpecM.get
  require σ0.mover.isNone .moverBusy
  let aw ← reg c.d c.op.rs1
  let base : Addr := aw.setWidth 12
  let srcH ← load c.d base
  let dstH ← load c.d (base + 1)
  let lenW ← load c.d (base + 2)
  let stW ← load c.d (base + 3)
  let (ss, gs_, es) ← capLive c.d srcH
  let (sd, gd, ed) ← capLive c.d dstH
  match es.kind, ed.kind with
  | .mem sb sl sp, .mem db dl dp => do
      require sp.r .permDenied
      require dp.w .permDenied
      let n := lenW.toNat
      require (decide (n ≤ sl.toNat) && decide (n ≤ dl.toNat)) .outOfRange
      let sa : Addr := stW.setWidth 12
      let σ ← SpecM.get
      demand (σ.domCovers c.d sa { r := false, w := true, x := false }) .memoryAuthority
      let job : MoverJob :=
        { owner := c.d, src := ⟨c.d, ss, gs_⟩, dst := ⟨c.d, sd, gd⟩
          srcCur := sb, dstCur := db, remaining := n, statusAddr := sa }
      set ({ σ with mover := some job })
      setReg c.d c.op.rd 0
  | _, _ => raise .badCap


/-- `move` ok clause: after a read-only prefix (require, register read, four
descriptor loads, two `capLive` lookups, permission/range checks, authority
`demand`), it programs the Mover with a live owned job (`wf_setMover`) and writes
`rd` (`wf_setReg`). -/
theorem move_ok (c : Ctx) (σ : MachineState) (hwf : Wf σ) :
    (∀ x σ', (moveExec c) σ = .ok x σ' → Wf σ') := by
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
                                                      have hsl : σ.liveRef ⟨c.d, ss, gs_⟩ = true := by unfold MachineState.liveRef; rw [hslive]; rfl
                                                      have hdl : σ.liveRef ⟨c.d, sd, gd⟩ = true := by unfold MachineState.liveRef; rw [hdlive]; rfl
                                                      exact wf_setReg _ c.d _ 0 (wf_setMover σ _ rfl rfl hsl hdl hwf)


/-- `move` err clause: after a read-only prefix (require, register read, four
descriptor loads, two `capLive` lookups, permission/range checks, authority
`demand`), it programs the Mover with a live owned job (`wf_setMover`) and writes
`rd` (`wf_setReg`). -/
theorem move_err (c : Ctx) (σ : MachineState) (hwf : Wf σ) :
    (∀ x σ', (moveExec c) σ = .err x σ' → Wf σ') := by
  intro x σ' he
  simp only [moveExec, SpecM.get, specM_bind] at he
  cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
  | err e0 σ0 => have hq := require_err_state _ _ σ hr0; rw [hr0] at he; injection he with _ h2; subst h2; subst hq; exact hwf
  | fault f => rw [hr0] at he; simp at he
  | ok u0 σ0 =>
      have hh0 := require_ok _ _ σ hr0; subst σ0
      rw [hr0] at he; simp only [SpecM.reg] at he
      set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
      cases hl1 : load c.d B σ with
      | err e σe => have hq := load_err_state _ _ σ hl1; rw [hl1] at he; injection he with _ h2; subst h2; subst hq; exact hwf
      | fault f => rw [hl1] at he; simp at he
      | ok srcH σ1 =>
          have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
          cases hl2 : load c.d (B + 1) σ with
          | err e σe => have hq := load_err_state _ _ σ hl2; rw [hl2] at he; injection he with _ h2; subst h2; subst hq; exact hwf
          | fault f => rw [hl2] at he; simp at he
          | ok dstH σ2 =>
              have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
              cases hl3 : load c.d (B + 2) σ with
              | err e σe => have hq := load_err_state _ _ σ hl3; rw [hl3] at he; injection he with _ h2; subst h2; subst hq; exact hwf
              | fault f => rw [hl3] at he; simp at he
              | ok lenW σ3 =>
                  have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                  cases hl4 : load c.d (B + 3) σ with
                  | err e σe => have hq := load_err_state _ _ σ hl4; rw [hl4] at he; injection he with _ h2; subst h2; subst hq; exact hwf
                  | fault f => rw [hl4] at he; simp at he
                  | ok stW σ4 =>
                      have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                      cases hc1 : capLive c.d srcH σ with
                      | err e σe => have hq := capLive_err_state c.d _ σ hc1; rw [hc1] at he; injection he with _ h2; subst h2; subst hq; exact hwf
                      | fault f => rw [hc1] at he; simp at he
                      | ok rs σ5 =>
                          have hcs := capLive_ok c.d _ σ hc1; obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                          rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                          cases hc2 : capLive c.d dstH σ with
                          | err e σe => have hq := capLive_err_state c.d _ σ hc2; rw [hc2] at he; injection he with _ h2; subst h2; subst hq; exact hwf
                          | fault f => rw [hc2] at he; simp at he
                          | ok rdd σ6 =>
                              have hcd := capLive_ok c.d _ σ hc2; obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                              rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                              cases hks : es.kind with
                              | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                          | gate _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact hwf
                                          | mem _ _ _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact hwf
                              | mem sb sl sp =>
                                  cases hkd : ed.kind with
                                  | gate _ => rw [hks, hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; exact hwf
                                  | mem db dl dp =>
                                      rw [hks, hkd] at he; simp only [specM_bind] at he
                                      cases hq1 : SpecM.require sp.r .permDenied σ with
                                      | err e σe => have hq := require_err_state _ _ σ hq1; rw [hq1] at he; injection he with _ h2; subst h2; subst hq; exact hwf
                                      | fault f => rw [hq1] at he; simp at he
                                      | ok _ σq1 =>
                                          have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                          cases hq2 : SpecM.require dp.w .permDenied σ with
                                          | err e σe => have hq := require_err_state _ _ σ hq2; rw [hq2] at he; injection he with _ h2; subst h2; subst hq; exact hwf
                                          | fault f => rw [hq2] at he; simp at he
                                          | ok _ σq2 =>
                                              have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                              cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                              | err e σe => have hq := require_err_state _ _ σ hq3; rw [hq3] at he; injection he with _ h2; subst h2; subst hq; exact hwf
                                              | fault f => rw [hq3] at he; simp at he
                                              | ok _ σq3 =>
                                                  have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                  cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                  | err e σe => exact absurd hd (by simp [SpecM.demand]; split <;> simp [SpecM.fatal])
                                                  | fault f => rw [hd] at he; simp at he
                                                  | ok _ σdd =>
                                                      have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                      simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he


/-- The per-opcode dispatch of `SystemOpsPreserveWf`. Two of eleven ops proved
(`unmap`, `yield`); the nine capability/gate/Mover ops are the remaining
kernel-level core. -/
theorem system_preserves : SystemOpsPreserveWf := by
  intro instr hmem c σ hwf hrun hinf
  fin_cases hmem
  case _ => exact ⟨capdup_preserves c σ hwf hinf, capdup_err c σ hwf⟩
  case _ => sorry  -- cap_drop   (reparent/orphan + clearSlot + sweeps)
  case _ => sorry  -- cap_revoke (destroyMarked + sweeps)
  case _ => exact memgrant_preserves c σ hwf
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
  case _ => exact ⟨move_ok c σ hwf, move_err c σ hwf⟩
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
