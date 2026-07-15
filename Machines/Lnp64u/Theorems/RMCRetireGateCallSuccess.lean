-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCallArm

/-!
# R-MC retirement: successful gate_call arms

Successful `gate_call` retirement, split at the optional argument transfer.
The null branch establishes the complete activation/callee/caller cycle with
an empty structural kill footprint; the non-null branch reuses the shared
`transferA` abstraction.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- A null argument selects the identity arm of the optional hardware
transfer, independently of the accumulator supplied by retirement. -/
theorem callTransferA_run_zero (σ acc : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argW d).eval σ = 0#32) :
    (callTransferA d).run σ acc = acc := by
  have hnz : (Hw.argNZ d).eval σ ≠ 1#1 := by
    intro h
    exact (argNZ_eval_iff σ d).mp h hz
  simp [callTransferA, Act.run, bv1_ne_one.mp hnz]

/-- A non-null argument selects the shared structural transfer action. -/
theorem callTransferA_run_nonzero (σ acc : Loom.Hw.St) (d : DomainId)
    (hnz : (Hw.argW d).eval σ ≠ 0#32) :
    (callTransferA d).run σ acc =
      (Hw.transferA d (Hw.callCal d) (Hw.argSel d)).run σ acc := by
  have hnzE : (Hw.argNZ d).eval σ = 1#1 :=
    (argNZ_eval_iff σ d).mpr hnz
  simp [callTransferA, Act.run, hnzE]

/-- A successful call with a null argument cannot invalidate a Mover
endpoint, so its auxiliary status-memory port is disabled. -/
theorem callCirc_memEn_zero_arg (σ : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argW d).eval σ = 0#32) :
    (Hw.callCirc d).memEn.eval σ = 0#1 := by
  have hnz : (Hw.argNZ d).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro h
    exact (argNZ_eval_iff σ d).mp h hz
  have hk : (Hw.movKilledE (Hw.callKilled d)).eval σ = 0#1 := by
    unfold Hw.movKilledE Hw.callKilled Hw.andAll
    simp only [Expr.eval]
    rw [hnz]
    exact (by decide : ∀ a b c : BitVec 1,
      a &&& ((0#1 &&& b) ||| (0#1 &&& c)) = 0#1) _ _ _
  unfold Hw.callCirc Hw.sweepMem Hw.andAll
  change (Hw.callOkE d).eval σ &&&
    ((Hw.movKilledE (Hw.callKilled d)).eval σ &&&
      (Hw.statusAuthE (Hw.callKilled d)).eval σ) = 0#1
  rw [hk]
  exact (by decide : ∀ a b : BitVec 1, a &&& (0#1 &&& b) = 0#1) _ _

/-- Consequently, the core phase of a null-argument call preserves memory,
including when all call checks pass. -/
theorem coreAct_mem_gateCall_zero_arg (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hz : (Hw.argW E).eval σ = 0#32) (b : Addr) :
    ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
      b.toNat 32 = σ.mems "mem" b.toNat 32 := by
  have hport := retireMem_gateCall_sel σ E hifsel hifexcl hopc
  have hmen : (Hw.callCirc E).memEn.eval σ = 0#1 :=
    callCirc_memEn_zero_arg σ E hz
  rw [coreAct_run_retire_eq m σ _ hifv hcl,
    retireAct_run_mems σ _ b.toNat 32]
  show (if (((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1,
          .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
        (.lit 0 : Expr 32))).1).eval σ = 1#1 then _
    else ((Hw.refillAct m).run σ σ)).mems "mem" b.toNat 32 = _
  rw [if_neg (by rw [hport.1, hmen]; decide)]
  exact refill_pres_mem m σ "mem" b.toNat 32

/-- Clearing the retiring in-flight valid bit after refill has exactly the
expected abstract effect.  This is the accumulator used by every successful
retirement payload. -/
theorem abs_refill_clearInflight (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP) :
    Hw.abs ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)) =
      { refillPhase m (Hw.abs σ) with inflight := none } := by
  have hrefill := abs_refill m hwf hfit σ hsync
  apply machineState_ext'
  · change (((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)).regs "cycle" 32) = _
    simp [Act.run, RegEnv.set]
    exact congrArg MachineState.cycle hrefill
  · change (fun a : Addr => ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)).mems "mem" a.toNat 32) = _
    simpa [Act.run] using congrArg MachineState.mem hrefill
  · change (fun d => Hw.absDom ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)) d) = _
    have hdom : ∀ d, Hw.absDom ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)) d =
        Hw.absDom ((Hw.refillAct m).run σ σ) d := by
      intro d
      apply absDom_congr
      intro q hq
      simp only [Act.run, RegEnv.set]
      have hne : q.1 ≠ "if_v" := by
        exact (show ∀ q ∈ domReadNames d, q.1 ≠ "if_v" from by
          fin_cases d <;> decide +kernel) q hq
      simp [hne]
    funext d
    rw [hdom]
    exact congrFun (congrArg MachineState.doms hrefill) d
  · change (fun g => Hw.absGate ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)) g) = _
    have hgate : ∀ g, Hw.absGate ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)) g =
        Hw.absGate ((Hw.refillAct m).run σ σ) g := by
      intro g
      apply absGate_congr
      intro q hq
      simp only [Act.run, RegEnv.set]
      have hne : q.1 ≠ "if_v" := by
        exact (show ∀ q ∈ gateReadNames g, q.1 ≠ "if_v" from by
          fin_cases g <;> decide +kernel) q hq
      simp [hne]
    funext g
    rw [hgate]
    exact congrFun (congrArg MachineState.gates hrefill) g
  · change Hw.absMover ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)) = _
    have hm : Hw.absMover ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)) =
        Hw.absMover ((Hw.refillAct m).run σ σ) := by
      unfold Hw.absMover
      simp [Act.run, RegEnv.set]
    rw [hm]
    exact congrArg MachineState.mover hrefill
  · rfl

/-- The specification enters the call body after advancing the caller PC,
whereas the hardware successful payload performs that advance itself.  Refill
does not change any value captured by the activation record, so the two pure
successful-call transformers coincide. -/
theorem callAbstractSuccess_refill_pc (m : Manifest) (σ : Loom.Hw.St)
    (d cal : DomainId) (g : GateId) (rd : RegId)
    (argHandle : Loom.Word32) (depth : Nat) (hne : d ≠ cal) :
    let base : MachineState :=
      { refillPhase m (Hw.abs σ) with inflight := none }
    let prefixed := base.setDom d (fun ds => { ds with pc := ds.pc + 1 })
    callAbstractSuccessAt prefixed prefixed d cal g rd argHandle depth
        (prefixed.doms d).pc =
      callAbstractSuccess (Hw.abs σ) base d cal g rd argHandle depth := by
  dsimp only
  unfold callAbstractSuccess callAbstractSuccessAt
  apply machineState_ext' <;> try rfl
  · funext x
    by_cases hxd : x = d
    · subst x
      simp [MachineState.setDom, Loom.Fun.update]
    · by_cases hxc : x = cal
      · subst x
        have hcald : cal ≠ d := hxd
        simp [MachineState.setDom, Loom.Fun.update, hcald,
          refillPhase_serving]
      · simp [MachineState.setDom, Loom.Fun.update, hxd, hxc]
  · funext h
    by_cases hh : h = g
    · subst h
      have hcald : cal ≠ d := Ne.symm hne
      simp [MachineState.setDom, Loom.Fun.update, hcald,
        refillPhase_gates,
        refillPhase_serving, refillPhase_dmaxdon]
    · simp [MachineState.setDom, hh, refillPhase_gates]

/-- Once the common gate-call checks have selected a ready callee, a null
argument reduces the specification body directly to the successful pure
transformer. -/
theorem gateCallExec_success_zero_of_ready (σ : Loom.Hw.St)
    (τ : MachineState) (d : DomainId) (c : Ctx)
    (hready : CallReady σ τ d c)
    (harg : (τ.doms c.d).reg c.op.rs2 = 0) :
    ∃ g : GateId, ∃ cal : DomainId,
      cal ≠ c.d ∧
      finOfBv (by decide : 2 ^ 2 = numGates)
          ((Hw.callGid d).eval σ) = g ∧
      finOfBv (by decide : 2 ^ 2 = numDomains)
          ((Hw.callCal d).eval σ) = cal ∧
      Machines.Lnp64u.Isa.Wip.gateCallExec c τ =
        .ok () (callAbstractSuccessAt τ τ c.d cal g c.op.rd 0
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ) (τ.doms c.d).pc) := by
  obtain ⟨S, G, e, g, cal, hlive, hkind, hact, hcal, hne, hrun,
      hserv, hdepth, hgid, hcalSel⟩ := hready
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ.doms c.d).reg c.op.rs2) τ = .ok 0 τ := by
    rw [harg]
    exact transferByHandle_eq_zero τ c.d cal
  refine ⟨g, cal, hne, hgid, hcalSel, ?_⟩
  exact gateCallExec_eq_selected c τ τ S G e g cal 0 hlive hkind hact
    hcal hne hrun hserv hdepth htransfer rfl rfl rfl rfl rfl

end Machines.Lnp64u.Theorems.RMC
