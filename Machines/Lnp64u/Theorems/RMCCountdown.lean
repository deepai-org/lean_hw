-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCMover
import Machines.Lnp64u.Theorems.RMCRefill

/-!
# R-MC support: the countdown arm of the square

On a cycle with an in-flight instruction that is *not* on its last cycle
(`if_v = 1`, `if_cl ≥ 2`), the core rule only decrements the countdown
latch (plus one hidden mark-engine round for an in-flight `cap_revoke`),
and the spec's core phase only decrements `cyclesLeft`. Everything else
is the refill/mover/tick composition, already bridged. This file proves
`square_countdown`: the full one-cycle square under those two hypotheses.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## Countdown-cycle signal facts -/

/-- No retirement happens while `if_cl ≥ 2`. -/
theorem retiringE_eval_countdown (σ : Loom.Hw.St)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    Hw.retiringE.eval σ = 0#1 := by
  show σ.regs "if_v" 1 &&&
    (if (σ.regs "if_cl" 8).ult (2#8) = true then 1#1 else 0#1) = 0#1
  rw [if_neg (show ¬((σ.regs "if_cl" 8).ult (2#8) = true) from by
    intro hcon
    have := of_decide_eq_true (show decide ((σ.regs "if_cl" 8).toNat
      < (2#8).toNat) = true from hcon)
    have h2 : (2#8 : BitVec 8).toNat = 2 := rfl
    omega)]
  generalize σ.regs "if_v" 1 = b
  revert b; decide

/-- The hidden mark-engine step of the countdown branch is `rv_*`-only. -/
private theorem rvArm_prefixed :
    WritesPrefixed "rv_" (Act.ite (Hw.isMn "cap_revoke")
      (.ite (.eq (.reg 8 "if_cl") (.lit (BitVec.ofNat 8 Hw.revokeCost)))
        Hw.rvInit Hw.rvStep) .skip) = true := by
  simp only [WritesPrefixed, Bool.and_eq_true]
  exact ⟨⟨rvInit_prefixed, rvStep_prefixed⟩, trivial⟩

/-! ## The countdown branch's register/memory effects -/

/-- Select the countdown branch of the core rule. -/
private theorem coreAct_run_countdown_eq (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    (Hw.coreAct m).run σ acc =
      (Act.ite (Hw.isMn "cap_revoke")
        (.ite (.eq (.reg 8 "if_cl") (.lit (BitVec.ofNat 8 Hw.revokeCost)))
          Hw.rvInit Hw.rvStep) .skip).run σ
        ((Act.write 8 "if_cl"
          (.sub (.reg 8 "if_cl") (.lit 1))).run σ acc) := by
  show (if (Expr.reg 1 "if_v").eval σ = 1#1 then _ else _) = _
  rw [if_pos (show (Expr.reg 1 "if_v").eval σ = 1#1 from hifv)]
  show (if (Expr.ult (.reg 8 "if_cl") (.lit 2)).eval σ = 1#1 then _ else _) = _
  rw [if_neg (show ¬((Expr.ult (.reg 8 "if_cl") (.lit 2)).eval σ = 1#1) from by
    intro hcon
    rw [ultE_eval] at hcon
    have h2 : ((Expr.lit (2 : BitVec 8)).eval σ).toNat = 2 := rfl
    have h3 : (Expr.reg 8 "if_cl").eval σ = σ.regs "if_cl" 8 := rfl
    rw [h3] at hcon
    omega)]
  rfl

/-- Frame: the countdown branch writes only `if_cl` and the hidden
mark-engine registers. -/
theorem countdown_regs (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat)
    (rn : String) (w : Nat)
    (hrv : rn.startsWith "rv_" = false) (hne : ¬(rn = "if_cl")) :
    ((Hw.coreAct m).run σ acc).regs rn w = acc.regs rn w := by
  rw [coreAct_run_countdown_eq m σ acc hifv hcl2,
    run_WritesPrefixed hrv w _ rvArm_prefixed]
  show (acc.regs.set "if_cl" _) rn w = acc.regs rn w
  simp only [RegEnv.set]
  rw [if_neg hne]

/-- The countdown latch decrements (reads pre-cycle). -/
theorem countdown_ifcl (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    ((Hw.coreAct m).run σ acc).regs "if_cl" 8 = σ.regs "if_cl" 8 - 1 := by
  rw [coreAct_run_countdown_eq m σ acc hifv hcl2,
    run_WritesPrefixed (by decide +kernel) 8 _ rvArm_prefixed]
  show (acc.regs.set "if_cl" ((σ.regs "if_cl" 8) - (1#8))) "if_cl" 8 = _
  simp [RegEnv.set]

/-- The countdown branch writes no memory. -/
theorem countdown_mems (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat)
    (mn : String) (ad w : Nat) :
    ((Hw.coreAct m).run σ acc).mems mn ad w = acc.mems mn ad w := by
  rw [coreAct_run_countdown_eq m σ acc hifv hcl2]
  rw [Loom.Hw.Compile.run_mems_notin mn _ (by
    show mn ∉ (Act.ite (Hw.isMn "cap_revoke") _ Act.skip).memWrites
    exact of_decide_eq_true rfl) σ _]
  rfl


/-! ## Spec-side equations -/

private theorem corePhase_countdown (m : Manifest) (τ : MachineState)
    (fl : InFlight) (hfl : τ.inflight = some fl) (h2 : 1 < fl.cyclesLeft) :
    corePhase m τ =
      { τ with inflight := some { fl with cyclesLeft := fl.cyclesLeft - 1 } } := by
  unfold corePhase
  rw [hfl]
  show (if fl.cyclesLeft ≤ 1 then _ else _) = _
  rw [if_neg (by omega : ¬ fl.cyclesLeft ≤ 1)]

theorem moverStatus_cycle (τ : MachineState) (job : MoverJob)
    (v : Loom.Word32) : (moverStatus τ job v).cycle = τ.cycle := by
  unfold Machines.Lnp64u.moverStatus
  split <;> rfl

theorem moverPhase_cycle (τ : MachineState) :
    (moverPhase τ).cycle = τ.cycle := by
  cases hj : τ.mover with
  | none => simp [Machines.Lnp64u.moverPhase, hj]
  | some job =>
      simp only [Machines.Lnp64u.moverPhase, hj]
      split
      · rw [moverStatus_cycle]
      · split
        · split
          · rw [moverStatus_cycle]; rfl
          · rfl
        · rw [moverStatus_cycle]

private theorem toNat_sub_one_bv8 (x : BitVec 8) (h : 1 ≤ x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub]
  have hlt := x.isLt
  show (2 ^ 8 - (1#8).toNat + x.toNat) % 2 ^ 8 = _
  rw [show (1#8 : BitVec 8).toNat = 1 from rfl]
  omega

/-! ## The countdown square -/

/-- **The countdown arm of the square**: with an in-flight instruction not
on its last cycle, one hardware cycle is exactly one spec step. -/
theorem square_countdown (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hnr := retiringE_eval_countdown σ hcl2
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  -- the decoded in-flight instruction
  have hfl : τ1.inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := σ.regs "if_word" 32
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    rw [Hw.absInflight]
    rw [if_pos (show σ.regs "if_v" 1 = 1 from hifv)]
  have hτ2 := corePhase_countdown m τ1 _ hfl (by simpa using hcl2)
  -- bridge hypotheses against the post-core spec state
  have hcaps : ∀ d, ((corePhase m τ1).doms d).caps
      = ((Hw.abs σ).doms d).caps := by
    intro d
    rw [hτ2]
    show (τ1.doms d).caps = _
    rw [hτ1, refillPhase_caps]
  have hgen : ∀ d, ((corePhase m τ1).doms d).slotGen
      = ((Hw.abs σ).doms d).slotGen := by
    intro d
    rw [hτ2]
    show (τ1.doms d).slotGen = _
    rw [hτ1, refillPhase_slotGen]
  have hrgn : ∀ d, ((corePhase m τ1).doms d).regions
      = ((Hw.abs σ).doms d).regions := by
    intro d
    rw [hτ2]
    show (τ1.doms d).regions = _
    rw [hτ1, refillPhase_regions]
  have hjob : (corePhase m τ1).mover = Hw.absMover σ := by
    rw [hτ2]
    show τ1.mover = _
    rw [hτ1, refillPhase_mover]
    rfl
  have hmem2 : ∀ ad, ((Hw.coreAct m).run σ σ1).mems "mem" ad 32
      = σ.mems "mem" ad 32 := by
    intro ad
    rw [countdown_mems m σ σ1 hifv hcl2, hσ1]
    exact Loom.Hw.Compile.run_mems_notin "mem" _
      (by rw [refillAct_memWrites]; simp) σ σ ad 32
  have hτm : ∀ b : Addr, (corePhase m τ1).mem b
      = σ.mems "mem" b.toNat 32 := by
    intro b
    rw [hτ2]
    show τ1.mem b = _
    rw [hτ1]
    rfl
  -- register preservation down to the post-refill accumulator
  have hp : ∀ (rn : String) (w : Nat), rn.startsWith "rv_" = false →
      rn.startsWith "mov_" = false → ¬(rn = "if_cl") →
      ¬(rn = "cycle" ∧ w = 32) →
      ((Hw.core m).cycle σ).regs rn w = σ1.regs rn w := by
    intro rn w h1 h2 h3 h4
    rw [core_cycle_unfold]
    rw [frame (show (rn, w) ∉ Hw.tickAct.regWrites from by
      intro hmem
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem
      exact h4 hmem)]
    rw [run_WritesPrefixed h2 w _ mover_prefixed]
    exact countdown_regs m σ σ1 hifv hcl2 rn w h1 h3
  -- the spec step, unfolded
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · -- cycle
    show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hτ2]
    rfl
  · -- mem
    funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    exact moverAct_mem_quiescent σ _ (corePhase m τ1) (Inert.of_nonretiring σ hnr) hcaps hgen hrgn
      hjob (fun d sc => andAll_retiring_quiescent σ hnr _) hmem2 hτm a
  · -- doms
    funext d
    have hRHS : (moverPhase (corePhase m τ1)).doms d = τ1.doms d := by
      rw [moverPhase_doms, hτ2]
    show Hw.absDom ((Hw.core m).cycle σ) d = _
    rw [hRHS]
    have hL1 : τ1.doms d = Hw.absDom σ1 d := by
      rw [← habs1]; rfl
    rw [hL1]
    apply domainState_ext'
    · funext r
      exact hp (Hw.dreg d r) 32 (by fin_cases d <;> fin_cases r <;> decide +kernel)
        (by fin_cases d <;> fin_cases r <;> decide +kernel)
        (by fin_cases d <;> fin_cases r <;> decide +kernel)
        (by fin_cases d <;> fin_cases r <;> decide +kernel)
    · exact hp (Hw.dpc d) 12 (by fin_cases d <;> decide +kernel)
        (by fin_cases d <;> decide +kernel) (by fin_cases d <;> decide +kernel)
        (by fin_cases d <;> decide +kernel)
    · funext s
      show (if ((Hw.core m).cycle σ).regs (Hw.dcapV d s) 1 = 1 then _ else _)
        = _
      rw [hp (Hw.dcapV d s) 1 (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel),
        hp (Hw.dcapKind d s) 32 (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel),
        hp (Hw.dcapLinV d s) 1 (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel),
        hp (Hw.dcapLin d s) 4 (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)]
      rfl
    · funext s
      exact hp (Hw.dgen d s) 8 (by fin_cases d <;> fin_cases s <;> decide +kernel)
        (by fin_cases d <;> fin_cases s <;> decide +kernel)
        (by fin_cases d <;> fin_cases s <;> decide +kernel)
        (by fin_cases d <;> fin_cases s <;> decide +kernel)
    · funext l
      show (if ((Hw.core m).cycle σ).regs (Hw.dcellV d l) 1 = 1 then _ else _)
        = _
      rw [hp (Hw.dcellV d l) 1 (by fin_cases d <;> fin_cases l <;> decide +kernel)
          (by fin_cases d <;> fin_cases l <;> decide +kernel)
          (by fin_cases d <;> fin_cases l <;> decide +kernel)
          (by fin_cases d <;> fin_cases l <;> decide +kernel),
        hp (Hw.dcellPar d l) 14 (by fin_cases d <;> fin_cases l <;> decide +kernel)
          (by fin_cases d <;> fin_cases l <;> decide +kernel)
          (by fin_cases d <;> fin_cases l <;> decide +kernel)
          (by fin_cases d <;> fin_cases l <;> decide +kernel)]
      rfl
    · funext r
      show (if ((Hw.core m).cycle σ).regs (Hw.drgnV d r) 1 = 1 then _ else _)
        = _
      rw [hp (Hw.drgnV d r) 1 (by fin_cases d <;> fin_cases r <;> decide +kernel)
          (by fin_cases d <;> fin_cases r <;> decide +kernel)
          (by fin_cases d <;> fin_cases r <;> decide +kernel)
          (by fin_cases d <;> fin_cases r <;> decide +kernel),
        hp (Hw.drgn d r) 42 (by fin_cases d <;> fin_cases r <;> decide +kernel)
          (by fin_cases d <;> fin_cases r <;> decide +kernel)
          (by fin_cases d <;> fin_cases r <;> decide +kernel)
          (by fin_cases d <;> fin_cases r <;> decide +kernel)]
      rfl
    · show Hw.decRun _ _ = _
      rw [hp (Hw.drun d) 2 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel) (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel),
        hp (Hw.drunG d) 2 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel) (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel)]
      rfl
    · show (if ((Hw.core m).cycle σ).regs (Hw.dsrvV d) 1 = 1 then _ else _) = _
      rw [hp (Hw.dsrvV d) 1 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel) (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel),
        hp (Hw.dsrv d) 2 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel) (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel)]
      rfl
    · exact hp (Hw.dcause d) 32 (by fin_cases d <;> decide +kernel)
        (by fin_cases d <;> decide +kernel) (by fin_cases d <;> decide +kernel)
        (by fin_cases d <;> decide +kernel)
    · show (((Hw.core m).cycle σ).regs (Hw.dbudget d) 32).toNat = _
      rw [hp (Hw.dbudget d) 32 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel) (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel)]
      rfl
    · show (((Hw.core m).cycle σ).regs (Hw.dmaxdon d) 32).toNat = _
      rw [hp (Hw.dmaxdon d) 32 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel) (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel)]
      rfl
  · -- gates
    funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g = τ1.gates g := by
      rw [moverPhase_gates, hτ2]
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS]
    have hL1 : τ1.gates g = Hw.absGate σ1 g := by rw [← habs1]; rfl
    rw [hL1]
    unfold Hw.absGate
    rw [hp (Hw.gcallee g) 2 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gentry g) 12 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gactV g) 1 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gcaller g) 2 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gcallerRd g) 3 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gspc g) 12 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gssrvV g) 1 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gssrv g) 2 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gdepth g) 3 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gdon g) 32 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel) (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel)]
    have hsreg : ∀ r : RegId, ((Hw.core m).cycle σ).regs (Hw.gsreg g r) 32
        = σ1.regs (Hw.gsreg g r) 32 := fun r =>
      hp (Hw.gsreg g r) 32 (by fin_cases g <;> fin_cases r <;> decide +kernel)
        (by fin_cases g <;> fin_cases r <;> decide +kernel)
        (by fin_cases g <;> fin_cases r <;> decide +kernel)
        (by fin_cases g <;> fin_cases r <;> decide +kernel)
    simp only [hsreg]
  · -- mover
    show Hw.absMover ((Hw.core m).cycle σ)
      = (moverPhase (corePhase m τ1)).mover
    rw [core_cycle_unfold]
    have htick : ∀ (rn : String) (w : Nat), ¬(rn = "cycle" ∧ w = 32) →
        (Hw.tickAct.run σ (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))).regs
          rn w = (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)).regs rn w := by
      intro rn w h4
      exact frame (by
        intro hmem
        simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
          Prod.mk.injEq] at hmem
        exact h4 hmem) σ _
    rw [show Hw.absMover (Hw.tickAct.run σ
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)))
        = Hw.absMover (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)) from by
      unfold Hw.absMover
      rw [htick "mov_v" 1 (by decide), htick "mov_owner" 2 (by decide),
        htick "mov_src" 14 (by decide), htick "mov_dst" 14 (by decide),
        htick "mov_srccur" 12 (by decide), htick "mov_dstcur" 12 (by decide),
        htick "mov_rem" 13 (by decide), htick "mov_status" 12 (by decide)]]
    exact absMover_moverAct_quiescent σ _ (corePhase m τ1) (Inert.of_nonretiring σ hnr) hcaps hgen hjob
  · -- inflight
    have hRHS : (moverPhase (corePhase m τ1)).inflight
        = some { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
                 word := σ.regs "if_word" 32
                 cyclesLeft := (σ.regs "if_cl" 8).toNat - 1 } := by
      rw [moverPhase_inflight, hτ2]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    have hifv4 : ((Hw.core m).cycle σ).regs "if_v" 1 = σ.regs "if_v" 1 := by
      rw [hp "if_v" 1 (by decide +kernel) (by decide +kernel) (by decide)
        (by decide), hσ1, refill_pres m σ (by decide)]
    have hifd4 : ((Hw.core m).cycle σ).regs "if_dom" 2
        = σ.regs "if_dom" 2 := by
      rw [hp "if_dom" 2 (by decide +kernel) (by decide +kernel) (by decide)
        (by decide), hσ1, refill_pres m σ (by decide)]
    have hifw4 : ((Hw.core m).cycle σ).regs "if_word" 32
        = σ.regs "if_word" 32 := by
      rw [hp "if_word" 32 (by decide +kernel) (by decide +kernel) (by decide)
        (by decide), hσ1, refill_pres m σ (by decide)]
    have hifcl4 : ((Hw.core m).cycle σ).regs "if_cl" 8
        = σ.regs "if_cl" 8 - 1 := by
      rw [core_cycle_unfold]
      rw [frame (show ("if_cl", 8) ∉ Hw.tickAct.regWrites from by decide)]
      rw [run_WritesPrefixed (by decide +kernel) 8 _ mover_prefixed]
      exact countdown_ifcl m σ σ1 hifv hcl2
    rw [hifv4, hifd4, hifw4, hifcl4]
    rw [if_pos (show σ.regs "if_v" 1 = 1 from hifv)]
    rw [toNat_sub_one_bv8 _ (by omega)]

end Machines.Lnp64u.Theorems.RMC
