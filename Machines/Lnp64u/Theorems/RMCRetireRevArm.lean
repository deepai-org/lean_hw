-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRevState
import Machines.Lnp64u.Theorems.RMCRetireGateCallSuccess

/-!
# R-MC retirement: full cap_revoke arm

This module assembles the converged revoke engine, structural destruction,
region sweep, and Mover bridges into the retiring instruction square.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

private theorem ifv_notin_revSuccessA (E : DomainId) :
    (("if_v" : String), (1 : Nat)) ∉ (revSuccessArmA E).regWrites := by
  fin_cases E <;> decide +kernel

/-- The successful circuit payload, run after refill and latch clear,
decodes to the complete named abstract revoke state on every domain. -/
theorem absDom_revSuccessA_refill (m : Manifest) (hwfm : m.WF)
    (hfit : Fits m) (sigma : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (sigma.regs (Hw.drctr d) 32).toNat =
      (sigma.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrv : RvSync sigma)
    (hifv : sigma.regs "if_v" 1 = 1#1)
    (hopc : (sigma.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (sigma.regs "if_cl" 8).toNat < 2)
    (hwf : Wf (Hw.abs sigma)) (E : DomainId) (RD : RegId)
    (hrd : (Hw.rdE.eval sigma).toNat = RD.val) (c : DomainId) :
    Hw.absDom
        ((Act.seq (.write 1 "if_v" (.lit 0)) (revSuccessArmA E)).run
          sigma ((Hw.refillAct m).run sigma sigma)) c =
      (revAbstractSuccess m (Hw.abs sigma) E RD (rvRoot sigma)).doms c := by
  let acc := (Act.write 1 "if_v" (.lit 0)).run sigma
    ((Hw.refillAct m).run sigma sigma)
  have habsAcc : Hw.abs acc =
      { refillPhase m (Hw.abs sigma) with inflight := none } :=
    abs_refill_clearInflight m hwfm hfit sigma hsync
  have hacc {rn : String} {w : Nat}
      (hif : (rn, w) ≠ ("if_v", 1))
      (hrefill : (rn, w) ∉
        ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
          ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
          ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) :
      acc.regs rn w = sigma.regs rn w := by
    rw [show acc.regs rn w =
        ((Hw.refillAct m).run sigma sigma).regs rn w from
      frame (by simpa [Act.regWrites] using hif) sigma
        ((Hw.refillAct m).run sigma sigma)]
    exact refill_pres m sigma hrefill
  have haccV : ∀ d s, acc.regs (Hw.dcapV d s) 1 =
      sigma.regs (Hw.dcapV d s) 1 := by
    intro d s
    exact hacc (by fin_cases d <;> fin_cases s <;> decide)
      (by fin_cases d <;> fin_cases s <;> decide)
  have haccG : ∀ d s, acc.regs (Hw.dgen d s) 8 =
      sigma.regs (Hw.dgen d s) 8 := by
    intro d s
    exact hacc (by fin_cases d <;> fin_cases s <;> decide)
      (by fin_cases d <;> fin_cases s <;> decide)
  have hcaps : ∀ d, ((Hw.abs acc).doms d).caps =
      ((Hw.abs sigma).doms d).caps := by
    intro d
    rw [habsAcc]
    exact refillPhase_caps m (Hw.abs sigma) d
  have hrgnV : ∀ d r, acc.regs (Hw.drgnV d r) 1 =
      sigma.regs (Hw.drgnV d r) 1 := by
    intro d r
    exact hacc (by fin_cases d <;> fin_cases r <;> decide)
      (by fin_cases d <;> fin_cases r <;> decide)
  have hrgn : ∀ d r, acc.regs (Hw.drgn d r) 42 =
      sigma.regs (Hw.drgn d r) 42 := by
    intro d r
    exact hacc (by fin_cases d <;> fin_cases r <;> decide)
      (by fin_cases d <;> fin_cases r <;> decide)
  have hpc : ∀ d, acc.regs (Hw.dpc d) 12 =
      sigma.regs (Hw.dpc d) 12 := by
    intro d
    exact hacc (by fin_cases d <;> decide) (by fin_cases d <;> decide)
  have hwfAcc : Wf (Hw.abs acc) := by
    rw [habsAcc]
    apply wf_of_skeleton_sameGates (refillPhase m (Hw.abs sigma))
      { refillPhase m (Hw.abs sigma) with inflight := none }
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) rfl rfl (by simp)
    exact refillPhase_preserves_wf m (Hw.abs sigma) hwf
  have hdom := absDom_revSuccessA sigma acc hrv hifv hopc hcl
    haccV haccG hcaps hrgnV hrgn hpc hwfAcc E RD hrd c
  change Hw.absDom ((revSuccessArmA E).run sigma acc) c = _
  unfold revSuccessArmA
  rw [hdom]
  rw [habsAcc]
  unfold revAbstractSuccess revRetireBase
  rw [destroyMarked_setPc, sweepRegions_setPc, sweepMover_setPc]
  by_cases hc : c = E
  · subst c
    simp [MachineState.setDom]
  · simp [MachineState.setDom, hc]

end Machines.Lnp64u.Theorems.RMC
