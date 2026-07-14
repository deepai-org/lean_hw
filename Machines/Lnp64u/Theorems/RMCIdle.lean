-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCSched
import Machines.Lnp64u.Theorems.RMCCountdown

/-!
# R-MC support: the idle-stall arm of the square

Core idle (`if_v = 0`) and nothing schedulable: the core rule falls
through the issue fold to `skip`, and the spec's core phase returns its
input. The cycle is refill + Mover + tick only — all bridged.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-- No retirement with an empty in-flight latch. -/
theorem retiringE_eval_idle (σ : Loom.Hw.St)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1) :
    Hw.retiringE.eval σ = 0#1 := by
  show σ.regs "if_v" 1 &&&
    (if (σ.regs "if_cl" 8).ult (2#8) = true then 1#1 else 0#1) = 0#1
  rw [bv1_ne_one.mp hifv0]
  generalize (if (σ.regs "if_cl" 8).ult (2#8) = true
    then (1:BitVec 1) else 0) = b
  revert b; decide

/-- **The idle-stall arm of the square**: idle core, nothing eligible. -/
theorem square_idle_stall (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1)
    (hsched : schedule m (refillPhase m (Hw.abs σ)) = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hnr := retiringE_eval_idle σ hifv0
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  -- circuit: no eligible domain, so the core rule is a no-op
  have hnone : ∀ d : DomainId, (Hw.eligE m d).eval σ ≠ 1#1 := by
    intro d hd
    exact ((schedule_none_iff m τ1).mp hsched) d
      ((eligE_eval m hwf hfit σ hsync hrc d).mp hd)
  have hcore : (Hw.coreAct m).run σ σ1 = σ1 :=
    coreAct_run_idle_none m σ σ1 hifv0 hnone
  -- spec: empty in-flight latch, nothing scheduled — core phase is identity
  have hifl : τ1.inflight = none := by
    show Hw.absInflight σ = none
    rw [Hw.absInflight, if_neg (show ¬(σ.regs "if_v" 1 = 1) from hifv0)]
  have hτ2 : corePhase m τ1 = τ1 := by
    unfold corePhase
    rw [hifl]
    show (match schedule m τ1 with
      | none => τ1
      | some d => _) = τ1
    rw [hsched]
  -- bridge hypotheses
  have hcaps : ∀ d, ((corePhase m τ1).doms d).caps
      = ((Hw.abs σ).doms d).caps := by
    intro d
    rw [hτ2, hτ1, refillPhase_caps]
  have hgen : ∀ d, ((corePhase m τ1).doms d).slotGen
      = ((Hw.abs σ).doms d).slotGen := by
    intro d
    rw [hτ2, hτ1, refillPhase_slotGen]
  have hrgn : ∀ d, ((corePhase m τ1).doms d).regions
      = ((Hw.abs σ).doms d).regions := by
    intro d
    rw [hτ2, hτ1, refillPhase_regions]
  have hjob : (corePhase m τ1).mover = Hw.absMover σ := by
    rw [hτ2, hτ1, refillPhase_mover]
    rfl
  have hmem2 : ∀ ad, ((Hw.coreAct m).run σ σ1).mems "mem" ad 32
      = σ.mems "mem" ad 32 := by
    intro ad
    rw [hcore, hσ1]
    exact Loom.Hw.Compile.run_mems_notin "mem" _
      (by rw [refillAct_memWrites]; simp) σ σ ad 32
  have hτm : ∀ b : Addr, (corePhase m τ1).mem b
      = σ.mems "mem" b.toNat 32 := by
    intro b
    rw [hτ2, hτ1]
    rfl
  -- register preservation down to the post-refill accumulator
  have hp : ∀ (rn : String) (w : Nat),
      rn.startsWith "mov_" = false → ¬(rn = "cycle" ∧ w = 32) →
      ((Hw.core m).cycle σ).regs rn w = σ1.regs rn w := by
    intro rn w h2 h4
    rw [core_cycle_unfold]
    rw [frame (show (rn, w) ∉ Hw.tickAct.regWrites from by
      intro hmem
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem
      exact h4 hmem)]
    rw [run_WritesPrefixed h2 w _ mover_prefixed]
    rw [hcore]
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hτ2]
    rfl
  · funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    exact moverAct_mem_quiescent σ _ (corePhase m τ1) (Inert.of_nonretiring σ hnr) hcaps hgen hrgn
      hjob (fun d sc => andAll_retiring_quiescent σ hnr _)
      (fun c r => andAll_retiring_quiescent σ hnr _)
      (fun c r => andAll_retiring_quiescent σ hnr _) hmem2 hτm a
  · funext d
    have hRHS : (moverPhase (corePhase m τ1)).doms d = τ1.doms d := by
      rw [moverPhase_doms, hτ2]
    show Hw.absDom ((Hw.core m).cycle σ) d = _
    rw [hRHS]
    have hL1 : τ1.doms d = Hw.absDom σ1 d := by
      rw [← habs1]; rfl
    rw [hL1]
    apply domainState_ext'
    · funext r
      exact hp (Hw.dreg d r) 32
        (by fin_cases d <;> fin_cases r <;> decide +kernel)
        (by fin_cases d <;> fin_cases r <;> decide +kernel)
    · exact hp (Hw.dpc d) 12 (by fin_cases d <;> decide +kernel)
        (by fin_cases d <;> decide +kernel)
    · funext s
      show (if ((Hw.core m).cycle σ).regs (Hw.dcapV d s) 1 = 1 then _ else _)
        = _
      rw [hp (Hw.dcapV d s) 1
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel),
        hp (Hw.dcapKind d s) 32
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel),
        hp (Hw.dcapLinV d s) 1
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel),
        hp (Hw.dcapLin d s) 4
          (by fin_cases d <;> fin_cases s <;> decide +kernel)
          (by fin_cases d <;> fin_cases s <;> decide +kernel)]
      rfl
    · funext s
      exact hp (Hw.dgen d s) 8
        (by fin_cases d <;> fin_cases s <;> decide +kernel)
        (by fin_cases d <;> fin_cases s <;> decide +kernel)
    · funext l
      show (if ((Hw.core m).cycle σ).regs (Hw.dcellV d l) 1 = 1 then _ else _)
        = _
      rw [hp (Hw.dcellV d l) 1
          (by fin_cases d <;> fin_cases l <;> decide +kernel)
          (by fin_cases d <;> fin_cases l <;> decide +kernel),
        hp (Hw.dcellPar d l) 14
          (by fin_cases d <;> fin_cases l <;> decide +kernel)
          (by fin_cases d <;> fin_cases l <;> decide +kernel)]
      rfl
    · funext r
      show (if ((Hw.core m).cycle σ).regs (Hw.drgnV d r) 1 = 1 then _ else _)
        = _
      rw [hp (Hw.drgnV d r) 1
          (by fin_cases d <;> fin_cases r <;> decide +kernel)
          (by fin_cases d <;> fin_cases r <;> decide +kernel),
        hp (Hw.drgn d r) 42
          (by fin_cases d <;> fin_cases r <;> decide +kernel)
          (by fin_cases d <;> fin_cases r <;> decide +kernel)]
      rfl
    · show Hw.decRun _ _ = _
      rw [hp (Hw.drun d) 2 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel),
        hp (Hw.drunG d) 2 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel)]
      rfl
    · show (if ((Hw.core m).cycle σ).regs (Hw.dsrvV d) 1 = 1 then _ else _)
        = _
      rw [hp (Hw.dsrvV d) 1 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel),
        hp (Hw.dsrv d) 2 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel)]
      rfl
    · exact hp (Hw.dcause d) 32 (by fin_cases d <;> decide +kernel)
        (by fin_cases d <;> decide +kernel)
    · show (((Hw.core m).cycle σ).regs (Hw.dbudget d) 32).toNat = _
      rw [hp (Hw.dbudget d) 32 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel)]
      rfl
    · show (((Hw.core m).cycle σ).regs (Hw.dmaxdon d) 32).toNat = _
      rw [hp (Hw.dmaxdon d) 32 (by fin_cases d <;> decide +kernel)
          (by fin_cases d <;> decide +kernel)]
      rfl
  · funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g = τ1.gates g := by
      rw [moverPhase_gates, hτ2]
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS]
    have hL1 : τ1.gates g = Hw.absGate σ1 g := by rw [← habs1]; rfl
    rw [hL1]
    unfold Hw.absGate
    rw [hp (Hw.gcallee g) 2 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gentry g) 12 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gactV g) 1 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gcaller g) 2 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gcallerRd g) 3 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gspc g) 12 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gssrvV g) 1 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gssrv g) 2 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gdepth g) 3 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel),
      hp (Hw.gdon g) 32 (by fin_cases g <;> decide +kernel)
        (by fin_cases g <;> decide +kernel)]
    have hsreg : ∀ r : RegId, ((Hw.core m).cycle σ).regs (Hw.gsreg g r) 32
        = σ1.regs (Hw.gsreg g r) 32 := fun r =>
      hp (Hw.gsreg g r) 32 (by fin_cases g <;> fin_cases r <;> decide +kernel)
        (by fin_cases g <;> fin_cases r <;> decide +kernel)
    simp only [hsreg]
  · show Hw.absMover ((Hw.core m).cycle σ)
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
  · have hRHS : (moverPhase (corePhase m τ1)).inflight = none := by
      rw [moverPhase_inflight, hτ2]
      exact hifl
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    rw [hp "if_v" 1 (by decide +kernel) (by decide), hσ1,
      refill_pres m σ (by decide)]
    rw [if_neg (show ¬(σ.regs "if_v" 1 = 1) from hifv0)]

end Machines.Lnp64u.Theorems.RMC
