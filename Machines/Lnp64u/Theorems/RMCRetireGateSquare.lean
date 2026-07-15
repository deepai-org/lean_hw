-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireDup

/-!
# R-MC retirement: structural gate-operation cycle assembly

Shared final-cycle assembly for gate operations whose core payload can kill a
Mover endpoint.  Call and return supply their operation-specific Mover and
status-memory bridges; tick, core framing, domains, gates, and inflight are
assembled once here.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- Assemble a retiring structural payload once its core abstraction and
post-Mover faces have been established.  Unlike `square_retire_install`, this
lemma does not assume the operation is inert: callers provide the exact Mover
and memory results for their kill footprint. -/
theorem square_retire_gate_payload (m : Manifest) (σ : Loom.Hw.St)
    (X : Act) (τ2 : MachineState)
    (hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w)
    (hXifv : ("if_v", 1) ∉ X.regWrites)
    (hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2)
    (habsD : ∀ x, Hw.absDom
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) x = τ2.doms x)
    (habsG : ∀ g, Hw.absGate
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) g = τ2.gates g)
    (hmover : Hw.absMover
      (Hw.moverAct.run σ
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))) =
      (moverPhase τ2).mover)
    (hmem : ∀ a : Addr,
      (Hw.moverAct.run σ
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))).mems "mem"
          a.toNat 32 = (moverPhase τ2).mem a)
    (hcyc : τ2.cycle = σ.regs "cycle" 32)
    (hτ2if : τ2.inflight = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  have hp : ∀ (rn : String) (w : Nat),
      rn.startsWith "mov_" = false → ¬(rn = "cycle" ∧ w = 32) →
      ((Hw.core m).cycle σ).regs rn w =
        ((Hw.coreAct m).run σ σ1).regs rn w := by
    intro rn w hmov hcycle
    rw [core_cycle_unfold]
    rw [frame (show (rn, w) ∉ Hw.tickAct.regWrites from by
      intro hmem'
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem'
      exact hcycle hmem')]
    rw [run_WritesPrefixed hmov w _ mover_prefixed]
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hspec, hcyc]
  · funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    rw [show (moverPhase (corePhase m τ1)).mem = (moverPhase τ2).mem from by
      rw [hspec]]
    exact hmem a
  · funext x
    have hRHS : (moverPhase (corePhase m τ1)).doms x = τ2.doms x := by
      rw [moverPhase_doms, hspec]
    show Hw.absDom ((Hw.core m).cycle σ) x = _
    rw [hRHS, ← habsD x]
    have hmovfree : ∀ q ∈ domReadNames x,
        q.1.startsWith "mov_" = false := by
      fin_cases x <;> decide +kernel
    have hcycfree : ∀ q ∈ domReadNames x,
        ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases x <;> exact of_decide_eq_true rfl
    apply absDom_congr
    intro p hp'
    rw [← hcoreR p.1 p.2]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g = τ2.gates g := by
      rw [moverPhase_gates, hspec]
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS, ← habsG g]
    have hmovfree : ∀ q ∈ gateReadNames g,
        q.1.startsWith "mov_" = false := by
      fin_cases g <;> decide +kernel
    have hcycfree : ∀ q ∈ gateReadNames g,
        ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases g <;> exact of_decide_eq_true rfl
    apply absGate_congr
    intro p hp'
    rw [← hcoreR p.1 p.2]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · show Hw.absMover ((Hw.core m).cycle σ) =
      (moverPhase (corePhase m τ1)).mover
    rw [core_cycle_unfold]
    have htick : ∀ (rn : String) (w : Nat), ¬(rn = "cycle" ∧ w = 32) →
        (Hw.tickAct.run σ
          (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))).regs rn w =
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)).regs rn w := by
      intro rn w hcycle
      exact frame (by
        intro hmem'
        simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
          Prod.mk.injEq] at hmem'
        exact hcycle hmem') σ _
    rw [show Hw.absMover (Hw.tickAct.run σ
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))) =
        Hw.absMover (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)) from by
      unfold Hw.absMover
      rw [htick "mov_v" 1 (by decide), htick "mov_owner" 2 (by decide),
        htick "mov_src" 14 (by decide), htick "mov_dst" 14 (by decide),
        htick "mov_srccur" 12 (by decide), htick "mov_dstcur" 12 (by decide),
        htick "mov_rem" 13 (by decide), htick "mov_status" 12 (by decide)]]
    rw [show (moverPhase (corePhase m τ1)).mover = (moverPhase τ2).mover
      from by rw [hspec]]
    exact hmover
  · have hRHS : (moverPhase (corePhase m τ1)).inflight = none := by
      rw [moverPhase_inflight, hspec, hτ2if]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    rw [hp "if_v" 1 (by decide +kernel) (by decide), hcoreR "if_v" 1]
    rw [show ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ σ1).regs
        "if_v" 1 = ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs
          "if_v" 1 from frame hXifv σ _]
    rw [show ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs "if_v" 1 =
        0#1 from by simp [Act.run, RegEnv.set, Expr.eval]]
    rw [if_neg (by decide)]

end Machines.Lnp64u.Theorems.RMC
