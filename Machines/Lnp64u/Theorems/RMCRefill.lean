-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCFrames
import Machines.Lnp64u.Theorems.RMCEnc
import Machines.Lnp64u.Logic.PhaseLemmas

/-!
# R-MC support: the refill bridge

`abs_refill`: decoding the refill rule's output is exactly the spec's
`refillPhase` — fieldwise. The only registers the rule writes are the four
`d*_budget` (guarded by the period-boundary test) and the four hidden
`d*_rctr` counters (invisible to `abs`), so every other field is a frame
fact over the rule's literal write list. The budget arm is where the
hidden-counter coupling pays off: the circuit's boundary test
`rctr = 0` *is* the spec's `cycle % P = 0` through `Coupled.rctr_sync`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- The refill rule's literal write list (order: per domain, budget then
counter). `Act.regWrites` ignores expressions, so this is definitional
even with a symbolic manifest. -/
theorem refillAct_regWrites (m : Manifest) :
    (Hw.refillAct m).regWrites =
      [("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32), ("d1_rctr", 32),
       ("d2_budget", 32), ("d2_rctr", 32), ("d3_budget", 32), ("d3_rctr", 32)] :=
  rfl

/-- Frame fact for every register the refill rule does not write. -/
theorem refill_pres (m : Manifest) (σ : Loom.Hw.St) {rn : String} {w : Nat}
    (h : (rn, w) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32), ("d1_rctr", 32),
        ("d2_budget", 32), ("d2_rctr", 32), ("d3_budget", 32), ("d3_rctr", 32)] :
        List (String × Nat))) :
    ((Hw.refillAct m).run σ σ).regs rn w = σ.regs rn w :=
  frame (by rw [refillAct_regWrites]; exact h) σ σ

/-- The refill rule never writes memory. -/
theorem refillAct_memWrites (m : Manifest) :
    (Hw.refillAct m).memWrites = [] := rfl

theorem refill_pres_mem (m : Manifest) (σ : Loom.Hw.St) (mn : String)
    (a w : Nat) :
    ((Hw.refillAct m).run σ σ).mems mn a w = σ.mems mn a w :=
  Loom.Hw.Compile.run_mems_notin mn (Hw.refillAct m)
    (by rw [refillAct_memWrites]; simp) σ σ a w

/-- The budget register after refill: quota at a period boundary
(`rctr = 0`), unchanged otherwise. Mirror of `refillAct_run_drctr`. -/
theorem refillAct_run_dbudget (m : Manifest) (σ acc : Loom.Hw.St) (d : DomainId) :
    ((Hw.refillAct m).run σ acc).regs (Hw.dbudget d) 32 =
      if σ.regs (Hw.drctr d) 32 = 0#32
      then BitVec.ofNat 32 (m.doms d).budgetQ
      else acc.regs (Hw.dbudget d) 32 := by
  fin_cases d <;>
    simp +decide [Hw.refillAct, finRange_dom, Hw.seqAll, Act.run, Expr.eval,
      Hw.refillCondE, RegEnv.set, Hw.drctr, Hw.dbudget, numDomains]

/-! ## Missing `refillPhase` field lemmas (regs/pc/cause/maxDonation/budget) -/

private theorem refillPhase_dregs (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).regs = (σ.doms d).regs := by
  unfold refillPhase; dsimp only; split <;> rfl

private theorem refillPhase_dpc (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).pc = (σ.doms d).pc := by
  unfold refillPhase; dsimp only; split <;> rfl

private theorem refillPhase_dcause (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).cause = (σ.doms d).cause := by
  unfold refillPhase; dsimp only; split <;> rfl

private theorem refillPhase_dmaxdon (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).maxDonation = (σ.doms d).maxDonation := by
  unfold refillPhase; dsimp only; split <;> rfl

theorem refillPhase_dbudget (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).budget =
      if σ.cycle.toNat % (m.doms d).periodP = 0 then (m.doms d).budgetQ
      else (σ.doms d).budget := by
  unfold refillPhase; dsimp only
  split <;> simp_all

/-! ## The fieldwise bridge -/

theorem domainState_ext' {a b : DomainState}
    (h1 : a.regs = b.regs) (h2 : a.pc = b.pc) (h3 : a.caps = b.caps)
    (h4 : a.slotGen = b.slotGen) (h5 : a.lineage = b.lineage)
    (h6 : a.regions = b.regions) (h7 : a.run = b.run)
    (h8 : a.serving = b.serving) (h9 : a.cause = b.cause)
    (h10 : a.budget = b.budget) (h11 : a.maxDonation = b.maxDonation) :
    a = b := by
  cases a; cases b; simp_all

theorem machineState_ext' {a b : MachineState}
    (h1 : a.cycle = b.cycle) (h2 : a.mem = b.mem) (h3 : a.doms = b.doms)
    (h4 : a.gates = b.gates) (h5 : a.mover = b.mover)
    (h6 : a.inflight = b.inflight) : a = b := by
  cases a; cases b; simp_all

/-- **The refill bridge.** Decoding the refill rule's output is the spec's
refill phase. The boundary test bridges through `Coupled.rctr_sync`; the
quota literal decodes exactly under the datapath fit. -/
theorem abs_refill (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId,
      (σ.regs (Hw.drctr d) 32).toNat =
        (σ.regs "cycle" 32).toNat % (m.doms d).periodP) :
    Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) := by
  apply machineState_ext'
  · -- cycle
    show ((Hw.refillAct m).run σ σ).regs "cycle" 32 = _
    rw [refill_pres m σ (by decide)]
    rfl
  · -- mem
    funext a
    show ((Hw.refillAct m).run σ σ).mems "mem" a.toNat 32 = _
    rw [refill_pres_mem m σ "mem" a.toNat 32]
    rfl
  · -- doms
    funext d
    apply domainState_ext'
    · rw [refillPhase_dregs]
      funext r
      exact refill_pres m σ (by fin_cases d <;> fin_cases r <;> decide)
    · rw [refillPhase_dpc]
      exact refill_pres m σ (by fin_cases d <;> decide)
    · show _ = ((refillPhase m (Hw.abs σ)).doms d).caps
      rw [refillPhase_caps]
      funext s
      show (if ((Hw.refillAct m).run σ σ).regs (Hw.dcapV d s) 1 = 1 then _ else _) = _
      rw [refill_pres m σ (show (Hw.dcapV d s, 1) ∉ _ by fin_cases d <;> fin_cases s <;> decide),
        refill_pres m σ (show (Hw.dcapKind d s, 32) ∉ _ by fin_cases d <;> fin_cases s <;> decide),
        refill_pres m σ (show (Hw.dcapLinV d s, 1) ∉ _ by fin_cases d <;> fin_cases s <;> decide),
        refill_pres m σ (show (Hw.dcapLin d s, 4) ∉ _ by fin_cases d <;> fin_cases s <;> decide)]
      rfl
    · show _ = ((refillPhase m (Hw.abs σ)).doms d).slotGen
      rw [refillPhase_slotGen]
      funext s
      show ((Hw.refillAct m).run σ σ).regs (Hw.dgen d s) 8 = _
      rw [refill_pres m σ (by fin_cases d <;> fin_cases s <;> decide)]
      rfl
    · show _ = ((refillPhase m (Hw.abs σ)).doms d).lineage
      rw [refillPhase_lineage]
      funext l
      show (if ((Hw.refillAct m).run σ σ).regs (Hw.dcellV d l) 1 = 1 then _ else _) = _
      rw [refill_pres m σ (show (Hw.dcellV d l, 1) ∉ _ by fin_cases d <;> fin_cases l <;> decide),
        refill_pres m σ (show (Hw.dcellPar d l, 14) ∉ _ by fin_cases d <;> fin_cases l <;> decide)]
      rfl
    · show _ = ((refillPhase m (Hw.abs σ)).doms d).regions
      rw [refillPhase_regions]
      funext r
      show (if ((Hw.refillAct m).run σ σ).regs (Hw.drgnV d r) 1 = 1 then _ else _) = _
      rw [refill_pres m σ (show (Hw.drgnV d r, 1) ∉ _ by fin_cases d <;> fin_cases r <;> decide),
        refill_pres m σ (show (Hw.drgn d r, 42) ∉ _ by fin_cases d <;> fin_cases r <;> decide)]
      rfl
    · show _ = ((refillPhase m (Hw.abs σ)).doms d).run
      rw [refillPhase_run]
      show Hw.decRun (((Hw.refillAct m).run σ σ).regs (Hw.drun d) 2)
          (((Hw.refillAct m).run σ σ).regs (Hw.drunG d) 2) = _
      rw [refill_pres m σ (show (Hw.drun d, 2) ∉ _ by fin_cases d <;> decide),
        refill_pres m σ (show (Hw.drunG d, 2) ∉ _ by fin_cases d <;> decide)]
      rfl
    · show _ = ((refillPhase m (Hw.abs σ)).doms d).serving
      rw [refillPhase_serving]
      show (if ((Hw.refillAct m).run σ σ).regs (Hw.dsrvV d) 1 = 1 then _ else _) = _
      rw [refill_pres m σ (show (Hw.dsrvV d, 1) ∉ _ by fin_cases d <;> decide),
        refill_pres m σ (show (Hw.dsrv d, 2) ∉ _ by fin_cases d <;> decide)]
      rfl
    · rw [refillPhase_dcause]
      exact refill_pres m σ (by fin_cases d <;> decide)
    · -- budget: the interesting arm
      rw [refillPhase_dbudget]
      show (((Hw.refillAct m).run σ σ).regs (Hw.dbudget d) 32).toNat = _
      rw [refillAct_run_dbudget]
      have hQ : (m.doms d).budgetQ < 2 ^ 32 :=
        Nat.lt_of_le_of_lt (hwf.budget_le d) (hfit.period_lt d)
      have hzero : (σ.regs (Hw.drctr d) 32 = 0#32) ↔
          ((Hw.abs σ).cycle.toNat % (m.doms d).periodP = 0) := by
        constructor
        · intro h
          have := hsync d
          rw [h] at this
          simpa [Hw.abs] using this.symm
        · intro h
          apply BitVec.eq_of_toNat_eq
          rw [hsync d]
          simpa [Hw.abs] using h
      by_cases hb : (σ.regs (Hw.drctr d) 32) = 0#32
      · rw [if_pos hb, if_pos (hzero.mp hb)]
        simp only [BitVec.toNat_ofNat]
        omega
      · rw [if_neg hb, if_neg (fun hc => hb (hzero.mpr hc))]
        rfl
    · rw [refillPhase_dmaxdon]
      show (((Hw.refillAct m).run σ σ).regs (Hw.dmaxdon d) 32).toNat = _
      rw [refill_pres m σ (by fin_cases d <;> decide)]
      rfl
  · -- gates
    funext g
    show Hw.absGate _ g = _
    have : (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates := refillPhase_gates m _
    rw [this]
    unfold Hw.absGate
    rw [refill_pres m σ (show (Hw.gcallee g, 2) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gentry g, 12) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gactV g, 1) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gcaller g, 2) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gcallerRd g, 3) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gspc g, 12) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gssrvV g, 1) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gssrv g, 2) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gdepth g, 3) ∉ _ by fin_cases g <;> decide),
      refill_pres m σ (show (Hw.gdon g, 32) ∉ _ by fin_cases g <;> decide)]
    have hsreg : ∀ r : RegId,
        ((Hw.refillAct m).run σ σ).regs (Hw.gsreg g r) 32 =
          σ.regs (Hw.gsreg g r) 32 := fun r =>
      refill_pres m σ (by fin_cases g <;> fin_cases r <;> decide)
    simp only [hsreg]
    rfl
  · -- mover
    show Hw.absMover _ = _
    have : (refillPhase m (Hw.abs σ)).mover = (Hw.abs σ).mover := refillPhase_mover m _
    rw [this]
    unfold Hw.absMover
    rw [refill_pres m σ (show ("mov_v", 1) ∉ _ by decide),
      refill_pres m σ (show ("mov_owner", 2) ∉ _ by decide),
      refill_pres m σ (show ("mov_src", 14) ∉ _ by decide),
      refill_pres m σ (show ("mov_dst", 14) ∉ _ by decide),
      refill_pres m σ (show ("mov_srccur", 12) ∉ _ by decide),
      refill_pres m σ (show ("mov_dstcur", 12) ∉ _ by decide),
      refill_pres m σ (show ("mov_rem", 13) ∉ _ by decide),
      refill_pres m σ (show ("mov_status", 12) ∉ _ by decide)]
    rfl
  · -- inflight
    show Hw.absInflight _ = _
    have : (refillPhase m (Hw.abs σ)).inflight = (Hw.abs σ).inflight := rfl
    rw [this]
    unfold Hw.absInflight
    rw [refill_pres m σ (show ("if_v", 1) ∉ _ by decide),
      refill_pres m σ (show ("if_dom", 2) ∉ _ by decide),
      refill_pres m σ (show ("if_word", 32) ∉ _ by decide),
      refill_pres m σ (show ("if_cl", 8) ∉ _ by decide)]
    rfl

end Machines.Lnp64u.Theorems.RMC
