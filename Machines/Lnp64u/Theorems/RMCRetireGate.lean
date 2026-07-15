-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGrant
import Machines.Lnp64u.Theorems.RMCRetireDrop

/-!
# R-MC retirement: shared gate-transfer support

Hardware/specification bridges for `transferA`, the capability-move composite
shared by `gate_call` and `gate_return`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 3200000
set_option maxRecDepth 200000

/-! ## Dynamic recipient selection -/

/-- The domain-indexed install fold selects exactly the decoded recipient. -/
theorem transfer_installFold_run (σ acc : Loom.Hw.St) (toE : Expr 2)
    (d : DomainId) (acs : Hw.CapSel) (oldE : Expr 14) :
    (Hw.seqAll ((List.finRange numDomains).map fun c =>
      Act.ite (.eq toE (Hw.dLit c))
        (let ns := Hw.freeSlotIdx c
         let newE := Hw.encRefE (Hw.dLit c) ns (Hw.genOfE c ns)
         Hw.installA c ns acs.kindW acs.linV (Hw.freeCellIdx c)
           (.mux (.eq (Hw.cellParAt d acs.lin) oldE) newE
             (Hw.cellParAt d acs.lin))) .skip)).run σ acc =
      let T : DomainId := finOfBv (by decide) (toE.eval σ)
      let ns := Hw.freeSlotIdx T
      let newE := Hw.encRefE (Hw.dLit T) ns (Hw.genOfE T ns)
      (Hw.installA T ns acs.kindW acs.linV (Hw.freeCellIdx T)
        (.mux (.eq (Hw.cellParAt d acs.lin) oldE) newE
          (Hw.cellParAt d acs.lin))).run σ acc := by
  let T : DomainId := finOfBv (by decide) (toE.eval σ)
  have hsel : (Expr.eq toE (Hw.dLit T)).eval σ = 1#1 := by
    rw [eqE_eval]
    apply BitVec.eq_of_toNat_eq
    change (toE.eval σ).toNat = (BitVec.ofNat 2 T.val).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt T.isLt]
    rfl
  have hexcl : ∀ j : DomainId, j ≠ T →
      (Expr.eq toE (Hw.dLit j)).eval σ ≠ 1#1 := by
    intro j hj hfire
    apply hj
    apply Fin.ext
    rw [eqE_eval] at hfire
    have hnat := congrArg BitVec.toNat hfire
    change (toE.eval σ).toNat = (BitVec.ofNat 2 j.val).toNat at hnat
    symm
    simpa [T, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show j.val < 2 ^ 2 from j.isLt)] using hnat
  exact seqAll_ite_run_unique σ acc
    (fun c : DomainId => Expr.eq toE (Hw.dLit c))
    (fun c : DomainId =>
      let ns := Hw.freeSlotIdx c
      let newE := Hw.encRefE (Hw.dLit c) ns (Hw.genOfE c ns)
      Hw.installA c ns acs.kindW acs.linV (Hw.freeCellIdx c)
        (.mux (.eq (Hw.cellParAt d acs.lin) oldE) newE
          (Hw.cellParAt d acs.lin)))
    T hsel hexcl (List.finRange numDomains) (List.mem_finRange T)
      (List.nodup_finRange _)

/-- `transferA` after selecting its dynamic recipient domain. -/
def transferChosenA (d T : DomainId) (acs : Hw.CapSel) : Act :=
  let oldE := Hw.encRefE (Hw.dLit d) acs.slot acs.gen
  let ns := Hw.freeSlotIdx T
  let newE := Hw.encRefE (Hw.dLit T) ns (Hw.genOfE T ns)
  Hw.seqAll
    [ Hw.installA T ns acs.kindW acs.linV (Hw.freeCellIdx T)
        (.mux (.eq (Hw.cellParAt d acs.lin) oldE) newE
          (Hw.cellParAt d acs.lin)),
      Hw.reparentA oldE newE,
      Hw.clearSlotA d acs.slot acs.linV acs.lin,
      Hw.sweepRegionsA
        (fun dm sl => .and (.eq dm (Hw.dLit d)) (.eq sl acs.slot)) ]

private theorem transferA_run (σ acc : Loom.Hw.St) (d : DomainId)
    (toE : Expr 2) (acs : Hw.CapSel) :
    (Hw.transferA d toE acs).run σ acc =
      let oldE := Hw.encRefE (Hw.dLit d) acs.slot acs.gen
      let newAt := Hw.muxFin (fun c =>
        Hw.encRefE (Hw.dLit c) (Hw.freeSlotIdx c)
          (Hw.genOfE c (Hw.freeSlotIdx c))) toE
      (Hw.sweepRegionsA
        (fun dm sl => .and (.eq dm (Hw.dLit d)) (.eq sl acs.slot))).run σ
        ((Hw.clearSlotA d acs.slot acs.linV acs.lin).run σ
          ((Hw.reparentA oldE newAt).run σ
            ((Hw.seqAll ((List.finRange numDomains).map fun c =>
              Act.ite (.eq toE (Hw.dLit c))
                (let ns := Hw.freeSlotIdx c
                 let newE := Hw.encRefE (Hw.dLit c) ns (Hw.genOfE c ns)
                 Hw.installA c ns acs.kindW acs.linV (Hw.freeCellIdx c)
                   (.mux (.eq (Hw.cellParAt d acs.lin) oldE) newE
                     (Hw.cellParAt d acs.lin))) .skip)).run σ acc))) := by
  rfl

private theorem transferChosenA_run (σ acc : Loom.Hw.St)
    (d T : DomainId) (acs : Hw.CapSel) :
    (transferChosenA d T acs).run σ acc =
      let oldE := Hw.encRefE (Hw.dLit d) acs.slot acs.gen
      let ns := Hw.freeSlotIdx T
      let newE := Hw.encRefE (Hw.dLit T) ns (Hw.genOfE T ns)
      (Hw.sweepRegionsA
        (fun dm sl => .and (.eq dm (Hw.dLit d)) (.eq sl acs.slot))).run σ
        ((Hw.clearSlotA d acs.slot acs.linV acs.lin).run σ
          ((Hw.reparentA oldE newE).run σ
            ((Hw.installA T ns acs.kindW acs.linV (Hw.freeCellIdx T)
              (.mux (.eq (Hw.cellParAt d acs.lin) oldE) newE
                (Hw.cellParAt d acs.lin))).run σ acc))) := by
  rfl

/-- The complete transfer composite reduces to the selected-recipient action. -/
theorem transferA_run_selected (σ acc : Loom.Hw.St) (d : DomainId)
    (toE : Expr 2) (acs : Hw.CapSel) :
    (Hw.transferA d toE acs).run σ acc =
      (transferChosenA d (finOfBv (by decide) (toE.eval σ)) acs).run σ acc := by
  let T : DomainId := finOfBv (by decide) (toE.eval σ)
  rw [transferA_run, transferChosenA_run]
  dsimp only
  have hfold := transfer_installFold_run σ acc toE d acs
    (Hw.encRefE (Hw.dLit d) acs.slot acs.gen)
  rw [hfold]
  congr 1
  rw [muxFin_eval (by decide : 2 ^ 2 = numDomains)]

/-! ## Selected installation abstraction -/

/-- The validity face of a selected transfer installation. -/
private theorem installA_selected_capV (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (s : Slot) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapV c s) 1 =
      if s = NS then 1#1 else acc.regs (Hw.dcapV c s) 1 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1 <;>
    simp only [hl, if_true, if_false, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
  all_goals
    by_cases hs : s = NS
    · subst s
      simp
    · simp [hs]

/-- The kind face of a selected transfer installation. -/
private theorem installA_selected_capKind (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (s : Slot) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapKind c s) 32 =
      if s = NS then kindE.eval σ else acc.regs (Hw.dcapKind c s) 32 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1 <;>
    simp only [hl, if_true, if_false, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
  all_goals
    by_cases hs : s = NS
    · subst s
      simp
    · simp [hs]

/-- The lineage-valid face of a selected transfer installation. -/
private theorem installA_selected_capLinV (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (s : Slot) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapLinV c s) 1 =
      if s = NS then linVE.eval σ else acc.regs (Hw.dcapLinV c s) 1 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1 <;>
    simp only [hl, if_true, if_false, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
  all_goals
    by_cases hs : s = NS
    · subst s
      simp
    · simp [hs]

/-- The lineage-index face of a selected transfer installation. -/
private theorem installA_selected_capLin (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (s : Slot) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapLin c s) 4 =
      if s = NS then nlE.eval σ else acc.regs (Hw.dcapLin c s) 4 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1 <;>
    simp only [hl, if_true, if_false, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
  all_goals
    by_cases hs : s = NS
    · subst s
      simp
    · simp [hs]

/-- The cell-valid face of a selected transfer installation. -/
private theorem installA_selected_cellV (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (l : LineageId) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcellV c l) 1 =
      if linVE.eval σ = 1#1 ∧ l = finOfBv (by decide) (nlE.eval σ) then
        1#1 else acc.regs (Hw.dcellV c l) 1 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1
  · simp only [hl, if_true, true_and, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
    by_cases heq : l = finOfBv (by decide) (nlE.eval σ)
    · subst l
      simp
    · simp [heq]
  · simp [hl]

/-- The cell-parent face of a selected transfer installation. -/
private theorem installA_selected_cellPar (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (l : LineageId) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcellPar c l) 14 =
      if linVE.eval σ = 1#1 ∧ l = finOfBv (by decide) (nlE.eval σ) then
        parE.eval σ else acc.regs (Hw.dcellPar c l) 14 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1
  · simp only [hl, if_true, true_and, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
    by_cases heq : l = finOfBv (by decide) (nlE.eval σ)
    · subst l
      simp
    · simp [heq]
  · simp [hl]

/-- Whole-domain abstraction of a selected transfer installation.  This
covers both root entries (`linVE = 0`) and derived entries (`linVE = 1`). -/
theorem absDom_installA_selected (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind) :
    Hw.absDom ((Hw.installA c nsE kindE linVE nlE parE).run σ acc) c =
      let NL : LineageId := finOfBv (by decide) (nlE.eval σ)
      { Hw.absDom acc c with
        caps := Loom.Fun.update (Hw.absDom acc c).caps NS
          (some { kind := kind
                  lineage := if linVE.eval σ = 1#1 then some NL else none })
        lineage := if linVE.eval σ = 1#1 then
          Loom.Fun.update (Hw.absDom acc c).lineage NL
            (some { parent := Hw.decRef (parE.eval σ) })
        else (Hw.absDom acc c).lineage } := by
  dsimp only
  apply domainState_ext'
  · funext r
    exact frame (show ((Hw.dreg c r : String), (32 : Nat)) ∉
      (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
        fin_cases c <;> fin_cases r <;> decide +kernel) σ acc
  · exact frame (show ((Hw.dpc c : String), (12 : Nat)) ∉
      (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
        fin_cases c <;> decide +kernel) σ acc
  · funext s
    change (if ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapV c s) 1 = 1#1 then
      some ({
        kind := Hw.decKind (((Hw.installA c nsE kindE linVE nlE parE).run
          σ acc).regs (Hw.dcapKind c s) 32)
        lineage := if ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
            (Hw.dcapLinV c s) 1 = 1#1 then
          some (finOfBv (by decide)
            (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
              (Hw.dcapLin c s) 4)) else none } : CapEntry)
      else none) = _
    rw [installA_selected_capV σ acc c nsE kindE linVE nlE parE NS hns s,
      installA_selected_capKind σ acc c nsE kindE linVE nlE parE NS hns s,
      installA_selected_capLinV σ acc c nsE kindE linVE nlE parE NS hns s,
      installA_selected_capLin σ acc c nsE kindE linVE nlE parE NS hns s]
    by_cases hs : s = NS
    · subst s
      rw [if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl,
        Loom.Fun.update_same, hkind, Hw.decKind_encKind]
    · rw [if_neg hs, if_neg hs, if_neg hs, if_neg hs,
        Loom.Fun.update_ne _ _ _ _ hs]
      rfl
  · rfl
  · funext l
    change (if ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcellV c l) 1 = 1#1 then
      some ({ parent := Hw.decRef
        (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
          (Hw.dcellPar c l) 14) } : LineageCell) else none) = _
    rw [installA_selected_cellV σ acc c nsE kindE linVE nlE parE NS hns l,
      installA_selected_cellPar σ acc c nsE kindE linVE nlE parE NS hns l]
    by_cases hl : linVE.eval σ = 1#1
    · rw [if_pos hl]
      by_cases heq : l = finOfBv (by decide) (nlE.eval σ)
      · subst l
        simp
      · simp [heq]
    · simp [hl]
  · funext r
    change (if ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (((Hw.installA c nsE kindE linVE nlE parE).run
        σ acc).regs (Hw.drgn c r) 42)) else none) = _
    rw [frame (show ((Hw.drgnV c r : String), (1 : Nat)) ∉
        (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
          fin_cases c <;> fin_cases r <;> decide +kernel) σ acc,
      frame (show ((Hw.drgn c r : String), (42 : Nat)) ∉
        (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
          fin_cases c <;> fin_cases r <;> decide +kernel) σ acc]
  · change Hw.decRun
      (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.drun c) 2)
      (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.drunG c) 2) = _
    rw [frame (show ((Hw.drun c : String), (2 : Nat)) ∉
        (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
          fin_cases c <;> decide +kernel) σ acc,
      frame (show ((Hw.drunG c : String), (2 : Nat)) ∉
        (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
          fin_cases c <;> decide +kernel) σ acc]
  · change (if ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dsrvV c) 1 = 1#1 then
      some (finOfBv (by decide)
        (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
          (Hw.dsrv c) 2)) else none) = _
    rw [frame (show ((Hw.dsrvV c : String), (1 : Nat)) ∉
        (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
          fin_cases c <;> decide +kernel) σ acc,
      frame (show ((Hw.dsrv c : String), (2 : Nat)) ∉
        (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
          fin_cases c <;> decide +kernel) σ acc]
  · exact frame (show ((Hw.dcause c : String), (32 : Nat)) ∉
      (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
        fin_cases c <;> decide +kernel) σ acc
  · change (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
      (Hw.dbudget c) 32).toNat = _
    rw [frame (show ((Hw.dbudget c : String), (32 : Nat)) ∉
      (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
        fin_cases c <;> decide +kernel) σ acc]
  · change (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
      (Hw.dmaxdon c) 32).toNat = _
    rw [frame (show ((Hw.dmaxdon c : String), (32 : Nat)) ∉
      (Hw.installA c nsE kindE linVE nlE parE).regWrites from by
        fin_cases c <;> decide +kernel) σ acc]

end Machines.Lnp64u.Theorems.RMC
