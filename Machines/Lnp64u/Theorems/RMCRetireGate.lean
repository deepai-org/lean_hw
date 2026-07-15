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

/-- Abstract recipient-side update performed by a transfer installation.
The optional pair carries the newly allocated lineage cell and its parent. -/
def installTransferred (τ : MachineState) (c : DomainId) (NS : Slot)
    (kind : CapKind) (moved : Option (LineageId × CapRef)) : MachineState :=
  τ.setDom c fun ds =>
    { ds with
      caps := Loom.Fun.update ds.caps NS
        (some { kind := kind, lineage := moved.map Prod.fst })
      lineage := match moved with
        | some (l, parent) =>
            Loom.Fun.update ds.lineage l (some { parent := parent })
        | none => ds.lineage }

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

private theorem installA_read_notin_other (c x : DomainId) (hxc : x ≠ c)
    (nsE : Expr 4) (kindE : Expr 32) (linVE : Expr 1)
    (nlE : Expr 4) (parE : Expr 14) :
    ∀ q ∈ domReadNames x,
      q ∉ (Hw.installA c nsE kindE linVE nlE parE).regWrites := by
  intro q hq
  obtain ⟨suffix, hsuffix⟩ := domReadNames_prefix x q hq
  rcases q with ⟨rn, w⟩
  simp only at hsuffix
  subst rn
  simp [Hw.installA, Hw.dcapV, Hw.dcapKind, Hw.dcapLinV, Hw.dcapLin,
    Hw.dcellV, Hw.dcellPar, toString_string, String.append_assoc,
    domPrefix_ne x c hxc]

/-- A selected installation changes no non-recipient domain. -/
theorem absDom_installA_selected_other (σ acc : Loom.Hw.St)
    (c x : DomainId) (hxc : x ≠ c)
    (nsE : Expr 4) (kindE : Expr 32) (linVE : Expr 1)
    (nlE : Expr 4) (parE : Expr 14) :
    Hw.absDom ((Hw.installA c nsE kindE linVE nlE parE).run σ acc) x =
      Hw.absDom acc x := by
  apply absDom_congr
  intro q hq
  exact frame
    (installA_read_notin_other c x hxc nsE kindE linVE nlE parE q hq)
    σ acc

/-- All-domain form of `absDom_installA_selected`: installation is exactly
one recipient-domain update. -/
theorem abs_installA_selected_doms (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind) :
    (Hw.abs ((Hw.installA c nsE kindE linVE nlE parE).run σ acc)).doms =
      let NL : LineageId := finOfBv (by decide) (nlE.eval σ)
      Loom.Fun.update (Hw.abs acc).doms c
        { Hw.absDom acc c with
          caps := Loom.Fun.update (Hw.absDom acc c).caps NS
            (some { kind := kind
                    lineage := if linVE.eval σ = 1#1 then some NL else none })
          lineage := if linVE.eval σ = 1#1 then
            Loom.Fun.update (Hw.absDom acc c).lineage NL
              (some { parent := Hw.decRef (parE.eval σ) })
          else (Hw.absDom acc c).lineage } := by
  dsimp only
  funext x
  by_cases hxc : x = c
  · subst x
    rw [Loom.Fun.update_same]
    exact absDom_installA_selected σ acc c nsE kindE linVE nlE parE NS
      kind hns hkind
  · rw [Loom.Fun.update_ne _ _ _ _ hxc]
    exact absDom_installA_selected_other σ acc c x hxc nsE kindE linVE nlE
      parE

/-- Machine-state spelling of the selected installation bridge. -/
theorem abs_installA_selected (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind) :
    (Hw.abs ((Hw.installA c nsE kindE linVE nlE parE).run σ acc)).doms =
      (installTransferred (Hw.abs acc) c NS kind
        (if linVE.eval σ = 1#1 then
          some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
        else none)).doms := by
  rw [abs_installA_selected_doms σ acc c nsE kindE linVE nlE parE NS kind
    hns hkind]
  unfold installTransferred MachineState.setDom
  dsimp only
  congr 1
  by_cases hl : linVE.eval σ = 1#1 <;> simp [hl]

/-! ## Installation followed by reparenting -/

/-- Reparenting after a selected installation.  The fresh lineage cell is
the sole exception to the usual pre-cycle/accumulator agreement premise:
it was free in the sampled state and its already-adjusted parent is not the
old reference, so neither the hardware nor abstract reparent pass changes it. -/
theorem absDom_reparent_installA_selected (σ acc : Loom.Hw.St)
    (T : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE oldE newE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hfree : linVE.eval σ = 1#1 →
      σ.regs (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 ≠ 1#1)
    (hparent : linVE.eval σ = 1#1 →
      Hw.decRef (parE.eval σ) ≠ Hw.decRef (oldE.eval σ))
    (c : DomainId) :
    Hw.absDom ((Hw.reparentA oldE newE).run σ
        ((Hw.installA T nsE kindE linVE nlE parE).run σ acc)) c =
      ((installTransferred (Hw.abs acc) T NS kind
        (if linVE.eval σ = 1#1 then
          some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
        else none)).reparent (Hw.decRef (oldE.eval σ))
          (Hw.decRef (newE.eval σ))).doms c := by
  let inst := (Hw.installA T nsE kindE linVE nlE parE).run σ acc
  let τi := installTransferred (Hw.abs acc) T NS kind
    (if linVE.eval σ = 1#1 then
      some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
    else none)
  have hi : (Hw.abs inst).doms = τi.doms := by
    exact abs_installA_selected σ acc T nsE kindE linVE nlE parE NS kind
      hns hkind
  have hr : ((Hw.abs inst).reparent (Hw.decRef (oldE.eval σ))
      (Hw.decRef (newE.eval σ))).doms =
      (τi.reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))).doms := by
    unfold MachineState.reparent
    dsimp only
    rw [hi]
  change Hw.absDom ((Hw.reparentA oldE newE).run σ inst) c = _
  apply domainState_ext
  · funext r
    rw [reparent_regs]
    rw [reparentA_frame_width σ inst oldE newE (Hw.dreg c r) 32
      (by decide)]
    exact congrArg (fun ds => ds.regs r) (congrFun hi c)
  · rw [reparent_pc]
    rw [reparentA_frame_width σ inst oldE newE (Hw.dpc c) 12 (by decide)]
    exact congrArg DomainState.pc (congrFun hi c)
  · funext s
    rw [← congrFun hr c]
    exact abs_reparentA_caps σ inst oldE newE c s
  · funext s
    rw [← congrFun hr c]
    exact abs_reparentA_slotGen σ inst oldE newE c s
  · funext l
    rw [← congrFun hr c]
    by_cases hl : linVE.eval σ = 1#1
    · by_cases hexc : c = T ∧
          l = finOfBv (by decide) (nlE.eval σ)
      · rcases hexc with ⟨rfl, rfl⟩
        rw [reparent_lineage]
        change (if ((Hw.reparentA oldE newE).run σ inst).regs
            (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 = 1#1 then
          some ({ parent := Hw.decRef
            (((Hw.reparentA oldE newE).run σ inst).regs
              (Hw.dcellPar T (finOfBv (by decide) (nlE.eval σ))) 14) } :
                LineageCell) else none) = _
        rw [reparentA_frame_width σ inst oldE newE
          (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 (by decide),
          installA_selected_cellV σ acc T nsE kindE linVE nlE parE NS hns,
          reparentA_cellPar σ inst oldE newE T
            (finOfBv (by decide) (nlE.eval σ)),
          installA_selected_cellPar σ acc T nsE kindE linVE nlE parE NS hns]
        have hfree0 := bv1_ne_one.mp (hfree hl)
        simp [hl, hfree0, hparent hl]
      · have hVi : inst.regs (Hw.dcellV c l) 1 =
            σ.regs (Hw.dcellV c l) 1 := by
          rw [installA_selected_cellV σ acc T nsE kindE linVE nlE parE NS
            hns l]
          have hn : ¬(c = T ∧ l = finOfBv (by decide) (nlE.eval σ)) := hexc
          by_cases hcT : c = T
          · subst c
            simp [hl, hn, hV T l]
          · have hreg : inst.regs (Hw.dcellV c l) 1 =
                acc.regs (Hw.dcellV c l) 1 := by
              apply frame
              exact installA_read_notin_other T c hcT nsE kindE linVE nlE
                parE (Hw.dcellV c l, 1) (by
                  simp [domReadNames])
            exact hreg.trans (hV c l)
        have hPi : inst.regs (Hw.dcellPar c l) 14 =
            σ.regs (Hw.dcellPar c l) 14 := by
          rw [installA_selected_cellPar σ acc T nsE kindE linVE nlE parE NS
            hns l]
          by_cases hcT : c = T
          · subst c
            simp [hl, hexc, hP T l]
          · have hreg : inst.regs (Hw.dcellPar c l) 14 =
                acc.regs (Hw.dcellPar c l) 14 := by
              apply frame
              exact installA_read_notin_other T c hcT nsE kindE linVE nlE
                parE (Hw.dcellPar c l, 14) (by
                  simp [domReadNames])
            exact hreg.trans (hP c l)
        exact abs_reparentA_lineage σ inst oldE newE c l hVi hPi
    · have hVi : inst.regs (Hw.dcellV c l) 1 =
          σ.regs (Hw.dcellV c l) 1 := by
        rw [installA_selected_cellV σ acc T nsE kindE linVE nlE parE NS hns]
        simp [hl, hV c l]
      have hPi : inst.regs (Hw.dcellPar c l) 14 =
          σ.regs (Hw.dcellPar c l) 14 := by
        rw [installA_selected_cellPar σ acc T nsE kindE linVE nlE parE NS
          hns]
        simp [hl, hP c l]
      exact abs_reparentA_lineage σ inst oldE newE c l hVi hPi
  · funext r
    rw [reparent_regions]
    rw [reparentA_frame_width σ inst oldE newE (Hw.drgnV c r) 1
      (by decide), reparentA_frame_width σ inst oldE newE (Hw.drgn c r) 42
      (by decide)]
    exact congrArg (fun ds => ds.regions r) (congrFun hi c)
  · rw [reparent_run]
    change Hw.decRun
      (((Hw.reparentA oldE newE).run σ inst).regs (Hw.drun c) 2)
      (((Hw.reparentA oldE newE).run σ inst).regs (Hw.drunG c) 2) = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.drun c) 2 (by decide),
      reparentA_frame_width σ inst oldE newE (Hw.drunG c) 2 (by decide)]
    exact congrArg DomainState.run (congrFun hi c)
  · rw [reparent_serving]
    change (if ((Hw.reparentA oldE newE).run σ inst).regs
        (Hw.dsrvV c) 1 = 1#1 then
      some (finOfBv (by decide)
        (((Hw.reparentA oldE newE).run σ inst).regs (Hw.dsrv c) 2))
      else none) = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.dsrvV c) 1 (by decide),
      reparentA_frame_width σ inst oldE newE (Hw.dsrv c) 2 (by decide)]
    exact congrArg DomainState.serving (congrFun hi c)
  · rw [reparent_cause]
    rw [reparentA_frame_width σ inst oldE newE (Hw.dcause c) 32 (by decide)]
    exact congrArg DomainState.cause (congrFun hi c)
  · rw [reparent_budget]
    change (((Hw.reparentA oldE newE).run σ inst).regs
      (Hw.dbudget c) 32).toNat = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.dbudget c) 32 (by decide)]
    exact congrArg DomainState.budget (congrFun hi c)
  · rw [reparent_maxDonation]
    change (((Hw.reparentA oldE newE).run σ inst).regs
      (Hw.dmaxdon c) 32).toNat = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.dmaxdon c) 32 (by decide)]
    exact congrArg DomainState.maxDonation (congrFun hi c)

/-- Pre-adjusting the moved cell's parent is equivalent to letting the
abstract reparent pass adjust it, provided the old and new references differ.
This is the semantic reason for the parent mux inside `Hw.transferA`. -/
theorem installTransferred_reparent_adjusted (τ : MachineState)
    (T : DomainId) (NS : Slot) (kind : CapKind) (NL : LineageId)
    (parent oldRef newRef : CapRef) (hne : newRef ≠ oldRef) :
    (installTransferred τ T NS kind
        (some (NL, if parent = oldRef then newRef else parent))).reparent
      oldRef newRef =
    (installTransferred τ T NS kind (some (NL, parent))).reparent
      oldRef newRef := by
  by_cases hp : parent = oldRef
  · subst parent
    simp [installTransferred, MachineState.reparent, MachineState.setDom,
      hne]
  · simp [installTransferred, MachineState.reparent, MachineState.setDom,
      hp]

/-! ## Clearing after the transfer move -/

/-- Transport `absDom_clearSlotA` across a known all-domain abstraction.
This is the compositional form needed after install and reparent. -/
theorem absDom_clearSlotA_of_doms (σ acc : Loom.Hw.St) (pre : MachineState)
    (d : DomainId) (S : Slot) (sE : Expr 4)
    (linVE : Expr 1) (linE : Expr 4)
    (hdoms : (Hw.abs acc).doms = pre.doms)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (hgen : acc.regs (Hw.dgen d S) 8 = σ.regs (Hw.dgen d S) 8)
    (hremoved : removedCell pre d S =
      if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (linE.eval σ)) else none)
    (c : DomainId) :
    Hw.absDom ((Hw.clearSlotA d sE linVE linE).run σ acc) c =
      ((pre.clearSlot d S).doms c) := by
  have hremoved' : removedCell (Hw.abs acc) d S =
      if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (linE.eval σ)) else none := by
    unfold removedCell
    rw [hdoms]
    exact hremoved
  rw [absDom_clearSlotA σ acc d S sE linVE linE hslot hgen hremoved' c]
  unfold MachineState.clearSlot MachineState.setDom
  rw [hdoms]

/-! ## Region sweep after a transferred slot is cleared -/

/-- Generic hardware/spec region-sweep bridge for an operation that has
removed exactly one `(domain, slot)` from the live-reference relation. -/
theorem absDom_sweepRegionsA_cleared (σ acc : Loom.Hw.St)
    (pre : MachineState) (d : DomainId) (S : Slot)
    (killed : Expr 2 → Expr 4 → Expr 1)
    (hdoms : (Hw.abs acc).doms = pre.doms)
    (hvalid : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1)
    (hpacked : ∀ c : DomainId, ∀ r : RegionId,
      acc.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42)
    (hregions : ∀ c : DomainId,
      (pre.doms c).regions = ((Hw.abs σ).doms c).regions)
    (hlive : ∀ ref : CapRef, pre.liveRef ref =
      if ref.dom = d ∧ ref.slot = S then false
      else (Hw.abs σ).liveRef ref)
    (hkill : ∀ c : DomainId, ∀ r : RegionId,
      (killed (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
        (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval σ = 1#1 ↔
      (Hw.decRegion (σ.regs (Hw.drgn c r) 42)).backing.dom = d ∧
        (Hw.decRegion (σ.regs (Hw.drgn c r) 42)).backing.slot = S)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) :
    Hw.absDom ((Hw.sweepRegionsA killed).run σ acc) c =
      (pre.sweepRegions.doms c) := by
  let out := (Hw.sweepRegionsA killed).run σ acc
  have hbase : Hw.absDom acc c = pre.doms c := congrFun hdoms c
  have hframe (q : String) (qW : Nat)
      (hne : ∀ c' : DomainId, ∀ r' : RegionId, q ≠ Hw.drgnV c' r') :
      out.regs q qW = acc.regs q qW :=
    sweepRegionsA_frame σ acc killed q qW hne
  have hframeW (q : String) (qW : Nat) (hne : qW ≠ 1) :
      out.regs q qW = acc.regs q qW :=
    sweepRegionsA_frame_width σ acc killed q qW hne
  apply domainState_ext
  · rw [sweepRegions_regs]
    funext rr
    change out.regs (Hw.dreg c rr) 32 = _
    rw [hframeW _ _ (by decide)]
    exact congrFun (congrArg DomainState.regs hbase) rr
  · rw [sweepRegions_pc]
    change out.regs (Hw.dpc c) 12 = _
    rw [hframeW _ _ (by decide)]
    exact congrArg DomainState.pc hbase
  · rw [sweepRegions_caps]
    funext s
    change (if out.regs (Hw.dcapV c s) 1 = 1#1 then
      some (⟨Hw.decKind (out.regs (Hw.dcapKind c s) 32),
        if out.regs (Hw.dcapLinV c s) 1 = 1#1 then
          some (finOfBv (by decide) (out.regs (Hw.dcapLin c s) 4))
        else none⟩ : CapEntry) else none) = _
    rw [hframe _ _ (fun c' r' => dcapV_ne_drgnV c c' s r'),
      hframeW _ _ (by decide),
      hframe _ _ (fun c' r' => dcapLinV_ne_drgnV c c' s r'),
      hframeW _ _ (by decide)]
    exact congrFun (congrArg DomainState.caps hbase) s
  · rw [sweepRegions_slotGen]
    funext s
    change out.regs (Hw.dgen c s) 8 = _
    rw [hframeW _ _ (by decide)]
    exact congrFun (congrArg DomainState.slotGen hbase) s
  · rw [sweepRegions_lineage]
    funext l
    change (if out.regs (Hw.dcellV c l) 1 = 1#1 then
      some ({ parent := Hw.decRef (out.regs (Hw.dcellPar c l) 14) } :
        LineageCell) else none) = _
    rw [hframe _ _ (fun c' r' => dcellV_ne_drgnV c c' l r'),
      hframeW _ _ (by decide)]
    exact congrFun (congrArg DomainState.lineage hbase) l
  · funext r
    rw [sweepRegions_drop_regions (Hw.abs σ) pre d S hregions hlive
      (fun c' r' rg hr => regionBacking_live hwf hr) c r]
    change (if out.regs (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (out.regs (Hw.drgn c r) 42)) else none) = _
    rw [sweepRegionsA_rgnV, sweepRegionsA_rgn, hvalid c r, hpacked c r]
    let rg := Hw.decRegion (σ.regs (Hw.drgn c r) 42)
    let k := (killed (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
      (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval σ
    have hkiff : k = 1#1 ↔ rg.backing.dom = d ∧ rg.backing.slot = S :=
      hkill c r
    by_cases hv : σ.regs (Hw.drgnV c r) 1 = 1#1
    · by_cases hk : rg.backing.dom = d ∧ rg.backing.slot = S
      · have hk1 : k = 1#1 := hkiff.mpr hk
        simp [regionKillCond, hv, hk, hk1, k, rg]
      · have hk0 : k = 0#1 := bv1_ne_one.mp (fun h => hk (hkiff.mp h))
        simp [regionKillCond, hv, hk, hk0, k, rg]
    · have hv0 : σ.regs (Hw.drgnV c r) 1 = 0#1 := bv1_ne_one.mp hv
      simp [regionKillCond, hv, hv0, k, rg]
  · rw [sweepRegions_run]
    change Hw.decRun (out.regs (Hw.drun c) 2)
      (out.regs (Hw.drunG c) 2) = _
    rw [hframeW _ _ (by decide), hframeW _ _ (by decide)]
    exact congrArg DomainState.run hbase
  · rw [sweepRegions_serving]
    change (if out.regs (Hw.dsrvV c) 1 = 1#1 then
      some (finOfBv (by decide) (out.regs (Hw.dsrv c) 2)) else none) = _
    rw [hframe _ _ (fun c' r' => dsrvV_ne_drgnV c c' r'),
      hframeW _ _ (by decide)]
    exact congrArg DomainState.serving hbase
  · rw [sweepRegions_cause]
    change out.regs (Hw.dcause c) 32 = _
    rw [hframeW _ _ (by decide)]
    exact congrArg DomainState.cause hbase
  · rw [sweepRegions_budget]
    change (out.regs (Hw.dbudget c) 32).toNat = _
    rw [hframeW _ _ (by decide)]
    exact congrArg DomainState.budget hbase
  · change (out.regs (Hw.dmaxdon c) 32).toNat =
      (pre.sweepRegions.doms c).maxDonation
    rw [sweepRegions_maxDonation, hframeW _ _ (by decide)]
    exact congrArg DomainState.maxDonation hbase

/-! ## Specification transfer decomposition -/

/-- A successful specification transfer exposes exactly the source entry,
recipient slot, optional moved lineage cell, and structural domain update.
The trailing `sweepMover` may change memory/Mover state but never `doms`. -/
theorem transferCap_decompose_doms (τ τ' : MachineState)
    (d : DomainId) (S : Slot) (T : DomainId) (newRef : CapRef)
    (ht : τ.transferCap d S T = some (τ', newRef)) :
    ∃ (e : CapEntry) (NS : Slot),
      (τ.doms d).caps S = some e ∧ τ.freeSlot T = some NS ∧
      newRef = ⟨T, NS, (τ.doms T).slotGen NS⟩ ∧
      match e.lineage with
      | none =>
          τ'.doms =
            ((((installTransferred τ T NS e.kind none).reparent
              ⟨d, S, (τ.doms d).slotGen S⟩ newRef).clearSlot d S).sweepRegions).doms
      | some L => ∃ (cell : LineageCell) (NL : LineageId),
          (τ.doms d).lineage L = some cell ∧ τ.freeCell T = some NL ∧
          τ'.doms =
            ((((installTransferred τ T NS e.kind
                (some (NL, cell.parent))).reparent
              ⟨d, S, (τ.doms d).slotGen S⟩ newRef).clearSlot d S).sweepRegions).doms := by
  unfold MachineState.transferCap at ht
  cases he : (τ.doms d).caps S with
  | none => simp [he] at ht
  | some e =>
      cases hs : τ.freeSlot T with
      | none => simp [he, hs] at ht
      | some NS =>
          cases hl : e.lineage with
          | none =>
              simp only [he, hs, hl, Option.bind_some, Option.pure_def,
                Option.bind_eq_bind] at ht
              injection ht with hstate href
              subst τ'
              subst newRef
              refine ⟨e, NS, he, hs, rfl, ?_⟩
              simp [installTransferred, MachineState.setDom,
                MachineState.sweepMover, MachineState.write]
          | some L =>
              cases hc : (τ.doms d).lineage L with
              | none => simp [he, hs, hl, hc] at ht
              | some cell =>
                  cases hfc : τ.freeCell T with
                  | none => simp [he, hs, hl, hc, hfc] at ht
                  | some NL =>
                      simp only [he, hs, hl, hc, hfc, Option.bind_some,
                        Option.pure_def, Option.bind_eq_bind] at ht
                      injection ht with hstate href
                      subst τ'
                      subst newRef
                      refine ⟨e, NS, he, hs, rfl, ?_⟩
                      refine ⟨cell, NL, hc, hfc, ?_⟩
                      simp [installTransferred, MachineState.setDom,
                        MachineState.sweepMover, MachineState.write]

end Machines.Lnp64u.Theorems.RMC
