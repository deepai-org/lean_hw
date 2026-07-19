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

private theorem st_ext {a b : Loom.Hw.St}
    (hregs : a.regs = b.regs) (hmems : a.mems = b.mems) : a = b := by
  cases a
  cases b
  simp_all

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

/-- The transfer sweep predicate is exactly equality with the source
domain and selected source slot. -/
theorem transferKilled_eval (σ : Loom.Hw.St) (d : DomainId)
    (slotE : Expr 4) (S : Slot)
    (hslot : slotE.eval σ = BitVec.ofNat 4 S.val)
    (dm : Expr 2) (sl : Expr 4) :
    ((Expr.and (.eq dm (Hw.dLit d)) (.eq sl slotE)).eval σ = 1#1) ↔
      finOfBv (by decide) (dm.eval σ) = d ∧
      finOfBv (by decide) (sl.eval σ) = S := by
  change ((if dm.eval σ = (Hw.dLit d).eval σ then 1#1 else 0#1) &&&
      (if sl.eval σ = slotE.eval σ then 1#1 else 0#1) = 1#1) ↔ _
  rw [bv1_and_eq_one, hslot]
  have ite_one_iff (p : Prop) [Decidable p] :
      ((if p then 1#1 else 0#1) = 1#1) ↔ p := by
    by_cases hp : p <;> simp [hp]
  rw [ite_one_iff, ite_one_iff]
  exact and_congr (bv2_lit_iff _ d) (bv4_slot_iff _ S)

/-- Specialization of the transfer kill predicate to a packed region's
backing reference. -/
theorem transferKilled_region_eval (σ : Loom.Hw.St) (d : DomainId)
    (slotE : Expr 4) (S : Slot)
    (hslot : slotE.eval σ = BitVec.ofNat 4 S.val) (rgE : Expr 42) :
    ((Expr.and
        (.eq (Hw.field rgE 40 2) (Hw.dLit d))
        (.eq (Hw.field rgE 36 4) slotE)).eval σ = 1#1) ↔
      (Hw.decRegion (rgE.eval σ)).backing.dom = d ∧
      (Hw.decRegion (rgE.eval σ)).backing.slot = S := by
  rw [transferKilled_eval σ d slotE S hslot]
  unfold Hw.decRegion Hw.decRef Hw.field
  rw [extractLsb'_extractLsb' _ 28 12 (by omega),
    extractLsb'_extractLsb' _ 28 8 (by omega)]
  rfl

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

/-- `reparentA` depends on its replacement expression only through its
value in the sampled state. -/
theorem reparentA_run_new_eval (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (newE newE' : Expr 14) (hnew : newE.eval σ = newE'.eval σ) :
    (Hw.reparentA oldE newE).run σ acc =
      (Hw.reparentA oldE newE').run σ acc := by
  apply st_ext
  · funext q w
    by_cases hw : w = 14
    · subst w
      by_cases hq : ∃ c : DomainId, ∃ l : LineageId,
          q = Hw.dcellPar c l
      · obtain ⟨c, l, rfl⟩ := hq
        rw [reparentA_cellPar, reparentA_cellPar, hnew]
      · rw [reparentA_frame σ acc oldE newE q 14 (fun c l h =>
            hq ⟨c, l, h⟩),
          reparentA_frame σ acc oldE newE' q 14 (fun c l h =>
            hq ⟨c, l, h⟩)]
    · rw [reparentA_frame_width σ acc oldE newE q w hw,
        reparentA_frame_width σ acc oldE newE' q w hw]
  · funext mn ad w
    rw [Loom.Hw.Act.run_mems_notin mn (Hw.reparentA oldE newE)
        (by rw [show (Hw.reparentA oldE newE).memWrites = [] from rfl]; simp)
        σ acc ad w,
      Loom.Hw.Act.run_mems_notin mn (Hw.reparentA oldE newE')
        (by rw [show (Hw.reparentA oldE newE').memWrites = [] from rfl]; simp)
        σ acc ad w]

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
  have hnew : (Hw.muxFin (fun c =>
      Hw.encRefE (Hw.dLit c) (Hw.freeSlotIdx c)
        (Hw.genOfE c (Hw.freeSlotIdx c))) toE).eval σ =
      (Hw.encRefE (Hw.dLit T) (Hw.freeSlotIdx T)
        (Hw.genOfE T (Hw.freeSlotIdx T))).eval σ := by
    rw [muxFin_eval (by decide : 2 ^ 2 = numDomains)]
  rw [reparentA_run_new_eval σ _ _ _ _ hnew]

end Machines.Lnp64u.Theorems.RMC
