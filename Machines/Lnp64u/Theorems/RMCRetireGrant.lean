-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireDup

/-!
# R-MC retirement: `mem_grant`

The target-domain variant of the capability-install proof.  `cap_dup`
established the table/install and watched-reference machinery; this file
adds the descriptor-target mux and domain-fold selection needed by
`mem_grant`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 3200000
set_option maxRecDepth 200000

/-! ## Target-domain selection -/

/-- The descriptor target circuit is the spec's `descDom`. -/
theorem descTgt_fin_eval (σ : Loom.Hw.St) (dw : Expr 32) :
    finOfBv (by decide : 2 ^ 2 = numDomains)
        ((Hw.descTgt dw).eval σ) =
      Machines.Lnp64u.Isa.descDom (dw.eval σ) := by
  rfl

/-- A target-indexed mux selects the descriptor's target domain. -/
theorem grant_muxFin_eval {w : Nat} (σ : Loom.Hw.St) (dw : Expr 32)
    (f : DomainId → Expr w) :
    (Hw.muxFin f (Hw.descTgt dw)).eval σ =
      (f (Machines.Lnp64u.Isa.descDom (dw.eval σ))).eval σ := by
  rw [muxFin_eval (by decide : 2 ^ 2 = numDomains)]
  rfl

/-- The grant free-slot guard is the target domain's guard. -/
theorem grant_freeSlotV_eval (σ : Loom.Hw.St) (dw : Expr 32) :
    (Hw.muxFin (fun c => Hw.freeSlotV c) (Hw.descTgt dw)).eval σ =
      (Hw.freeSlotV (Machines.Lnp64u.Isa.descDom (dw.eval σ))).eval σ :=
  grant_muxFin_eval σ dw _

/-- The grant free-cell guard is the target domain's guard. -/
theorem grant_freeCellV_eval (σ : Loom.Hw.St) (dw : Expr 32) :
    (Hw.muxFin (fun c => Hw.freeCellV c) (Hw.descTgt dw)).eval σ =
      (Hw.freeCellV (Machines.Lnp64u.Isa.descDom (dw.eval σ))).eval σ :=
  grant_muxFin_eval σ dw _

/-- The result-handle mux selects the target-relative handle circuit. -/
theorem grant_handle_mux_eval (σ : Loom.Hw.St) (dw : Expr 32) :
    (Hw.muxFin (fun c => Hw.handleE (Hw.freeSlotIdx c)
        (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
      (Hw.descTgt dw)).eval σ =
      (Hw.handleE
        (Hw.freeSlotIdx (Machines.Lnp64u.Isa.descDom (dw.eval σ)))
        (Hw.genOfE (Machines.Lnp64u.Isa.descDom (dw.eval σ))
          (Hw.freeSlotIdx (Machines.Lnp64u.Isa.descDom (dw.eval σ))))
        (.lit 0)).eval σ :=
  grant_muxFin_eval σ dw _

/-! ## Domain-fold selection -/

/-- Exactly one branch of the grant's domain-indexed install fold fires. -/
theorem grant_installFold_run (σ acc : Loom.Hw.St) (dw : Expr 32)
    (kindE : Expr 32) (parentE : Expr 14) :
    (Hw.seqAll ((List.finRange numDomains).map fun c =>
      Act.ite (.eq (Hw.descTgt dw) (Hw.dLit c))
        (Hw.installA c (Hw.freeSlotIdx c) kindE (.lit 1)
          (Hw.freeCellIdx c) parentE)
        .skip)).run σ acc =
      (Hw.installA (Machines.Lnp64u.Isa.descDom (dw.eval σ))
        (Hw.freeSlotIdx (Machines.Lnp64u.Isa.descDom (dw.eval σ)))
        kindE (.lit 1)
        (Hw.freeCellIdx (Machines.Lnp64u.Isa.descDom (dw.eval σ)))
        parentE).run σ acc := by
  let T : DomainId := Machines.Lnp64u.Isa.descDom (dw.eval σ)
  have hsel : (Expr.eq (Hw.descTgt dw) (Hw.dLit T)).eval σ = 1#1 := by
    rw [eqE_eval]
    apply BitVec.eq_of_toNat_eq
    change T.val = (BitVec.ofNat 2 T.val).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt T.isLt]
  have hexcl : ∀ j : DomainId, j ≠ T →
      (Expr.eq (Hw.descTgt dw) (Hw.dLit j)).eval σ ≠ 1#1 := by
    intro j hj hfire
    apply hj
    apply Fin.ext
    rw [eqE_eval] at hfire
    have hnat := congrArg BitVec.toNat hfire
    change T.val = (BitVec.ofNat 2 j.val).toNat at hnat
    symm
    simpa [T, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show j.val < 2 ^ 2 from j.isLt)] using hnat
  exact seqAll_ite_run_unique σ acc
    (fun c : DomainId => Expr.eq (Hw.descTgt dw) (Hw.dLit c))
    (fun c : DomainId => Hw.installA c (Hw.freeSlotIdx c) kindE
      (.lit 1) (Hw.freeCellIdx c) parentE) T hsel hexcl
    (List.finRange numDomains) (List.mem_finRange T) (List.nodup_finRange _)

/-! ## Generic selected install -/

/-- Once the dynamic slot and lineage indices are known, `installA` is
exactly six register writes.  Keeping this value-parametric makes the
cap-table face reusable beyond `mem_grant`. -/
theorem installA_run_selected (σ acc : Loom.Hw.St) (c : DomainId)
    (nsE : Expr 4) (kindE : Expr 32) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (NL : LineageId)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hnl : nlE.eval σ = BitVec.ofNat 4 NL.val) :
    (Hw.installA c nsE kindE (.lit 1) nlE parE).run σ acc =
      (Act.seq
        (Hw.seqAll [.write 1 (Hw.dcapV c NS) (.lit 1),
          .write 32 (Hw.dcapKind c NS) kindE,
          .write 1 (Hw.dcapLinV c NS) (.lit 1),
          .write 4 (Hw.dcapLin c NS) nlE])
        (.seq (.write 1 (Hw.dcellV c NL) (.lit 1))
          (.write 14 (Hw.dcellPar c NL) parE))).run σ acc := by
  show ((Hw.seqAll ((List.finRange numLineage).map fun l =>
      Act.ite (.and (.lit 1) (.eq nlE (Hw.lLit l)))
        (.seq (.write 1 (Hw.dcellV c l) (.lit 1))
          (.write 14 (Hw.dcellPar c l) parE)) .skip)).run σ
    ((Hw.seqAll ((List.finRange numSlots).map fun s =>
      Act.ite (.eq nsE (Hw.sLit s))
        (Hw.seqAll [.write 1 (Hw.dcapV c s) (.lit 1),
          .write 32 (Hw.dcapKind c s) kindE,
          .write 1 (Hw.dcapLinV c s) (.lit 1),
          .write 4 (Hw.dcapLin c s) nlE]) .skip)).run σ acc)) = _
  have hs : (Expr.eq nsE (Hw.sLit NS)).eval σ = 1#1 := by
    rw [eqE_eval, hns]
    rfl
  have hsx : ∀ j : Slot, j ≠ NS →
      (Expr.eq nsE (Hw.sLit j)).eval σ ≠ 1#1 := by
    intro j hj hfire
    apply hj
    apply Fin.ext
    rw [eqE_eval, hns] at hfire
    have hnat := congrArg BitVec.toNat hfire
    change (BitVec.ofNat 4 NS.val).toNat =
      (BitVec.ofNat 4 j.val).toNat at hnat
    simpa [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show j.val < 2 ^ 4 from j.isLt),
      Nat.mod_eq_of_lt (show NS.val < 2 ^ 4 from NS.isLt)] using hnat.symm
  rw [seqAll_ite_run_unique σ acc
    (fun s : Slot => Expr.eq nsE (Hw.sLit s))
    (fun s : Slot => Hw.seqAll [.write 1 (Hw.dcapV c s) (.lit 1),
      .write 32 (Hw.dcapKind c s) kindE,
      .write 1 (Hw.dcapLinV c s) (.lit 1),
      .write 4 (Hw.dcapLin c s) nlE]) NS hs hsx
    (List.finRange numSlots) (List.mem_finRange NS) (List.nodup_finRange _)]
  have hl : (Expr.and (.lit 1) (Expr.eq nlE (Hw.lLit NL))).eval σ = 1#1 := by
    change (1#1 &&& (Expr.eq nlE (Hw.lLit NL)).eval σ) = 1#1
    rw [bv1_and_eq_one]
    constructor
    · rfl
    · rw [eqE_eval, hnl]
      change BitVec.ofNat 4 NL.val = BitVec.ofNat 4 NL.val
      rfl
  have hlx : ∀ j : LineageId, j ≠ NL →
      (Expr.and (.lit 1) (Expr.eq nlE (Hw.lLit j))).eval σ ≠ 1#1 := by
    intro j hj hfire
    change (1#1 &&& (Expr.eq nlE (Hw.lLit j)).eval σ) = 1#1 at hfire
    rw [bv1_and_eq_one] at hfire
    apply hj
    apply Fin.ext
    rw [eqE_eval, hnl] at hfire
    have hnat := congrArg BitVec.toNat hfire.2
    change (BitVec.ofNat 4 NL.val).toNat =
      (BitVec.ofNat 4 j.val).toNat at hnat
    simpa [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show j.val < 2 ^ 4 from j.isLt),
      Nat.mod_eq_of_lt (show NL.val < 2 ^ 4 from NL.isLt)] using hnat.symm
  exact seqAll_ite_run_unique σ _
    (fun l : LineageId => Expr.and (.lit 1) (Expr.eq nlE (Hw.lLit l)))
    (fun l : LineageId => Act.seq
      (.write 1 (Hw.dcellV c l) (.lit 1))
      (.write 14 (Hw.dcellPar c l) parE)) NL hl hlx
    (List.finRange numLineage) (List.mem_finRange NL) (List.nodup_finRange _)

/-! ## Selected full grant action -/

/-- The complete fired `mem_grant` core action. -/
def grantFull (e : DomainId) : Act :=
  .seq (.write 1 "if_v" (.lit 0)) <| Hw.seqAll
    [ Hw.seqAll ((List.finRange numDomains).map fun c =>
        .ite (.eq (Hw.descTgt (Hw.readReg e Hw.rs2E)) (Hw.dLit c))
          (Hw.installA c (Hw.freeSlotIdx c)
            (Hw.narrowKindE (Hw.grantSel e).kindW
              (Hw.readReg e Hw.rs2E))
            (.lit 1) (Hw.freeCellIdx c)
            (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
              (Hw.grantSel e).gen))
          .skip),
      Hw.writeReg e Hw.rdE (Hw.muxFin (fun c =>
        Hw.handleE (Hw.freeSlotIdx c) (Hw.genOfE c (Hw.freeSlotIdx c))
          (.lit 0)) (Hw.descTgt (Hw.readReg e Hw.rs2E))),
      Hw.pcAdvA e ]

/-- Same action after selecting the descriptor target domain. -/
def grantChosen (e t : DomainId) : Act :=
  .seq (.write 1 "if_v" (.lit 0)) <| Hw.seqAll
    [ Hw.installA t (Hw.freeSlotIdx t)
        (Hw.narrowKindE (Hw.grantSel e).kindW (Hw.readReg e Hw.rs2E))
        (.lit 1) (Hw.freeCellIdx t)
        (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
          (Hw.grantSel e).gen),
      Hw.writeReg e Hw.rdE (Hw.muxFin (fun c =>
        Hw.handleE (Hw.freeSlotIdx c) (Hw.genOfE c (Hw.freeSlotIdx c))
          (.lit 0)) (Hw.descTgt (Hw.readReg e Hw.rs2E))),
      Hw.pcAdvA e ]

/-- The domain fold in `grantFull` reduces to `grantChosen`. -/
theorem grantFull_run_selected (σ acc : Loom.Hw.St) (e : DomainId) :
    (grantFull e).run σ acc =
      (grantChosen e
        (Machines.Lnp64u.Isa.descDom ((Hw.readReg e Hw.rs2E).eval σ))).run
        σ acc := by
  unfold grantFull grantChosen
  show (Hw.pcAdvA e).run σ
      ((Hw.writeReg e Hw.rdE _).run σ
        ((Hw.seqAll ((List.finRange numDomains).map fun c =>
          Act.ite (.eq (Hw.descTgt (Hw.readReg e Hw.rs2E)) (Hw.dLit c))
            (Hw.installA c (Hw.freeSlotIdx c)
              (Hw.narrowKindE (Hw.grantSel e).kindW
                (Hw.readReg e Hw.rs2E))
              (.lit 1) (Hw.freeCellIdx c)
              (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
                (Hw.grantSel e).gen)) .skip)).run σ
          ((Act.write 1 "if_v" (.lit 0)).run σ acc))) = _
  rw [grant_installFold_run σ _ (Hw.readReg e Hw.rs2E)
    (Hw.narrowKindE (Hw.grantSel e).kindW (Hw.readReg e Hw.rs2E))
    (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
      (Hw.grantSel e).gen)]
  simp [Hw.seqAll, Act.run]

/-! ## Fully selected register action -/

/-- The selected grant with both allocation indices made static. -/
def grantExplicit (e t : DomainId) (NS : Slot) (NL : LineageId) : Act :=
  .seq (.write 1 "if_v" (.lit 0)) <| Hw.seqAll
    [ Hw.seqAll [.write 1 (Hw.dcapV t NS) (.lit 1),
        .write 32 (Hw.dcapKind t NS)
          (Hw.narrowKindE (Hw.grantSel e).kindW (Hw.readReg e Hw.rs2E)),
        .write 1 (Hw.dcapLinV t NS) (.lit 1),
        .write 4 (Hw.dcapLin t NS) (Hw.freeCellIdx t)],
      .seq (.write 1 (Hw.dcellV t NL) (.lit 1))
        (.write 14 (Hw.dcellPar t NL)
          (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
            (Hw.grantSel e).gen)),
      Hw.writeReg e Hw.rdE (Hw.muxFin (fun c =>
        Hw.handleE (Hw.freeSlotIdx c) (Hw.genOfE c (Hw.freeSlotIdx c))
          (.lit 0)) (Hw.descTgt (Hw.readReg e Hw.rs2E))),
      Hw.pcAdvA e ]

/-- Once both free indices are identified, the selected action is a fixed
sequence of architectural register writes. -/
theorem grantChosen_run_explicit (σ acc : Loom.Hw.St) (e t : DomainId)
    (NS : Slot) (NL : LineageId)
    (hns : (Hw.freeSlotIdx t).eval σ = BitVec.ofNat 4 NS.val)
    (hnl : (Hw.freeCellIdx t).eval σ = BitVec.ofNat 4 NL.val) :
    (grantChosen e t).run σ acc = (grantExplicit e t NS NL).run σ acc := by
  unfold grantChosen grantExplicit
  show (Hw.pcAdvA e).run σ
      ((Hw.writeReg e Hw.rdE _).run σ
        ((Hw.installA t (Hw.freeSlotIdx t)
          (Hw.narrowKindE (Hw.grantSel e).kindW (Hw.readReg e Hw.rs2E))
          (.lit 1) (Hw.freeCellIdx t)
          (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
            (Hw.grantSel e).gen)).run σ
          ((Act.write 1 "if_v" (.lit 0)).run σ acc))) = _
  rw [installA_run_selected σ _ t (Hw.freeSlotIdx t)
    (Hw.narrowKindE (Hw.grantSel e).kindW (Hw.readReg e Hw.rs2E))
    (Hw.freeCellIdx t)
    (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
      (Hw.grantSel e).gen) NS NL hns hnl]
  simp [Hw.seqAll, Act.run]

/-! ## Selected table face -/

def grantTailCellV (e t : DomainId) (NL : LineageId) : Act :=
  .write 14 (Hw.dcellPar t NL)
    (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot (Hw.grantSel e).gen)

def grantTailLin (e t : DomainId) (NL : LineageId) : Act :=
  .seq (.write 1 (Hw.dcellV t NL) (.lit 1)) (grantTailCellV e t NL)

def grantTailLinV (e t : DomainId) (NS : Slot) (NL : LineageId) : Act :=
  .seq (.write 4 (Hw.dcapLin t NS) (Hw.freeCellIdx t))
    (grantTailLin e t NL)

def grantTailKind (e t : DomainId) (NS : Slot) (NL : LineageId) : Act :=
  .seq (.write 1 (Hw.dcapLinV t NS) (.lit 1))
    (grantTailLinV e t NS NL)

/-- The fixed table writes following the capability-valid write. -/
def grantTableTailV (e t : DomainId) (NS : Slot) (NL : LineageId) : Act :=
  .seq (.write 32 (Hw.dcapKind t NS)
    (Hw.narrowKindE (Hw.grantSel e).kindW (Hw.readReg e Hw.rs2E)))
    (grantTailKind e t NS NL)

/-- The fixed table-writing prefix of a selected grant. -/
def grantTables (e t : DomainId) (NS : Slot) (NL : LineageId) : Act :=
  .seq (.write 1 "if_v" (.lit 0)) <|
    .seq (.write 1 (Hw.dcapV t NS) (.lit 1))
      (grantTableTailV e t NS NL)

/-- Peel the architectural result and pc writes around the fixed table
prefix for any register they do not touch. -/
private theorem grantExplicit_run_tables_reg (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (rn : String) (w : Nat)
    (hpc : (rn, w) ∉ (Hw.pcAdvA e).regWrites)
    (hwr : (rn, w) ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) :
    ((grantExplicit e t NS NL).run σ acc).regs rn w =
      ((grantTables e t NS NL).run σ acc).regs rn w := by
  unfold grantExplicit grantTables
  show ((Hw.pcAdvA e).run σ ((Hw.writeReg e Hw.rdE _).run σ _)).regs rn w = _
  rw [frame hpc σ _, frame (show (rn, w) ∉
    (Hw.writeReg e Hw.rdE (Hw.muxFin (fun c =>
      Hw.handleE (Hw.freeSlotIdx c) (Hw.genOfE c (Hw.freeSlotIdx c))
        (.lit 0)) (Hw.descTgt (Hw.readReg e Hw.rs2E)))).regWrites from hwr) σ _]
  rfl

private theorem seq_write_suffix_hit (σ acc : Loom.Hw.St) (rn : String)
    (w : Nat) (v : Expr w) (tail : Act)
    (h : (rn, w) ∉ tail.regWrites) :
    ((Act.seq (.write w rn v) tail).run σ acc).regs rn w = v.eval σ := by
  show (tail.run σ ((Act.write w rn v).run σ acc)).regs rn w = _
  rw [frame h σ _]
  simp [Act.run, RegEnv.set]

private theorem grantTables_capV (σ acc : Loom.Hw.St) (e t : DomainId)
    (NS : Slot) (NL : LineageId) (s : Slot) :
    ((grantTables e t NS NL).run σ acc).regs (Hw.dcapV t s) 1 =
      if s = NS then 1#1 else acc.regs (Hw.dcapV t s) 1 := by
  unfold grantTables
  simp only [Hw.seqAll, Act.run, RegEnv.set]
  by_cases hs : s = NS
  · subst s
    rw [if_pos rfl]
    show ((grantTableTailV e t NS NL).run σ
      ((Act.write 1 (Hw.dcapV t NS) (.lit 1)).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ acc))).regs
        (Hw.dcapV t NS) 1 = 1#1
    rw [frame (show ((Hw.dcapV t NS : String), (1 : Nat)) ∉
      (grantTableTailV e t NS NL).regWrites from by
        exact (by native_decide : ∀ (e t : DomainId) (NS : Slot)
          (NL : LineageId), ((Hw.dcapV t NS : String), (1 : Nat)) ∉
            (grantTableTailV e t NS NL).regWrites) e t NS NL) σ _]
    simp [Act.run, RegEnv.set]
    rfl
  · rw [if_neg hs]
    rw [frame (show ((Hw.dcapV t s : String), (1 : Nat)) ∉
      (grantTableTailV e t NS NL).regWrites from by
        exact (by native_decide : ∀ (e t : DomainId) (NS s : Slot)
          (NL : LineageId), ((Hw.dcapV t s : String), (1 : Nat)) ∉
            (grantTableTailV e t NS NL).regWrites) e t NS s NL) σ _]
    simp only [RegEnv.set]
    rw [if_neg (show ¬Hw.dcapV t s = Hw.dcapV t NS from by
      intro h; apply hs; exact (by native_decide : ∀ (t : DomainId)
        (s NS : Slot), Hw.dcapV t s = Hw.dcapV t NS → s = NS) t s NS h),
      if_neg (show ¬Hw.dcapV t s = "if_v" from by
        exact (by native_decide : ∀ (t : DomainId) (s : Slot),
          Hw.dcapV t s ≠ "if_v") t s)]

private theorem grantExplicit_capV (σ acc : Loom.Hw.St) (e t : DomainId)
    (NS : Slot) (NL : LineageId) (s : Slot) :
    ((grantExplicit e t NS NL).run σ acc).regs (Hw.dcapV t s) 1 =
      if s = NS then 1#1 else acc.regs (Hw.dcapV t s) 1 := by
  rw [grantExplicit_run_tables_reg σ acc e t NS NL (Hw.dcapV t s) 1
    (by exact (by native_decide : ∀ (e t : DomainId) (s : Slot),
      ((Hw.dcapV t s : String), 1) ∉ (Hw.pcAdvA e).regWrites) e t s)
    (by exact (by native_decide : ∀ (e t : DomainId) (s : Slot),
      ((Hw.dcapV t s : String), 1) ∉
        (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) e t s)]
  exact grantTables_capV σ acc e t NS NL s

private theorem grantTables_capKind (σ acc : Loom.Hw.St) (e t : DomainId)
    (NS : Slot) (NL : LineageId) (s : Slot) :
    ((grantTables e t NS NL).run σ acc).regs (Hw.dcapKind t s) 32 =
      if s = NS then
        (Hw.narrowKindE (Hw.grantSel e).kindW
          (Hw.readReg e Hw.rs2E)).eval σ
      else acc.regs (Hw.dcapKind t s) 32 := by
  by_cases hs : s = NS
  · subst s
    rw [if_pos rfl]
    unfold grantTables grantTableTailV
    exact seq_write_suffix_hit σ _ (Hw.dcapKind t NS) 32 _
      (grantTailKind e t NS NL) (by
        exact (by native_decide : ∀ (e t : DomainId) (NS : Slot)
          (NL : LineageId), ((Hw.dcapKind t NS : String), (32 : Nat)) ∉
            (grantTailKind e t NS NL).regWrites) e t NS NL)
  · rw [if_neg hs]
    apply frame
    exact (by native_decide : ∀ (e t : DomainId) (NS s : Slot)
      (NL : LineageId), s ≠ NS → ((Hw.dcapKind t s : String), (32 : Nat)) ∉
        (grantTables e t NS NL).regWrites) e t NS s NL hs

private theorem grantExplicit_capKind (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (s : Slot) :
    ((grantExplicit e t NS NL).run σ acc).regs (Hw.dcapKind t s) 32 =
      if s = NS then
        (Hw.narrowKindE (Hw.grantSel e).kindW
          (Hw.readReg e Hw.rs2E)).eval σ
      else acc.regs (Hw.dcapKind t s) 32 := by
  rw [grantExplicit_run_tables_reg σ acc e t NS NL (Hw.dcapKind t s) 32
    (by exact (by native_decide : ∀ (e t : DomainId) (s : Slot),
      ((Hw.dcapKind t s : String), 32) ∉ (Hw.pcAdvA e).regWrites) e t s)
    (by exact (by native_decide : ∀ (e t : DomainId) (s : Slot),
      ((Hw.dcapKind t s : String), 32) ∉
        (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) e t s)]
  exact grantTables_capKind σ acc e t NS NL s

private theorem grantTables_capLinV (σ acc : Loom.Hw.St) (e t : DomainId)
    (NS : Slot) (NL : LineageId) (s : Slot) :
    ((grantTables e t NS NL).run σ acc).regs (Hw.dcapLinV t s) 1 =
      if s = NS then 1#1 else acc.regs (Hw.dcapLinV t s) 1 := by
  by_cases hs : s = NS
  · subst s
    rw [if_pos rfl]
    unfold grantTables grantTableTailV grantTailKind
    exact seq_write_suffix_hit σ _ (Hw.dcapLinV t NS) 1 _
      (grantTailLinV e t NS NL) (by
        exact (by native_decide : ∀ (e t : DomainId) (NS : Slot)
          (NL : LineageId), ((Hw.dcapLinV t NS : String), (1 : Nat)) ∉
            (grantTailLinV e t NS NL).regWrites) e t NS NL)
  · rw [if_neg hs]
    apply frame
    exact (by native_decide : ∀ (e t : DomainId) (NS s : Slot)
      (NL : LineageId), s ≠ NS → ((Hw.dcapLinV t s : String), (1 : Nat)) ∉
        (grantTables e t NS NL).regWrites) e t NS s NL hs

private theorem grantExplicit_capLinV (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (s : Slot) :
    ((grantExplicit e t NS NL).run σ acc).regs (Hw.dcapLinV t s) 1 =
      if s = NS then 1#1 else acc.regs (Hw.dcapLinV t s) 1 := by
  rw [grantExplicit_run_tables_reg σ acc e t NS NL (Hw.dcapLinV t s) 1
    (by exact (by native_decide : ∀ (e t : DomainId) (s : Slot),
      ((Hw.dcapLinV t s : String), 1) ∉ (Hw.pcAdvA e).regWrites) e t s)
    (by exact (by native_decide : ∀ (e t : DomainId) (s : Slot),
      ((Hw.dcapLinV t s : String), 1) ∉
        (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) e t s)]
  exact grantTables_capLinV σ acc e t NS NL s

private theorem grantTables_capLin (σ acc : Loom.Hw.St) (e t : DomainId)
    (NS : Slot) (NL : LineageId) (s : Slot) :
    ((grantTables e t NS NL).run σ acc).regs (Hw.dcapLin t s) 4 =
      if s = NS then (Hw.freeCellIdx t).eval σ
      else acc.regs (Hw.dcapLin t s) 4 := by
  by_cases hs : s = NS
  · subst s
    rw [if_pos rfl]
    unfold grantTables grantTableTailV grantTailKind grantTailLinV
    exact seq_write_suffix_hit σ _ (Hw.dcapLin t NS) 4 _
      (grantTailLin e t NL) (by
        exact (by native_decide : ∀ (e t : DomainId) (NS : Slot)
          (NL : LineageId), ((Hw.dcapLin t NS : String), (4 : Nat)) ∉
            (grantTailLin e t NL).regWrites) e t NS NL)
  · rw [if_neg hs]
    apply frame
    exact (by native_decide : ∀ (e t : DomainId) (NS s : Slot)
      (NL : LineageId), s ≠ NS → ((Hw.dcapLin t s : String), (4 : Nat)) ∉
        (grantTables e t NS NL).regWrites) e t NS s NL hs

private theorem grantExplicit_capLin (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (s : Slot) :
    ((grantExplicit e t NS NL).run σ acc).regs (Hw.dcapLin t s) 4 =
      if s = NS then (Hw.freeCellIdx t).eval σ
      else acc.regs (Hw.dcapLin t s) 4 := by
  rw [grantExplicit_run_tables_reg σ acc e t NS NL (Hw.dcapLin t s) 4
    (by exact (by native_decide : ∀ (e t : DomainId) (s : Slot),
      ((Hw.dcapLin t s : String), 4) ∉ (Hw.pcAdvA e).regWrites) e t s)
    (by exact (by native_decide : ∀ (e t : DomainId) (s : Slot),
      ((Hw.dcapLin t s : String), 4) ∉
        (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) e t s)]
  exact grantTables_capLin σ acc e t NS NL s

private theorem grantTables_cellV (σ acc : Loom.Hw.St) (e t : DomainId)
    (NS : Slot) (NL : LineageId) (l : LineageId) :
    ((grantTables e t NS NL).run σ acc).regs (Hw.dcellV t l) 1 =
      if l = NL then 1#1 else acc.regs (Hw.dcellV t l) 1 := by
  by_cases hl : l = NL
  · subst l
    rw [if_pos rfl]
    unfold grantTables grantTableTailV grantTailKind grantTailLinV
      grantTailLin
    exact seq_write_suffix_hit σ _ (Hw.dcellV t NL) 1 _
      (grantTailCellV e t NL) (by
        exact (by native_decide : ∀ (e t : DomainId) (NL : LineageId),
          ((Hw.dcellV t NL : String), (1 : Nat)) ∉
            (grantTailCellV e t NL).regWrites) e t NL)
  · rw [if_neg hl]
    apply frame
    exact (by native_decide : ∀ (e t : DomainId) (NS : Slot)
      (NL l : LineageId), l ≠ NL → ((Hw.dcellV t l : String), (1 : Nat)) ∉
        (grantTables e t NS NL).regWrites) e t NS NL l hl

private theorem grantExplicit_cellV (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (l : LineageId) :
    ((grantExplicit e t NS NL).run σ acc).regs (Hw.dcellV t l) 1 =
      if l = NL then 1#1 else acc.regs (Hw.dcellV t l) 1 := by
  rw [grantExplicit_run_tables_reg σ acc e t NS NL (Hw.dcellV t l) 1
    (by exact (by native_decide : ∀ (e t : DomainId) (l : LineageId),
      ((Hw.dcellV t l : String), 1) ∉ (Hw.pcAdvA e).regWrites) e t l)
    (by exact (by native_decide : ∀ (e t : DomainId) (l : LineageId),
      ((Hw.dcellV t l : String), 1) ∉
        (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) e t l)]
  exact grantTables_cellV σ acc e t NS NL l

private theorem grantTables_cellPar (σ acc : Loom.Hw.St) (e t : DomainId)
    (NS : Slot) (NL : LineageId) (l : LineageId) :
    ((grantTables e t NS NL).run σ acc).regs (Hw.dcellPar t l) 14 =
      if l = NL then
        (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
          (Hw.grantSel e).gen).eval σ
      else acc.regs (Hw.dcellPar t l) 14 := by
  by_cases hl : l = NL
  · subst l
    rw [if_pos rfl]
    unfold grantTables grantTableTailV grantTailKind grantTailLinV
      grantTailLin grantTailCellV
    simp [Act.run, RegEnv.set]
  · rw [if_neg hl]
    apply frame
    exact (by native_decide : ∀ (e t : DomainId) (NS : Slot)
      (NL l : LineageId), l ≠ NL → ((Hw.dcellPar t l : String), (14 : Nat)) ∉
        (grantTables e t NS NL).regWrites) e t NS NL l hl

private theorem grantExplicit_cellPar (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (l : LineageId) :
    ((grantExplicit e t NS NL).run σ acc).regs (Hw.dcellPar t l) 14 =
      if l = NL then
        (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
          (Hw.grantSel e).gen).eval σ
      else acc.regs (Hw.dcellPar t l) 14 := by
  rw [grantExplicit_run_tables_reg σ acc e t NS NL (Hw.dcellPar t l) 14
    (by exact (by native_decide : ∀ (e t : DomainId) (l : LineageId),
      ((Hw.dcellPar t l : String), 14) ∉ (Hw.pcAdvA e).regWrites) e t l)
    (by exact (by native_decide : ∀ (e t : DomainId) (l : LineageId),
      ((Hw.dcellPar t l : String), 14) ∉
        (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) e t l)]
  exact grantTables_cellPar σ acc e t NS NL l

private theorem quietCap_notin_grantExplicit (x e t : DomainId)
    (NS : Slot) (NL : LineageId) :
    ∀ q ∈ domQuietNamesCap x, q ∉ (grantExplicit e t NS NL).regWrites := by
  exact (by native_decide : ∀ (x e t : DomainId) (NS : Slot)
    (NL : LineageId), ∀ q ∈ domQuietNamesCap x,
      q ∉ (grantExplicit e t NS NL).regWrites) x e t NS NL

private theorem absDom_grantExplicit_caps (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (kind : CapKind)
    (hnl : (Hw.freeCellIdx t).eval σ = BitVec.ofNat 4 NL.val)
    (hkind : (Hw.narrowKindE (Hw.grantSel e).kindW
      (Hw.readReg e Hw.rs2E)).eval σ = Hw.encKind kind) :
    (Hw.absDom ((grantExplicit e t NS NL).run σ acc) t).caps =
      Loom.Fun.update (Hw.absDom acc t).caps NS
        (some { kind := kind, lineage := some NL }) := by
  funext s
  show (if ((grantExplicit e t NS NL).run σ acc).regs
      (Hw.dcapV t s) 1 = 1 then
        some (CapEntry.mk (Hw.decKind
          (((grantExplicit e t NS NL).run σ acc).regs
            (Hw.dcapKind t s) 32))
          (if ((grantExplicit e t NS NL).run σ acc).regs
            (Hw.dcapLinV t s) 1 = 1
            then some (finOfBv (by decide)
              (((grantExplicit e t NS NL).run σ acc).regs
                (Hw.dcapLin t s) 4)) else none))
      else none) = _
  by_cases hs : s = NS
  · subst s
    rw [Loom.Fun.update_same, grantExplicit_capV, if_pos rfl,
      grantExplicit_capKind, if_pos rfl, grantExplicit_capLinV, if_pos rfl,
      grantExplicit_capLin, if_pos rfl, hkind, decKind_encKind, hnl,
      finOfBv_ofNat4]
    simp
  · rw [Loom.Fun.update_ne _ _ _ _ hs, grantExplicit_capV, if_neg hs,
      grantExplicit_capKind, if_neg hs, grantExplicit_capLinV, if_neg hs,
      grantExplicit_capLin, if_neg hs]
    rfl

private theorem absDom_grantExplicit_lineage (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (parent : CapRef)
    (hparent : (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
      (Hw.grantSel e).gen).eval σ = Hw.encRef parent) :
    (Hw.absDom ((grantExplicit e t NS NL).run σ acc) t).lineage =
      Loom.Fun.update (Hw.absDom acc t).lineage NL
        (some { parent := parent }) := by
  funext l
  show (if ((grantExplicit e t NS NL).run σ acc).regs
      (Hw.dcellV t l) 1 = 1 then
        some (LineageCell.mk (Hw.decRef
          (((grantExplicit e t NS NL).run σ acc).regs
            (Hw.dcellPar t l) 14))) else none) = _
  by_cases hl : l = NL
  · subst l
    rw [Loom.Fun.update_same, grantExplicit_cellV, if_pos rfl,
      grantExplicit_cellPar, if_pos rfl, hparent, decRef_encRef]
    simp
  · rw [Loom.Fun.update_ne _ _ _ _ hl, grantExplicit_cellV, if_neg hl,
      grantExplicit_cellPar, if_neg hl]
    rfl

private theorem absDom_grantExplicit_target (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId)
    (kind : CapKind) (parent : CapRef)
    (hnl : (Hw.freeCellIdx t).eval σ = BitVec.ofNat 4 NL.val)
    (hkind : (Hw.narrowKindE (Hw.grantSel e).kindW
      (Hw.readReg e Hw.rs2E)).eval σ = Hw.encKind kind)
    (hparent : (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
      (Hw.grantSel e).gen).eval σ = Hw.encRef parent) :
    Hw.absDom ((grantExplicit e t NS NL).run σ acc) t =
      { Hw.absDom acc t with
        regs := fun r => ((grantExplicit e t NS NL).run σ acc).regs
          (Hw.dreg t r) 32
        pc := ((grantExplicit e t NS NL).run σ acc).regs (Hw.dpc t) 12
        caps := Loom.Fun.update (Hw.absDom acc t).caps NS
          (some { kind := kind, lineage := some NL })
        lineage := Loom.Fun.update (Hw.absDom acc t).lineage NL
          (some { parent := parent }) } := by
  rw [absDom_regpccap t (fun q hq =>
    frame (quietCap_notin_grantExplicit t e t NS NL q hq) σ _)]
  apply domainState_ext'
  · rfl
  · rfl
  · exact absDom_grantExplicit_caps σ acc e t NS NL kind hnl hkind
  · rfl
  · exact absDom_grantExplicit_lineage σ acc e t NS NL parent hparent
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## Issuer register and pc faces -/

/-- The fixed table-writing prefix does not touch architectural registers. -/
private theorem grantTables_dreg (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (r : RegId) :
    ((grantTables e t NS NL).run σ acc).regs (Hw.dreg e r) 32 =
      acc.regs (Hw.dreg e r) 32 := by
  rw [frame (show ((Hw.dreg e r : String), (32 : Nat)) ∉
    (grantTables e t NS NL).regWrites from by
      exact (by native_decide : ∀ (e t : DomainId) (NS : Slot)
        (NL : LineageId) (r : RegId),
          ((Hw.dreg e r : String), (32 : Nat)) ∉
            (grantTables e t NS NL).regWrites) e t NS NL r) σ acc]

/-- The issuing domain receives exactly the returned target-relative handle,
with the architectural hardwired-r0 behavior. -/
private theorem grantExplicit_reg_final (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId)
    (rd : RegId) (v : BitVec 32)
    (hrd : (Hw.rdE.eval σ).toNat = rd.val)
    (hval : (Hw.muxFin (fun c => Hw.handleE (Hw.freeSlotIdx c)
        (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
      (Hw.descTgt (Hw.readReg e Hw.rs2E))).eval σ = v)
    (r : RegId) :
    ((grantExplicit e t NS NL).run σ acc).regs (Hw.dreg e r) 32 =
      ((Hw.absDom acc e).setReg rd v).regs r := by
  unfold grantExplicit
  change ((Hw.pcAdvA e).run σ
    ((Hw.writeReg e Hw.rdE
      (Hw.muxFin (fun c => Hw.handleE (Hw.freeSlotIdx c)
        (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
        (Hw.descTgt (Hw.readReg e Hw.rs2E)))).run σ
      ((grantTables e t NS NL).run σ acc))).regs (Hw.dreg e r) 32 = _
  rw [frame (show ((Hw.dreg e r : String), (32 : Nat)) ∉
    (Hw.pcAdvA e).regWrites from by
      fin_cases e <;> fin_cases r <;> decide +kernel) σ _]
  rw [setReg_regs]
  have hacc : ((grantTables e t NS NL).run σ acc).regs
      (Hw.dreg e r) 32 = (Hw.absDom acc e).regs r := by
    rw [grantTables_dreg]
    rfl
  by_cases h0 : rd = (0 : RegId)
  · rw [if_pos h0]
    rw [writeReg_run_of_zero σ _ e Hw.rdE _ (by rw [hrd, h0]; rfl)]
    exact hacc
  · rw [if_neg h0]
    rw [writeReg_run_of_nz σ _ e Hw.rdE _ rd hrd.symm
      (fun hc => h0 (Fin.ext hc))]
    show (RegEnv.set _ (Hw.dreg e rd) _) (Hw.dreg e r) 32 = _
    simp only [RegEnv.set]
    by_cases hr : r = rd
    · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial, hval]
    · rw [if_neg (fun hc => hr (dreg_inj e r rd hc)), if_neg hr, hacc]

/-- The final grant action advances only the issuing domain's pc. The value
is sampled from the cycle input, as for every hardware pc advance. -/
private theorem grantExplicit_pc_final (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) :
    ((grantExplicit e t NS NL).run σ acc).regs (Hw.dpc e) 12 =
      σ.regs (Hw.dpc e) 12 + 1 := by
  unfold grantExplicit
  change (RegEnv.set _ (Hw.dpc e)
      ((Expr.add (Hw.rPc e) (.lit 1)).eval σ)) (Hw.dpc e) 12 = _
  simp only [RegEnv.set]
  rw [if_pos trivial]
  rfl

/-- When issuer and target coincide, the result/pc update and the fresh
capability/lineage update compose in one domain record. -/
theorem absDom_grantExplicit_same (σ acc : Loom.Hw.St)
    (e : DomainId) (NS : Slot) (NL : LineageId)
    (kind : CapKind) (parent : CapRef) (rd : RegId) (v : BitVec 32)
    (hnl : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL.val)
    (hkind : (Hw.narrowKindE (Hw.grantSel e).kindW
      (Hw.readReg e Hw.rs2E)).eval σ = Hw.encKind kind)
    (hparent : (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
      (Hw.grantSel e).gen).eval σ = Hw.encRef parent)
    (hrd : (Hw.rdE.eval σ).toNat = rd.val)
    (hval : (Hw.muxFin (fun c => Hw.handleE (Hw.freeSlotIdx c)
        (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
      (Hw.descTgt (Hw.readReg e Hw.rs2E))).eval σ = v)
    (hpc : σ.regs (Hw.dpc e) 12 = acc.regs (Hw.dpc e) 12) :
    Hw.absDom ((grantExplicit e e NS NL).run σ acc) e =
      ({ Hw.absDom acc e with
        pc := (Hw.absDom acc e).pc + 1
        caps := Loom.Fun.update (Hw.absDom acc e).caps NS
          (some { kind := kind, lineage := some NL })
        lineage := Loom.Fun.update (Hw.absDom acc e).lineage NL
          (some { parent := parent }) }).setReg rd v := by
  rw [absDom_grantExplicit_target σ acc e e NS NL kind parent hnl hkind
    hparent]
  apply domainState_ext'
  · funext r
    simpa only [setReg_regs] using
      (grantExplicit_reg_final σ acc e e NS NL rd v hrd hval r)
  · rw [setReg_pc, grantExplicit_pc_final, hpc]
    rfl
  · rw [setReg_caps]
  · rw [setReg_slotGen]
  · rw [setReg_lineage]
  · rw [setReg_regions]
  · rw [setReg_run]
  · rw [setReg_serving]
  · rw [setReg_cause]
  · rw [setReg_budget]
  · rw [setReg_maxDonation]

private theorem quiet_notin_grantExplicit_owner_ne (e t : DomainId)
    (hne : e ≠ t) (NS : Slot) (NL : LineageId) :
    ∀ q ∈ domQuietNames e, q ∉ (grantExplicit e t NS NL).regWrites := by
  fin_cases e <;> fin_cases t <;>
    first
      | exact absurd rfl hne
      | native_decide +revert

/-- For a cross-domain grant, the issuer changes only by `rd` and pc. -/
theorem absDom_grantExplicit_owner_ne (σ acc : Loom.Hw.St)
    (e t : DomainId) (hne : e ≠ t) (NS : Slot) (NL : LineageId)
    (rd : RegId) (v : BitVec 32)
    (hrd : (Hw.rdE.eval σ).toNat = rd.val)
    (hval : (Hw.muxFin (fun c => Hw.handleE (Hw.freeSlotIdx c)
        (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
      (Hw.descTgt (Hw.readReg e Hw.rs2E))).eval σ = v)
    (hpc : σ.regs (Hw.dpc e) 12 = acc.regs (Hw.dpc e) 12) :
    Hw.absDom ((grantExplicit e t NS NL).run σ acc) e =
      ({ Hw.absDom acc e with pc := (Hw.absDom acc e).pc + 1 }).setReg
        rd v := by
  rw [absDom_regpc e (fun q hq =>
    frame (quiet_notin_grantExplicit_owner_ne e t hne NS NL q hq) σ _)]
  apply domainState_ext'
  · funext r
    simpa only [setReg_regs] using
      (grantExplicit_reg_final σ acc e t NS NL rd v hrd hval r)
  · rw [setReg_pc, grantExplicit_pc_final, hpc]
    rfl
  · rw [setReg_caps]
  · rw [setReg_slotGen]
  · rw [setReg_lineage]
  · rw [setReg_regions]
  · rw [setReg_run]
  · rw [setReg_serving]
  · rw [setReg_cause]
  · rw [setReg_budget]
  · rw [setReg_maxDonation]

private theorem grantExplicit_target_dreg_ne (e t : DomainId) (hne : e ≠ t)
    (NS : Slot) (NL : LineageId) (r : RegId) :
    ((Hw.dreg t r : String), (32 : Nat)) ∉
      (grantExplicit e t NS NL).regWrites := by
  fin_cases e <;> fin_cases t <;>
    first
      | exact absurd rfl hne
      | fin_cases r <;> native_decide +revert

private theorem grantExplicit_target_dpc_ne (e t : DomainId) (hne : e ≠ t)
    (NS : Slot) (NL : LineageId) :
    ((Hw.dpc t : String), (12 : Nat)) ∉
      (grantExplicit e t NS NL).regWrites := by
  fin_cases e <;> fin_cases t <;>
    first
      | exact absurd rfl hne
      | native_decide +revert

/-- For a cross-domain grant, the target changes only by the fresh
capability and lineage-cell updates. -/
theorem absDom_grantExplicit_target_ne (σ acc : Loom.Hw.St)
    (e t : DomainId) (hne : e ≠ t) (NS : Slot) (NL : LineageId)
    (kind : CapKind) (parent : CapRef)
    (hnl : (Hw.freeCellIdx t).eval σ = BitVec.ofNat 4 NL.val)
    (hkind : (Hw.narrowKindE (Hw.grantSel e).kindW
      (Hw.readReg e Hw.rs2E)).eval σ = Hw.encKind kind)
    (hparent : (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
      (Hw.grantSel e).gen).eval σ = Hw.encRef parent) :
    Hw.absDom ((grantExplicit e t NS NL).run σ acc) t =
      { Hw.absDom acc t with
        caps := Loom.Fun.update (Hw.absDom acc t).caps NS
          (some { kind := kind, lineage := some NL })
        lineage := Loom.Fun.update (Hw.absDom acc t).lineage NL
          (some { parent := parent }) } := by
  rw [absDom_grantExplicit_target σ acc e t NS NL kind parent hnl hkind
    hparent]
  apply domainState_ext'
  · funext r
    exact frame (grantExplicit_target_dreg_ne e t hne NS NL r) σ acc
  · exact frame (grantExplicit_target_dpc_ne e t hne NS NL) σ acc
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
