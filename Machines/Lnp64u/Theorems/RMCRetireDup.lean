-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireMove
import Machines.Lnp64u.Theorems.RMCRetireCapShared
import Machines.Lnp64u.Logic.Tombstone

/-!
# R-MC retirement: `cap_dup` support (NEXTSTEPS tier 2, stage D1)

Free-slot/free-cell priority-encoder bridges: the circuits' foldr-mux
trees against the spec's lowest-index `find?`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000




/-! ## Install-face infrastructure -/

/-- The full `cap_dup` core act (dispatch `if_v` clear + the ok action). -/
def dupFull (e : DomainId) : Act :=
  .seq (.write 1 "if_v" (.lit 0))
    (Hw.seqAll
      [ Hw.installA e (Hw.freeSlotIdx e)
          (.mux (Hw.kIsMem (Hw.dupSel e).kindW)
            (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
            (Hw.dupSel e).kindW)
          (.lit 1) (Hw.freeCellIdx e)
          (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen),
        Hw.writeReg e Hw.rdE (Hw.handleE (Hw.freeSlotIdx e)
          (Hw.genOfE e (Hw.freeSlotIdx e))
          (Hw.field (Hw.dupSel e).kindW 0 1)),
        Hw.pcAdvA e ])


private theorem quietCap_notin_dup (x e : DomainId) :
    ∀ q ∈ domQuietNamesCap x, q ∉ (dupFull e).regWrites := by
  fin_cases x <;> fin_cases e <;> decide +kernel

private theorem read_notin_dup_ne (x e : DomainId) (hne : x ≠ e) :
    ∀ q ∈ domReadNames x, q ∉ (dupFull e).regWrites := by
  fin_cases x <;> fin_cases e <;>
    first
      | exact absurd rfl hne
      | decide +kernel

private theorem gate_notin_dup (g : GateId) (e : DomainId) :
    ∀ q ∈ gateReadNames g, q ∉ (dupFull e).regWrites := by
  fin_cases g <;> fin_cases e <;> decide +kernel

private theorem ifv_notin_dupX (e : DomainId) :
    (("if_v" : String), (1 : Nat)) ∉
      (Hw.seqAll
        [ Hw.installA e (Hw.freeSlotIdx e)
            (.mux (Hw.kIsMem (Hw.dupSel e).kindW)
              (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
              (Hw.dupSel e).kindW)
            (.lit 1) (Hw.freeCellIdx e)
            (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen),
          Hw.writeReg e Hw.rdE (Hw.handleE (Hw.freeSlotIdx e)
            (Hw.genOfE e (Hw.freeSlotIdx e))
            (Hw.field (Hw.dupSel e).kindW 0 1)),
          Hw.pcAdvA e ]).regWrites := by
  fin_cases e <;> decide +kernel

/-- A successful duplicate install leaves every non-owner abstract domain
unchanged from the post-refill accumulator. -/
private theorem absDom_dupFull_ne (m : Manifest) (σ : Loom.Hw.St)
    (e x : DomainId) (hne : x ≠ e) :
    Hw.absDom ((dupFull e).run σ ((Hw.refillAct m).run σ σ)) x =
      Hw.absDom ((Hw.refillAct m).run σ σ) x := by
  apply absDom_congr
  intro p hp
  exact frame (read_notin_dup_ne x e hne p hp) σ _

/-- A successful duplicate install does not alter any gate record. -/
private theorem absGate_dupFull (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (g : GateId) :
    Hw.absGate ((dupFull e).run σ ((Hw.refillAct m).run σ σ)) g =
      Hw.absGate ((Hw.refillAct m).run σ σ) g := by
  apply absGate_congr
  intro p hp
  exact frame (gate_notin_dup g e p hp) σ _



/-! ## `dupFull` register walks -/

/-- Peel the trailing `writeReg`/`pcAdvA` and the leading `if_v` clear
around `installA`, for any non-`dreg`/`dpc`/`if_v` register. -/
private theorem dupFull_run_inst (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (rn : String) (w : Nat)
    (hwr : (rn, w) ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites)
    (hpc : ¬(rn = Hw.dpc e))
    (hifv : ¬(rn = "if_v")) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs rn w
      = (((Hw.seqAll ((List.finRange numLineage).map fun l' => Act.ite (.and (.lit 1) (.eq (Hw.freeCellIdx e) (Hw.lLit l'))) (.seq (.write 1 (Hw.dcellV e l') (.lit 1)) (.write 14 (Hw.dcellPar e l') (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen))) .skip))).run σ (((Hw.seqAll ((List.finRange numSlots).map fun s' => Act.ite (.eq (Hw.freeSlotIdx e) (Hw.sLit s')) (Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1), .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW), .write 1 (Hw.dcapLinV e s') (.lit 1), .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) .skip))).run σ
          ((Act.write 1 "if_v" (.lit 0)).run σ
            ((Hw.refillAct m).run σ σ)))).regs rn w := by
  show ((Hw.pcAdvA e).run σ
    ((Hw.writeReg e Hw.rdE (Hw.handleE (Hw.freeSlotIdx e) (Hw.genOfE e (Hw.freeSlotIdx e)) (Hw.field (Hw.dupSel e).kindW 0 1))).run σ
      (((Hw.seqAll ((List.finRange numLineage).map fun l' => Act.ite (.and (.lit 1) (.eq (Hw.freeCellIdx e) (Hw.lLit l'))) (.seq (.write 1 (Hw.dcellV e l') (.lit 1)) (.write 14 (Hw.dcellPar e l') (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen))) .skip))).run σ (((Hw.seqAll ((List.finRange numSlots).map fun s' => Act.ite (.eq (Hw.freeSlotIdx e) (Hw.sLit s')) (Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1), .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW), .write 1 (Hw.dcapLinV e s') (.lit 1), .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) .skip))).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ
          ((Hw.refillAct m).run σ σ)))))).regs rn w = _
  rw [frame (fun hm => hpc (congrArg Prod.fst (List.mem_singleton.mp hm)))
    σ _]
  rw [frame (show (rn, w)
      ∉ (Hw.writeReg e Hw.rdE (Hw.handleE (Hw.freeSlotIdx e) (Hw.genOfE e (Hw.freeSlotIdx e)) (Hw.field (Hw.dupSel e).kindW 0 1))).regWrites from hwr) σ _]

/-- The capability-table registers through a fired `dupFull`. -/
private theorem dupFull_capV (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS2 : Slot)
    (hidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS2.val)
    (s : Slot) :
    (((Hw.seqAll ((List.finRange numSlots).map fun s' => Act.ite (.eq (Hw.freeSlotIdx e) (Hw.sLit s')) (Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1), .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW), .write 1 (Hw.dcapLinV e s') (.lit 1), .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) .skip))).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ
          ((Hw.refillAct m).run σ σ))).regs (Hw.dcapV e s) 1
      = if s = NS2 then 1#1 else σ.regs (Hw.dcapV e s) 1 := by
  rw [seqAll_ite_run_unique σ _
    (fun s' : Slot => Expr.eq (Hw.freeSlotIdx e) (Hw.sLit s'))
    (fun s' : Slot => Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1),
      .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW),
      .write 1 (Hw.dcapLinV e s') (.lit 1),
      .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) NS2
    (by
        show (Expr.eq (Hw.freeSlotIdx e) (Hw.sLit NS2)).eval σ = 1#1
        rw [eqE_eval, hidx]
        rfl)
      (fun j hj => by
        intro hc0
        have hc : (Expr.eq (Hw.freeSlotIdx e) (Hw.sLit j)).eval σ = 1#1 := hc0
        rw [eqE_eval, hidx] at hc
        apply hj
        apply Fin.ext
        have : (BitVec.ofNat 4 NS2.val).toNat
            = (BitVec.ofNat 4 j.val).toNat := by rw [hc]; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show j.val < 2 ^ 4 from by
            have := j.isLt; omega),
          Nat.mod_eq_of_lt (show NS2.val < 2 ^ 4 from by
            have := NS2.isLt; omega)] at this
        omega)
    _ (List.mem_finRange NS2) (List.nodup_finRange _)]
  show (RegEnv.set (RegEnv.set (RegEnv.set (RegEnv.set _
      (Hw.dcapV e NS2) ((Expr.lit 1).eval σ))
      (Hw.dcapKind e NS2) ((Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW).eval σ))
      (Hw.dcapLinV e NS2) ((Expr.lit 1).eval σ))
      (Hw.dcapLin e NS2) ((Hw.freeCellIdx e).eval σ))
    (Hw.dcapV e s) 1 = _
  simp only [RegEnv.set]
  rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
    ¬(Hw.dcapV e s1 = Hw.dcapLin e s2)) e s NS2)]
  rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
    ¬(Hw.dcapV e s1 = Hw.dcapLinV e s2)) e s NS2)]
  rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
    ¬(Hw.dcapV e s1 = Hw.dcapKind e s2)) e s NS2)]
  by_cases hs : s = NS2
  · rw [if_pos (by rw [hs]), if_pos hs]
    rfl
  · rw [if_neg (fun hc => hs ((by decide +kernel :
      ∀ (e : DomainId) (s1 s2 : Slot),
        Hw.dcapV e s1 = Hw.dcapV e s2 → s1 = s2) e s NS2 hc)), if_neg hs]
    rw [frame (fun hm => absurd
      (congrArg Prod.fst (List.mem_singleton.mp hm))
      ((by decide +kernel : ∀ (e : DomainId) (s' : Slot),
        ¬(Hw.dcapV e s' = "if_v")) e s)) σ _]
    exact refill_pres m σ ((by decide +kernel : ∀ (e : DomainId) (s' : Slot),
      ((Hw.dcapV e s' : String), (1 : Nat)) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) e s)


private theorem dupFull_dcapKind (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS2 : Slot)
    (hidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS2.val)
    (s : Slot) :
    (((Hw.seqAll ((List.finRange numSlots).map fun s' => Act.ite (.eq (Hw.freeSlotIdx e) (Hw.sLit s')) (Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1), .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW), .write 1 (Hw.dcapLinV e s') (.lit 1), .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) .skip))).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ
          ((Hw.refillAct m).run σ σ))).regs (Hw.dcapKind e s) 32
      = if s = NS2 then ((Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW).eval σ) else σ.regs (Hw.dcapKind e s) 32 := by
  rw [seqAll_ite_run_unique σ _
    (fun s' : Slot => Expr.eq (Hw.freeSlotIdx e) (Hw.sLit s'))
    (fun s' : Slot => Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1),
      .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW),
      .write 1 (Hw.dcapLinV e s') (.lit 1),
      .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) NS2
    (by
        show (Expr.eq (Hw.freeSlotIdx e) (Hw.sLit NS2)).eval σ = 1#1
        rw [eqE_eval, hidx]
        rfl)
      (fun j hj => by
        intro hc0
        have hc : (Expr.eq (Hw.freeSlotIdx e) (Hw.sLit j)).eval σ
            = 1#1 := hc0
        rw [eqE_eval, hidx] at hc
        apply hj
        apply Fin.ext
        have : (BitVec.ofNat 4 NS2.val).toNat
            = (BitVec.ofNat 4 j.val).toNat := by rw [hc]; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show j.val < 2 ^ 4 from by
            have := j.isLt; omega),
          Nat.mod_eq_of_lt (show NS2.val < 2 ^ 4 from by
            have := NS2.isLt; omega)] at this
        omega)
    _ (List.mem_finRange NS2) (List.nodup_finRange _)]
  show (RegEnv.set (RegEnv.set (RegEnv.set (RegEnv.set _
      (Hw.dcapV e NS2) ((Expr.lit 1).eval σ))
      (Hw.dcapKind e NS2) ((Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW).eval σ))
      (Hw.dcapLinV e NS2) ((Expr.lit 1).eval σ))
      (Hw.dcapLin e NS2) ((Hw.freeCellIdx e).eval σ))
    (Hw.dcapKind e s) 32 = _
  simp only [RegEnv.set]
  rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
    ¬(Hw.dcapKind e s1 = Hw.dcapLin e s2)) e s NS2)]
  rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
    ¬(Hw.dcapKind e s1 = Hw.dcapLinV e s2)) e s NS2)]
  by_cases hs : s = NS2
  · rw [if_pos (by rw [hs]), if_pos hs]
    rfl
  · rw [if_neg (fun hc => hs ((by decide +kernel :
      ∀ (e : DomainId) (s1 s2 : Slot),
        Hw.dcapKind e s1 = Hw.dcapKind e s2 → s1 = s2) e s NS2 hc)), if_neg hs]
    rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
      ¬(Hw.dcapKind e s1 = Hw.dcapV e s2)) e s NS2)]
    rw [frame (fun hm => absurd
      (congrArg Prod.fst (List.mem_singleton.mp hm))
      ((by decide +kernel : ∀ (e : DomainId) (s' : Slot),
        ¬(Hw.dcapKind e s' = "if_v")) e s)) σ _]
    exact refill_pres m σ ((by decide +kernel :
      ∀ (e : DomainId) (s' : Slot),
      ((Hw.dcapKind e s' : String), (32 : Nat)) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) e s)

private theorem dupFull_dcapLinV (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS2 : Slot)
    (hidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS2.val)
    (s : Slot) :
    (((Hw.seqAll ((List.finRange numSlots).map fun s' => Act.ite (.eq (Hw.freeSlotIdx e) (Hw.sLit s')) (Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1), .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW), .write 1 (Hw.dcapLinV e s') (.lit 1), .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) .skip))).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ
          ((Hw.refillAct m).run σ σ))).regs (Hw.dcapLinV e s) 1
      = if s = NS2 then (1#1) else σ.regs (Hw.dcapLinV e s) 1 := by
  rw [seqAll_ite_run_unique σ _
    (fun s' : Slot => Expr.eq (Hw.freeSlotIdx e) (Hw.sLit s'))
    (fun s' : Slot => Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1),
      .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW),
      .write 1 (Hw.dcapLinV e s') (.lit 1),
      .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) NS2
    (by
        show (Expr.eq (Hw.freeSlotIdx e) (Hw.sLit NS2)).eval σ = 1#1
        rw [eqE_eval, hidx]
        rfl)
      (fun j hj => by
        intro hc0
        have hc : (Expr.eq (Hw.freeSlotIdx e) (Hw.sLit j)).eval σ
            = 1#1 := hc0
        rw [eqE_eval, hidx] at hc
        apply hj
        apply Fin.ext
        have : (BitVec.ofNat 4 NS2.val).toNat
            = (BitVec.ofNat 4 j.val).toNat := by rw [hc]; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show j.val < 2 ^ 4 from by
            have := j.isLt; omega),
          Nat.mod_eq_of_lt (show NS2.val < 2 ^ 4 from by
            have := NS2.isLt; omega)] at this
        omega)
    _ (List.mem_finRange NS2) (List.nodup_finRange _)]
  show (RegEnv.set (RegEnv.set (RegEnv.set (RegEnv.set _
      (Hw.dcapV e NS2) ((Expr.lit 1).eval σ))
      (Hw.dcapKind e NS2) ((Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW).eval σ))
      (Hw.dcapLinV e NS2) ((Expr.lit 1).eval σ))
      (Hw.dcapLin e NS2) ((Hw.freeCellIdx e).eval σ))
    (Hw.dcapLinV e s) 1 = _
  simp only [RegEnv.set]
  rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
    ¬(Hw.dcapLinV e s1 = Hw.dcapLin e s2)) e s NS2)]
  by_cases hs : s = NS2
  · rw [if_pos (by rw [hs]), if_pos hs]
    rfl
  · rw [if_neg (fun hc => hs ((by decide +kernel :
      ∀ (e : DomainId) (s1 s2 : Slot),
        Hw.dcapLinV e s1 = Hw.dcapLinV e s2 → s1 = s2) e s NS2 hc)), if_neg hs]
    rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
      ¬(Hw.dcapLinV e s1 = Hw.dcapKind e s2)) e s NS2)]
    rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
      ¬(Hw.dcapLinV e s1 = Hw.dcapV e s2)) e s NS2)]
    rw [frame (fun hm => absurd
      (congrArg Prod.fst (List.mem_singleton.mp hm))
      ((by decide +kernel : ∀ (e : DomainId) (s' : Slot),
        ¬(Hw.dcapLinV e s' = "if_v")) e s)) σ _]
    exact refill_pres m σ ((by decide +kernel :
      ∀ (e : DomainId) (s' : Slot),
      ((Hw.dcapLinV e s' : String), (1 : Nat)) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) e s)

private theorem dupFull_dcapLin (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS2 : Slot)
    (hidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS2.val)
    (s : Slot) :
    (((Hw.seqAll ((List.finRange numSlots).map fun s' => Act.ite (.eq (Hw.freeSlotIdx e) (Hw.sLit s')) (Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1), .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW), .write 1 (Hw.dcapLinV e s') (.lit 1), .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) .skip))).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ
          ((Hw.refillAct m).run σ σ))).regs (Hw.dcapLin e s) 4
      = if s = NS2 then ((Hw.freeCellIdx e).eval σ) else σ.regs (Hw.dcapLin e s) 4 := by
  rw [seqAll_ite_run_unique σ _
    (fun s' : Slot => Expr.eq (Hw.freeSlotIdx e) (Hw.sLit s'))
    (fun s' : Slot => Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1),
      .write 32 (Hw.dcapKind e s') (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW),
      .write 1 (Hw.dcapLinV e s') (.lit 1),
      .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)]) NS2
    (by
        show (Expr.eq (Hw.freeSlotIdx e) (Hw.sLit NS2)).eval σ = 1#1
        rw [eqE_eval, hidx]
        rfl)
      (fun j hj => by
        intro hc0
        have hc : (Expr.eq (Hw.freeSlotIdx e) (Hw.sLit j)).eval σ
            = 1#1 := hc0
        rw [eqE_eval, hidx] at hc
        apply hj
        apply Fin.ext
        have : (BitVec.ofNat 4 NS2.val).toNat
            = (BitVec.ofNat 4 j.val).toNat := by rw [hc]; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show j.val < 2 ^ 4 from by
            have := j.isLt; omega),
          Nat.mod_eq_of_lt (show NS2.val < 2 ^ 4 from by
            have := NS2.isLt; omega)] at this
        omega)
    _ (List.mem_finRange NS2) (List.nodup_finRange _)]
  show (RegEnv.set (RegEnv.set (RegEnv.set (RegEnv.set _
      (Hw.dcapV e NS2) ((Expr.lit 1).eval σ))
      (Hw.dcapKind e NS2) ((Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW) (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW).eval σ))
      (Hw.dcapLinV e NS2) ((Expr.lit 1).eval σ))
      (Hw.dcapLin e NS2) ((Hw.freeCellIdx e).eval σ))
    (Hw.dcapLin e s) 4 = _
  simp only [RegEnv.set]
  by_cases hs : s = NS2
  · rw [if_pos (by rw [hs]), if_pos hs]
    rfl
  · rw [if_neg (fun hc => hs ((by decide +kernel :
      ∀ (e : DomainId) (s1 s2 : Slot),
        Hw.dcapLin e s1 = Hw.dcapLin e s2 → s1 = s2) e s NS2 hc)), if_neg hs]
    rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
      ¬(Hw.dcapLin e s1 = Hw.dcapLinV e s2)) e s NS2)]
    rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
      ¬(Hw.dcapLin e s1 = Hw.dcapKind e s2)) e s NS2)]
    rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (s1 s2 : Slot),
      ¬(Hw.dcapLin e s1 = Hw.dcapV e s2)) e s NS2)]
    rw [frame (fun hm => absurd
      (congrArg Prod.fst (List.mem_singleton.mp hm))
      ((by decide +kernel : ∀ (e : DomainId) (s' : Slot),
        ¬(Hw.dcapLin e s' = "if_v")) e s)) σ _]
    exact refill_pres m σ ((by decide +kernel :
      ∀ (e : DomainId) (s' : Slot),
      ((Hw.dcapLin e s' : String), (4 : Nat)) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) e s)

private theorem dupFull_dcellV (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NL2 : LineageId)
    (hidx : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL2.val)
    (acc : Loom.Hw.St) (hacc : ∀ l' : LineageId,
      acc.regs (Hw.dcellV e l') 1 = σ.regs (Hw.dcellV e l') 1)
    (l : LineageId) :
    (((Hw.seqAll ((List.finRange numLineage).map fun l' => Act.ite (.and (.lit 1) (.eq (Hw.freeCellIdx e) (Hw.lLit l'))) (.seq (.write 1 (Hw.dcellV e l') (.lit 1)) (.write 14 (Hw.dcellPar e l') (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen))) .skip))).run σ acc).regs (Hw.dcellV e l) 1
      = if l = NL2 then (1#1) else σ.regs (Hw.dcellV e l) 1 := by
  rw [seqAll_ite_run_unique σ _
    (fun l' : LineageId => Expr.and (Expr.lit 1)
      (Expr.eq (Hw.freeCellIdx e) (Hw.lLit l')))
    (fun l' : LineageId => Act.seq (.write 1 (Hw.dcellV e l') (.lit 1))
      (.write 14 (Hw.dcellPar e l') (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen))) NL2
    (by
        have h1 : (Expr.eq (Hw.freeCellIdx e) (Hw.lLit NL2)).eval σ
            = 1#1 := by
          rw [eqE_eval, hidx]
          rfl
        show ((Expr.lit 1).eval σ &&&
          (Expr.eq (Hw.freeCellIdx e) (Hw.lLit NL2)).eval σ) = 1#1
        rw [h1]
        change (1#1 &&& 1#1) = 1#1
        decide)
      (fun j hj => by
        intro hc0
        have hc : ((Expr.lit 1).eval σ &&&
          (Expr.eq (Hw.freeCellIdx e) (Hw.lLit j)).eval σ) = 1#1 := hc0
        have hc2 : (Expr.eq (Hw.freeCellIdx e) (Hw.lLit j)).eval σ
            = 1#1 := by
          by_cases hb : (Expr.eq (Hw.freeCellIdx e)
              (Hw.lLit j)).eval σ = 1#1
          · exact hb
          · rw [bv1_ne_one.mp hb] at hc
            change (1#1 &&& 0#1) = 1#1 at hc
            exact absurd hc (by decide)
        rw [eqE_eval, hidx] at hc2
        apply hj
        apply Fin.ext
        have : (BitVec.ofNat 4 NL2.val).toNat
            = (BitVec.ofNat 4 j.val).toNat := by rw [hc2]; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show j.val < 2 ^ 4 from by
            have := j.isLt; omega),
          Nat.mod_eq_of_lt (show NL2.val < 2 ^ 4 from by
            have := NL2.isLt; omega)] at this
        omega)
    _ (List.mem_finRange NL2) (List.nodup_finRange _)]
  show (RegEnv.set (RegEnv.set acc.regs
      (Hw.dcellV e NL2) ((Expr.lit 1).eval σ))
      (Hw.dcellPar e NL2) ((Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen).eval σ))
    (Hw.dcellV e l) 1 = _
  simp only [RegEnv.set]
  rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (l1 l2 : LineageId),
    ¬(Hw.dcellV e l1 = Hw.dcellPar e l2)) e l NL2)]
  by_cases hl : l = NL2
  · rw [if_pos (by rw [hl]), if_pos hl]
    rfl
  · rw [if_neg (fun hc => hl ((by decide +kernel :
      ∀ (e : DomainId) (l1 l2 : LineageId),
        Hw.dcellV e l1 = Hw.dcellV e l2 → l1 = l2) e l NL2 hc)), if_neg hl]
    exact hacc l

private theorem dupFull_dcellPar (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NL2 : LineageId)
    (hidx : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL2.val)
    (acc : Loom.Hw.St) (hacc : ∀ l' : LineageId,
      acc.regs (Hw.dcellPar e l') 14 = σ.regs (Hw.dcellPar e l') 14)
    (l : LineageId) :
    (((Hw.seqAll ((List.finRange numLineage).map fun l' => Act.ite (.and (.lit 1) (.eq (Hw.freeCellIdx e) (Hw.lLit l'))) (.seq (.write 1 (Hw.dcellV e l') (.lit 1)) (.write 14 (Hw.dcellPar e l') (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen))) .skip))).run σ acc).regs (Hw.dcellPar e l) 14
      = if l = NL2 then ((Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen).eval σ) else σ.regs (Hw.dcellPar e l) 14 := by
  rw [seqAll_ite_run_unique σ _
    (fun l' : LineageId => Expr.and (Expr.lit 1)
      (Expr.eq (Hw.freeCellIdx e) (Hw.lLit l')))
    (fun l' : LineageId => Act.seq (.write 1 (Hw.dcellV e l') (.lit 1))
      (.write 14 (Hw.dcellPar e l') (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen))) NL2
    (by
        have h1 : (Expr.eq (Hw.freeCellIdx e) (Hw.lLit NL2)).eval σ
            = 1#1 := by
          rw [eqE_eval, hidx]
          rfl
        show ((Expr.lit 1).eval σ &&&
          (Expr.eq (Hw.freeCellIdx e) (Hw.lLit NL2)).eval σ) = 1#1
        rw [h1]
        change (1#1 &&& 1#1) = 1#1
        decide)
      (fun j hj => by
        intro hc0
        have hc : ((Expr.lit 1).eval σ &&&
          (Expr.eq (Hw.freeCellIdx e) (Hw.lLit j)).eval σ) = 1#1 := hc0
        have hc2 : (Expr.eq (Hw.freeCellIdx e) (Hw.lLit j)).eval σ
            = 1#1 := by
          by_cases hb : (Expr.eq (Hw.freeCellIdx e)
              (Hw.lLit j)).eval σ = 1#1
          · exact hb
          · rw [bv1_ne_one.mp hb] at hc
            change (1#1 &&& 0#1) = 1#1 at hc
            exact absurd hc (by decide)
        rw [eqE_eval, hidx] at hc2
        apply hj
        apply Fin.ext
        have : (BitVec.ofNat 4 NL2.val).toNat
            = (BitVec.ofNat 4 j.val).toNat := by rw [hc2]; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show j.val < 2 ^ 4 from by
            have := j.isLt; omega),
          Nat.mod_eq_of_lt (show NL2.val < 2 ^ 4 from by
            have := NL2.isLt; omega)] at this
        omega)
    _ (List.mem_finRange NL2) (List.nodup_finRange _)]
  show (RegEnv.set (RegEnv.set acc.regs
      (Hw.dcellV e NL2) ((Expr.lit 1).eval σ))
      (Hw.dcellPar e NL2) ((Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen).eval σ))
    (Hw.dcellPar e l) 14 = _
  simp only [RegEnv.set]
  by_cases hl : l = NL2
  · rw [if_pos (by rw [hl]), if_pos hl]
    rfl
  · rw [if_neg (fun hc => hl ((by decide +kernel :
      ∀ (e : DomainId) (l1 l2 : LineageId),
        Hw.dcellPar e l1 = Hw.dcellPar e l2 → l1 = l2) e l NL2 hc)), if_neg hl]
    rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (l1 l2 : LineageId),
      ¬(Hw.dcellPar e l1 = Hw.dcellV e l2)) e l NL2)]
    exact hacc l

/-! ## Final `dupFull` table faces -/

private theorem dupFull_capV_final (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS : Slot)
    (hidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS.val)
    (s : Slot) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.dcapV e s) 1 =
      if s = NS then 1#1 else σ.regs (Hw.dcapV e s) 1 := by
  rw [dupFull_run_inst m σ e (Hw.dcapV e s) 1
    (by fin_cases e <;> fin_cases s <;> decide +kernel)
    (by fin_cases e <;> fin_cases s <;> decide +kernel)
    (by fin_cases e <;> fin_cases s <;> decide +kernel)]
  rw [frame (show ((Hw.dcapV e s : String), (1 : Nat)) ∉
      (Hw.seqAll ((List.finRange numLineage).map fun l' =>
        Act.ite (.and (.lit 1) (.eq (Hw.freeCellIdx e) (Hw.lLit l')))
          (.seq (.write 1 (Hw.dcellV e l') (.lit 1))
            (.write 14 (Hw.dcellPar e l')
              (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
                (Hw.dupSel e).gen))) .skip)).regWrites from by
        fin_cases e <;> fin_cases s <;> decide +kernel) σ _]
  exact dupFull_capV m σ e NS hidx s

private theorem dupFull_capKind_final (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS : Slot)
    (hidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS.val)
    (s : Slot) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.dcapKind e s) 32 =
      if s = NS then
        (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW)
          (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
          (Hw.dupSel e).kindW).eval σ
      else σ.regs (Hw.dcapKind e s) 32 := by
  rw [dupFull_run_inst m σ e (Hw.dcapKind e s) 32
    (by fin_cases e <;> fin_cases s <;> decide +kernel)
    (by fin_cases e <;> fin_cases s <;> decide +kernel)
    (by fin_cases e <;> fin_cases s <;> decide +kernel)]
  rw [frame (show ((Hw.dcapKind e s : String), (32 : Nat)) ∉
      (Hw.seqAll ((List.finRange numLineage).map fun l' =>
        Act.ite (.and (.lit 1) (.eq (Hw.freeCellIdx e) (Hw.lLit l')))
          (.seq (.write 1 (Hw.dcellV e l') (.lit 1))
            (.write 14 (Hw.dcellPar e l')
              (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
                (Hw.dupSel e).gen))) .skip)).regWrites from by
        fin_cases e <;> fin_cases s <;> decide +kernel) σ _]
  exact dupFull_dcapKind m σ e NS hidx s

private theorem dupFull_capLinV_final (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS : Slot)
    (hidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS.val)
    (s : Slot) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.dcapLinV e s) 1 =
      if s = NS then 1#1 else σ.regs (Hw.dcapLinV e s) 1 := by
  rw [dupFull_run_inst m σ e (Hw.dcapLinV e s) 1
    (by fin_cases e <;> fin_cases s <;> decide +kernel)
    (by fin_cases e <;> fin_cases s <;> decide +kernel)
    (by fin_cases e <;> fin_cases s <;> decide +kernel)]
  rw [frame (show ((Hw.dcapLinV e s : String), (1 : Nat)) ∉
      (Hw.seqAll ((List.finRange numLineage).map fun l' =>
        Act.ite (.and (.lit 1) (.eq (Hw.freeCellIdx e) (Hw.lLit l')))
          (.seq (.write 1 (Hw.dcellV e l') (.lit 1))
            (.write 14 (Hw.dcellPar e l')
              (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
                (Hw.dupSel e).gen))) .skip)).regWrites from by
        fin_cases e <;> fin_cases s <;> decide +kernel) σ _]
  exact dupFull_dcapLinV m σ e NS hidx s

private theorem dupFull_capLin_final (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS : Slot)
    (hidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS.val)
    (s : Slot) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.dcapLin e s) 4 =
      if s = NS then (Hw.freeCellIdx e).eval σ
      else σ.regs (Hw.dcapLin e s) 4 := by
  rw [dupFull_run_inst m σ e (Hw.dcapLin e s) 4
    (by fin_cases e <;> fin_cases s <;> decide +kernel)
    (by fin_cases e <;> fin_cases s <;> decide +kernel)
    (by fin_cases e <;> fin_cases s <;> decide +kernel)]
  rw [frame (show ((Hw.dcapLin e s : String), (4 : Nat)) ∉
      (Hw.seqAll ((List.finRange numLineage).map fun l' =>
        Act.ite (.and (.lit 1) (.eq (Hw.freeCellIdx e) (Hw.lLit l')))
          (.seq (.write 1 (Hw.dcellV e l') (.lit 1))
            (.write 14 (Hw.dcellPar e l')
              (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
                (Hw.dupSel e).gen))) .skip)).regWrites from by
        fin_cases e <;> fin_cases s <;> decide +kernel) σ _]
  exact dupFull_dcapLin m σ e NS hidx s

private theorem dupFull_cellV_final (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NL : LineageId)
    (hidx : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL.val)
    (l : LineageId) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.dcellV e l) 1 =
      if l = NL then 1#1 else σ.regs (Hw.dcellV e l) 1 := by
  rw [dupFull_run_inst m σ e (Hw.dcellV e l) 1
    (by fin_cases e <;> fin_cases l <;> decide +kernel)
    (by fin_cases e <;> fin_cases l <;> decide +kernel)
    (by fin_cases e <;> fin_cases l <;> decide +kernel)]
  apply dupFull_dcellV m σ e NL hidx
  intro l'
  rw [frame (show ((Hw.dcellV e l' : String), (1 : Nat)) ∉
      (Hw.seqAll ((List.finRange numSlots).map fun s' =>
        Act.ite (.eq (Hw.freeSlotIdx e) (Hw.sLit s'))
          (Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1),
            .write 32 (Hw.dcapKind e s')
              (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW)
                (Hw.narrowKindE (Hw.dupSel e).kindW
                  (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW),
            .write 1 (Hw.dcapLinV e s') (.lit 1),
            .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)])
          .skip)).regWrites from by
        fin_cases e <;> fin_cases l' <;> decide +kernel) σ _]
  rw [frame (show ((Hw.dcellV e l' : String), (1 : Nat)) ∉
      (Act.write 1 "if_v" (.lit 0)).regWrites from by
        fin_cases e <;> fin_cases l' <;> decide +kernel) σ _]
  exact refill_pres m σ (by
    fin_cases e <;> fin_cases l' <;> decide +kernel)

private theorem dupFull_cellPar_final (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NL : LineageId)
    (hidx : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL.val)
    (l : LineageId) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.dcellPar e l) 14 =
      if l = NL then
        (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
          (Hw.dupSel e).gen).eval σ
      else σ.regs (Hw.dcellPar e l) 14 := by
  rw [dupFull_run_inst m σ e (Hw.dcellPar e l) 14
    (by fin_cases e <;> fin_cases l <;> decide +kernel)
    (by fin_cases e <;> fin_cases l <;> decide +kernel)
    (by fin_cases e <;> fin_cases l <;> decide +kernel)]
  apply dupFull_dcellPar m σ e NL hidx
  intro l'
  rw [frame (show ((Hw.dcellPar e l' : String), (14 : Nat)) ∉
      (Hw.seqAll ((List.finRange numSlots).map fun s' =>
        Act.ite (.eq (Hw.freeSlotIdx e) (Hw.sLit s'))
          (Hw.seqAll [.write 1 (Hw.dcapV e s') (.lit 1),
            .write 32 (Hw.dcapKind e s')
              (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW)
                (Hw.narrowKindE (Hw.dupSel e).kindW
                  (Hw.readReg e Hw.rs2E)) (Hw.dupSel e).kindW),
            .write 1 (Hw.dcapLinV e s') (.lit 1),
            .write 4 (Hw.dcapLin e s') (Hw.freeCellIdx e)])
          .skip)).regWrites from by
        fin_cases e <;> fin_cases l' <;> decide +kernel) σ _]
  rw [frame (show ((Hw.dcellPar e l' : String), (14 : Nat)) ∉
      (Act.write 1 "if_v" (.lit 0)).regWrites from by
        fin_cases e <;> fin_cases l' <;> decide +kernel) σ _]
  exact refill_pres m σ (by
    fin_cases e <;> fin_cases l' <;> decide +kernel)

/-- The abstract capability table after `dupFull` is one functional update. -/
private theorem absDom_dupFull_caps (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS : Slot) (NL : LineageId) (kind : CapKind)
    (hsidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS.val)
    (hlidx : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL.val)
    (hkind : (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW)
        (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
        (Hw.dupSel e).kindW).eval σ = Hw.encKind kind) :
    (Hw.absDom ((dupFull e).run σ ((Hw.refillAct m).run σ σ)) e).caps =
      Loom.Fun.update ((Hw.abs σ).doms e).caps NS
        (some { kind := kind, lineage := some NL }) := by
  funext s
  show (if ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
      (Hw.dcapV e s) 1 = 1 then
        some (CapEntry.mk (Hw.decKind
          (((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.dcapKind e s) 32))
          (if ((dupFull e).run σ
            ((Hw.refillAct m).run σ σ)).regs (Hw.dcapLinV e s) 1 = 1
            then some (finOfBv (by decide)
              (((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
                (Hw.dcapLin e s) 4))
            else none))
      else none) = _
  by_cases hs : s = NS
  · subst s
    rw [Loom.Fun.update_same, dupFull_capV_final m σ e NS hsidx NS,
      if_pos rfl, dupFull_capKind_final m σ e NS hsidx NS, if_pos rfl,
      dupFull_capLinV_final m σ e NS hsidx NS, if_pos rfl,
      dupFull_capLin_final m σ e NS hsidx NS, if_pos rfl,
      hkind, decKind_encKind, hlidx, finOfBv_ofNat4]
    simp
  · rw [Loom.Fun.update_ne _ _ _ _ hs,
      dupFull_capV_final m σ e NS hsidx s, if_neg hs,
      dupFull_capKind_final m σ e NS hsidx s, if_neg hs,
      dupFull_capLinV_final m σ e NS hsidx s, if_neg hs,
      dupFull_capLin_final m σ e NS hsidx s, if_neg hs]
    rfl

/-- The abstract lineage table after `dupFull` is one functional update. -/
private theorem absDom_dupFull_lineage (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NL : LineageId) (parent : CapRef)
    (hlidx : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL.val)
    (hparent : (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
        (Hw.dupSel e).gen).eval σ = Hw.encRef parent) :
    (Hw.absDom ((dupFull e).run σ ((Hw.refillAct m).run σ σ)) e).lineage =
      Loom.Fun.update ((Hw.abs σ).doms e).lineage NL
        (some { parent := parent }) := by
  funext l
  show (if ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
      (Hw.dcellV e l) 1 = 1 then
        some (LineageCell.mk (Hw.decRef
          (((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.dcellPar e l) 14)))
      else none) = _
  by_cases hl : l = NL
  · subst l
    rw [Loom.Fun.update_same, dupFull_cellV_final m σ e NL hlidx NL,
      if_pos rfl, dupFull_cellPar_final m σ e NL hlidx NL, if_pos rfl,
      hparent, decRef_encRef]
    simp
  · rw [Loom.Fun.update_ne _ _ _ _ hl,
      dupFull_cellV_final m σ e NL hlidx l, if_neg hl,
      dupFull_cellPar_final m σ e NL hlidx l, if_neg hl]
    rfl

/-- Owner-domain shape after a successful duplicate install. Register and
program-counter values stay exposed for the operation-specific result bridge;
the capability and lineage faces are already the spec updates. -/
private theorem absDom_dupFull_owner (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS : Slot) (NL : LineageId) (kind : CapKind)
    (parent : CapRef)
    (hsidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS.val)
    (hlidx : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL.val)
    (hkind : (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW)
        (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
        (Hw.dupSel e).kindW).eval σ = Hw.encKind kind)
    (hparent : (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
        (Hw.dupSel e).gen).eval σ = Hw.encRef parent) :
    Hw.absDom ((dupFull e).run σ ((Hw.refillAct m).run σ σ)) e =
      { Hw.absDom ((Hw.refillAct m).run σ σ) e with
        regs := fun r => ((dupFull e).run σ
          ((Hw.refillAct m).run σ σ)).regs (Hw.dreg e r) 32
        pc := ((dupFull e).run σ
          ((Hw.refillAct m).run σ σ)).regs (Hw.dpc e) 12
        caps := Loom.Fun.update ((Hw.abs σ).doms e).caps NS
          (some { kind := kind, lineage := some NL })
        lineage := Loom.Fun.update ((Hw.abs σ).doms e).lineage NL
          (some { parent := parent }) } := by
  rw [absDom_regpccap e (fun q hq =>
    frame (quietCap_notin_dup e e q hq) σ _)]
  apply domainState_ext'
  · rfl
  · rfl
  · exact absDom_dupFull_caps m σ e NS NL kind hsidx hlidx hkind
  · rfl
  · exact absDom_dupFull_lineage m σ e NL parent hlidx hparent
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The architectural register face of `dupFull`: only `rd` receives the
returned handle, with the usual hardwired-r0 behavior. -/
private theorem dupFull_reg_final (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (rd : RegId) (v : BitVec 32)
    (hrd : (Hw.rdE.eval σ).toNat = rd.val)
    (hval : (Hw.handleE (Hw.freeSlotIdx e)
        (Hw.genOfE e (Hw.freeSlotIdx e))
        (Hw.field (Hw.dupSel e).kindW 0 1)).eval σ = v)
    (r : RegId) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.dreg e r) 32 =
      (((Hw.absDom ((Hw.refillAct m).run σ σ) e).setReg rd v).regs r) := by
  unfold dupFull
  show ((Hw.pcAdvA e).run σ
    ((Hw.writeReg e Hw.rdE
      (Hw.handleE (Hw.freeSlotIdx e) (Hw.genOfE e (Hw.freeSlotIdx e))
        (Hw.field (Hw.dupSel e).kindW 0 1))).run σ
      ((Hw.installA e (Hw.freeSlotIdx e)
        (.mux (Hw.kIsMem (Hw.dupSel e).kindW)
          (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
          (Hw.dupSel e).kindW)
        (.lit 1) (Hw.freeCellIdx e)
        (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
          (Hw.dupSel e).gen)).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ
          ((Hw.refillAct m).run σ σ))))).regs (Hw.dreg e r) 32 = _
  rw [frame (show ((Hw.dreg e r : String), (32 : Nat)) ∉
      (Hw.pcAdvA e).regWrites from by
        fin_cases e <;> fin_cases r <;> decide +kernel) σ _]
  rw [setReg_regs]
  have hacc : ((Hw.installA e (Hw.freeSlotIdx e)
      (.mux (Hw.kIsMem (Hw.dupSel e).kindW)
        (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
        (Hw.dupSel e).kindW)
      (.lit 1) (Hw.freeCellIdx e)
      (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
        (Hw.dupSel e).gen)).run σ
      ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ))).regs (Hw.dreg e r) 32 =
      (Hw.absDom ((Hw.refillAct m).run σ σ) e).regs r := by
    rw [frame (show ((Hw.dreg e r : String), (32 : Nat)) ∉
      (Hw.installA e (Hw.freeSlotIdx e)
        (.mux (Hw.kIsMem (Hw.dupSel e).kindW)
          (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
          (Hw.dupSel e).kindW)
        (.lit 1) (Hw.freeCellIdx e)
        (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
          (Hw.dupSel e).gen)).regWrites from by
        fin_cases e <;> fin_cases r <;> decide +kernel) σ _]
    rw [frame (show ((Hw.dreg e r : String), (32 : Nat)) ∉
      (Act.write 1 "if_v" (.lit 0)).regWrites from by
        fin_cases e <;> fin_cases r <;> decide +kernel) σ _]
    rfl
  by_cases h0 : rd = (0 : RegId)
  · rw [if_pos h0]
    rw [writeReg_run_of_zero σ _ e Hw.rdE _ (by rw [hrd, h0]; rfl)]
    exact hacc
  · rw [if_neg h0]
    rw [writeReg_run_of_nz σ _ e Hw.rdE _ rd hrd.symm
      (fun hc => h0 (Fin.ext hc))]
    show (RegEnv.set _ (Hw.dreg e rd) _ ) (Hw.dreg e r) 32 = _
    simp only [RegEnv.set]
    by_cases hr : r = rd
    · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial, hval]
    · rw [if_neg (fun hc => hr (dreg_inj e r rd hc)), if_neg hr, hacc]

/-- The program-counter face of `dupFull` is the retirement increment. -/
private theorem dupFull_pc_final (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) :
    ((dupFull e).run σ ((Hw.refillAct m).run σ σ)).regs (Hw.dpc e) 12 =
      (Hw.absDom ((Hw.refillAct m).run σ σ) e).pc + 1 := by
  show (RegEnv.set _ (Hw.dpc e)
      ((Expr.add (Hw.rPc e) (.lit 1)).eval σ)) (Hw.dpc e) 12 = _
  simp only [RegEnv.set]
  rw [if_pos trivial]
  show σ.regs (Hw.dpc e) 12 + 1 =
    ((Hw.refillAct m).run σ σ).regs (Hw.dpc e) 12 + 1
  rw [refill_pres m σ (by
    fin_cases e <;> decide +kernel)]

/-- Complete owner-domain correspondence for a successful install. -/
private theorem absDom_dupFull_install (m : Manifest) (σ : Loom.Hw.St)
    (e : DomainId) (NS : Slot) (NL : LineageId) (kind : CapKind)
    (parent : CapRef) (rd : RegId) (v : BitVec 32)
    (hsidx : (Hw.freeSlotIdx e).eval σ = BitVec.ofNat 4 NS.val)
    (hlidx : (Hw.freeCellIdx e).eval σ = BitVec.ofNat 4 NL.val)
    (hkind : (Expr.mux (Hw.kIsMem (Hw.dupSel e).kindW)
        (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
        (Hw.dupSel e).kindW).eval σ = Hw.encKind kind)
    (hparent : (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot
        (Hw.dupSel e).gen).eval σ = Hw.encRef parent)
    (hrd : (Hw.rdE.eval σ).toNat = rd.val)
    (hval : (Hw.handleE (Hw.freeSlotIdx e)
        (Hw.genOfE e (Hw.freeSlotIdx e))
        (Hw.field (Hw.dupSel e).kindW 0 1)).eval σ = v) :
    Hw.absDom ((dupFull e).run σ ((Hw.refillAct m).run σ σ)) e =
      ({ Hw.absDom ((Hw.refillAct m).run σ σ) e with
        pc := (Hw.absDom ((Hw.refillAct m).run σ σ) e).pc + 1
        caps := Loom.Fun.update ((Hw.abs σ).doms e).caps NS
          (some { kind := kind, lineage := some NL })
        lineage := Loom.Fun.update ((Hw.abs σ).doms e).lineage NL
          (some { parent := parent }) }).setReg rd v := by
  rw [absDom_dupFull_owner m σ e NS NL kind parent hsidx hlidx hkind hparent]
  apply domainState_ext'
  · funext r
    simpa only [setReg_regs] using
      (dupFull_reg_final m σ e rd v hrd hval r)
  · rw [setReg_pc]
    exact dupFull_pc_final m σ e
  · rw [setReg_caps]
  · rw [setReg_slotGen]
  · rw [setReg_lineage]
  · rw [setReg_regions]
  · rw [setReg_run]
  · rw [setReg_serving]
  · rw [setReg_cause]
  · rw [setReg_budget]
  · rw [setReg_maxDonation]

/-! ## The `cap_dup` arm: head + spec do-term -/

set_option maxHeartbeats 51200000 in
/-- The `cap_dup` retirement arm (opcode 16). -/
theorem square_retire_dup (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 16#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (16#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (16#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hdupmn : (Hw.isMn "cap_dup").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "cap_dup" = 16#6).symm
  have hret := retiringE_one σ hifv hcl
  have hin : Inert σ := Inert.of_benign7 σ (fun mn' hmn' =>
    isMn_ne_of_opc σ mn' 16#6 hopc
      ((by decide +kernel : ∀ mn' ∈ ["cap_drop", "cap_revoke", "gate_call",
        "gate_return", "move"], (16#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn'))
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 16#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 16#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 16#6 hopc (by decide +kernel))
  have hben5 : ∀ mn ∈ memMns, (Hw.isMn mn).eval σ ≠ 1#1 := fun mn hmn =>
    isMn_ne_of_opc σ mn 16#6 hopc
      ((by decide +kernel : ∀ mn ∈ memMns, (16#6 : BitVec 6)
        ≠ Hw.opcodeOf mn) mn hmn)
  have hselC := retireFor_sel_of_opc σ E "cap_dup" 16#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨Hw.ladder E (Hw.dupChecks E) (Hw.seqAll
      [ Hw.installA E (Hw.freeSlotIdx E)
          (.mux (Hw.kIsMem (Hw.dupSel E).kindW)
            (Hw.narrowKindE (Hw.dupSel E).kindW (Hw.readReg E Hw.rs2E))
            (Hw.dupSel E).kindW)
          (.lit 1) (Hw.freeCellIdx E)
          (Hw.encRefE (Hw.dLit E) (Hw.dupSel E).slot (Hw.dupSel E).gen),
        Hw.writeReg E Hw.rdE (Hw.handleE (Hw.freeSlotIdx E)
          (Hw.genOfE E (Hw.freeSlotIdx E))
          (Hw.field (Hw.dupSel E).kindW 0 1)),
        Hw.pcAdvA E ]),
      .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_right _ (List.mem_cons_self ..))
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ)
      = refillPhase m (Hw.abs σ) := abs_refill m hwf hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y
    rw [← habs1]
    rfl
  have hG1 : ∀ g, (refillPhase m (Hw.abs σ)).gates g
      = Hw.absGate ((Hw.refillAct m).run σ σ) g := by
    intro g
    rw [← habs1]
    rfl
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  set HWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hHWv
  set DWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs2 with hDWv
  have hSPr : ∀ rs : RegId,
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg rs
        = ((Hw.abs σ).doms E).reg rs := fun rs => specReg_bridge m σ E rs
  have hSval : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (HWv.extractLsb' 0 4)).val
      = (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := by
    rw [hR1]
    rfl
  have hlivE := capSel_live_eval σ E (Hw.readReg E Hw.rs1E) _ hSval
  rw [hR1] at hlivE
  have hkwE : (Hw.dupSel E).kindW.eval σ
      = σ.regs (Hw.dcapKind E (finOfBv (by decide)
          (HWv.extractLsb' 0 4))) 32 :=
    capSel_kindW_eval σ E (Hw.readReg E Hw.rs1E) _ hSval
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ))
      = retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hDO : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (match ((SpecM.reg E (operandsOf W).rs1 >>= fun hw =>
          SpecM.reg E (operandsOf W).rs2 >>= fun dw =>
          Machines.Lnp64u.Isa.capLive E hw >>= fun x =>
          match x with
          | (s, g, e) =>
            match e.kind with
            | .mem base len perms =>
                Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
                Machines.Lnp64u.Isa.allocDerived E kind ⟨E, s, g⟩ >>=
                  fun h => SpecM.setReg E (operandsOf W).rd h
            | .gate gid =>
                (pure (CapKind.gate gid) : SpecM CapKind) >>= fun kind =>
                Machines.Lnp64u.Isa.allocDerived E kind ⟨E, s, g⟩ >>=
                  fun h => SpecM.setReg E (operandsOf W).rd h)
          (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))) with
        | .ok _ σ' => σ'
        | .err e σ' =>
            σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault fl => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E fl) := by
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl
  have hladder : ∀ acc : Loom.Hw.St, (Hw.retireFor E).run σ acc
      = (
          if (Expr.not (Hw.dupSel E).live).eval σ = 1#1
          then (Hw.respA E (.err .staleHandle)).run σ acc
          else if (Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1
          then (Hw.respA E (.err .badCap)).run σ acc
          else if (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14) (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14) (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1
          then (Hw.respA E (.err .outOfRange)).run σ acc
          else if (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.not (Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)))).eval σ = 1#1
          then (Hw.respA E (.err .outOfRange)).run σ acc
          else if (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))])).eval σ = 1#1
          then (Hw.respA E (.err .permDenied)).run σ acc
          else if (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ = 1#1
          then (Hw.respA E (.err .permDenied)).run σ acc
          else if (Expr.not (Hw.freeSlotV E)).eval σ = 1#1
          then (Hw.respA E (.err .slotOccupied)).run σ acc
          else if (Expr.not (Hw.freeCellV E)).eval σ = 1#1
          then (Hw.respA E (.err .noLineage)).run σ acc
          else (Hw.seqAll
            [ Hw.installA E (Hw.freeSlotIdx E)
                (.mux (Hw.kIsMem (Hw.dupSel E).kindW)
                  (Hw.narrowKindE (Hw.dupSel E).kindW (Hw.readReg E Hw.rs2E))
                  (Hw.dupSel E).kindW)
                (.lit 1) (Hw.freeCellIdx E)
                (Hw.encRefE (Hw.dLit E) (Hw.dupSel E).slot (Hw.dupSel E).gen),
              Hw.writeReg E Hw.rdE (Hw.handleE (Hw.freeSlotIdx E)
                (Hw.genOfE E (Hw.freeSlotIdx E))
                (Hw.field (Hw.dupSel E).kindW 0 1)),
              Hw.pcAdvA E ]).run σ acc) := by
    intro acc
    rw [hselC acc]
    rfl
  have hRD : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1 = HWv :=
    hSPr (operandsOf W).rs1
  have hRD2 : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2 = DWv :=
    hSPr (operandsOf W).rs2
  by_cases hlv : σ.regs (Hw.dcapV E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1
      ∧ σ.regs (Hw.dgen E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 8 = HWv.extractLsb' 4 8
      ∧ HWv.extractLsb' 4 8 ≠ 0
  case neg =>
    -- stale handle
    have hlive0 : ¬((Hw.dupSel E).live.eval σ = 1#1) :=
      fun hc => hlv (hlivE.mp hc)
    have hlcN : ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = none := by
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_neg hlv
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.staleHandle.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_pos (show (Expr.not (Hw.dupSel E).live).eval σ = 1#1 from by
          show ~~~((Hw.dupSel E).live.eval σ) = 1#1
          rw [bv1_ne_one.mp hlive0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcN]
      rfl
  case pos =>
  have hliv1 : (Hw.dupSel E).live.eval σ = 1#1 := hlivE.mpr hlv
  have hlcS : ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
      (Handle.decode HWv).slot (Handle.decode HWv).gen
      = some { kind := Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)
               lineage := if σ.regs (Hw.dcapLinV E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1
                 then some (finOfBv (by decide)
                   (σ.regs (Hw.dcapLin E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 4))
                 else none } := by
    rw [specLiveCap_bridge, abs_liveCap]
    exact if_pos hlv
  obtain ⟨ce, hlcS', hcek⟩ :
      ∃ c0 : CapEntry, ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = some c0
      ∧ c0.kind = Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) := ⟨_, hlcS, rfl⟩
  have hclsE2 : (Hw.dupSel E).clsOk.eval σ
      = (if (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 0 1 = HWv.extractLsb' 12 1
        then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.dupSel E).kindW.eval σ).extractLsb' 0 1
        = ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 12 1
      then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwE, hR1]
  by_cases hbit : HWv.getLsbD 12 = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 0
  case neg =>
    -- class mismatch
    have hcls0 : ¬((Hw.dupSel E).clsOk.eval σ = 1#1) := by
      rw [hclsE2]
      intro h
      by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 0 1 = HWv.extractLsb' 12 1
      · exact hbit ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) HWv 0 12).mp hcx).symm
      · rw [if_neg hcx] at h
        exact absurd h (by decide)
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_pos (show (Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1 from by
          show ~~~((Hw.dupSel E).clsOk.eval σ) = 1#1
          rw [bv1_ne_one.mp hcls0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [show (decide ((Handle.decode HWv).cls
          = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).cls)) = false from decide_eq_false
        (fun hA => hbit ((cls_eq_iff_bits HWv (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mp hA))]
      rfl
  case pos =>
  have hcls1 : (Hw.dupSel E).clsOk.eval σ = 1#1 := by
    rw [hclsE2]
    rw [if_pos ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) HWv 0 12).mpr hbit.symm)]
  have hdecT : (decide ((Handle.decode HWv).cls
      = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).cls)) = true :=
    decide_eq_true ((cls_eq_iff_bits HWv (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mpr hbit)
  by_cases hmem : (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 0 = false
  case neg =>
    -- gate kind: narrowing skipped
    have hgatebit :
        (σ.regs (Hw.dcapKind E (finOfBv (by decide)
          (HWv.extractLsb' 0 4))) 32).getLsbD 0 = true := by
      cases h : (σ.regs (Hw.dcapKind E (finOfBv (by decide)
        (HWv.extractLsb' 0 4))) 32).getLsbD 0
      · exact absurd h hmem
      · rfl
    have hgate : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide)
        (HWv.extractLsb' 0 4))) 32) =
        .gate (finOfBv (by decide) ((σ.regs (Hw.dcapKind E
          (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 2)) :=
      (decKind_gate_iff _).mp hgatebit
    have hkm0 : (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = 0#1 := by
      show (if ((Hw.dupSel E).kindW.eval σ).extractLsb' 0 1
          = (Expr.lit 0).eval σ then (1#1 : BitVec 1) else 0#1) = 0#1
      rw [show ((Expr.lit 0 : Expr 1)).eval σ = 0#1 from rfl]
      simp only [hkwE]
      rw [if_neg (fun hx => by
        have := (extract1_eq_zero_iff (σ.regs (Hw.dcapKind E
          (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 0).mp hx
        rw [this] at hgatebit
        exact absurd hgatebit (by decide))]
    have hc3z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
        (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14)
          (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
            (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1) := by
      show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&& _ = 1#1)
      rw [hkm0]
      rw [bv1_and_eq_one]
      simp
    have hc4z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
        (Expr.not (Expr.ult
          (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13)
            (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13))
          (.lit 4096)))).eval σ = 1#1) := by
      show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&& _ = 1#1)
      rw [hkm0]
      rw [bv1_and_eq_one]
      simp
    have hc5z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
        (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E))
            (.not (Hw.kR (Hw.dupSel E).kindW)),
          .and (Hw.descW (Hw.readReg E Hw.rs2E))
            (.not (Hw.kW (Hw.dupSel E).kindW)),
          .and (Hw.descX (Hw.readReg E Hw.rs2E))
            (.not (Hw.kX (Hw.dupSel E).kindW))])).eval σ = 1#1) := by
      show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&& _ = 1#1)
      rw [hkm0]
      rw [bv1_and_eq_one]
      simp
    have hc6z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
        (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E))
          (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ = 1#1) := by
      show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&& _ = 1#1)
      rw [hkm0]
      rw [bv1_and_eq_one]
      simp
    have hcapsB : ∀ s : Slot,
        (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 }))).doms E).caps s
          = ((Hw.abs σ).doms E).caps s := fun s => by
      show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
        ({ (refillPhase m (Hw.abs σ)).doms E with
          pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).caps s = _
      rw [Loom.Fun.update_same]
      show ((refillPhase m (Hw.abs σ)).doms E).caps s = _
      rw [refillPhase_caps]
    have hgenB : ∀ s : Slot,
        (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 }))).doms E).slotGen s
          = ((Hw.abs σ).doms E).slotGen s := fun s => by
      show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
        ({ (refillPhase m (Hw.abs σ)).doms E with
          pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).slotGen s = _
      rw [Loom.Fun.update_same]
      show ((refillPhase m (Hw.abs σ)).doms E).slotGen s = _
      rw [refillPhase_slotGen]
    have hlinB : ∀ l : LineageId,
        (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 }))).doms E).lineage l
          = ((Hw.abs σ).doms E).lineage l := fun l => by
      show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
        ({ (refillPhase m (Hw.abs σ)).doms E with
          pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).lineage l = _
      rw [Loom.Fun.update_same]
      show ((refillPhase m (Hw.abs σ)).doms E).lineage l = _
      rw [refillPhase_lineage]
    have hfsB : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 }))).freeSlot E
        = (Hw.abs σ).freeSlot E := freeSlot_congr _ _ E hcapsB hgenB
    have hfcB : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 }))).freeCell E
        = (Hw.abs σ).freeCell E := freeCell_congr _ _ E hlinB
    cases hfs : (Hw.abs σ).freeSlot E with
    | none =>
      have hfsv0 : ¬((Hw.freeSlotV E).eval σ = 1#1) := fun hc => by
        have h2 := (freeSlotV_eval σ E).mp hc
        rw [hfs] at h2
        exact absurd h2 (by decide)
      refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
        hswz hben5 E rfl Errno.slotOccupied.toWord ?_ ?_
      · intro acc
        rw [hladder acc,
          if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
            show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
            rw [hliv1]
            decide),
          if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
            show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
            rw [hcls1]
            decide),
          if_neg hc3z, if_neg hc4z, if_neg hc5z, if_neg hc6z,
          if_pos (show (Expr.not (Hw.freeSlotV E)).eval σ = 1#1 from by
            show ~~~((Hw.freeSlotV E).eval σ) = 1#1
            rw [bv1_ne_one.mp hfsv0]
            decide)]
        rfl
      · rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        simp only [hRD, hRD2, hlcS', hcek]
        rw [hdecT]
        simp only [reduceIte, specM_bind, specM_pure, hcek, hgate,
          Machines.Lnp64u.Isa.allocDerived, SpecM.get, SpecM.raise]
        rw [hfsB.trans hfs]
        rfl
    | some NS =>
      have hfsv1 : (Hw.freeSlotV E).eval σ = 1#1 :=
        (freeSlotV_eval σ E).mpr (by rw [hfs]; rfl)
      cases hfc : (Hw.abs σ).freeCell E with
      | none =>
        have hfcv0 : ¬((Hw.freeCellV E).eval σ = 1#1) := fun hc => by
          have h2 := (freeCellV_eval σ E).mp hc
          rw [hfc] at h2
          exact absurd h2 (by decide)
        refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
          hswz hben5 E rfl Errno.noLineage.toWord ?_ ?_
        · intro acc
          rw [hladder acc,
            if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
              show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
              rw [hliv1]
              decide),
            if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
              show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
              rw [hcls1]
              decide),
            if_neg hc3z, if_neg hc4z, if_neg hc5z, if_neg hc6z,
            if_neg (show ¬((Expr.not (Hw.freeSlotV E)).eval σ = 1#1) from by
              show ¬(~~~((Hw.freeSlotV E).eval σ) = 1#1)
              rw [hfsv1]
              decide),
            if_pos (show (Expr.not (Hw.freeCellV E)).eval σ = 1#1 from by
              show ~~~((Hw.freeCellV E).eval σ) = 1#1
              rw [bv1_ne_one.mp hfcv0]
              decide)]
          rfl
        · rw [hcore0, hDO]
          simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
            SpecM.reg, SpecM.load, SpecM.demand,
            Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
            SpecM.modify, specM_pure]
          simp only [hRD, hRD2, hlcS', hcek]
          rw [hdecT]
          simp only [reduceIte, specM_bind, specM_pure, hcek, hgate,
            Machines.Lnp64u.Isa.allocDerived, SpecM.get, SpecM.set,
            SpecM.modify, SpecM.raise]
          rw [hfsB.trans hfs]
          simp only [specM_bind, specM_pure]
          rw [hfcB.trans hfc]
          rfl
      | some NL =>
        -- Successful gate installation: shared table/value bridges.
        have hsidx : (Hw.freeSlotIdx E).eval σ = BitVec.ofNat 4 NS.val :=
          freeSlotIdx_eval σ E NS hfs
        have hlidx : (Hw.freeCellIdx E).eval σ = BitVec.ofNat 4 NL.val :=
          freeCellIdx_eval σ E NL hfc
        let S : Slot := finOfBv (by decide) (HWv.extractLsb' 0 4)
        let K : CapKind := .gate (finOfBv (by decide)
          ((σ.regs (Hw.dcapKind E S) 32).extractLsb' 1 2))
        let P : CapRef := ⟨E, S, HWv.extractLsb' 4 8⟩
        let G : Gen := ((Hw.abs σ).doms E).slotGen NS
        let V : BitVec 32 := Handle.encode ⟨NS, G, .gate⟩
        have hkind : (Expr.mux (Hw.kIsMem (Hw.dupSel E).kindW)
            (Hw.narrowKindE (Hw.dupSel E).kindW (Hw.readReg E Hw.rs2E))
            (Hw.dupSel E).kindW).eval σ = Hw.encKind K := by
          show (if (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = 1#1
            then (Hw.narrowKindE (Hw.dupSel E).kindW
              (Hw.readReg E Hw.rs2E)).eval σ
            else (Hw.dupSel E).kindW.eval σ) = _
          rw [if_neg (by simpa [hkm0]), hkwE]
          show σ.regs (Hw.dcapKind E S) 32 = Hw.encKind K
          rw [← hkc E S]
          congr 1
        have hparent : (Hw.encRefE (Hw.dLit E) (Hw.dupSel E).slot
            (Hw.dupSel E).gen).eval σ = Hw.encRef P := by
          simpa only [Hw.dupSel, hR1] using
            (encRefE_sel_eval σ E (Hw.readReg E Hw.rs1E))
        have hgenE : (Hw.genOfE E (Hw.freeSlotIdx E)).eval σ = G := by
          rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots)]
          have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
              ((Hw.freeSlotIdx E).eval σ) = NS := by
            rw [hsidx]
            exact finOfBv_ofNat4 (by decide) NS
          rw [hfin]
          rfl
        have hclsE : (Hw.field (Hw.dupSel E).kindW 0 1).eval σ = 1#1 := by
          show ((Hw.dupSel E).kindW.eval σ).extractLsb' 0 1 = 1#1
          rw [hkwE]
          exact (extract1_eq_one _ 0).mpr hgatebit
        have hval : (Hw.handleE (Hw.freeSlotIdx E)
            (Hw.genOfE E (Hw.freeSlotIdx E))
            (Hw.field (Hw.dupSel E).kindW 0 1)).eval σ = V := by
          rw [handleE_pack σ _ _ _ .gate (by simpa using hclsE), hsidx,
            hgenE]
          show Handle.encode
            ⟨finOfBv (by decide) (BitVec.ofNat 4 NS.val), G, .gate⟩ = V
          rw [finOfBv_ofNat4]
        let τ0 : MachineState :=
          ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
            (fun ds => { ds with pc := ds.pc + 1 })
        let τi : MachineState := (τ0.installDerived E NS NL K P).1
        let τ2 : MachineState := τi.setDom E
          (fun ds => ds.setReg (operandsOf W).rd V)
        have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
          rw [hcore0, hDO]
          simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
            SpecM.reg, SpecM.load, SpecM.demand,
            Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
            SpecM.modify, specM_pure]
          simp only [hRD, hRD2, hlcS', hcek]
          rw [hdecT]
          simp only [reduceIte, specM_bind, specM_pure, hcek, hgate,
            Machines.Lnp64u.Isa.allocDerived, SpecM.get, SpecM.raise]
          rw [hfsB.trans hfs]
          simp only [specM_bind, specM_pure]
          rw [hfcB.trans hfc]
          simp only [SpecM.set, SpecM.setReg, SpecM.modify, specM_bind,
            specM_pure]
          unfold τ2 τi τ0
          unfold MachineState.installDerived MachineState.setDom
          dsimp only
          apply machineState_ext' <;> try rfl
          funext d
          by_cases hd : d = E
          · subst d
            simp only [Loom.Fun.update_same]
            rw [refillPhase_caps, refillPhase_lineage]
            apply domainState_ext'
            · funext r
              by_cases h0 : (operandsOf W).rd = (0 : RegId) <;>
                by_cases hr : r = (operandsOf W).rd <;>
                simp [setReg_regs, h0, hr]
              unfold V G
              rfl
            · rw [setReg_pc, setReg_pc]
            · rw [setReg_caps, setReg_caps]
            · rw [setReg_slotGen, setReg_slotGen]
            · rw [setReg_lineage, setReg_lineage]
              unfold P S
              rfl
            · rw [setReg_regions, setReg_regions]
            · rw [setReg_run, setReg_run]
            · rw [setReg_serving, setReg_serving]
            · rw [setReg_cause, setReg_cause]
            · rw [setReg_budget, setReg_budget]
            · rw [setReg_maxDonation, setReg_maxDonation]
          · simp only [Loom.Fun.update_ne _ _ _ _ hd]
        let X : Act := Hw.seqAll
          [ Hw.installA E (Hw.freeSlotIdx E)
              (.mux (Hw.kIsMem (Hw.dupSel E).kindW)
                (Hw.narrowKindE (Hw.dupSel E).kindW
                  (Hw.readReg E Hw.rs2E)) (Hw.dupSel E).kindW)
              (.lit 1) (Hw.freeCellIdx E)
              (Hw.encRefE (Hw.dLit E) (Hw.dupSel E).slot
                (Hw.dupSel E).gen),
            Hw.writeReg E Hw.rdE
              (Hw.handleE (Hw.freeSlotIdx E)
                (Hw.genOfE E (Hw.freeSlotIdx E))
                (Hw.field (Hw.dupSel E).kindW 0 1)),
            Hw.pcAdvA E ]
        have hcoreR : ∀ (rn : String) (w : Nat),
            ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
              ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
                ((Hw.refillAct m).run σ σ)).regs rn w := by
          intro rn w
          rw [coreAct_run_retire_eq m σ _ hifv hcl,
            retireAct_run_regs σ _ E rfl rn w, hladder]
          rw [if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1)
              from by show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
                      rw [hliv1]; decide),
            if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1)
              from by show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
                      rw [hcls1]; decide),
            if_neg hc3z, if_neg hc4z, if_neg hc5z, if_neg hc6z,
            if_neg (show ¬((Expr.not (Hw.freeSlotV E)).eval σ = 1#1)
              from by show ¬(~~~((Hw.freeSlotV E).eval σ) = 1#1)
                      rw [hfsv1]; decide),
            if_neg (show ¬((Expr.not (Hw.freeCellV E)).eval σ = 1#1)
              from by
                have hfcv1 : (Hw.freeCellV E).eval σ = 1#1 :=
                  (freeCellV_eval σ E).mpr (by rw [hfc]; rfl)
                show ¬(~~~((Hw.freeCellV E).eval σ) = 1#1)
                rw [hfcv1]
                decide)]
          rfl
        have habsD : ∀ x,
            Hw.absDom ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
              ((Hw.refillAct m).run σ σ)) x = τ2.doms x := by
          intro x
          change Hw.absDom ((dupFull E).run σ
            ((Hw.refillAct m).run σ σ)) x = τ2.doms x
          by_cases hx : x = E
          · subst x
            rw [absDom_dupFull_install m σ E NS NL K P
              (operandsOf W).rd V hsidx hlidx hkind hparent rfl hval]
            rw [← hL1 E]
            unfold τ2 τi τ0 MachineState.installDerived MachineState.setDom
            dsimp only
            rw [Loom.Fun.update_same, Loom.Fun.update_same,
              Loom.Fun.update_same]
            rw [refillPhase_caps, refillPhase_lineage]
          · rw [absDom_dupFull_ne m σ E x hx, ← hL1 x]
            unfold τ2 τi τ0 MachineState.installDerived MachineState.setDom
            dsimp only
            rw [Loom.Fun.update_ne _ _ _ _ hx,
              Loom.Fun.update_ne _ _ _ _ hx,
              Loom.Fun.update_ne _ _ _ _ hx]
        have habsG : ∀ g,
            Hw.absGate ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
              ((Hw.refillAct m).run σ σ)) g = τ2.gates g := by
          intro g
          change Hw.absGate ((dupFull E).run σ
            ((Hw.refillAct m).run σ σ)) g = τ2.gates g
          rw [absGate_dupFull m σ E g, ← hG1 g]
          rfl
        have hjob : τ2.mover = Hw.absMover σ := by
          show (refillPhase m (Hw.abs σ)).mover = Hw.absMover σ
          rw [refillPhase_mover]
          rfl
        have hτ0caps : ∀ (d : DomainId) (s : Slot),
            (τ0.doms d).caps s = ((Hw.abs σ).doms d).caps s := by
          intro d s
          unfold τ0 MachineState.setDom
          dsimp only
          by_cases hd : d = E
          · subst d
            rw [Loom.Fun.update_same]
            exact congrFun (refillPhase_caps m (Hw.abs σ) E) s
          · rw [Loom.Fun.update_ne _ _ _ _ hd]
            exact congrFun (refillPhase_caps m (Hw.abs σ) d) s
        have hτ0gen : ∀ (d : DomainId) (s : Slot),
            (τ0.doms d).slotGen s = ((Hw.abs σ).doms d).slotGen s := by
          intro d s
          unfold τ0 MachineState.setDom
          dsimp only
          by_cases hd : d = E
          · subst d
            rw [Loom.Fun.update_same]
            exact congrFun (refillPhase_slotGen m (Hw.abs σ) E) s
          · rw [Loom.Fun.update_ne _ _ _ _ hd]
            exact congrFun (refillPhase_slotGen m (Hw.abs σ) d) s
        have hfree0 : (τ0.doms E).caps NS = none := by
          rw [hτ0caps E NS]
          exact freeSlot_caps_none (Hw.abs σ) E hfs
        have hwcaps : ∀ (r : CapRef),
            (∃ ce, ((Hw.abs σ).doms r.dom).liveCap r.slot r.gen = some ce) →
            (τ2.doms r.dom).caps r.slot =
              ((Hw.abs σ).doms r.dom).caps r.slot := by
          intro r hlive
          have hlive0 : ∃ ce, (τ0.doms r.dom).liveCap r.slot r.gen = some ce := by
            obtain ⟨ce, hce⟩ := hlive
            refine ⟨ce, ?_⟩
            unfold DomainState.liveCap
            rw [hτ0caps r.dom r.slot, hτ0gen r.dom r.slot]
            exact hce
          have hi := installDerived_caps_at_live τ0 E NS NL K P r
            hfree0 hlive0
          show ((τi.setDom E (fun ds => ds.setReg (operandsOf W).rd V)).doms
              r.dom).caps r.slot = _
          rw [show ((τi.setDom E
              (fun ds => ds.setReg (operandsOf W).rd V)).doms r.dom).caps
                r.slot = (τi.doms r.dom).caps r.slot from by
            unfold MachineState.setDom
            dsimp only
            by_cases hd : r.dom = E
            · rw [hd, Loom.Fun.update_same, setReg_caps]
            · rw [Loom.Fun.update_ne _ _ _ _ hd]]
          exact hi.trans (hτ0caps r.dom r.slot)
        have hwgen : ∀ (r : CapRef),
            (τ2.doms r.dom).slotGen r.slot =
              ((Hw.abs σ).doms r.dom).slotGen r.slot := by
          intro r
          show ((τi.setDom E (fun ds => ds.setReg (operandsOf W).rd V)).doms
              r.dom).slotGen r.slot = _
          rw [show ((τi.setDom E
              (fun ds => ds.setReg (operandsOf W).rd V)).doms r.dom).slotGen
                r.slot = (τi.doms r.dom).slotGen r.slot from by
            unfold MachineState.setDom
            dsimp only
            by_cases hd : r.dom = E
            · rw [hd, Loom.Fun.update_same, setReg_slotGen]
            · rw [Loom.Fun.update_ne _ _ _ _ hd]]
          rw [show (τi.doms r.dom).slotGen r.slot =
              (τ0.doms r.dom).slotGen r.slot from
            installDerived_slotGen τ0 E NS NL K P r.dom r.slot]
          exact hτ0gen r.dom r.slot
        have hτ2regions : ∀ d : DomainId,
            (τ2.doms d).regions = ((Hw.abs σ).doms d).regions := by
          intro d
          unfold τ2 τi τ0 MachineState.installDerived MachineState.setDom
          dsimp only
          by_cases hd : d = E
          · subst d
            rw [Loom.Fun.update_same, Loom.Fun.update_same,
              Loom.Fun.update_same, setReg_regions]
            exact refillPhase_regions m (Hw.abs σ) E
          · rw [Loom.Fun.update_ne _ _ _ _ hd,
              Loom.Fun.update_ne _ _ _ _ hd,
              Loom.Fun.update_ne _ _ _ _ hd]
            exact refillPhase_regions m (Hw.abs σ) d
        have hauthτ2 : ∀ (ow : Expr 2) (sa : Expr 12),
            ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
              (List.finRange numRegions).map fun r =>
                Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
                  Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                    ⟨false, true, false⟩])).eval σ = 1#1) ↔
              τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
                ⟨false, true, false⟩ = true := by
          intro ow sa
          rw [sAuth_quiescent_eval σ hin.killed hmapz hunmapz ow sa]
          rw [MachineState.domCovers, MachineState.domCovers]
          simp only [hτ2regions]
        have hmemτ2 : ∀ b : Addr,
            ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems
              "mem" b.toNat 32 = τ2.mem b := by
          intro b
          rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
          rw [refill_pres_mem m σ "mem" b.toNat 32]
          rfl
        have hswτ2 : ∀ sc : Expr 12, Expr.eval σ
            (((List.finRange numDomains).foldr
              (fun d acc' =>
                Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d,
                    Hw.isMn "sw", Hw.domCoversE d
                      (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                      ⟨false, true, false⟩,
                    .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                      0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
              (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
          intro sc
          rw [srcWord_quiescent σ hswz sc]
          rfl
        refine square_retire_install m hwf hfit σ hsync hifv hcl hin X τ2
          hcoreR ?_ hspec habsD habsG hjob ?_ ?_ ?_ ?_ hauthτ2 hmemτ2
          hswτ2 ?_ ?_
        · unfold X
          exact ifv_notin_dupX E
        · intro hv
          exact hwcaps _ (watched_live_of_reachable m σ hsr hv).1
        · intro _
          exact hwgen _
        · intro hv
          exact hwcaps _ (watched_live_of_reachable m σ hsr hv).2
        · intro _
          exact hwgen _
        · rfl
        · rfl
  case pos =>
  -- memory kind: narrowing applies
  have hmk : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) = .mem ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12)
      ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13) (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) :=
    (decKind_mem_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mp hmem
  have hkm1 : (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = 1#1 := by
    show (if ((Hw.dupSel E).kindW.eval σ).extractLsb' 0 1
        = (Expr.lit 0).eval σ then (1#1 : BitVec 1) else 0#1) = 1#1
    rw [show ((Expr.lit 0 : Expr 1)).eval σ = 0#1 from rfl]
    simp only [hkwE]
    rw [if_pos ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 0).mpr hmem)]
  have hklenE : (Hw.kLen (Hw.dupSel E).kindW).eval σ
      = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13 := by
    show ((Hw.dupSel E).kindW.eval σ).extractLsb' 13 13 = _
    rw [hkwE]
  have hkbaseE : (Hw.kBase (Hw.dupSel E).kindW).eval σ
      = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12 := by
    show ((Hw.dupSel E).kindW.eval σ).extractLsb' 1 12 = _
    rw [hkwE]
  have hoffE : (Hw.descOffE (Hw.readReg E Hw.rs2E)).eval σ = DWv.extractLsb' 5 12 := by
    show ((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12 = _
    rw [hR2]
  have hlenE : (Hw.descLenE (Hw.readReg E Hw.rs2E)).eval σ = DWv.extractLsb' 17 13 := by
    show ((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 17 13 = _
    rw [hR2]
  -- range check
  by_cases hr1 : ((DWv.extractLsb' 5 12).toNat
      + (DWv.extractLsb' 17 13).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)
  case neg =>
    -- narrow out of range
    have hc3 : (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14) (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14) (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1 := by
      show ((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
        (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14)
          (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
            (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ) = 1#1
      rw [hkm1]
      rw [(ultE_eval _ _ σ).mpr (by
        show (((Hw.kLen (Hw.dupSel E).kindW).eval σ).setWidth 14).toNat
          < ((((Hw.descOffE (Hw.readReg E Hw.rs2E)).eval σ).setWidth 14)
            + (((Hw.descLenE (Hw.readReg E Hw.rs2E)).eval σ).setWidth 14)).toNat
        rw [hklenE, hoffE, hlenE, toNat_setWidth_le (by omega)]
        rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
          toNat_setWidth_le (by omega)]
        have b1 := (DWv.extractLsb' 5 12).isLt
        have b2 := (DWv.extractLsb' 17 13).isLt
        rw [Nat.mod_eq_of_lt (by omega)]
        omega)]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.outOfRange.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_pos hc3]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = false from
        decide_eq_false hr1]
      rfl
  case pos =>
  have hc3z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14) (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14) (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
      (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14)
        (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
          (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ = 1#1)
    rw [bv1_ne_one.mp (show ¬((Expr.ult
        (.zext (Hw.kLen (Hw.dupSel E).kindW) 14)
        (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
          (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ = 1#1) from by
      intro hc
      have h2 : ((((Hw.dupSel E).kindW.eval σ).extractLsb' 13 13
          ).setWidth 14).toNat
          < (((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
            ).setWidth 14)
            + ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 17 13
              ).setWidth 14)).toNat :=
        (ultE_eval _ _ σ).mp hc
      rw [hkwE, hR2] at h2
      rw [toNat_setWidth_le (by omega), BitVec.toNat_add,
        toNat_setWidth_le (by omega), toNat_setWidth_le (by omega)] at h2
      have b1 := (DWv.extractLsb' 5 12).isLt
      have b2 := (DWv.extractLsb' 17 13).isLt
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      omega)]
    generalize (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = b
    revert b
    decide
  -- one-bit extract as ofBool (for the perm-bit walks)
  have hEx1 : ∀ {n : Nat} (x : BitVec n) (i : Nat),
      x.extractLsb' i 1 = BitVec.ofBool (x.getLsbD i) := by
    intro n x i
    cases h : x.getLsbD i
    · rw [(extract1_eq_zero_iff x i).mpr h]; rfl
    · rw [(extract1_eq_one_iff x i).mpr h]; rfl
  -- no-wrap check
  by_cases hr2 : (((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
      + (DWv.extractLsb' 5 12).toNat < 4096)
  case neg =>
    -- narrowed base out of physical memory
    have hult0 : ¬((Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ = 1#1) := by
      intro hc
      have h2 : ((((Hw.dupSel E).kindW.eval σ).extractLsb' 1 12
          ).setWidth 13
          + (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
            ).setWidth 13).toNat
          < ((4096 : BitVec 13)).toNat :=
        (ultE_eval _ _ σ).mp hc
      rw [hkwE, hR2] at h2
      rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
        toNat_setWidth_le (by omega)] at h2
      have b1 := ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).isLt
      have b2 := (DWv.extractLsb' 5 12).isLt
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      exact hr2 (by
        have h3 : ((4096 : BitVec 13)).toNat = 4096 := rfl
        omega)
    have hc4 : (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
        (Expr.not (Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)))).eval σ = 1#1 := by
      show ((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
        ~~~((Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ)) = 1#1
      rw [hkm1, bv1_ne_one.mp hult0]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.outOfRange.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_neg hc3z,
        if_pos hc4]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = false from decide_eq_false hr2]
      rfl
  case pos =>
  have hult1 : (Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ = 1#1 := by
    rw [ultE_eval]
    show ((((Hw.dupSel E).kindW.eval σ).extractLsb' 1 12).setWidth 13
      + (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
        ).setWidth 13).toNat < ((4096 : BitVec 13)).toNat
    rw [hkwE, hR2]
    rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
      toNat_setWidth_le (by omega)]
    have b1 := ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).isLt
    have b2 := (DWv.extractLsb' 5 12).isLt
    rw [Nat.mod_eq_of_lt (by omega)]
    show _ < (4096 : BitVec 13).toNat
    have h3 : ((4096 : BitVec 13)).toNat = 4096 := rfl
    omega
  have hc4z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
      (Expr.not (Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
      ~~~((Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ) = 1#1)
    rw [hult1]
    generalize (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = b
    revert b
    decide
  -- permission checks
  have hpermsOr : ((Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))]).eval σ = 1#1)
      ↔ ¬((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) = true) := by
    show ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 2 1 &&&
        ~~~(((Hw.dupSel E).kindW.eval σ).extractLsb' 26 1)) |||
      ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 3 1 &&&
        ~~~(((Hw.dupSel E).kindW.eval σ).extractLsb' 27 1)) |||
       (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 4 1 &&&
        ~~~(((Hw.dupSel E).kindW.eval σ).extractLsb' 28 1)))) = 1#1 ↔ _
    rw [hkwE, hR2]
    rw [show (Machines.Lnp64u.Isa.descPerms DWv)
        = ⟨DWv.getLsbD 2, DWv.getLsbD 3, DWv.getLsbD 4⟩ from rfl]
    rw [show (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))
        = ⟨(σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 26, (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 27, (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 28⟩ from by
      show (⟨((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 0,
        ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 1,
        ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 2⟩ : Perms) = _
      simp [BitVec.getLsbD_extractLsb']]
    rw [hEx1 DWv 2, hEx1 DWv 3, hEx1 DWv 4,
      hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 26, hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 27, hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 28]
    cases DWv.getLsbD 2 <;> cases DWv.getLsbD 3 <;> cases DWv.getLsbD 4 <;>
      cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 26 <;> cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 27 <;>
      cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 28 <;> simp [Perms.le]
  by_cases hr3 : ((Machines.Lnp64u.Isa.descPerms DWv).le
      (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) = true)
  case neg =>
    -- permission escalation
    have hc5 : (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))])).eval σ
        = 1#1 := by
      show ((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
        (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))]).eval σ) = 1#1
      rw [hkm1, hpermsOr.mpr hr3]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.permDenied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_neg hc3z,
        if_neg hc4z,
        if_pos hc5]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = false from by
        cases h : ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)))
        · rfl
        · exact absurd h hr3]
      rfl
  case pos =>
  have hc5z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
      (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))])).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
      (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))]).eval σ = 1#1)
    rw [bv1_ne_one.mp (fun hc => (hpermsOr.mp hc) hr3)]
    generalize (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = b
    revert b
    decide
  -- W^X check
  have hwxOr : ((Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ = 1#1)
      ↔ ¬((Machines.Lnp64u.Isa.descPerms DWv).wx = true) := by
    show ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 3 1) &&&
      (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 4 1)) = 1#1 ↔ _
    rw [hR2]
    rw [show (Machines.Lnp64u.Isa.descPerms DWv)
        = ⟨DWv.getLsbD 2, DWv.getLsbD 3, DWv.getLsbD 4⟩ from rfl]
    rw [hEx1 DWv 3, hEx1 DWv 4]
    cases DWv.getLsbD 3 <;> cases DWv.getLsbD 4 <;> simp [Perms.wx]
  by_cases hr4 : ((Machines.Lnp64u.Isa.descPerms DWv).wx = true)
  case neg =>
    -- W^X violation
    have hc6 : (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ
        = 1#1 := by
      show ((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
        (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ) = 1#1
      rw [hkm1, hwxOr.mpr hr4]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.permDenied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_neg hc3z,
        if_neg hc4z,
        if_neg hc5z,
        if_pos hc6]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = false from by
        cases h : ((Machines.Lnp64u.Isa.descPerms DWv).wx)
        · rfl
        · exact absurd h hr4]
      rfl
  case pos =>
  have hc6z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
      (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
      (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ = 1#1)
    rw [bv1_ne_one.mp (fun hc => absurd hr4 (fun h4 =>
      (hwxOr.mp hc) h4))]
    generalize (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = b
    revert b
    decide
  -- free-slot / free-cell bridges (the pc bump touches neither table)
  have hcapsB : ∀ s : Slot, (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).caps s
      = ((Hw.abs σ).doms E).caps s := fun s => by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
      ({ (refillPhase m (Hw.abs σ)).doms E with
        pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).caps s = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).caps s = _
    rw [refillPhase_caps]
  have hgenB : ∀ s : Slot, (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).slotGen s
      = ((Hw.abs σ).doms E).slotGen s := fun s => by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
      ({ (refillPhase m (Hw.abs σ)).doms E with
        pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).slotGen s
      = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).slotGen s = _
    rw [refillPhase_slotGen]
  have hlinB : ∀ l : LineageId, (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).lineage l
      = ((Hw.abs σ).doms E).lineage l := fun l => by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
      ({ (refillPhase m (Hw.abs σ)).doms E with
        pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).lineage l
      = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).lineage l = _
    rw [refillPhase_lineage]
  have hfsB : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).freeSlot E = (Hw.abs σ).freeSlot E :=
    freeSlot_congr _ _ E hcapsB hgenB
  have hfcB : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).freeCell E = (Hw.abs σ).freeCell E :=
    freeCell_congr _ _ E hlinB
  cases hfs : (Hw.abs σ).freeSlot E with
  | none =>
    -- no free slot
    have hfsv0 : ¬((Hw.freeSlotV E).eval σ = 1#1) := fun hc => by
      have h2 := (freeSlotV_eval σ E).mp hc
      rw [hfs] at h2
      exact absurd h2 (by decide)
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.slotOccupied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_neg hc3z,
        if_neg hc4z,
        if_neg hc5z,
        if_neg hc6z,
        if_pos (show (Expr.not (Hw.freeSlotV E)).eval σ = 1#1 from by
          show ~~~((Hw.freeSlotV E).eval σ) = 1#1
          rw [bv1_ne_one.mp hfsv0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = true from hr4]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [Machines.Lnp64u.Isa.allocDerived, SpecM.get, specM_bind,
        SpecM.raise, specM_pure]
      rw [hfsB.trans hfs]
      rfl
  | some NS =>
    have hfsv1 : (Hw.freeSlotV E).eval σ = 1#1 :=
      (freeSlotV_eval σ E).mpr (by rw [hfs]; rfl)
    cases hfc : (Hw.abs σ).freeCell E with
    | none =>
      -- no free lineage cell
      have hfcv0 : ¬((Hw.freeCellV E).eval σ = 1#1) := fun hc => by
        have h2 := (freeCellV_eval σ E).mp hc
        rw [hfc] at h2
        exact absurd h2 (by decide)
      refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
        hswz hben5 E rfl Errno.noLineage.toWord ?_ ?_
      · intro acc
        rw [hladder acc,
          if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
            show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
            rw [hliv1]
            decide),
          if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
            show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
            rw [hcls1]
            decide),
          if_neg hc3z,
          if_neg hc4z,
          if_neg hc5z,
          if_neg hc6z,
          if_neg (show ¬((Expr.not (Hw.freeSlotV E)).eval σ = 1#1) from by
            show ¬(~~~((Hw.freeSlotV E).eval σ) = 1#1)
            rw [hfsv1]
            decide),
          if_pos (show (Expr.not (Hw.freeCellV E)).eval σ = 1#1 from by
            show ~~~((Hw.freeCellV E).eval σ) = 1#1
            rw [bv1_ne_one.mp hfcv0]
            decide)]
        rfl
      · rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        simp only [hRD, hRD2]
        simp only [hlcS', hcek]
        rw [hdecT]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [hcek]
        simp only [hmk]
        simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
          SpecM.raise, specM_pure]
        rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
            + (Machines.Lnp64u.Isa.descLen DWv).toNat
            ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
          decide_eq_true hr1]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
            + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
            = true from decide_eq_true hr2]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
            (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = true from hr4]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [Machines.Lnp64u.Isa.allocDerived, SpecM.get, specM_bind,
          SpecM.raise, specM_pure]
        rw [hfsB.trans hfs]
        simp only [specM_bind, specM_pure]
        rw [hfcB.trans hfc]
        rfl
    | some NL =>
      -- install (mem kind)
      have hsidx : (Hw.freeSlotIdx E).eval σ = BitVec.ofNat 4 NS.val :=
        freeSlotIdx_eval σ E NS hfs
      have hlidx : (Hw.freeCellIdx E).eval σ = BitVec.ofNat 4 NL.val :=
        freeCellIdx_eval σ E NL hfc
      let S : Slot := finOfBv (by decide) (HWv.extractLsb' 0 4)
      let K : CapKind := .mem
        ((σ.regs (Hw.dcapKind E S) 32).extractLsb' 1 12 +
          Machines.Lnp64u.Isa.descOff DWv)
        (Machines.Lnp64u.Isa.descLen DWv)
        (Machines.Lnp64u.Isa.descPerms DWv)
      let P : CapRef := ⟨E, S, HWv.extractLsb' 4 8⟩
      let G : Gen := ((Hw.abs σ).doms E).slotGen NS
      let V : BitVec 32 := Handle.encode ⟨NS, G, .mem⟩
      have hkind : (Expr.mux (Hw.kIsMem (Hw.dupSel E).kindW)
          (Hw.narrowKindE (Hw.dupSel E).kindW (Hw.readReg E Hw.rs2E))
          (Hw.dupSel E).kindW).eval σ = Hw.encKind K := by
        show (if (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = 1#1
          then (Hw.narrowKindE (Hw.dupSel E).kindW
            (Hw.readReg E Hw.rs2E)).eval σ
          else (Hw.dupSel E).kindW.eval σ) = _
        rw [if_pos hkm1, narrowKindE_pack, hkwE, hR2]
      have hparent : (Hw.encRefE (Hw.dLit E) (Hw.dupSel E).slot
          (Hw.dupSel E).gen).eval σ = Hw.encRef P := by
        simpa only [Hw.dupSel, hR1] using
          (encRefE_sel_eval σ E (Hw.readReg E Hw.rs1E))
      have hgenE : (Hw.genOfE E (Hw.freeSlotIdx E)).eval σ = G := by
        rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots)]
        have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
            ((Hw.freeSlotIdx E).eval σ) = NS := by
          rw [hsidx]
          exact finOfBv_ofNat4 (by decide) NS
        rw [hfin]
        rfl
      have hclsE : (Hw.field (Hw.dupSel E).kindW 0 1).eval σ = 0#1 := by
        show ((Hw.dupSel E).kindW.eval σ).extractLsb' 0 1 = 0#1
        rw [hkwE]
        exact (extract1_eq_zero_iff _ 0).mpr hmem
      have hval : (Hw.handleE (Hw.freeSlotIdx E)
          (Hw.genOfE E (Hw.freeSlotIdx E))
          (Hw.field (Hw.dupSel E).kindW 0 1)).eval σ = V := by
        rw [handleE_pack σ _ _ _ .mem (by simpa using hclsE), hsidx,
          hgenE]
        show Handle.encode
          ⟨finOfBv (by decide) (BitVec.ofNat 4 NS.val), G, .mem⟩ = V
        rw [finOfBv_ofNat4]
      let τ0 : MachineState :=
        ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })
      let τi : MachineState := (τ0.installDerived E NS NL K P).1
      let τ2 : MachineState := τi.setDom E
        (fun ds => ds.setReg (operandsOf W).rd V)
      have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
        rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        simp only [hRD, hRD2, hlcS', hcek]
        rw [hdecT]
        simp only [reduceIte, specM_bind, specM_pure, hcek, hmk]
        simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
          SpecM.raise, specM_pure]
        rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
            + (Machines.Lnp64u.Isa.descLen DWv).toNat
            ≤ ((σ.regs (Hw.dcapKind E S) 32).extractLsb' 13 13).toNat))
            = true from decide_eq_true hr1]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show (decide (((σ.regs (Hw.dcapKind E S) 32).extractLsb'
            1 12).toNat + (Machines.Lnp64u.Isa.descOff DWv).toNat
            < memWords)) = true from decide_eq_true hr2]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
            (Hw.decPerms ((σ.regs (Hw.dcapKind E S) 32).extractLsb' 26 3)))
            = true from hr3]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show (Machines.Lnp64u.Isa.descPerms DWv).wx = true from hr4]
        simp only [reduceIte, specM_bind, specM_pure,
          Machines.Lnp64u.Isa.allocDerived, SpecM.get, SpecM.set,
          SpecM.modify, SpecM.raise]
        rw [hfsB.trans hfs]
        simp only [specM_bind, specM_pure]
        rw [hfcB.trans hfc]
        simp only [SpecM.set, SpecM.setReg, SpecM.modify, specM_bind,
          specM_pure]
        unfold τ2 τi τ0
        unfold MachineState.installDerived MachineState.setDom
        dsimp only
        apply machineState_ext' <;> try rfl
        funext d
        by_cases hd : d = E
        · subst d
          simp only [Loom.Fun.update_same]
          rw [refillPhase_caps, refillPhase_lineage]
          apply domainState_ext'
          · funext r
            by_cases h0 : (operandsOf W).rd = (0 : RegId) <;>
              by_cases hr : r = (operandsOf W).rd <;>
              simp [setReg_regs, h0, hr]
            unfold V G
            rfl
          · rw [setReg_pc, setReg_pc]
          · rw [setReg_caps, setReg_caps]
          · rw [setReg_slotGen, setReg_slotGen]
          · rw [setReg_lineage, setReg_lineage]
            unfold P S
            rfl
          · rw [setReg_regions, setReg_regions]
          · rw [setReg_run, setReg_run]
          · rw [setReg_serving, setReg_serving]
          · rw [setReg_cause, setReg_cause]
          · rw [setReg_budget, setReg_budget]
          · rw [setReg_maxDonation, setReg_maxDonation]
        · simp only [Loom.Fun.update_ne _ _ _ _ hd]
      let X : Act := Hw.seqAll
        [ Hw.installA E (Hw.freeSlotIdx E)
            (.mux (Hw.kIsMem (Hw.dupSel E).kindW)
              (Hw.narrowKindE (Hw.dupSel E).kindW
                (Hw.readReg E Hw.rs2E)) (Hw.dupSel E).kindW)
            (.lit 1) (Hw.freeCellIdx E)
            (Hw.encRefE (Hw.dLit E) (Hw.dupSel E).slot
              (Hw.dupSel E).gen),
          Hw.writeReg E Hw.rdE
            (Hw.handleE (Hw.freeSlotIdx E)
              (Hw.genOfE E (Hw.freeSlotIdx E))
              (Hw.field (Hw.dupSel E).kindW 0 1)),
          Hw.pcAdvA E ]
      have hcoreR : ∀ (rn : String) (w : Nat),
          ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
            ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
              ((Hw.refillAct m).run σ σ)).regs rn w := by
        intro rn w
        rw [coreAct_run_retire_eq m σ _ hifv hcl,
          retireAct_run_regs σ _ E rfl rn w, hladder]
        rw [if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1)
            from by show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
                    rw [hliv1]; decide),
          if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1)
            from by show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
                    rw [hcls1]; decide),
          if_neg hc3z, if_neg hc4z, if_neg hc5z, if_neg hc6z,
          if_neg (show ¬((Expr.not (Hw.freeSlotV E)).eval σ = 1#1)
            from by show ¬(~~~((Hw.freeSlotV E).eval σ) = 1#1)
                    rw [hfsv1]; decide),
          if_neg (show ¬((Expr.not (Hw.freeCellV E)).eval σ = 1#1)
            from by
              have hfcv1 : (Hw.freeCellV E).eval σ = 1#1 :=
                (freeCellV_eval σ E).mpr (by rw [hfc]; rfl)
              show ¬(~~~((Hw.freeCellV E).eval σ) = 1#1)
              rw [hfcv1]
              decide)]
        rfl
      have habsD : ∀ x,
          Hw.absDom ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
            ((Hw.refillAct m).run σ σ)) x = τ2.doms x := by
        intro x
        change Hw.absDom ((dupFull E).run σ
          ((Hw.refillAct m).run σ σ)) x = τ2.doms x
        by_cases hx : x = E
        · subst x
          rw [absDom_dupFull_install m σ E NS NL K P
            (operandsOf W).rd V hsidx hlidx hkind hparent rfl hval]
          rw [← hL1 E]
          unfold τ2 τi τ0 MachineState.installDerived MachineState.setDom
          dsimp only
          rw [Loom.Fun.update_same, Loom.Fun.update_same,
            Loom.Fun.update_same]
          rw [refillPhase_caps, refillPhase_lineage]
        · rw [absDom_dupFull_ne m σ E x hx, ← hL1 x]
          unfold τ2 τi τ0 MachineState.installDerived MachineState.setDom
          dsimp only
          rw [Loom.Fun.update_ne _ _ _ _ hx,
            Loom.Fun.update_ne _ _ _ _ hx,
            Loom.Fun.update_ne _ _ _ _ hx]
      have habsG : ∀ g,
          Hw.absGate ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
            ((Hw.refillAct m).run σ σ)) g = τ2.gates g := by
        intro g
        change Hw.absGate ((dupFull E).run σ
          ((Hw.refillAct m).run σ σ)) g = τ2.gates g
        rw [absGate_dupFull m σ E g, ← hG1 g]
        rfl
      have hjob : τ2.mover = Hw.absMover σ := by
        show (refillPhase m (Hw.abs σ)).mover = Hw.absMover σ
        rw [refillPhase_mover]
        rfl
      have hτ0caps : ∀ (d : DomainId) (s : Slot),
          (τ0.doms d).caps s = ((Hw.abs σ).doms d).caps s := by
        intro d s
        unfold τ0 MachineState.setDom
        dsimp only
        by_cases hd : d = E
        · subst d
          rw [Loom.Fun.update_same]
          exact congrFun (refillPhase_caps m (Hw.abs σ) E) s
        · rw [Loom.Fun.update_ne _ _ _ _ hd]
          exact congrFun (refillPhase_caps m (Hw.abs σ) d) s
      have hτ0gen : ∀ (d : DomainId) (s : Slot),
          (τ0.doms d).slotGen s = ((Hw.abs σ).doms d).slotGen s := by
        intro d s
        unfold τ0 MachineState.setDom
        dsimp only
        by_cases hd : d = E
        · subst d
          rw [Loom.Fun.update_same]
          exact congrFun (refillPhase_slotGen m (Hw.abs σ) E) s
        · rw [Loom.Fun.update_ne _ _ _ _ hd]
          exact congrFun (refillPhase_slotGen m (Hw.abs σ) d) s
      have hfree0 : (τ0.doms E).caps NS = none := by
        rw [hτ0caps E NS]
        exact freeSlot_caps_none (Hw.abs σ) E hfs
      have hwcaps : ∀ (r : CapRef),
          (∃ ce, ((Hw.abs σ).doms r.dom).liveCap r.slot r.gen = some ce) →
          (τ2.doms r.dom).caps r.slot =
            ((Hw.abs σ).doms r.dom).caps r.slot := by
        intro r hlive
        have hlive0 : ∃ ce, (τ0.doms r.dom).liveCap r.slot r.gen = some ce := by
          obtain ⟨ce, hce⟩ := hlive
          refine ⟨ce, ?_⟩
          unfold DomainState.liveCap
          rw [hτ0caps r.dom r.slot, hτ0gen r.dom r.slot]
          exact hce
        have hi := installDerived_caps_at_live τ0 E NS NL K P r
          hfree0 hlive0
        show ((τi.setDom E (fun ds => ds.setReg (operandsOf W).rd V)).doms
            r.dom).caps r.slot = _
        rw [show ((τi.setDom E
            (fun ds => ds.setReg (operandsOf W).rd V)).doms r.dom).caps
              r.slot = (τi.doms r.dom).caps r.slot from by
          unfold MachineState.setDom
          dsimp only
          by_cases hd : r.dom = E
          · rw [hd, Loom.Fun.update_same, setReg_caps]
          · rw [Loom.Fun.update_ne _ _ _ _ hd]]
        exact hi.trans (hτ0caps r.dom r.slot)
      have hwgen : ∀ (r : CapRef),
          (τ2.doms r.dom).slotGen r.slot =
            ((Hw.abs σ).doms r.dom).slotGen r.slot := by
        intro r
        show ((τi.setDom E (fun ds => ds.setReg (operandsOf W).rd V)).doms
            r.dom).slotGen r.slot = _
        rw [show ((τi.setDom E
            (fun ds => ds.setReg (operandsOf W).rd V)).doms r.dom).slotGen
              r.slot = (τi.doms r.dom).slotGen r.slot from by
          unfold MachineState.setDom
          dsimp only
          by_cases hd : r.dom = E
          · rw [hd, Loom.Fun.update_same, setReg_slotGen]
          · rw [Loom.Fun.update_ne _ _ _ _ hd]]
        rw [show (τi.doms r.dom).slotGen r.slot =
            (τ0.doms r.dom).slotGen r.slot from
          installDerived_slotGen τ0 E NS NL K P r.dom r.slot]
        exact hτ0gen r.dom r.slot
      have hτ2regions : ∀ d : DomainId,
          (τ2.doms d).regions = ((Hw.abs σ).doms d).regions := by
        intro d
        unfold τ2 τi τ0 MachineState.installDerived MachineState.setDom
        dsimp only
        by_cases hd : d = E
        · subst d
          rw [Loom.Fun.update_same, Loom.Fun.update_same,
            Loom.Fun.update_same, setReg_regions]
          exact refillPhase_regions m (Hw.abs σ) E
        · rw [Loom.Fun.update_ne _ _ _ _ hd,
            Loom.Fun.update_ne _ _ _ _ hd,
            Loom.Fun.update_ne _ _ _ _ hd]
          exact refillPhase_regions m (Hw.abs σ) d
      have hauthτ2 : ∀ (ow : Expr 2) (sa : Expr 12),
          ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
            (List.finRange numRegions).map fun r =>
              Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
                Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                  ⟨false, true, false⟩])).eval σ = 1#1) ↔
            τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
              ⟨false, true, false⟩ = true := by
        intro ow sa
        rw [sAuth_quiescent_eval σ hin.killed hmapz hunmapz ow sa]
        rw [MachineState.domCovers, MachineState.domCovers]
        simp only [hτ2regions]
      have hmemτ2 : ∀ b : Addr,
          ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems
            "mem" b.toNat 32 = τ2.mem b := by
        intro b
        rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
        rw [refill_pres_mem m σ "mem" b.toNat 32]
        rfl
      have hswτ2 : ∀ sc : Expr 12, Expr.eval σ
          (((List.finRange numDomains).foldr
            (fun d acc' =>
              Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d,
                  Hw.isMn "sw", Hw.domCoversE d
                    (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                    ⟨false, true, false⟩,
                  .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                    0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
            (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
        intro sc
        rw [srcWord_quiescent σ hswz sc]
        rfl
      refine square_retire_install m hwf hfit σ hsync hifv hcl hin X τ2
        hcoreR ?_ hspec habsD habsG hjob ?_ ?_ ?_ ?_ hauthτ2 hmemτ2
        hswτ2 ?_ ?_
      · unfold X
        exact ifv_notin_dupX E
      · intro hv
        exact hwcaps _ (watched_live_of_reachable m σ hsr hv).1
      · intro _
        exact hwgen _
      · intro hv
        exact hwcaps _ (watched_live_of_reachable m σ hsr hv).2
      · intro _
        exact hwgen _
      · rfl
      · rfl

end Machines.Lnp64u.Theorems.RMC

