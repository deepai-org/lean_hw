-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCOps
import Machines.Lnp64u.Theorems.RMCRefill

/-!
# R-MC support: the halt bridge (`haltAct` ↔ `haltDom`)

Every fault path in the design — fetch/decode/budget faults at issue and
every per-op `Fault` arm at retirement — runs `haltAct`: halt the domain,
set the cause, and unwind a served gate activation to its caller. The
spec side is `Kernel.haltDom` (through `Step.haltWith`). This file
characterizes the circuit's run shape with the guarded-fold dispatch
lemmas (the gate and caller loops have mutually exclusive index-equality
conditions) and will carry the abs-level bridge.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## Run-shape characterizations -/

/-- The three unconditional halt writes. -/
private def haltBase3 (d : DomainId) (cause : BitVec 32) : Act :=
  .seq (.write 2 (Hw.drun d) (.lit 1)) <|
  .seq (.write 32 (Hw.dcause d) (.lit cause)) <|
  (.write 1 (Hw.dsrvV d) (.lit 0))

/-- The per-gate unwind arm's condition. -/
private def gateCond (d : DomainId) (g : GateId) : Expr 1 :=
  Hw.andAll [.reg 1 (Hw.dsrvV d),
    .eq (.reg 2 (Hw.dsrv d)) (.lit (BitVec.ofNat 2 g.val)),
    .reg 1 (Hw.gactV g)]

/-- The per-gate unwind arm's body. -/
private def gateBody (_d : DomainId) (g : GateId) : Act :=
  .seq (.write 1 (Hw.gactV g) (.lit 0))
    (Hw.seqAll <| (List.finRange numDomains).map fun c =>
      .ite (.eq (.reg 2 (Hw.gcaller g)) (.lit (BitVec.ofNat 2 c.val)))
        (.seq (.write 2 (Hw.drun c) (.lit 0))
          (Hw.writeReg c (.reg 3 (Hw.gcallerRd g)) (.lit Errno.calleeFault.toWord)))
        .skip)

private theorem haltAct_shape (d : DomainId) (cause : BitVec 32) :
    Hw.haltAct d cause =
      .seq (.write 2 (Hw.drun d) (.lit 1))
        (.seq (.write 32 (Hw.dcause d) (.lit cause))
          (.seq (.write 1 (Hw.dsrvV d) (.lit 0))
            (Hw.seqAll <| (List.finRange numGates).map fun g =>
              .ite (gateCond d g) (gateBody d g) .skip))) := rfl

/-- The unwind loop is off when `d` is not serving. -/
theorem haltAct_run_of_not_serving (σ acc : Loom.Hw.St) (d : DomainId)
    (cause : BitVec 32) (hsv : σ.regs (Hw.dsrvV d) 1 ≠ 1#1) :
    (Hw.haltAct d cause).run σ acc = (haltBase3 d cause).run σ acc := by
  rw [haltAct_shape]
  show (Hw.seqAll ((List.finRange numGates).map fun g =>
      Act.ite (gateCond d g) (gateBody d g) .skip)).run σ
    ((haltBase3 d cause).run σ acc) = _
  exact seqAll_ite_run_none σ _ _ _ _ (fun g _ => by
    show ¬((σ.regs (Hw.dsrvV d) 1 &&&
      ((Expr.eq (.reg 2 (Hw.dsrv d)) (.lit (BitVec.ofNat 2 g.val))).eval σ &&&
       σ.regs (Hw.gactV g) 1)) = 1#1)
    rw [bv1_ne_one.mp hsv]
    generalize ((Expr.eq (.reg 2 (Hw.dsrv d))
      (.lit (BitVec.ofNat 2 g.val))).eval σ &&& σ.regs (Hw.gactV g) 1) = b
    revert b
    decide)

/-- The unwind loop is off when the served gate has no live activation. -/
theorem haltAct_run_of_no_act (σ acc : Loom.Hw.St) (d : DomainId)
    (cause : BitVec 32)
    (g : GateId) (hg : g.val = (σ.regs (Hw.dsrv d) 2).toNat)
    (hact : σ.regs (Hw.gactV g) 1 ≠ 1#1) :
    (Hw.haltAct d cause).run σ acc = (haltBase3 d cause).run σ acc := by
  rw [haltAct_shape]
  show (Hw.seqAll ((List.finRange numGates).map fun g' =>
      Act.ite (gateCond d g') (gateBody d g') .skip)).run σ
    ((haltBase3 d cause).run σ acc) = _
  refine seqAll_ite_run_none σ _ _ _ _ (fun g' _ => ?_)
  show ¬((σ.regs (Hw.dsrvV d) 1 &&&
    ((Expr.eq (.reg 2 (Hw.dsrv d)) (.lit (BitVec.ofNat 2 g'.val))).eval σ &&&
     σ.regs (Hw.gactV g') 1)) = 1#1)
  by_cases hgg : g' = g
  · subst hgg
    rw [bv1_ne_one.mp hact]
    generalize σ.regs (Hw.dsrvV d) 1 = a
    generalize (Expr.eq (.reg 2 (Hw.dsrv d))
      (.lit (BitVec.ofNat 2 g'.val))).eval σ = b
    revert a b
    decide
  · have hne : (Expr.eq (.reg 2 (Hw.dsrv d))
        (.lit (BitVec.ofNat 2 g'.val))).eval σ = 0#1 := by
      apply bv1_ne_one.mp
      intro hc
      rw [eqE_eval] at hc
      apply hgg
      apply Fin.ext
      have hc' : σ.regs (Hw.dsrv d) 2 = BitVec.ofNat 2 g'.val := hc
      rw [hg, hc', BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by have := g'.isLt; omega)).symm
    rw [hne]
    generalize σ.regs (Hw.dsrvV d) 1 = a
    generalize σ.regs (Hw.gactV g') 1 = c
    revert a c
    decide

/-- With `d` serving gate `g` (live activation), the halt is the base
writes plus exactly `g`'s unwind. -/
theorem haltAct_run_of_serving (σ acc : Loom.Hw.St) (d : DomainId)
    (cause : BitVec 32) (g : GateId)
    (hg : g.val = (σ.regs (Hw.dsrv d) 2).toNat)
    (hsv : σ.regs (Hw.dsrvV d) 1 = 1#1)
    (hact : σ.regs (Hw.gactV g) 1 = 1#1) :
    (Hw.haltAct d cause).run σ acc
      = (gateBody d g).run σ ((haltBase3 d cause).run σ acc) := by
  rw [haltAct_shape]
  show (Hw.seqAll ((List.finRange numGates).map fun g' =>
      Act.ite (gateCond d g') (gateBody d g') .skip)).run σ
    ((haltBase3 d cause).run σ acc) = _
  refine seqAll_ite_run_unique σ _ _ _ g ?_ ?_ _ (List.mem_finRange g)
    (List.nodup_finRange _)
  · show (σ.regs (Hw.dsrvV d) 1 &&&
      ((Expr.eq (.reg 2 (Hw.dsrv d)) (.lit (BitVec.ofNat 2 g.val))).eval σ &&&
       σ.regs (Hw.gactV g) 1)) = 1#1
    rw [hsv, hact, show (Expr.eq (.reg 2 (Hw.dsrv d))
        (.lit (BitVec.ofNat 2 g.val))).eval σ = 1#1 from by
      rw [eqE_eval]
      show σ.regs (Hw.dsrv d) 2 = BitVec.ofNat 2 g.val
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, ← hg]
      exact (Nat.mod_eq_of_lt (by have := g.isLt; omega)).symm]
    decide
  · intro g' hne
    show ¬((σ.regs (Hw.dsrvV d) 1 &&&
      ((Expr.eq (.reg 2 (Hw.dsrv d)) (.lit (BitVec.ofNat 2 g'.val))).eval σ &&&
       σ.regs (Hw.gactV g') 1)) = 1#1)
    have hne' : (Expr.eq (.reg 2 (Hw.dsrv d))
        (.lit (BitVec.ofNat 2 g'.val))).eval σ = 0#1 := by
      apply bv1_ne_one.mp
      intro hc
      rw [eqE_eval] at hc
      apply hne
      apply Fin.ext
      have hc' : σ.regs (Hw.dsrv d) 2 = BitVec.ofNat 2 g'.val := hc
      rw [hg, hc', BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by have := g'.isLt; omega)).symm
    rw [hne']
    generalize σ.regs (Hw.dsrvV d) 1 = a
    generalize σ.regs (Hw.gactV g') 1 = c
    revert a c
    decide


/-- The architectural register write: a no-op for `r0`, else exactly one
register write at the decoded index. -/
theorem writeReg_run_of_zero (σ acc : Loom.Hw.St) (c : DomainId)
    (rE : Expr 3) (vE : Expr 32) (hr : (rE.eval σ).toNat = 0) :
    (Hw.writeReg c rE vE).run σ acc = acc := by
  rw [Hw.writeReg, show (List.finRange numRegs).filterMap
      (fun i => if i.val = 0 then none
        else some (Act.ite (.eq rE (.lit (BitVec.ofNat 3 i.val)))
          (.write 32 (Hw.dreg c i) vE) .skip))
    = ([1, 2, 3, 4, 5, 6, 7] : List RegId).map
      (fun i => Act.ite (.eq rE (.lit (BitVec.ofNat 3 i.val)))
        (.write 32 (Hw.dreg c i) vE) .skip) from rfl]
  refine seqAll_ite_run_none σ acc _ _ _ (fun i hi => ?_)
  intro hc
  rw [eqE_eval] at hc
  have : (rE.eval σ).toNat = i.val := by
    rw [hc, show (Expr.lit (BitVec.ofNat 3 i.val)).eval σ
      = BitVec.ofNat 3 i.val from rfl, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
  rw [hr] at this
  fin_cases hi <;> simp_all

theorem writeReg_run_of_nz (σ acc : Loom.Hw.St) (c : DomainId)
    (rE : Expr 3) (vE : Expr 32) (r : RegId)
    (hr : r.val = (rE.eval σ).toNat) (hnz : r.val ≠ 0) :
    (Hw.writeReg c rE vE).run σ acc
      = (Act.write 32 (Hw.dreg c r) vE).run σ acc := by
  rw [Hw.writeReg, show (List.finRange numRegs).filterMap
      (fun i => if i.val = 0 then none
        else some (Act.ite (.eq rE (.lit (BitVec.ofNat 3 i.val)))
          (.write 32 (Hw.dreg c i) vE) .skip))
    = ([1, 2, 3, 4, 5, 6, 7] : List RegId).map
      (fun i => Act.ite (.eq rE (.lit (BitVec.ofNat 3 i.val)))
        (.write 32 (Hw.dreg c i) vE) .skip) from rfl]
  refine seqAll_ite_run_unique σ acc _ _ r ?_ ?_ _ ?_ (by decide)
  · rw [eqE_eval]
    show rE.eval σ = BitVec.ofNat 3 r.val
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← hr]
    exact (Nat.mod_eq_of_lt (by have := r.isLt; omega)).symm
  · intro j hj hc
    rw [eqE_eval] at hc
    apply hj
    apply Fin.ext
    have : (rE.eval σ).toNat = j.val := by
      rw [hc, show (Expr.lit (BitVec.ofNat 3 j.val)).eval σ
        = BitVec.ofNat 3 j.val from rfl, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := j.isLt; omega)
    omega
  · fin_cases r <;> first | (exact absurd rfl hnz) | decide

/-- The unwind body selects exactly the caller domain. -/
theorem gateBody_run (σ acc : Loom.Hw.St) (d : DomainId) (g : GateId)
    (c : DomainId) (hc : c.val = (σ.regs (Hw.gcaller g) 2).toNat) :
    (gateBody d g).run σ acc
      = (Hw.writeReg c (.reg 3 (Hw.gcallerRd g))
          (.lit Errno.calleeFault.toWord)).run σ
        ((Act.write 2 (Hw.drun c) (.lit 0)).run σ
          ((Act.write 1 (Hw.gactV g) (.lit 0)).run σ acc)) := by
  show (Hw.seqAll ((List.finRange numDomains).map fun c' =>
      Act.ite (.eq (.reg 2 (Hw.gcaller g)) (.lit (BitVec.ofNat 2 c'.val)))
        (.seq (.write 2 (Hw.drun c') (.lit 0))
          (Hw.writeReg c' (.reg 3 (Hw.gcallerRd g))
            (.lit Errno.calleeFault.toWord)))
        .skip)).run σ
    ((Act.write 1 (Hw.gactV g) (.lit 0)).run σ acc) = _
  rw [seqAll_ite_run_unique σ _ _ _ c ?_ ?_ _ (List.mem_finRange c)
    (List.nodup_finRange _)]
  · rfl
  · rw [eqE_eval]
    show σ.regs (Hw.gcaller g) 2 = BitVec.ofNat 2 c.val
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← hc]
    exact (Nat.mod_eq_of_lt (by have := c.isLt; omega)).symm
  · intro j hj hcon
    rw [eqE_eval] at hcon
    apply hj
    apply Fin.ext
    have : σ.regs (Hw.gcaller g) 2 = BitVec.ofNat 2 j.val := hcon
    rw [hc, this, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := j.isLt; omega)).symm


/-! ## Name discrimination for the halt write set -/

private theorem drun_inj (x y : DomainId) : Hw.drun x = Hw.drun y ↔ x = y := by
  constructor
  · intro h
    fin_cases x <;> fin_cases y <;> first | rfl | (exact absurd h (by decide +kernel))
  · intro h; rw [h]

private theorem gactV_inj (x y : GateId) : Hw.gactV x = Hw.gactV y ↔ x = y := by
  constructor
  · intro h
    fin_cases x <;> fin_cases y <;> first | rfl | (exact absurd h (by decide +kernel))
  · intro h; rw [h]

/-! ## The abs-level bridge, base-only case -/

/-- Register reads through the three base writes. -/
private theorem base3_read (σ acc : Loom.Hw.St) (d : DomainId)
    (cause : BitVec 32) (rn : String) (w : Nat)
    (h1 : rn ≠ Hw.drun d) (h2 : rn ≠ Hw.dcause d) (h3 : rn ≠ Hw.dsrvV d) :
    ((haltBase3 d cause).run σ acc).regs rn w = acc.regs rn w := by
  show (((acc.regs.set (Hw.drun d) (1:BitVec 2)).set (Hw.dcause d)
    ((Expr.lit cause).eval σ)).set (Hw.dsrvV d) (0:BitVec 1)) rn w = _
  simp only [RegEnv.set]
  rw [if_neg h3, if_neg h2, if_neg h1]

private theorem base3_read_drun (σ acc : Loom.Hw.St) (d : DomainId)
    (cause : BitVec 32) :
    ((haltBase3 d cause).run σ acc).regs (Hw.drun d) 2 = 1#2 := by
  show (((acc.regs.set (Hw.drun d) (1:BitVec 2)).set (Hw.dcause d)
    ((Expr.lit cause).eval σ)).set (Hw.dsrvV d) (0:BitVec 1)) (Hw.drun d) 2 = _
  simp only [RegEnv.set]
  rw [if_neg (by fin_cases d <;> decide +kernel :
      Hw.drun d ≠ Hw.dsrvV d),
    if_neg (by fin_cases d <;> decide +kernel : Hw.drun d ≠ Hw.dcause d)]
  simp

private theorem base3_read_dcause (σ acc : Loom.Hw.St) (d : DomainId)
    (cause : BitVec 32) :
    ((haltBase3 d cause).run σ acc).regs (Hw.dcause d) 32 = cause := by
  show (((acc.regs.set (Hw.drun d) (1:BitVec 2)).set (Hw.dcause d)
    ((Expr.lit cause).eval σ)).set (Hw.dsrvV d) (0:BitVec 1)) (Hw.dcause d) 32 = _
  simp only [RegEnv.set]
  rw [if_neg (by fin_cases d <;> decide +kernel :
      Hw.dcause d ≠ Hw.dsrvV d)]
  simp [Expr.eval]

private theorem base3_read_dsrvV (σ acc : Loom.Hw.St) (d : DomainId)
    (cause : BitVec 32) :
    ((haltBase3 d cause).run σ acc).regs (Hw.dsrvV d) 1 = 0#1 := by
  show (((acc.regs.set (Hw.drun d) (1:BitVec 2)).set (Hw.dcause d)
    ((Expr.lit cause).eval σ)).set (Hw.dsrvV d) (0:BitVec 1)) (Hw.dsrvV d) 1 = _
  simp only [RegEnv.set]
  simp


/-- The base-only halt (no unwind): decoding the three writes is
`haltBase`. -/
theorem abs_haltBase3 (σ acc : Loom.Hw.St) (τ : MachineState) (d : DomainId)
    (cause : BitVec 32)
    (hdoms : ∀ x, Hw.absDom acc x = τ.doms x)
    (hgates : ∀ g, Hw.absGate acc g = τ.gates g) :
    (∀ x, Hw.absDom ((haltBase3 d cause).run σ acc) x
      = (τ.haltBase d cause).doms x) ∧
    (∀ g, Hw.absGate ((haltBase3 d cause).run σ acc) g
      = (τ.haltBase d cause).gates g) := by
  constructor
  · intro x
    show Hw.absDom _ x = (Loom.Fun.update τ.doms d _) x
    by_cases hxd : x = d
    · subst hxd
      rw [Loom.Fun.update_same]
      apply domainState_ext'
      · funext r
        rw [show (Hw.absDom ((haltBase3 x cause).run σ acc) x).regs r
            = ((haltBase3 x cause).run σ acc).regs (Hw.dreg x r) 32 from rfl,
          base3_read σ acc x cause _ _
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel)]
        exact congrFun (congrArg DomainState.regs (hdoms x)) r
      · rw [show (Hw.absDom ((haltBase3 x cause).run σ acc) x).pc
            = ((haltBase3 x cause).run σ acc).regs (Hw.dpc x) 12 from rfl,
          base3_read σ acc x cause _ _
            (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel)]
        exact congrArg DomainState.pc (hdoms x)
      · funext s
        show (if ((haltBase3 x cause).run σ acc).regs (Hw.dcapV x s) 1 = 1
          then _ else _) = _
        rw [base3_read σ acc x cause _ _
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          base3_read σ acc x cause (Hw.dcapKind x s) 32
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          base3_read σ acc x cause (Hw.dcapLinV x s) 1
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          base3_read σ acc x cause (Hw.dcapLin x s) 4
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel)]
        exact congrFun (congrArg DomainState.caps (hdoms x)) s
      · funext s
        show ((haltBase3 x cause).run σ acc).regs (Hw.dgen x s) 8 = _
        rw [base3_read σ acc x cause _ _
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel)]
        exact congrFun (congrArg DomainState.slotGen (hdoms x)) s
      · funext l
        show (if ((haltBase3 x cause).run σ acc).regs (Hw.dcellV x l) 1 = 1
          then _ else _) = _
        rw [base3_read σ acc x cause _ _
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel),
          base3_read σ acc x cause (Hw.dcellPar x l) 14
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel)]
        exact congrFun (congrArg DomainState.lineage (hdoms x)) l
      · funext r
        show (if ((haltBase3 x cause).run σ acc).regs (Hw.drgnV x r) 1 = 1
          then _ else _) = _
        rw [base3_read σ acc x cause _ _
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel),
          base3_read σ acc x cause (Hw.drgn x r) 42
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel)]
        exact congrFun (congrArg DomainState.regions (hdoms x)) r
      · show Hw.decRun (((haltBase3 x cause).run σ acc).regs (Hw.drun x) 2)
          _ = RunState.halted
        rw [base3_read_drun]
        rfl
      · show (if ((haltBase3 x cause).run σ acc).regs (Hw.dsrvV x) 1 = 1
          then _ else _) = _
        rw [base3_read_dsrvV]
        rfl
      · show ((haltBase3 x cause).run σ acc).regs (Hw.dcause x) 32 = _
        rw [base3_read_dcause]
      · show (((haltBase3 x cause).run σ acc).regs (Hw.dbudget x) 32).toNat = _
        rw [base3_read σ acc x cause _ _
            (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel)]
        exact congrArg DomainState.budget (hdoms x)
      · show (((haltBase3 x cause).run σ acc).regs (Hw.dmaxdon x) 32).toNat = _
        rw [base3_read σ acc x cause _ _
            (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel)]
        exact congrArg DomainState.maxDonation (hdoms x)
    · rw [Loom.Fun.update_ne _ _ _ _ hxd, ← hdoms x]
      apply absDom_congr
      intro p hp
      apply base3_read
      · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.drun d from by
          fin_cases x <;> fin_cases d <;>
            first
              | exact absurd rfl hxd
              | exact of_decide_eq_true rfl) p hp
      · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.dcause d from by
          fin_cases x <;> fin_cases d <;>
            first
              | exact absurd rfl hxd
              | exact of_decide_eq_true rfl) p hp
      · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.dsrvV d from by
          fin_cases x <;> fin_cases d <;>
            first
              | exact absurd rfl hxd
              | exact of_decide_eq_true rfl) p hp
  · intro g
    show Hw.absGate _ g = τ.gates g
    rw [← hgates g]
    apply absGate_congr
    intro p hp
    apply base3_read
    · exact (show ∀ q ∈ gateReadNames g, q.1 ≠ Hw.drun d from by
        fin_cases g <;> fin_cases d <;> exact of_decide_eq_true rfl) p hp
    · exact (show ∀ q ∈ gateReadNames g, q.1 ≠ Hw.dcause d from by
        fin_cases g <;> fin_cases d <;> exact of_decide_eq_true rfl) p hp
    · exact (show ∀ q ∈ gateReadNames g, q.1 ≠ Hw.dsrvV d from by
        fin_cases g <;> fin_cases d <;> exact of_decide_eq_true rfl) p hp


/-! ## The unwind face -/

/-- Register reads through the two unconditional unwind writes. -/
private theorem unwind2_read (σ acc : Loom.Hw.St) (g : GateId) (cl : DomainId)
    (rn : String) (w : Nat)
    (h1 : rn ≠ Hw.gactV g) (h2 : rn ≠ Hw.drun cl) :
    ((Act.write 2 (Hw.drun cl) (.lit 0)).run σ
      ((Act.write 1 (Hw.gactV g) (.lit 0)).run σ acc)).regs rn w
      = acc.regs rn w := by
  show ((acc.regs.set (Hw.gactV g) (0:BitVec 1)).set (Hw.drun cl)
    (0:BitVec 2)) rn w = _
  simp only [RegEnv.set]
  rw [if_neg h2, if_neg h1]

/-- Decoding the unwind body is `Kernel.unwindGate`. -/
theorem abs_gateBody (σ acc' : Loom.Hw.St) (τ' : MachineState)
    (d : DomainId) (g : GateId) (cl : DomainId) (rd : RegId)
    (hcl : cl.val = (σ.regs (Hw.gcaller g) 2).toNat)
    (hrd : rd.val = (σ.regs (Hw.gcallerRd g) 3).toNat)
    (hdoms : ∀ x, Hw.absDom acc' x = τ'.doms x)
    (hgates : ∀ h, Hw.absGate acc' h = τ'.gates h) :
    (∀ x, Hw.absDom ((gateBody d g).run σ acc') x
      = (τ'.unwindGate g cl rd).doms x) ∧
    (∀ h, Hw.absGate ((gateBody d g).run σ acc') h
      = (τ'.unwindGate g cl rd).gates h) := by
  rw [gateBody_run σ acc' d g cl hcl]
  set A2 := (Act.write 2 (Hw.drun cl) (.lit 0)).run σ
    ((Act.write 1 (Hw.gactV g) (.lit 0)).run σ acc') with hA2
  -- the final register file, with or without the reply write
  by_cases hrd0 : rd.val = 0
  · -- r0 reply: both sides drop the write
    rw [writeReg_run_of_zero σ A2 cl _ _
      (show ((Expr.reg 3 (Hw.gcallerRd g)).eval σ).toNat = 0 from by
        show (σ.regs (Hw.gcallerRd g) 3).toNat = 0
        rw [← hrd]; exact hrd0)]
    constructor
    · intro x
      show Hw.absDom A2 x = (Loom.Fun.update _ cl _) x
      by_cases hxc : x = cl
      · subst hxc
        rw [Loom.Fun.update_same]
        show Hw.absDom A2 x = ({ (τ'.doms x) with run := .running } :
          DomainState).setReg rd Errno.calleeFault.toWord
        rw [DomainState.setReg, if_pos (Fin.ext hrd0)]
        rw [← hdoms x]
        apply domainState_ext'
        · funext r
          exact unwind2_read σ acc' g x _ _
            (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
        · exact unwind2_read σ acc' g x _ _
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
        · funext s
          show (if A2.regs (Hw.dcapV x s) 1 = 1 then _ else _) = _
          rw [unwind2_read σ acc' g x (Hw.dcapV x s) 1
              (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
            unwind2_read σ acc' g x (Hw.dcapKind x s) 32
              (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
            unwind2_read σ acc' g x (Hw.dcapLinV x s) 1
              (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
            unwind2_read σ acc' g x (Hw.dcapLin x s) 4
              (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)]
          rfl
        · funext s
          exact unwind2_read σ acc' g x _ _
            (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
        · funext l
          show (if A2.regs (Hw.dcellV x l) 1 = 1 then _ else _) = _
          rw [unwind2_read σ acc' g x (Hw.dcellV x l) 1
              (by fin_cases x <;> fin_cases g <;> fin_cases l <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl),
            unwind2_read σ acc' g x (Hw.dcellPar x l) 14
              (by fin_cases x <;> fin_cases g <;> fin_cases l <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)]
          rfl
        · funext r
          show (if A2.regs (Hw.drgnV x r) 1 = 1 then _ else _) = _
          rw [unwind2_read σ acc' g x (Hw.drgnV x r) 1
              (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl),
            unwind2_read σ acc' g x (Hw.drgn x r) 42
              (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)]
          rfl
        · show Hw.decRun (A2.regs (Hw.drun x) 2) (A2.regs (Hw.drunG x) 2)
            = .running
          rw [show A2.regs (Hw.drun x) 2 = 0#2 from by
            rw [hA2]
            show ((_root_.Loom.Hw.RegEnv.set _ (Hw.drun x) (0:BitVec 2)))
              (Hw.drun x) 2 = 0#2
            simp [RegEnv.set]]
          rfl
        · show (if A2.regs (Hw.dsrvV x) 1 = 1 then _ else _) = _
          rw [unwind2_read σ acc' g x (Hw.dsrvV x) 1
              (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> exact of_decide_eq_true rfl),
            unwind2_read σ acc' g x (Hw.dsrv x) 2
              (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> exact of_decide_eq_true rfl)]
          rfl
        · exact unwind2_read σ acc' g x _ _
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
        · show (A2.regs (Hw.dbudget x) 32).toNat = _
          rw [unwind2_read σ acc' g x _ _
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
          rfl
        · show (A2.regs (Hw.dmaxdon x) 32).toNat = _
          rw [unwind2_read σ acc' g x _ _
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
          rfl
      · rw [Loom.Fun.update_ne _ _ _ _ hxc, ← hdoms x]
        apply absDom_congr
        intro p hp
        apply unwind2_read
        · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.gactV g from by
            fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl) p hp
        · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.drun cl from by
            fin_cases x <;> fin_cases cl <;>
              first
                | exact absurd rfl hxc
                | exact of_decide_eq_true rfl) p hp
    · intro h
      show Hw.absGate A2 h = (Loom.Fun.update _ g _) h
      by_cases hhg : h = g
      · subst hhg
        rw [Loom.Fun.update_same]
        show Hw.absGate A2 h = { (τ'.gates h) with act := none }
        rw [← hgates h]
        unfold Hw.absGate
        rw [show A2.regs (Hw.gactV h) 1 = 0#1 from by
          rw [hA2]
          show (((_root_.Loom.Hw.RegEnv.set acc'.regs (Hw.gactV h)
            (0:BitVec 1))).set (Hw.drun cl) (0:BitVec 2)) (Hw.gactV h) 1 = 0#1
          simp only [RegEnv.set]
          rw [if_neg (by fin_cases h <;> fin_cases cl <;>
            exact of_decide_eq_true rfl : Hw.gactV h ≠ Hw.drun cl)]
          simp]
        rw [unwind2_read σ acc' h cl (Hw.gcallee h) 2
            (by fin_cases h <;> exact of_decide_eq_true rfl)
            (by fin_cases h <;> fin_cases cl <;> exact of_decide_eq_true rfl),
          unwind2_read σ acc' h cl (Hw.gentry h) 12
            (by fin_cases h <;> exact of_decide_eq_true rfl)
            (by fin_cases h <;> fin_cases cl <;> exact of_decide_eq_true rfl)]
        rfl
      · rw [Loom.Fun.update_ne _ _ _ _ hhg, ← hgates h]
        apply absGate_congr
        intro p hp
        apply unwind2_read
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.gactV g from by
            fin_cases h <;> fin_cases g <;>
              first
                | exact absurd rfl hhg
                | exact of_decide_eq_true rfl) p hp
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.drun cl from by
            fin_cases h <;> fin_cases cl <;> exact of_decide_eq_true rfl) p hp
  · -- live reply register
    rw [writeReg_run_of_nz σ A2 cl _ _ rd
      (show rd.val = ((Expr.reg 3 (Hw.gcallerRd g)).eval σ).toNat from hrd)
      hrd0]
    set S3 := (Act.write 32 (Hw.dreg cl rd) (.lit Errno.calleeFault.toWord)).run
      σ A2 with hS3
    have hread3 : ∀ (rn : String) (w : Nat), rn ≠ Hw.gactV g →
        rn ≠ Hw.drun cl → rn ≠ Hw.dreg cl rd →
        S3.regs rn w = acc'.regs rn w := by
      intro rn w h1 h2 h3
      rw [hS3]
      show (_root_.Loom.Hw.RegEnv.set A2.regs (Hw.dreg cl rd) _) rn w = _
      simp only [RegEnv.set]
      rw [if_neg h3]
      exact unwind2_read σ acc' g cl rn w h1 h2
    constructor
    · intro x
      show Hw.absDom S3 x = (Loom.Fun.update _ cl _) x
      by_cases hxc : x = cl
      · subst hxc
        rw [Loom.Fun.update_same]
        show Hw.absDom S3 x = ({ (τ'.doms x) with run := .running } :
          DomainState).setReg rd Errno.calleeFault.toWord
        rw [DomainState.setReg, if_neg (fun hc => hrd0 (congrArg Fin.val hc))]
        rw [← hdoms x]
        apply domainState_ext'
        · funext r
          show S3.regs (Hw.dreg x r) 32 = Loom.Fun.update _ rd _ r
          by_cases hr : r = rd
          · subst hr
            rw [Loom.Fun.update_same, hS3]
            show (_root_.Loom.Hw.RegEnv.set A2.regs (Hw.dreg x r) _)
              (Hw.dreg x r) 32 = _
            simp [RegEnv.set, Expr.eval]
          · rw [Loom.Fun.update_ne _ _ _ _ hr]
            rw [hread3 _ _
              (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases r <;> fin_cases rd <;>
                first
                  | exact absurd rfl hr
                  | exact of_decide_eq_true rfl)]
            rfl
        · exact hread3 _ _
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases rd <;> exact of_decide_eq_true rfl)
        · funext s
          show (if S3.regs (Hw.dcapV x s) 1 = 1 then _ else _) = _
          rw [hread3 (Hw.dcapV x s) 1
              (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> fin_cases rd <;>
                exact of_decide_eq_true rfl),
            hread3 (Hw.dcapKind x s) 32
              (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> fin_cases rd <;>
                exact of_decide_eq_true rfl),
            hread3 (Hw.dcapLinV x s) 1
              (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> fin_cases rd <;>
                exact of_decide_eq_true rfl),
            hread3 (Hw.dcapLin x s) 4
              (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases s <;> fin_cases rd <;>
                exact of_decide_eq_true rfl)]
          rfl
        · funext s
          exact hread3 _ _
            (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> fin_cases rd <;>
              exact of_decide_eq_true rfl)
        · funext l
          show (if S3.regs (Hw.dcellV x l) 1 = 1 then _ else _) = _
          rw [hread3 (Hw.dcellV x l) 1
              (by fin_cases x <;> fin_cases g <;> fin_cases l <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases l <;> fin_cases rd <;>
                exact of_decide_eq_true rfl),
            hread3 (Hw.dcellPar x l) 14
              (by fin_cases x <;> fin_cases g <;> fin_cases l <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases l <;> fin_cases rd <;>
                exact of_decide_eq_true rfl)]
          rfl
        · funext r
          show (if S3.regs (Hw.drgnV x r) 1 = 1 then _ else _) = _
          rw [hread3 (Hw.drgnV x r) 1
              (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases r <;> fin_cases rd <;>
                exact of_decide_eq_true rfl),
            hread3 (Hw.drgn x r) 42
              (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
                exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases r <;> fin_cases rd <;>
                exact of_decide_eq_true rfl)]
          rfl
        · show Hw.decRun (S3.regs (Hw.drun x) 2) (S3.regs (Hw.drunG x) 2)
            = .running
          rw [show S3.regs (Hw.drun x) 2 = 0#2 from by
            rw [hS3]
            show (_root_.Loom.Hw.RegEnv.set A2.regs (Hw.dreg x rd) _)
              (Hw.drun x) 2 = 0#2
            simp only [RegEnv.set]
            rw [if_neg (by fin_cases x <;> fin_cases rd <;>
              exact of_decide_eq_true rfl : Hw.drun x ≠ Hw.dreg x rd)]
            rw [hA2]
            show ((_root_.Loom.Hw.RegEnv.set _ (Hw.drun x) (0:BitVec 2)))
              (Hw.drun x) 2 = 0#2
            simp [RegEnv.set]]
          rfl
        · show (if S3.regs (Hw.dsrvV x) 1 = 1 then _ else _) = _
          rw [hread3 (Hw.dsrvV x) 1
              (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases rd <;> exact of_decide_eq_true rfl),
            hread3 (Hw.dsrv x) 2
              (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> exact of_decide_eq_true rfl)
              (by fin_cases x <;> fin_cases rd <;> exact of_decide_eq_true rfl)]
          rfl
        · exact hread3 _ _
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases rd <;> exact of_decide_eq_true rfl)
        · show (S3.regs (Hw.dbudget x) 32).toNat = _
          rw [hread3 _ _
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases rd <;> exact of_decide_eq_true rfl)]
          rfl
        · show (S3.regs (Hw.dmaxdon x) 32).toNat = _
          rw [hread3 _ _
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases rd <;> exact of_decide_eq_true rfl)]
          rfl
      · rw [Loom.Fun.update_ne _ _ _ _ hxc, ← hdoms x]
        apply absDom_congr
        intro p hp
        apply hread3
        · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.gactV g from by
            fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl) p hp
        · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.drun cl from by
            fin_cases x <;> fin_cases cl <;>
              first
                | exact absurd rfl hxc
                | exact of_decide_eq_true rfl) p hp
        · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.dreg cl rd from by
            fin_cases x <;> fin_cases cl <;>
              first
                | exact absurd rfl hxc
                | (fin_cases rd <;> exact of_decide_eq_true rfl)) p hp
    · intro h
      show Hw.absGate S3 h = (Loom.Fun.update _ g _) h
      by_cases hhg : h = g
      · subst hhg
        rw [Loom.Fun.update_same]
        show Hw.absGate S3 h = { (τ'.gates h) with act := none }
        rw [← hgates h]
        unfold Hw.absGate
        rw [show S3.regs (Hw.gactV h) 1 = 0#1 from by
          rw [hS3]
          show (_root_.Loom.Hw.RegEnv.set A2.regs (Hw.dreg cl rd)
            ((Expr.lit Errno.calleeFault.toWord).eval σ))
            (Hw.gactV h) 1 = 0#1
          simp only [RegEnv.set]
          rw [if_neg (by fin_cases h <;> fin_cases cl <;> fin_cases rd <;>
            exact of_decide_eq_true rfl : Hw.gactV h ≠ Hw.dreg cl rd)]
          rw [hA2]
          show (((_root_.Loom.Hw.RegEnv.set acc'.regs (Hw.gactV h)
            (0:BitVec 1))).set (Hw.drun cl) (0:BitVec 2)) (Hw.gactV h) 1 = 0#1
          simp only [RegEnv.set]
          rw [if_neg (by fin_cases h <;> fin_cases cl <;>
            exact of_decide_eq_true rfl : Hw.gactV h ≠ Hw.drun cl)]
          simp]
        rw [hread3 (Hw.gcallee h) 2
            (by fin_cases h <;> exact of_decide_eq_true rfl)
            (by fin_cases h <;> fin_cases cl <;> exact of_decide_eq_true rfl)
            (by fin_cases h <;> fin_cases cl <;> fin_cases rd <;>
              exact of_decide_eq_true rfl),
          hread3 (Hw.gentry h) 12
            (by fin_cases h <;> exact of_decide_eq_true rfl)
            (by fin_cases h <;> fin_cases cl <;> exact of_decide_eq_true rfl)
            (by fin_cases h <;> fin_cases cl <;> fin_cases rd <;>
              exact of_decide_eq_true rfl)]
        rfl
      · rw [Loom.Fun.update_ne _ _ _ _ hhg, ← hgates h]
        apply absGate_congr
        intro p hp
        apply hread3
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.gactV g from by
            fin_cases h <;> fin_cases g <;>
              first
                | exact absurd rfl hhg
                | exact of_decide_eq_true rfl) p hp
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.drun cl from by
            fin_cases h <;> fin_cases cl <;> exact of_decide_eq_true rfl) p hp
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.dreg cl rd from by
            fin_cases h <;> fin_cases cl <;> fin_cases rd <;>
              exact of_decide_eq_true rfl) p hp

end Machines.Lnp64u.Theorems.RMC
