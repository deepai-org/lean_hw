-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCOps

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

end Machines.Lnp64u.Theorems.RMC
