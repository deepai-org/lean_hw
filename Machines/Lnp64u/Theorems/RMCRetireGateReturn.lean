-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCallSuccess

/-!
# R-MC retirement: gate_return semantic spine

Named specification semantics and exact outcome reductions for
`gate_return`.  The successful transfer path deliberately uses the same
`transferByHandle`/`transferA` infrastructure as `gate_call`.
-/

namespace Machines.Lnp64u.Isa.Wip

open Machines.Lnp64u Loom.Isa SpecM

/-- The `gate_return` opcode's operational semantics, named so the
retirement proof can reduce the system table without duplicating its bind
tree. -/
def gateReturnExec (c : Ctx) : SpecM Unit := do
  let σ ← get
  match (σ.doms c.d).serving with
  | none => fatal .protocol
  | some gid =>
      match (σ.gates gid).act with
      | none => fatal .protocol
      | some act => do
          let rw ← reg c.d c.op.rs1
          let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
          let σ ← get
          set ({ σ with
            gates := Loom.Fun.update σ.gates gid
              { (σ.gates gid) with act := none } })
          updDom c.d fun ds =>
            { ds with regs := act.savedRegs, pc := act.savedPc
                      serving := act.savedServing }
          updDom act.caller fun ds => { ds with run := .running }
          setReg act.caller act.callerRd reply

end Machines.Lnp64u.Isa.Wip

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- The system table's opcode-23 entry is the named return semantics. -/
theorem gateReturn_system_exec :
    (Machines.Lnp64u.Isa.system.get ⟨7, by decide⟩).sem.exec =
      Machines.Lnp64u.Isa.Wip.gateReturnExec := by
  rfl

/-- Exact retirement reduction for a decoded gate return. -/
theorem retire_gateReturn_exec (τ : MachineState) (E : DomainId)
    (W : Loom.Word32)
    (hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (23#6 : BitVec 6))) :
    retire τ E W =
      let c : Ctx := { d := E, pc := (τ.doms E).pc, op := operandsOf W }
      let τ0 := τ.setDom E fun ds => { ds with pc := ds.pc + 1 }
      match Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 with
      | .ok _ τ' => τ'
      | .err e τ' =>
          τ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
      | .fault f => haltWith τ E f := by
  have hfind : isa.find? (fun d => d.opcode == (23#6 : BitVec 6)) =
      some (Machines.Lnp64u.Isa.system.get ⟨7, by decide⟩) := by
    rfl
  rw [retire_of_decode_some _ E W _ (hdec.trans hfind)]
  rw [gateReturn_system_exec]
  rfl

/-! ## Hardware dispatch and response ladder -/

/-- Optional reply-capability transfer at the head of a successful return. -/
def gateReturnTransferA (d : DomainId) : Act :=
  .ite (Hw.retNZ d) (Hw.transferA d (Hw.retCl d) (Hw.retSel d)) .skip

/-- Clear the activation bit of the dynamically selected serving gate. -/
def gateReturnClearA (d : DomainId) : Act :=
  Hw.seqAll ((List.finRange numGates).map fun g =>
    .ite (.eq (Hw.retGid d) (Hw.gLit g))
      (.write 1 (Hw.gactV g) (.lit 0)) .skip)

/-- Restore the returning domain's register file, PC, and prior serving tag. -/
def gateReturnRestoreA (d : DomainId) : Act :=
  let gid := Hw.retGid d
  Hw.seqAll
    [ Hw.seqAll ((List.finRange numRegs).map fun r =>
        .write 32 (Hw.dreg d r)
          (Hw.muxFin (fun g => .reg 32 (Hw.gsreg g r)) gid)),
      .write 12 (Hw.dpc d)
        (Hw.muxFin (fun g => .reg 12 (Hw.gspc g)) gid),
      .write 1 (Hw.dsrvV d)
        (Hw.muxFin (fun g => .reg 1 (Hw.gssrvV g)) gid),
      .write 2 (Hw.dsrv d)
        (Hw.muxFin (fun g => .reg 2 (Hw.gssrv g)) gid) ]

/-- Resume the caller selected from the active gate. -/
def gateReturnResumeA (d : DomainId) : Act :=
  Hw.seqAll ((List.finRange numDomains).map fun c =>
    .ite (.eq (Hw.retCl d) (Hw.dLit c))
      (.write 2 (Hw.drun c) (.lit 0)) .skip)

/-- Reply word returned to the caller: null for a null input, otherwise the
target-relative handle produced by the structural transfer. -/
def gateReturnReplyE (d : DomainId) : Expr 32 :=
  .mux (Hw.retNZ d)
    (Hw.transferHandleAt (Hw.retCl d) (Hw.retSel d)) (.lit 0)

/-- Write the reply word to the caller's saved destination register. -/
def gateReturnReplyA (d : DomainId) : Act :=
  let rdi := Hw.muxFin (fun g => .reg 3 (Hw.gcallerRd g)) (Hw.retGid d)
  Hw.seqAll ((List.finRange numDomains).map fun c =>
    .ite (.eq (Hw.retCl d) (Hw.dLit c))
      (Hw.writeReg c rdi (gateReturnReplyE d)) .skip)

/-- Successful hardware payload selected after every `gate_return` check
passes.  Naming its stages lets the abstraction proof reason about the return
tail independently of opcode dispatch and the response ladder. -/
def gateReturnSuccessA (d : DomainId) : Act :=
  let gid := Hw.retGid d
  Hw.seqAll
    [ gateReturnTransferA d,
      gateReturnClearA d,
      Hw.seqAll ((List.finRange numRegs).map fun r =>
        .write 32 (Hw.dreg d r)
          (Hw.muxFin (fun g => .reg 32 (Hw.gsreg g r)) gid)),
      .write 12 (Hw.dpc d)
        (Hw.muxFin (fun g => .reg 12 (Hw.gspc g)) gid),
      .write 1 (Hw.dsrvV d)
        (Hw.muxFin (fun g => .reg 1 (Hw.gssrvV g)) gid),
      .write 2 (Hw.dsrv d)
        (Hw.muxFin (fun g => .reg 2 (Hw.gssrv g)) gid),
      gateReturnResumeA d,
      gateReturnReplyA d ]

/-- Operational decomposition of the successful return payload. -/
theorem gateReturnSuccessA_run (σ acc : Loom.Hw.St) (d : DomainId) :
    (gateReturnSuccessA d).run σ acc =
      (gateReturnReplyA d).run σ
        ((gateReturnResumeA d).run σ
          ((gateReturnRestoreA d).run σ
            ((gateReturnClearA d).run σ
              ((gateReturnTransferA d).run σ acc)))) := by
  rfl

/-- The named successful payload is definitionally the body of the return
response ladder. -/
theorem retCirc_act_eq (d : DomainId) :
    (Hw.retCirc d).act =
      Hw.ladder d (Hw.retChecks d) (gateReturnSuccessA d) := by
  rfl

/-- Retirement dispatch selects the return circuit on opcode 23. -/
theorem retireFor_gateReturn_run (σ acc : Loom.Hw.St) (d : DomainId)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6) :
    (Hw.retireFor d).run σ acc =
      (Hw.ladder d (Hw.retChecks d) (gateReturnSuccessA d)).run σ acc := by
  rw [← retCirc_act_eq]
  exact retireFor_sel_of_opc σ d "gate_return" 23#6 hopc
    (by decide +kernel)
    (by decide +kernel)
    (Hw.retCirc d)
    (List.mem_append_right _ (by simp)) acc

/-- When all return checks pass, dispatch runs the successful payload. -/
theorem retireFor_gateReturn_success (σ acc : Loom.Hw.St) (d : DomainId)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hok : (Hw.retOkE d).eval σ = 1#1) :
    (Hw.retireFor d).run σ acc = (gateReturnSuccessA d).run σ acc := by
  rw [retireFor_gateReturn_run σ acc d hopc]
  apply ladder_run_all_pass
  exact (okOf_eval_iff σ (Hw.retChecks d)).mp hok

/-- Generic first-failure selector for the return response ladder. -/
theorem retireFor_gateReturn_first_failure (σ acc : Loom.Hw.St)
    (d : DomainId) (pre post : List Hw.Check) (cond : Expr 1)
    (resp : Hw.Resp)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hchecks : Hw.retChecks d = pre ++ (cond, resp) :: post)
    (hpre : ∀ x ∈ pre, x.1.eval σ ≠ 1#1)
    (hfail : cond.eval σ = 1#1) :
    (Hw.retireFor d).run σ acc = (Hw.respA d resp).run σ acc := by
  rw [retireFor_gateReturn_run σ acc d hopc, hchecks]
  exact ladder_run_first_failure σ acc d pre post cond resp
    (gateReturnSuccessA d) hpre hfail

/-! ## Dynamic return selectors -/

/-- An abstract serving witness identifies the gate selected by `retGid`. -/
theorem retGid_eval_selected (σ : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (hserv : ((Hw.abs σ).doms d).serving = some gid) :
    finOfBv (by decide : 2 ^ 2 = numGates) ((Hw.retGid d).eval σ) = gid := by
  change (if σ.regs (Hw.dsrvV d) 1 = 1#1 then
      some (finOfBv (by decide) (σ.regs (Hw.dsrv d) 2)) else none) =
    some gid at hserv
  by_cases hv : σ.regs (Hw.dsrvV d) 1 = 1#1
  · rw [if_pos hv] at hserv
    exact Option.some.inj hserv
  · rw [if_neg hv] at hserv
    contradiction

/-- The active selected gate identifies the caller selected by `retCl`. -/
theorem retCl_eval_selected (σ : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (act : Activation)
    (hserv : ((Hw.abs σ).doms d).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    finOfBv (by decide : 2 ^ 2 = numDomains) ((Hw.retCl d).eval σ) =
      act.caller := by
  have hgid := retGid_eval_selected σ d gid hserv
  unfold Hw.retCl
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
  change (if σ.regs (Hw.gactV gid) 1 = 1#1 then
      some
        { caller := finOfBv (by decide) (σ.regs (Hw.gcaller gid) 2)
          callerRd := finOfBv (by decide) (σ.regs (Hw.gcallerRd gid) 3)
          savedRegs := fun r => σ.regs (Hw.gsreg gid r) 32
          savedPc := σ.regs (Hw.gspc gid) 12
          savedServing := if σ.regs (Hw.gssrvV gid) 1 = 1#1 then
            some (finOfBv (by decide) (σ.regs (Hw.gssrv gid) 2)) else none
          depth := (σ.regs (Hw.gdepth gid) 3).toNat
          donated := (σ.regs (Hw.gdon gid) 32).toNat }
      else none) = some act at hact
  by_cases hv : σ.regs (Hw.gactV gid) 1 = 1#1
  · rw [if_pos hv] at hact
    have ha := Option.some.inj hact
    rw [← ha]
    rfl
  · rw [if_neg hv] at hact
    contradiction

/-- The hardware return-word expression is the architectural `rs1` read. -/
theorem retW_eval (σ : Loom.Hw.St) (hz : R0Zero σ) (d : DomainId)
    (r : RegId) (hr : r.val = (Hw.rs1E.eval σ).toNat) :
    (Hw.retW d).eval σ = ((Hw.abs σ).doms d).reg r := by
  exact readReg_eval σ hz d Hw.rs1E r hr

/-- The optional return-transfer guard is exactly non-nullness of the reply
handle word. -/
theorem retNZ_eval_iff (σ : Loom.Hw.St) (d : DomainId) :
    (Hw.retNZ d).eval σ = 1#1 ↔ (Hw.retW d).eval σ ≠ 0#32 := by
  unfold Hw.retNZ
  exact neqE_eval _ _ σ

/-! ## Global kill-tree selection -/

/-- On a successful retiring return, the global core kill tree selects
exactly that return's optional reply-transfer predicate. -/
theorem killedByCoreE_gateReturn_eval (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ = 1#1)
    (hok : ∀ d : DomainId, d = E → (Hw.retOkE d).eval σ = 1#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled E dm sl).eval σ := by
  have hdrop0 : (Hw.isMn "cap_drop").eval σ = 0#1 := bv1_ne_one.mp hdrop
  have hrev0 : (Hw.isMn "cap_revoke").eval σ = 0#1 := bv1_ne_one.mp hrev
  have hcall0 : (Hw.isMn "gate_call").eval σ = 0#1 := bv1_ne_one.mp hcall
  have honeAnd : ∀ x : BitVec 1, 1#1 &&& x = x := by decide
  have hzeroAnd : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
  have hzeroOr : ∀ x : BitVec 1, 0#1 ||| x = x := by decide
  have horZero : ∀ x : BitVec 1, x ||| 0#1 = x := by decide
  unfold Hw.killedByCoreE
  fin_cases E <;>
    simp [Hw.orAll, List.finRange, Expr.eval, Fin.ext_iff, hret, hif,
      hdrop0, hrev0, hcall0, hreturn, hok, honeAnd, hzeroAnd, hzeroOr,
      horZero] <;>
    congr 2

/-- A failed return has no kill footprint because `retOkE` gates its
optional transfer in both retirement and Mover re-derivation. -/
theorem killedByCoreE_gateReturn_failed (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ = 1#1)
    (hbad : ∀ d : DomainId, d = E → (Hw.retOkE d).eval σ = 0#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = 0#1 := by
  have hdrop0 : (Hw.isMn "cap_drop").eval σ = 0#1 := bv1_ne_one.mp hdrop
  have hrev0 : (Hw.isMn "cap_revoke").eval σ = 0#1 := bv1_ne_one.mp hrev
  have hcall0 : (Hw.isMn "gate_call").eval σ = 0#1 := bv1_ne_one.mp hcall
  have honeAnd : ∀ x : BitVec 1, 1#1 &&& x = x := by decide
  have hzeroAnd : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
  have hzeroOr : ∀ x : BitVec 1, 0#1 ||| x = x := by decide
  unfold Hw.killedByCoreE
  fin_cases E <;>
    simp [Hw.orAll, List.finRange, Expr.eval, Fin.ext_iff, hret, hif,
      hdrop0, hrev0, hcall0, hreturn, hbad, honeAnd, hzeroAnd, hzeroOr]

/-- Failed returns are Mover-inert once the unrelated job-install gate is
known off. -/
theorem Inert.of_failed_gateReturn (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ = 1#1)
    (hbad : ∀ d : DomainId, d = E → (Hw.retOkE d).eval σ = 0#1)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1) : Inert σ where
  killed := killedByCoreE_gateReturn_failed σ E hret hif hdrop hrev
    hcall hreturn hbad
  newJob := hnew

/-- Pure successful-return tail after the optional reply transfer.  `base`
is the state returned by `transferByHandle`. -/
def returnAbstractSuccess (base : MachineState) (d : DomainId)
    (gid : GateId) (act : Activation) (reply : Loom.Word32) : MachineState :=
  let gate := { (base.gates gid) with act := none }
  let σ1 : MachineState :=
    { base with gates := Loom.Fun.update base.gates gid gate }
  let σ2 := σ1.setDom d fun ds =>
    { ds with regs := act.savedRegs, pc := act.savedPc
              serving := act.savedServing }
  let σ3 := σ2.setDom act.caller fun ds => { ds with run := .running }
  σ3.setDom act.caller fun ds => ds.setReg act.callerRd reply

/-- Returning outside a serving activation faults with `protocol`. -/
theorem gateReturnExec_notServing (c : Ctx) (τ : MachineState)
    (hserv : (τ.doms c.d).serving = none) :
    Machines.Lnp64u.Isa.Wip.gateReturnExec c τ = .fault .protocol := by
  unfold Machines.Lnp64u.Isa.Wip.gateReturnExec
  simp [SpecM.get, hserv, SpecM.fatal]

/-- A serving tag whose gate has no activation also faults with `protocol`. -/
theorem gateReturnExec_inactive (c : Ctx) (τ : MachineState)
    (gid : GateId) (hserv : (τ.doms c.d).serving = some gid)
    (hact : (τ.gates gid).act = none) :
    Machines.Lnp64u.Isa.Wip.gateReturnExec c τ = .fault .protocol := by
  unfold Machines.Lnp64u.Isa.Wip.gateReturnExec
  simp [SpecM.get, hserv, hact, SpecM.fatal]

/-- Once a live activation is selected, a reply-transfer errno is propagated
without applying the restore tail. -/
theorem gateReturnExec_transferErr (c : Ctx) (τ : MachineState)
    (gid : GateId) (act : Activation) (er : Errno)
    (hserv : (τ.doms c.d).serving = some gid)
    (hact : (τ.gates gid).act = some act)
    (htransfer : Machines.Lnp64u.Isa.transferByHandle c.d act.caller
      ((τ.doms c.d).reg c.op.rs1) τ = .err er τ) :
    Machines.Lnp64u.Isa.Wip.gateReturnExec c τ = .err er τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateReturnExec
  simp only [SpecM.get, specM_bind, hserv, hact, SpecM.reg]
  rw [htransfer]

/-- A successful reply transfer reduces the remainder of `gateReturnExec`
to the pure restore/resume transformer. -/
theorem gateReturnExec_success (c : Ctx) (τ τt : MachineState)
    (gid : GateId) (act : Activation) (reply : Loom.Word32)
    (hserv : (τ.doms c.d).serving = some gid)
    (hact : (τ.gates gid).act = some act)
    (htransfer : Machines.Lnp64u.Isa.transferByHandle c.d act.caller
      ((τ.doms c.d).reg c.op.rs1) τ = .ok reply τt) :
    Machines.Lnp64u.Isa.Wip.gateReturnExec c τ =
      .ok () (returnAbstractSuccess τt c.d gid act reply) := by
  unfold Machines.Lnp64u.Isa.Wip.gateReturnExec
  simp only [SpecM.get, specM_bind, hserv, hact, SpecM.reg]
  rw [htransfer]
  simp [SpecM.set, SpecM.updDom, SpecM.modify, SpecM.setReg,
    returnAbstractSuccess]

end Machines.Lnp64u.Theorems.RMC
