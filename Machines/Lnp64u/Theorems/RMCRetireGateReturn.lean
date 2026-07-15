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

/-- Successful hardware payload selected after every `gate_return` check
passes.  Naming the payload lets the abstraction proof reason about the
return tail independently of opcode dispatch and the response ladder. -/
def gateReturnSuccessA (d : DomainId) : Act :=
  let gid := Hw.retGid d
  let cl := Hw.retCl d
  let rcs := Hw.retSel d
  let reply := .mux (Hw.retNZ d) (Hw.transferHandleAt cl rcs) (.lit 0)
  Hw.seqAll
    [ .ite (Hw.retNZ d) (Hw.transferA d cl rcs) .skip,
      Hw.seqAll ((List.finRange numGates).map fun g =>
        .ite (.eq gid (Hw.gLit g))
          (.write 1 (Hw.gactV g) (.lit 0)) .skip),
      Hw.seqAll ((List.finRange numRegs).map fun r =>
        .write 32 (Hw.dreg d r)
          (Hw.muxFin (fun g => .reg 32 (Hw.gsreg g r)) gid)),
      .write 12 (Hw.dpc d)
        (Hw.muxFin (fun g => .reg 12 (Hw.gspc g)) gid),
      .write 1 (Hw.dsrvV d)
        (Hw.muxFin (fun g => .reg 1 (Hw.gssrvV g)) gid),
      .write 2 (Hw.dsrv d)
        (Hw.muxFin (fun g => .reg 2 (Hw.gssrv g)) gid),
      Hw.seqAll ((List.finRange numDomains).map fun c =>
        .ite (.eq cl (Hw.dLit c))
          (.write 2 (Hw.drun c) (.lit 0)) .skip),
      (let rdi := Hw.muxFin (fun g => .reg 3 (Hw.gcallerRd g)) gid
       Hw.seqAll ((List.finRange numDomains).map fun c =>
        .ite (.eq cl (Hw.dLit c)) (Hw.writeReg c rdi reply) .skip)) ]

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
