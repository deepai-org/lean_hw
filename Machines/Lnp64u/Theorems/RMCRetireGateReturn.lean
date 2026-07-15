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
