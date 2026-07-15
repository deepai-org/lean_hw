-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCall

/-!
# R-MC retirement: full gate_call arm

Top-level decode and specification reduction for the `gate_call` retirement
square.  The semantic, transfer, status-memory, and Mover bridges live in
`RMCRetireGateCall`; this file assembles them against the core cycle.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- The system table's opcode-22 entry is the named gate-call semantics used
by the proof-side bridge library. -/
theorem gateCall_system_exec :
    (Machines.Lnp64u.Isa.system.get ⟨6, by decide⟩).sem.exec =
      Machines.Lnp64u.Isa.Wip.gateCallExec := by
  rfl

/-- Exact retirement reduction for a decoded gate call: architectural PC
advance followed by the named gate-call body and the standard outcome
triage. -/
theorem retire_gateCall_exec (τ : MachineState) (E : DomainId)
    (W : Loom.Word32)
    (hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6))) :
    retire τ E W =
      let c : Ctx := { d := E, pc := (τ.doms E).pc, op := operandsOf W }
      let τ0 := τ.setDom E fun ds => { ds with pc := ds.pc + 1 }
      match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err e τ' =>
          τ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
      | .fault f => haltWith τ E f := by
  have hfind : isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) =
      some (Machines.Lnp64u.Isa.system.get ⟨6, by decide⟩) := by
    rfl
  rw [retire_of_decode_some _ E W _ (hdec.trans hfind)]
  rw [gateCall_system_exec]
  rfl

end Machines.Lnp64u.Theorems.RMC
