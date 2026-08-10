-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Acc8.Core
import Machines.Acc8.Iss
import Loom.Hw.Diff

/-!
# Acc8 lockstep: EDSL core vs ISS (task 1.11, pathfinder half)

Runs the golden and loop programs on both the spec ISS and the EDSL core,
comparing the full architectural state every cycle. The trace-format payoff
in miniature: one divergence pinpoints the cycle.
-/

namespace Tests.Acc8Core

open Machines.Acc8 Loom.Hw

private def oracle (sp : Machines.Acc8.St) : Oracle where
  read := fun c =>
    if c.kind = "reg" then
      if c.name = "acc" then some sp.acc.toNat
      else if c.name = "pc" then some sp.pc.toNat
      else if c.name = "halted" then some (if sp.halted then 1 else 0)
      else none
    else if c.name = "prog" then some (sp.prog (BitVec.ofNat 8 c.addr)).toNat
    else if c.name = "mem" then some (sp.mem (BitVec.ofNat 8 c.addr)).toNat
    else none

private def runLockstep (label : String) (prog : List (BitVec 16))
    (cycles : Nat) : IO Loom.Runner.Result := do
  let img := loadProg prog
  let d := Core.design img
  Loom.Runner.run { label, steps := cycles, maxEvents := 8 }
    (d.reset, boot img) fun _ state => do
      let hw := d.cycle state.1
      let sp := Machines.Acc8.step state.2
      return ((hw, sp), d.sampleAgainstOracle 256 hw (oracle sp))

private def loop : List (BitVec 16) :=
  [ asm "ldi" 5, asm "sta" 0, asm "lda" 0, asm "sub" 1
  , asm "sta" 0, asm "jnz" 2, asm "hlt" 0 ]

#eval do
  (← runLockstep "Acc8 golden core/ISS" golden 15).requirePass
  (← runLockstep "Acc8 loop core/ISS" loop 45).requirePass

end Tests.Acc8Core
