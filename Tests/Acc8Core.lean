import Machines.Acc8.Core
import Machines.Acc8.Iss

/-!
# Acc8 lockstep: EDSL core vs ISS (task 1.11, pathfinder half)

Runs the golden and loop programs on both the spec ISS and the EDSL core,
comparing the full architectural state every cycle. The trace-format payoff
in miniature: one divergence pinpoints the cycle.
-/

namespace Tests.Acc8Core

open Machines.Acc8 Loom.Hw

private def agree (hw : Loom.Hw.St) (sp : Machines.Acc8.St) : Bool :=
  hw.regs "acc" 8 == sp.acc &&
  hw.regs "pc" 8 == sp.pc &&
  (hw.regs "halted" 1 == 1#1) == sp.halted &&
  (List.range 256).all fun a => hw.mems "mem" a 8 == sp.mem (BitVec.ofNat 8 a)

private def lockstep (prog : List (BitVec 16)) (cycles : Nat) : Bool :=
  let img := loadProg prog
  let d := Core.design img
  let rec go : Nat → Loom.Hw.St → Machines.Acc8.St → Bool
    | 0, _, _ => true
    | n + 1, hw, sp =>
        agree hw sp && go n (d.cycle hw) (step sp)
  go cycles d.reset (boot img)

private def loop : List (BitVec 16) :=
  [ asm "ldi" 5, asm "sta" 0, asm "lda" 0, asm "sub" 1
  , asm "sta" 0, asm "jnz" 2, asm "hlt" 0 ]

#eval do
  unless lockstep golden 15 do
    throw (IO.userError "Acc8 core/ISS lockstep diverged on golden")
  unless lockstep loop 45 do
    throw (IO.userError "Acc8 core/ISS lockstep diverged on loop")
  IO.println "Acc8 core/ISS lockstep passed (golden, loop)"

end Tests.Acc8Core
