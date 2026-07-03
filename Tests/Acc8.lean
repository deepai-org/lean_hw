import Machines.Acc8.Iss

/-!
# Acc8 golden tests

`#guard` checks run at elaboration time: the ISS boots the golden image and
the results below are the checked-in goldens (PLAN §10 item 6, Acc8 half).
-/

namespace Tests.Acc8

open Machines.Acc8

-- The golden program halts and leaves 7 + 35 - 2 = 40 in cell 3.
#guard goldenResult.halted
#guard goldenResult.mem 3 == 40
#guard goldenResult.acc == 40
-- A loop: count 5 down to 0, accumulating into cell 0 via cell arithmetic.
-- ldi 5 / sta 0 / lda 0 / sub 1 / sta 0 / jnz 2 / hlt : leaves 0 in cell 0.
private def loop : List (BitVec 16) :=
  [ asm "ldi" 5, asm "sta" 0, asm "lda" 0, asm "sub" 1
  , asm "sta" 0, asm "jnz" 2, asm "hlt" 0 ]
#guard (run 40 (boot (loadProg loop))).halted
#guard (run 40 (boot (loadProg loop))).mem 0 == 0
-- Decode failure halts: an image of illegal opcodes halts on cycle one.
#guard (run 2 (boot (fun _ => 0x00ff))).halted

end Tests.Acc8
