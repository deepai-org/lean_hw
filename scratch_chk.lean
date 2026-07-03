import Machines.Acc8.Core
open Machines.Acc8 Loom.Hw
-- what does one cycle of the design look like?
example (prog : BitVec 8 → BitVec 16) (σ : Loom.Hw.St) : True := by
  have := (Core.design prog).cycle σ
  trivial
#check @Loom.Hw.Design.cycle
#check @Loom.Hw.Act.run
