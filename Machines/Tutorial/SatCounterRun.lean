-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Tutorial.SatCounter
import Loom.Hw.Diff


/-!
# Tutorial differential run: the counter vs a reference model

The worked example for `TUTORIAL.md` step 3, checked in so the document's
code cannot drift from the library. The `#eval` executes at build time: a
mismatch or an undeclared coordinate fails the build.
-/

namespace Machines.Tutorial.SatCounterRun

open Loom.Hw Machines.Tutorial.SatCounter

structure Ref where
  count : Nat := 0
  sat   : Bool := false

def Ref.step (r : Ref) : Ref :=
  if r.count = 255 then { r with sat := true }
  else { r with count := r.count + 1 }

def oracle (r : Ref) : Oracle where
  read := fun c =>
    if c.kind = "reg" && c.name = "count" then some r.count
    else if c.kind = "reg" && c.name = "sat" then some (if r.sat then 1 else 0)
    else none

#eval do
  let result ← Loom.Runner.run { label := "satcounter vs reference", steps := 300 }
    (design.reset, ({} : Ref)) fun _ s => do
      let hw := design.cycle s.1
      let ref := s.2.step
      return ((hw, ref), design.sampleAgainstOracle 8 hw (oracle ref))
  result.requirePass

end Machines.Tutorial.SatCounterRun
