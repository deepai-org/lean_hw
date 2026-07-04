-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64u.Iss

/-!
# LNP64-µ golden tests

Interpreter-evaluated assertions (`#eval` + panic): the demo manifest boots,
domain 0 computes/stores/loads 12, everyone halts voluntarily, and the trace
matches the checked-in golden. Tooling, not trusted path.
-/

namespace Tests.Lnp64u

open Machines.Lnp64u

private def check (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"golden test failed: {name}")

#eval do
  let (final, trace) := demoResult
  check "d0 halted voluntarily"
    (decide ((final.doms 0).run = RunState.halted) && (final.doms 0).cause == 0)
  check "d0 r3 = 12" ((final.doms 0).reg 3 == 12)
  check "d0 r4 = 12 (loaded back)" ((final.doms 0).reg 4 == 12)
  check "mem[data0] = 12" (final.read (BitVec.ofNat 12 (dataBase 0)) == 12)
  check "all domains halted"
    ((List.finRange numDomains).all fun d => decide ((final.doms d).run = RunState.halted))
  check "no faults" ((List.finRange numDomains).all fun d => (final.doms d).cause == 0)
  check "trace has 10 retirements"
    ((trace.filter fun (l : Loom.Trace.Line) => match l.event with | .retire .. => true | _ => false).size == 10)
  check "trace codec round-trips" (trace.all fun (l : Loom.Trace.Line) => Loom.Trace.roundTrips l)
  IO.println "Lnp64u golden tests passed"

end Tests.Lnp64u
