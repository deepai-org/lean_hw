-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.EmitIO
import Machines.CapWalk.Engine

/-!
# D39 regression: a design can keep a register off its interface

`Loom/Hw/Outputs.lean` (spec: `Loom/Hw/OUTPUTS_SPEC.md`) adds
`Design.outputs : Option (List String)` — the registers a design exports as
`o_<name>` ports. Checked here:

* **`none` is the identity.** The default selection compiles to the pre-D39
  port list, so every existing artifact is byte-identical.
* **A selection removes ports**, and only the selected ones remain — the
  property `Loom.Hw.compile_not_exported` states in general.
* **An undeclared selection entry is an emit-time error**, naming it: a typo
  must not silently drop a port.
* **The artifact that needed it**: `capwalk`'s six MAC key registers exist,
  are written by no rule, and appear at no port (CE5, retired).
-/

namespace Tests.Outputs

open Loom.Hw

/-- Two registers; `sel` picks the D39 selection. -/
private def d (sel : Option (List String)) : Design where
  name := "obs"
  regs := [⟨"pub", 8, 0⟩, ⟨"secret", 8, 42⟩]
  mems := []
  rules := [⟨"r", .write 8 "pub" (.add (.reg 8 "pub") (.reg 8 "secret"))⟩]
  outputs := sel

private def outNames (x : Design) : List String :=
  (Compile.compile x).outs.map (·.name)

-- `none` reproduces the pre-D39 port list exactly.
#guard outNames (d none) == ["o_pub", "o_secret"]
#guard (d none).exportedRegs.length == 2
#guard (d none).outputsOkB

-- A selection removes the unselected register from the interface, and only
-- from the interface: the register is still declared and still driven.
#guard outNames (d (some ["pub"])) == ["o_pub"]
#guard (d (some ["pub"])).regs.length == 2
#guard ((Compile.compile (d (some ["pub"]))).regs.map (·.name)) == ["pub", "secret"]
#guard outNames (d (some [])) == []
#guard outNames (d (some ["secret", "pub"])) == ["o_pub", "o_secret"]  -- declaration order

-- Well-formedness: a selection may only name declared registers.
#guard (d (some ["pub"])).outputsOkB
#guard !(d (some ["pub", "typo"])).outputsOkB
#guard (d (some ["pub", "typo"])).outputsUndeclared == ["typo"]

-- Composition (spec §4): the selection renames with the registers, `par`
-- concatenates, `connect` leaves it alone.
#guard ((d (some ["pub"])).prefixed "u0_").outputs == some ["u0_pub"]
#guard outNames ((d (some ["pub"])).prefixed "u0_") == ["o_u0_pub"]
#guard outNames (((d (some ["pub"])).prefixed "u0_").par ((d none).prefixed "u1_"))
        == ["o_u0_pub", "o_u1_pub", "o_u1_secret"]
#guard outNames ((d (some ["pub"])).connect (fun _ _ => none)) == ["o_pub"]

/-! The artifact that needed the capability (CAPWALK CE5, retired). The key
is six ordinary registers that no rule writes and no port carries. -/

private def cw : Design := Machines.CapWalk.Engine.design

#guard (cw.regs.map (·.name)).contains "mac_k0"
#guard (cw.regs.map (·.name)).contains "mac_iv"
#guard !(outNames cw).contains "o_mac_k0"
#guard !(outNames cw).contains "o_mac_iv"
#guard (Machines.CapWalk.Engine.keyRegs.map (·.name)).all
        fun n => !(outNames cw).contains s!"o_{n}"
-- No rule writes a key register (they are reset-loaded state).
#guard Machines.CapWalk.Engine.keyRegs.all fun r =>
        cw.rules.all fun rl =>
          !((rl.body.regWrites.map (·.1)).contains r.name)
-- The selection is well-formed and drops exactly the six key registers.
#guard cw.outputsOkB
#guard cw.regs.length - cw.exportedRegs.length == 6

/-! The refusal is an emit-time *error*: `Design.emit` throws and names the
selection entry, and writes nothing. -/
#eval show IO Unit from do
  let path : System.FilePath := "scratch/outputs_d39_test.v"
  if ← path.pathExists then IO.FS.removeFile path
  let refused ←
    try
      (d (some ["pub", "typo"])).emit path
      pure ""
    catch e => pure (toString e)
  unless (refused.splitOn "'typo'").length == 2 do
    throw <| IO.userError s!"D39: emit did not refuse the undeclared \
      selection entry (got: {refused})"
  if ← path.pathExists then
    throw <| IO.userError "D39: emit refused but still wrote the file"
  -- the well-formed selection emits, and the port is gone from the text
  (d (some ["pub"])).emit path
  let text ← IO.FS.readFile path
  unless (text.splitOn "o_secret").length == 1 do
    throw <| IO.userError "D39: the unexported register still has a port"
  unless (text.splitOn "o_pub").length == 3 do   -- port + assign
    throw <| IO.userError "D39: the exported register lost its port"
  unless (text.splitOn "reg [7:0] secret;").length == 2 do
    throw <| IO.userError "D39: the internal register lost its declaration"
  IO.FS.removeFile path

end Tests.Outputs
