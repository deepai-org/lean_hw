import Loom.Hw.Compile
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Hw.Demo
open Machines.Lnp64u Machines.Lnp64u.Hw Machines.Lnp64u.Demo
def main : IO Unit := do
  IO.println s!"design rules: {(core sysManifest).rules.length}"
  IO.println s!"module regs: {(Loom.Hw.Compile.compile (core sysManifest)).regs.length}"
