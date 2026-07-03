import Machines.Lnp64u.Isa.Base
import Machines.Lnp64u.Isa.System

/-!
# The LNP64-µ instruction set

`isa` is the single source of truth: decoder, assembler, ISS, conformance
suite, book, and the T1 obligations are all projections of this array
(25 declarations: 14 base + 11 system).
-/

namespace Machines.Lnp64u

/-- The complete instruction set. -/
def isa : IsaT := (Isa.base ++ Isa.system).toArray

/-- Per-class worst-case execution costs of the multicycle core, in cycles.
These are the constants T7's WCET lemmas quote; Phase 2/3 validates them
against the RTL per target (they are *spec* constants: the refinement proof
must show the core meets them). -/
def WcetClass.cost : WcetClass → Nat
  | .alu    => 2
  | .mem    => 3
  | .capOp  => 8
  | .revoke => 24
  | .gate   => 8
  | .mover  => 6
  | .sched  => 1

end Machines.Lnp64u
