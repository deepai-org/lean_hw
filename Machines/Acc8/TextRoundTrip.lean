import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.RoundTrip
import Machines.Acc8.Core
import Machines.Acc8.Iss

/-!
# Acc8 text-level round trip (task 2.3, concrete instance)

`lake exe emit` writes `Print.print acc8Module` to `rtl/acc8.v`. The check
below re-parses that exact text inside Lean and compares the result against
the compiled module, so the pretty-printer drops out of the trusted base
for the Acc8 artifact: the emitted TEXT determines the `Module` AST that
the emission theorem (A-EV) speaks about, up to `Module.Matches` (which
covers everything printed — the complete memory init images on
`[0, 2^addrWidth)` included).

`Module.parseCheck_sound` (in `Loom/Emit/MicroVerilog/RoundTrip.lean`)
upgrades a `parseCheck` verdict into the round-trip statement
`∃ m', parse (print acc8Module) = some m' ∧ m'.Matches acc8Module`.

The verdict here is checked by `#guard`, i.e. by the compiled evaluator at
elaboration time — the same corroboration level as the ISS golden tests in
`Tests/Acc8.lean` (and as decision D2's compiled-eval pipeline checks). A
`by decide +kernel` proof of `acc8Module.parseCheck = true` is *stated
correctly* but was measured at > 4 min and > 40 GB of kernel reduction
(`String.append`'s ByteArray model makes building the ~30 KB text
quadratic in the kernel), so it is not committed; the fully
kernel-checked round-trip instance lives in `RoundTrip.lean` (`demo`),
which exercises every grammar production on a small module.
-/

namespace Machines.Acc8

open Loom.Emit.MicroVerilog

/-- The compiled Acc8 core with the golden boot image — byte-for-byte the
module that `lake exe emit` prints to `rtl/acc8.v` (see `Tools/Emit.lean`). -/
def acc8Module : Module :=
  Loom.Hw.Compile.compile (Core.design (loadProg golden))

-- Text-level round-trip regression for the emitted Acc8 Verilog:
-- parsing the exact printed text recovers the compiled module.
#guard acc8Module.parseCheck

end Machines.Acc8
