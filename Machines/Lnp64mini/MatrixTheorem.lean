-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64mini.Harness

/-! # W5, the deeper half: the opcode matrix as a theorem

`opDiffSelftest` runs the generated ALU matrix and fails a gate on mismatch.
This file states the same fact as a THEOREM, discharged by `native_decide` at
build time: a build of this library in which the design and the ISS disagree
on the matrix does not exist.

What this is and is not (PLATONIC.md, W5): `native_decide` evaluates with the
compiler, so the trusted base is the test's trusted base -- this is not a
symbolic proof of the ISA. What it removes is the HARNESS from the loop:
nothing has to remember to run it, no output has to be read, no exit code has
to be wired into CI. The claim lives in the artifact the kernel accepts.

Scope: the three ALU forms x nine boundary vectors (the matrix that caught the
six-opcode ISS bug). The full opDiffSelftest additionally covers loads/stores
on both memory paths, branches, the constant battery and the jump family; those
stay in the gate -- their cmd streams and multi-path checks are where the test
form earns its keep. -/

namespace Machines.Lnp64mini

theorem matrix_agrees : matrixMismatches () = 0 := by native_decide

end Machines.Lnp64mini
