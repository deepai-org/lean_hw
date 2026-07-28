-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.SymbolicSound
import Loom.Hw.CompileCorrect

/-!
# The end-to-end statement (`toProgram_denotes`)

`Design.toProgram` makes the shipped release witness the verified compiler's
own output: the constructor reproduces the generated program exactly
(validated by `Scratch/ToProgramParity*.lean` on both Acc8 and LNP64-µ). The
theorem stated here — with its proof deliberately left as audit-visible
`sorry`s in the `Wip` namespace — is what retires the per-node certificate
pipeline: once `toProgram_denotes` is proved, the `denotation` field of
`VerifiedSymbolicArtifact` for any design follows from the single data
equality `program = d.toProgram` plus this generic theorem, instead of from
one re-derivation per wire, register, and port.

## The hard lemma

Of `ModuleBehavior`'s twelve conjuncts, eleven are bookkeeping (name and
count agreement, structural index/table well-formedness, read validity,
output naming — each fixed by construction of `toProgram`). The load-bearing
conjunct is `RegisterBehaviorRopeFrom`: every register root reference in
`d.registersOf` must *semantically denote* `Compile.nextReg` folded over the
design's rules — that is, elaborating the flattened SSA wires and resolving
register `i`'s root must evaluate, in every state, to the verified
compilation's next-state function. That is `toProgram_registerBehavior`
below. It is the generic, once-for-all form of exactly the obligation the
per-design pipeline discharges today with 825 generated theorems and
68,028 CPU-s per release: today's `hybrid registers` phase is this lemma,
instantiated nodewise at one design.

The underlying induction is a flatten-soundness invariant: if a `FlattenSt`
is consistent (its emitted wires elaborate to an environment in which every
CSE entry resolves to a value extensionally equal to the expression it was
allocated for), then `flatten e` returns a name resolving to a value
extensionally equal to `e`, and consistency is preserved. Stating that
invariant requires committing to the environment-consistency predicate,
which is the first real design decision of the proof and is deliberately
left inside the `sorry`.
-/

namespace Loom.Release.SSA

open Loom.Hw Loom.Emit.MicroVerilog Loom.Release

/-- One memory root per declaration of `d.toProgram`, its port wires
referenced symbolically. -/
def _root_.Loom.Hw.Design.memoriesOf (d : Loom.Hw.Design)
    (blockSize : Nat := 128) : List Symbolic.MemoryRoot :=
  (d.toProgram (blockSize := blockSize)).mems.zipIdx.map fun (mem, index) =>
    { index
      init := mem.init
      ports := mem.writes.zipIdx.map fun (write, port) =>
        { index := port
          refs := { en := operandRef write.en, addr := operandRef write.addr,
                    data := operandRef write.data } } }

namespace Wip

/-- **The hard lemma** (stated, unproved). Every register root of the
constructed witness semantically denotes the verified compilation's
next-state expression. This single generic statement is what today's 825
per-register generated theorems (the 68,028 CPU-s `hybrid registers`
phase) instantiate at one design; proving it once retires that phase for
every design. -/
theorem toProgram_registerBehavior (d : Loom.Hw.Design) (wf : Compile.DesignWF d) :
    Symbolic.RegisterBehaviorRopeFrom d d.toProgram d.tableOf 0
      d.registersOf := by
  sorry

/-- The memory conjunct: initialization images and write-port references of
the constructed witness denote `Compile.compilePort`. Structurally the same
flatten-soundness argument as `toProgram_registerBehavior` at the three port
faces, plus a direct image correspondence. -/
theorem toProgram_memoryBehavior (d : Loom.Hw.Design) (wf : Compile.DesignWF d) :
    Symbolic.MemoryBehaviorsFrom d d.toProgram d.tableOf 0 d.memoriesOf := by
  sorry

/-- **The end-to-end statement (Task 0).** The witness constructed from the
verified compiler's output denotes that compilation at every wire, register,
write port, initialization cell, and output.

With this proved, `VerifiedSymbolicArtifact.denotation` for a shipped
`program` reduces to the data equality `program = d.toProgram` — checkable
by reflection — and the per-design certificate pipeline is retired. The
`refinement` and `invariants` fields are untouched: they already flow
through `Compile.compile` and R-MC. -/
theorem toProgram_denotes (d : Loom.Hw.Design) (wf : Compile.DesignWF d) :
    Symbolic.ModuleBehavior d d.toProgram d.indexedsOf d.tableOf
      d.registersOf d.memoriesOf d.outputsOf := by
  sorry

end Wip

end Loom.Release.SSA
