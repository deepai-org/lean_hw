-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas
import Loom.Release.ToProgramWellFormed
import Loom.Release.SymbolicSound
import Loom.Hw.CompileCorrect

/-!
# The end-to-end statement (`toProgram_denotes`)

`Design.toProgram` makes the shipped release witness the verified compiler's
own output: the constructor reproduces the generated program exactly
(validated by `Scratch/ToProgramParity*.lean` on both Acc8 and LNP64-µ). The
theorem stated here — with the remaining hard conjuncts deliberately left as
audit-visible `sorry`s in the `Wip` namespace — is what retires the per-node
certificate pipeline: once `toProgram_denotes` is proved, the `denotation`
field of `VerifiedSymbolicArtifact` for any design follows from the single
data equality `program = d.toProgram` plus this generic theorem, instead of
from one re-derivation per wire, register, and port.

## The hard lemma

Of `ModuleBehavior`'s twelve conjuncts, ten are bookkeeping or now proved:
name and count agreement, output naming (fixed by construction of
`toProgram`), and the two wire-graph conjuncts — `IndexedRopeMatches` and
`IndexedRopeWellFormed` — which are theorems
(`toProgram_wireMatches`/`toProgram_wireWellFormed` below, assembled in
`Loom/Release/ToProgramWellFormed.lean` from the flatten-soundness invariant
of `Loom/Release/FlattenWF.lean`) conditional on one kernel-reducible
Boolean per design, `moduleEmitOkB` (the same D12 shape as
`designReadsValidB`). Two open conjuncts remain. The load-bearing one is
`RegisterBehaviorRopeFrom`: every register root reference in
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

/-- The memory-count agreement: one `MemoryRoot` per concrete memory, by
construction of `d.memoriesOf` as a map over `(d.toProgram).mems`. -/
theorem memoriesOf_length (d : Loom.Hw.Design) (blockSize : Nat) :
    (d.memoriesOf blockSize).length =
      (d.toProgram (blockSize := blockSize)).mems.length := by
  unfold Loom.Hw.Design.memoriesOf
  simp

/-- The indexed wires are the string-free view of the rendered wires with
correct global numbering: both ropes chunk the same underlying flat list
(`toIndexedWires_eq_flattenModule`), so this is per-wire `matchesRaw` —
operand canonicality from the flatten-soundness invariant — lifted through
the shared shape by `indexedRopeMatches_shaped`. Conditional on the design's
one kernel-reducible emission Boolean (decision D12 shape), which supplies
`FlattenSt.WF` through `flattenModule_wf`. -/
theorem toProgram_wireMatches (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true) :
    Symbolic.IndexedRopeMatches 0 (d.toProgram).wires d.indexedsOf :=
  toProgram_wireMatches_of_check d hemit

/-- Well-formedness of the indexed wire graph: every wire is found by
`lookupIndexed?` at its own number and references only registers or strictly
earlier wires at consistent widths. The flatten-soundness invariant
(`FlattenSt.WF`, from `flattenModule_wf` via the same emission Boolean)
supplies the per-wire `RhsOk` facts; `lookupIndexed?_shaped` and the
`RhsOk → indexedRhsWellFormed` bridge assemble them over the witness
layout. -/
theorem toProgram_wireWellFormed (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true) :
    Symbolic.IndexedRopeWellFormed d.toProgram d.indexedsOf d.tableOf 0
      d.indexedsOf :=
  toProgram_wireWellFormed_of_check d hemit

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

/-- Source read discipline against the constructed witness, discharged by
the existing decidable check (decision D12, `Loom/Hw/DESIGN.md`).

Not derivable from `Compile.DesignWF` alone: read validity additionally
needs (a) that no source register is named like a numbered wire
(`wireNumber? name = none`) and (b) that every register *read* in a rule
body is declared at its intrinsic width — `DesignWF` constrains only
writes. The obligation is deliberately carried as one kernel-reducible
Boolean (`Symbolic.designReadsValidB`), so a concrete design pays a single
`by decide`-style hypothesis rather than a hand proof; the check is
load-bearing, not stylistic — the Lean semantics gives an undeclared or
wrong-width read the environment default, while the printed Verilog would
reference an undriven implicit net. -/
theorem toProgram_readsValid (d : Loom.Hw.Design)
    (hreads : Symbolic.designReadsValidB d d.toProgram = true) :
    Symbolic.DesignReadsValid d d.toProgram :=
  Symbolic.designReadsValidB_sound hreads

/-- **The end-to-end statement (Task 0).** The witness constructed from the
verified compiler's output denotes that compilation at every wire, register,
write port, initialization cell, and output.

Of the four conjuncts formerly open, the two wire-graph facts are now
theorems (`toProgram_wireMatches`/`toProgram_wireWellFormed`), each
conditional on the single kernel-reducible Boolean `moduleEmitOkB` — one
`by decide`-style hypothesis per concrete design, the same D12 shape as
`hreads`. The two remaining `sorry`s are the semantic conjuncts
`toProgram_registerBehavior` and `toProgram_memoryBehavior` above.

With those proved, `VerifiedSymbolicArtifact.denotation` for a shipped
`program` reduces to the data equality `program = d.toProgram` — checkable
by reflection — and the per-design certificate pipeline is retired. The
`refinement` and `invariants` fields are untouched: they already flow
through `Compile.compile` and R-MC. -/
theorem toProgram_denotes (d : Loom.Hw.Design) (wf : Compile.DesignWF d)
    (hemit : moduleEmitOkB (Compile.compile d) = true)
    (hreads : Symbolic.designReadsValidB d d.toProgram = true) :
    Symbolic.ModuleBehavior d d.toProgram d.indexedsOf d.tableOf
      d.registersOf d.memoriesOf d.outputsOf :=
  Symbolic.moduleBehavior_of_checks d d.toProgram d.indexedsOf d.tableOf
    d.registersOf d.memoriesOf d.outputsOf
    (toProgram_name d 128 16).symm
    (toProgram_wireMatches d hemit)
    (toProgram_wireWellFormed d hemit)
    (toProgram_readsValid d hreads)
    (registersOf_listLength d 128).symm
    ((toProgram_regs_length d 128 16).trans (registersOf_listLength d 128).symm)
    ((toProgram_mems_length d 128 16).symm.trans (memoriesOf_length d 128).symm)
    (memoriesOf_length d 128).symm
    (outputsOf_listLength d 128).symm
    (toProgram_registerBehavior d wf)
    (toProgram_memoryBehavior d wf)
    (toProgram_outputBehavior d)

end Wip

end Loom.Release.SSA
