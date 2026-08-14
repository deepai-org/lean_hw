-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas
import Loom.Release.ToProgramWellFormed
import Loom.Release.ToProgramBehavior
import Loom.Release.ReadsValidKernel
import Loom.Release.SymbolicSound

/-!
# The end-to-end statement (`toProgram_denotes`)

`Design.toProgram` makes the shipped release witness the verified compiler's
own output: the constructor reproduces the generated program exactly
(validated by `Scratch/ToProgramParity*.lean` on both Acc8 and LNP64-µ). The
theorem stated here — now **proved**, with zero open conjuncts — is what
retires the per-node certificate pipeline: the `denotation` field of
`VerifiedSymbolicArtifact` for any design follows from the single data
equality `program = d.toProgram` plus this generic theorem, instead of from
one re-derivation per wire, register, and port.

All twelve conjuncts of `ModuleBehavior` are theorems, conditional on four
kernel-reducible Booleans per design (the D12 shape): `moduleEmitOkB`
(emission obligations, supplying the flatten-soundness invariant
`FlattenSt.WF`), `moduleMatchOkB` (the matcher's width discipline),
`moduleNamesOkB` (declared-name token discipline, D14), and
`designReadsValidB` (source read discipline). The two formerly hard
semantic conjuncts — every register root denoting `Compile.nextReg` folded
over the design's rules, and every memory root denoting its initialization
image and `Compile.compilePort` — are `toProgram_registerBehavior` and
`toProgram_memoryBehavior` in `Loom/Release/ToProgramBehavior.lean`,
assembled from the flatten-soundness invariant's semantic half
(`Loom/Release/FlattenMatches.lean`). A concrete design pays four
`by decide`-style hypotheses; today's 825-theorem, 68,028 CPU-s
`hybrid registers` phase is this theorem's register conjunct instantiated
nodewise at one design.
-/

namespace Loom.Release.SSA

open Loom.Hw Loom.Emit.MicroVerilog Loom.Release

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

/-- Source read discipline against the constructed witness, discharged by
the existing decidable check (decision D12, `Loom/Hw/DESIGN.md`).

Not derivable from `Compile.DesignWF` alone: read validity additionally
needs (a) that no source register is named like a numbered wire
(`wireNumber? name = none`) and (b) that every register *read* in a rule
body is declared at its intrinsic width — `DesignWF` constrains only
writes. The obligation is deliberately carried as one kernel-reducible
Boolean (`designReadsOkB`, the kernel-reducible form of
`Symbolic.designReadsValidB` — decision D12; the original's
`wireNumber?` arms do not kernel-reduce), so a concrete design pays a single
`by decide`-style hypothesis rather than a hand proof; the check is
load-bearing, not stylistic — the Lean semantics gives an undeclared or
wrong-width read the environment default, while the printed Verilog would
reference an undriven implicit net. -/
theorem toProgram_readsValid (d : Loom.Hw.Design)
    (hreads : designReadsOkB d d.toProgram = true) :
    Symbolic.DesignReadsValid d d.toProgram :=
  designReadsOkB_sound hreads

/-- **The end-to-end statement (Task 0), proved.** The witness constructed
from the verified compiler's output denotes that compilation at every wire,
register, write port, initialization cell, and output — conditional only on
the four kernel-reducible design Booleans `hemit`/`hmw`/`hnames`/`hreads`,
each one `by decide`-style hypothesis per concrete design.

`VerifiedSymbolicArtifact.denotation` for a shipped `program` therefore
reduces to the data equality `program = d.toProgram` — checkable by
reflection — and the per-design certificate pipeline is retired. The
`refinement` and `invariants` fields are untouched: they already flow
through `Compile.compile` and R-MC. -/
theorem toProgram_denotes (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true)
    (hmw : moduleMatchOkB (Compile.compile d) = true)
    (hnames : moduleNamesOkB (Compile.compile d) = true)
    (hreads : designReadsOkB d d.toProgram = true)
    (hcomb : d.combOutputs = []) :
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
    (toProgram_registerBehavior d hemit hmw hnames)
    (toProgram_memoryBehavior d hemit hmw hnames)
    (toProgram_outputBehavior d hcomb)

/-! ## Axiom audit -/

#print axioms toProgram_denotes

end Loom.Release.SSA
