-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas
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

/-- The memory-count agreement: one `MemoryRoot` per concrete memory, by
construction of `d.memoriesOf` as a map over `(d.toProgram).mems`. -/
theorem memoriesOf_length (d : Loom.Hw.Design) (blockSize : Nat) :
    (d.memoriesOf blockSize).length =
      (d.toProgram (blockSize := blockSize)).mems.length := by
  unfold Loom.Hw.Design.memoriesOf
  simp

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

/-- The indexed wires are the string-free view of the rendered wires with
correct global numbering. Proof shape: both ropes chunk the same underlying
flat list (`st.wires.toList` from the same traversal, since
`d.toIndexedWires` reruns `flatten` on the same expressions in the same
order and `indexedRhsOf`/`operandRef` are the per-wire translation), so
after a chunking-alignment lemma this reduces to
`indexedBlockMatches`-per-leaf, which follows from `wireNumber?`-roundtrip
facts about the canonical `n<i>` names produced by `freshWire` and
`Ref.render ∘ operandRef = id` on operand strings. -/
theorem toProgram_wireMatches (d : Loom.Hw.Design) :
    Symbolic.IndexedRopeMatches 0 (d.toProgram).wires d.indexedsOf := by
  sorry

/-- Well-formedness of the indexed wire graph: every wire is found by
`lookupIndexed?` at its own number and references only registers or
strictly earlier wires at consistent widths. Proof shape: a `FlattenSt`
invariant — every CSE-table entry maps to an already-emitted wire whose
name is `n<i>` for `i < st.next`, and `flatten` returns either a register
name or such an earlier wire at the expression's width — plus a
`balancedPath?`/`lookupIndexed?` correctness lemma for the
`shapeWireRope`/`tableOf` layout. -/
theorem toProgram_wireWellFormed (d : Loom.Hw.Design) :
    Symbolic.IndexedRopeWellFormed d.toProgram d.indexedsOf d.tableOf 0
      d.indexedsOf := by
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

With this proved, `VerifiedSymbolicArtifact.denotation` for a shipped
`program` reduces to the data equality `program = d.toProgram` — checkable
by reflection — and the per-design certificate pipeline is retired. The
`refinement` and `invariants` fields are untouched: they already flow
through `Compile.compile` and R-MC. -/
theorem toProgram_denotes (d : Loom.Hw.Design) (wf : Compile.DesignWF d)
    (hreads : Symbolic.designReadsValidB d d.toProgram = true) :
    Symbolic.ModuleBehavior d d.toProgram d.indexedsOf d.tableOf
      d.registersOf d.memoriesOf d.outputsOf :=
  Symbolic.moduleBehavior_of_checks d d.toProgram d.indexedsOf d.tableOf
    d.registersOf d.memoriesOf d.outputsOf
    (toProgram_name d 128 16).symm
    (toProgram_wireMatches d)
    (toProgram_wireWellFormed d)
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
