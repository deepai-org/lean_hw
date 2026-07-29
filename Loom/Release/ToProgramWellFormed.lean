-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas

/-!
# Assembly toward `toProgram_wireWellFormed`

Bridging facts that connect the constructed witness's three faces — the
flat wire list (`FlattenSt.wires` of `flattenModule`), the indexed view
(`Design.toIndexedWires`), and the shaped ropes (`Design.indexedsOf`,
`(d.toProgram).wires`). The first brick: `toIndexedWires` reruns `flatten`
with `for` loops that discard results, and its final state is exactly
`flattenModule`'s, so the indexed wires are literally the numbered
projection of the same flat array the program's raw rope is shaped from.
-/

namespace Loom.Release.SSA

open Loom.Hw Loom.Emit.MicroVerilog

/-- In `Id`, bind is application; making that a rewrite lets `simp` erase
the monadic plumbing `for` desugaring leaves behind. -/
private theorem id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) :
    x >>= f = f x := rfl

private theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- The register loop of `toIndexedWires` has the same state effect as
`flattenRegs`. -/
theorem forRegs_state (regs : List RegDef) (s : FlattenSt) :
    ((show StateM FlattenSt Unit from do
        for r in regs do
          _ ← flatten r.next).run s).2 =
      ((flattenRegs regs).run s).2 := by
  induction regs generalizing s with
  | nil => rfl
  | cons r rest ih =>
      rw [flattenRegs_run_cons]
      simp only [List.forIn_cons, StateT.run_bind, StateT.run_pure]
      exact ih ((flatten r.next).run s).2

/-- The write-port loop of `toIndexedWires` has the same state effect as
`flattenWrites`. -/
theorem forWrites_state {aw dw : Nat} (ports : List (WritePort aw dw))
    (s : FlattenSt) :
    ((show StateM FlattenSt Unit from do
        for p in ports do
          _ ← flatten p.en
          _ ← flatten p.addr
          _ ← flatten p.data).run s).2 =
      ((flattenWrites ports).run s).2 := by
  induction ports generalizing s with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.forIn_cons, flattenWrites, StateT.run_bind,
        StateT.run_pure]
      exact ih ((flatten p.data).run
        ((flatten p.addr).run ((flatten p.en).run s).2).2).2

/-- The memory loop of `toIndexedWires` has the same state effect as
`flattenMems` (for any `blockSize`: image chunking allocates no wires). -/
theorem forMems_state (mems : List MemDef) (blockSize : Nat) (s : FlattenSt) :
    ((show StateM FlattenSt Unit from do
        for mm in mems do
          for p in mm.wrPorts do
            _ ← flatten p.en
            _ ← flatten p.addr
            _ ← flatten p.data).run s).2 =
      ((flattenMems blockSize mems).run s).2 := by
  induction mems generalizing s with
  | nil => rfl
  | cons mm rest ih =>
      rw [flattenMems_run_cons]
      simp only [List.forIn_cons, StateT.run_bind, StateT.run_pure,
        id_bind_eq, id_pure_eq]
      have hstate := forWrites_state mm.wrPorts s
      simp only [StateT.run_bind, StateT.run_pure, id_bind_eq,
        id_pure_eq] at hstate
      rw [hstate]
      have tail := ih ((flattenWrites mm.wrPorts).run s).2
      simp only [StateT.run_bind, StateT.run_pure, id_bind_eq,
        id_pure_eq] at tail
      exact tail

/-- The output loop of `toIndexedWires` has the same state effect as
`flattenOuts`. -/
theorem forOuts_state (outs : List OutDef) (s : FlattenSt) :
    ((show StateM FlattenSt Unit from do
        for o in outs do
          _ ← flatten o.val).run s).2 =
      ((flattenOuts outs).run s).2 := by
  induction outs generalizing s with
  | nil => rfl
  | cons o rest ih =>
      rw [flattenOuts_run_cons]
      simp only [List.forIn_cons, StateT.run_bind, StateT.run_pure]
      exact ih ((flatten o.val).run s).2

/-- `toIndexedWires` is the numbered projection of the exact flat wire
array `flattenModule` produces — the two constructions share one state. -/
theorem toIndexedWires_eq_flattenModule (d : Loom.Hw.Design) (blockSize : Nat) :
    d.toIndexedWires =
      ((((flattenModule (Compile.compile d) blockSize).run {}).2).wires.toList.zipIdx.map
        fun (wire, number) =>
          { number, width := wire.width, rhs := indexedRhsOf wire.rhs }) := by
  have state_eq :
      ((show StateM FlattenSt Unit from do
          for r in (Compile.compile d).regs do
            _ ← flatten r.next
          for mm in (Compile.compile d).mems do
            for p in mm.wrPorts do
              _ ← flatten p.en
              _ ← flatten p.addr
              _ ← flatten p.data
          for o in (Compile.compile d).outs do
            _ ← flatten o.val).run {}).2 =
      ((flattenModule (Compile.compile d) blockSize).run {}).2 := by
    rw [flattenModule_run]
    calc ((show StateM FlattenSt Unit from do
            for r in (Compile.compile d).regs do
              _ ← flatten r.next
            for mm in (Compile.compile d).mems do
              for p in mm.wrPorts do
                _ ← flatten p.en
                _ ← flatten p.addr
                _ ← flatten p.data
            for o in (Compile.compile d).outs do
              _ ← flatten o.val).run {}).2
        = ((show StateM FlattenSt Unit from do
            for o in (Compile.compile d).outs do
              _ ← flatten o.val).run
            ((show StateM FlattenSt Unit from do
              for mm in (Compile.compile d).mems do
                for p in mm.wrPorts do
                  _ ← flatten p.en
                  _ ← flatten p.addr
                  _ ← flatten p.data).run
              ((show StateM FlattenSt Unit from do
                for r in (Compile.compile d).regs do
                  _ ← flatten r.next).run {}).2).2).2 := rfl
      _ = _ := by
        rw [forRegs_state, forMems_state (blockSize := blockSize), forOuts_state]
  exact congrArg
    (fun st : FlattenSt => st.wires.toList.zipIdx.map
      fun (wire, number) =>
        ({ number, width := wire.width,
           rhs := indexedRhsOf wire.rhs } : Symbolic.IndexedWire))
    state_eq

end Loom.Release.SSA
