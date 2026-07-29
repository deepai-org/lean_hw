-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas
import Loom.Release.RopeLayout

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

/-- Raw-side layout: `lookupRaw?` on the witness shape answers with the
wire the flat list holds at that number — `lookupIndexed?_shaped` without
the number guard. -/
theorem lookupRaw?_shaped (k leafSize : Nat) (hs : 0 < leafSize)
    (xs : List Wire) (n : Nat) (wire : Wire) (hfound : xs[n]? = some wire) :
    Symbolic.lookupRaw?
      (balancedRope ((listChunks (2 ^ k)
        ((listChunks leafSize xs).map Rope.leaf)).map balancedRope))
      { leafSize := leafSize,
        leafCount := (xs.length + leafSize - 1) / leafSize }
      n = some wire := by
  have hn : n < xs.length := lt_of_getElem?_eq_some hfound
  have hcount : n / leafSize < (xs.length + leafSize - 1) / leafSize := by
    rw [show xs.length + leafSize - 1 = xs.length - 1 + leafSize by omega,
      Nat.add_div_right _ hs]
    have := Nat.div_le_div_right (c := leafSize)
      (show n ≤ xs.length - 1 by omega)
    omega
  obtain ⟨path, hpath⟩ :=
    Option.isSome_iff_exists.mp (balancedPath?_isSome _ _ hcount)
  have resolved : (balancedRope ((listChunks (2 ^ k)
      ((listChunks leafSize xs).map Rope.leaf)).map balancedRope)).resolve?
        ⟨path, n % leafSize⟩ = some wire := by
    rw [balancedRope_chunks_pow2,
      balancedRope_resolve_path (listChunks leafSize xs) (n / leafSize) path
        (by rw [listChunks_length leafSize hs xs]; exact hpath) (n % leafSize),
      listChunks_getElem leafSize hs xs n]
    exact hfound
  simp [Symbolic.lookupRaw?, hs, hpath, resolved, guard]

/-! ## Declaration lookup transfer

`refWidthBefore?` consults `program.regs`/`program.mems`; the flatten
invariant speaks about the module's `RegDef`/`MemDef` lists. Flattening
preserves names and widths pointwise in order, so `find?` answers
correspond. -/

/-- `find?` on flattened registers returns the declaration's name and
width. -/
theorem flattenRegs_find?_meta (regs : List RegDef) (s : FlattenSt)
    (name : String) :
    (((flattenRegs regs).run s).1.find? (fun c => c.name == name)).map
        (fun c => (c.name, c.width)) =
      (regs.find? (fun r => r.name == name)).map
        (fun r => (r.name, r.width)) := by
  induction regs generalizing s with
  | nil => rfl
  | cons r rest ih =>
      rw [flattenRegs_run_cons]
      by_cases hname : r.name == name
      · simp [hname]
      · simp only [List.find?_cons, hname]
        exact ih ((flatten r.next).run s).2

/-- `find?` on flattened memories returns the declaration's name and both
widths. -/
theorem flattenMems_find?_meta (mems : List MemDef) (blockSize : Nat)
    (s : FlattenSt) (name : String) :
    (((flattenMems blockSize mems).run s).1.find?
        (fun c => c.name == name)).map
        (fun c => (c.name, c.addrWidth, c.dataWidth)) =
      (mems.find? (fun mm => mm.name == name)).map
        (fun mm => (mm.name, mm.addrWidth, mm.dataWidth)) := by
  induction mems generalizing s with
  | nil => rfl
  | cons mm rest ih =>
      rw [flattenMems_run_cons]
      by_cases hname : mm.name == name
      · simp [hname]
      · simp only [List.find?_cons, hname]
        exact ih ((flattenWrites mm.wrPorts).run s).2

end Loom.Release.SSA
