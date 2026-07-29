-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas
import Loom.Release.RopeLayout
import Loom.Release.FlattenWF

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

/-! ## The decidable emission check

`flattenModule_wf` consumes `ModuleEmitOk`; a concrete design should pay one
kernel-reducible Boolean instead of a hand proof (the same D12 shape as
`Symbolic.designReadsValidB`). The checker mirrors `ExprEmitOk`
case-for-case. -/

/-- Decidable form of `ExprEmitOk`. -/
def exprEmitOkB (regs : List RegDef) (mems : List MemDef) :
    {w : Nat} → Emit.MicroVerilog.Expr w → Bool
  | w, .reg _ name =>
      match regs.find? (fun c => c.name == name) with
      | some r => r.width == w && (Symbolic.wireNumber? name).isNone
      | none => false
  | _, .lit _ => true
  | dw, @Emit.MicroVerilog.Expr.memRead _ mem aw addr =>
      (match mems.find? (fun c => c.name == mem) with
       | some header => header.addrWidth == aw && header.dataWidth == dw
       | none => false) &&
      exprEmitOkB regs mems addr
  | _, .and a b | _, .or a b | _, .xor a b | _, .add a b | _, .sub a b
  | _, .shl a b | _, .shr a b | _, .eq a b | _, .ult a b | _, .slt a b =>
      exprEmitOkB regs mems a && exprEmitOkB regs mems b
  | _, .not a => exprEmitOkB regs mems a
  | _, .mux c t f =>
      exprEmitOkB regs mems c && exprEmitOkB regs mems t &&
        exprEmitOkB regs mems f
  | _, @Emit.MicroVerilog.Expr.slice _ a _ w' =>
      decide (0 < w') && exprEmitOkB regs mems a
  | _, .zext a _ => exprEmitOkB regs mems a
  | w', @Emit.MicroVerilog.Expr.sext w a _ =>
      decide (w < w' → 0 < w) && decide (w' < w → 0 < w') &&
        exprEmitOkB regs mems a

theorem exprEmitOkB_sound {regs : List RegDef} {mems : List MemDef}
    {w : Nat} (e : Emit.MicroVerilog.Expr w) :
    exprEmitOkB regs mems e = true → ExprEmitOk regs mems e := by
  induction e with
  | lit v => exact fun _ => trivial
  | reg wr name =>
      intro accepted
      simp only [exprEmitOkB] at accepted
      cases found : regs.find? (fun c => c.name == name) with
      | none => simp [found] at accepted
      | some r =>
          simp only [found, Bool.and_eq_true, beq_iff_eq,
            Option.isNone_iff_eq_none] at accepted
          exact ⟨accepted.2, r, found, accepted.1⟩
  | memRead dw mem addr ih =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      obtain ⟨hfind, haddr⟩ := accepted
      refine ⟨?_, ih haddr⟩
      cases found : mems.find? (fun c => c.name == mem) with
      | none => simp [found] at hfind
      | some header =>
          simp only [found, Bool.and_eq_true, beq_iff_eq] at hfind
          exact ⟨header, rfl, hfind.1, hfind.2⟩
  | and a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | or a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | xor a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | add a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | sub a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | shl a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | shr a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | eq a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | ult a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | slt a b iha ihb =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨iha accepted.1, ihb accepted.2⟩
  | not a ih => exact fun accepted => ih accepted
  | mux c t f ihc iht ihf =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true] at accepted
      exact ⟨ihc accepted.1.1, iht accepted.1.2, ihf accepted.2⟩
  | slice a lo w' ih =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact ⟨accepted.1, ih accepted.2⟩
  | zext a w' ih => exact fun accepted => ih accepted
  | sext a w' ih =>
      intro accepted
      simp only [exprEmitOkB, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact ⟨accepted.1.1, accepted.1.2, ih accepted.2⟩

/-- One kernel-reducible Boolean per design: every expression the printer
traversal flattens meets its emission obligations. -/
def moduleEmitOkB (m : Module) : Bool :=
  m.regs.all (fun r => exprEmitOkB m.regs m.mems r.next) &&
    m.mems.all (fun mm => mm.wrPorts.all fun p =>
      exprEmitOkB m.regs m.mems p.en && exprEmitOkB m.regs m.mems p.addr &&
        exprEmitOkB m.regs m.mems p.data) &&
    m.outs.all (fun o => exprEmitOkB m.regs m.mems o.val)

theorem moduleEmitOkB_sound (m : Module) (accepted : moduleEmitOkB m = true) :
    ModuleEmitOk m := by
  simp only [moduleEmitOkB, Bool.and_eq_true, List.all_eq_true] at accepted
  obtain ⟨⟨hregs, hmems⟩, houts⟩ := accepted
  refine ⟨fun r hr => exprEmitOkB_sound r.next (hregs r hr),
    fun mm hmm p hp => ?_,
    fun o ho => exprEmitOkB_sound o.val (houts o ho)⟩
  have hport := hmems mm hmm p hp
  exact ⟨exprEmitOkB_sound p.en hport.1.1, exprEmitOkB_sound p.addr hport.1.2,
    exprEmitOkB_sound p.data hport.2⟩

/-! ## Default-shape projections

The remaining lemmas fix the default witness shape (`blockSize = 128`,
`chunkLeaves = 16 = 2 ^ 4`) and connect the three faces of the construction
through the shared flattening state. -/

/-- The flattening state underlying `d.toProgram` (default `blockSize`),
shared with `d.toIndexedWires` by `toIndexedWires_eq_flattenModule`. -/
def _root_.Loom.Hw.Design.flattenStOf (d : Loom.Hw.Design) : FlattenSt :=
  ((flattenModule (Compile.compile d) 128).run {}).2

/-- The missing `toProgram` projection: the wire rope is the shaped view of
the flat traversal output. -/
theorem toProgram_wires (d : Loom.Hw.Design) (blockSize chunkLeaves : Nat) :
    (d.toProgram blockSize chunkLeaves).wires =
      shapeWireRope blockSize chunkLeaves
        ((((flattenModule (Compile.compile d) blockSize).run {}).2).wires.toList) :=
  rfl

theorem toProgram_wires_shaped (d : Loom.Hw.Design) :
    (d.toProgram).wires =
      balancedRope ((listChunks (2 ^ 4)
        ((listChunks 128 d.flattenStOf.wires.toList).map Rope.leaf)).map
        balancedRope) := rfl

theorem indexedsOf_shaped (d : Loom.Hw.Design) :
    d.indexedsOf =
      balancedRope ((listChunks (2 ^ 4)
        ((listChunks 128 d.toIndexedWires).map Rope.leaf)).map
        balancedRope) := rfl

theorem tableOf_shaped (d : Loom.Hw.Design) :
    d.tableOf =
      { leafSize := 128,
        leafCount := (d.toIndexedWires.length + 128 - 1) / 128 } := rfl

/-- `toIndexedWires_eq_flattenModule` at the default shape, phrased through
the shared state. -/
theorem toIndexedWires_eq (d : Loom.Hw.Design) :
    d.toIndexedWires =
      d.flattenStOf.wires.toList.zipIdx.map fun (wire, number) =>
        { number, width := wire.width, rhs := indexedRhsOf wire.rhs } :=
  toIndexedWires_eq_flattenModule d 128

/-- Element `i` of the indexed view is the numbered translation of element
`i` of the flat wire list. -/
theorem toIndexedWires_getElem? (d : Loom.Hw.Design) (i : Nat) :
    d.toIndexedWires[i]? =
      (d.flattenStOf.wires.toList[i]?).map fun wire =>
        { number := i, width := wire.width, rhs := indexedRhsOf wire.rhs } := by
  rw [toIndexedWires_eq d, List.getElem?_map, List.getElem?_zipIdx]
  cases d.flattenStOf.wires.toList[i]? <;> simp

theorem toIndexedWires_length (d : Loom.Hw.Design) :
    d.toIndexedWires.length = d.flattenStOf.wires.toList.length := by
  rw [toIndexedWires_eq d, List.length_map, List.length_zipIdx]

/-- Indexed lookup on the default shape answers with the stored wire. -/
theorem lookupIndexed?_toIndexedWires (d : Loom.Hw.Design)
    {n : Nat} {wire : Symbolic.IndexedWire}
    (found : d.toIndexedWires[n]? = some wire) :
    Symbolic.lookupIndexed? d.indexedsOf d.tableOf n = some wire := by
  have hnum : ∀ (i : Nat) (w : Symbolic.IndexedWire),
      d.toIndexedWires[i]? = some w → w.number = i := by
    intro i w hw
    rw [toIndexedWires_getElem?] at hw
    obtain ⟨raw, -, hmap⟩ := Option.map_eq_some_iff.mp hw
    subst hmap
    rfl
  rw [indexedsOf_shaped, tableOf_shaped]
  exact lookupIndexed?_shaped 4 128 (by omega) d.toIndexedWires hnum n wire
    found

/-- Raw lookup on the constructed program answers with the flat list's
wire. -/
theorem lookupRaw?_toProgram (d : Loom.Hw.Design) {n : Nat} {wire : Wire}
    (found : d.flattenStOf.wires.toList[n]? = some wire) :
    Symbolic.lookupRaw? (d.toProgram).wires d.tableOf n = some wire := by
  rw [toProgram_wires_shaped, tableOf_shaped, toIndexedWires_length]
  exact lookupRaw?_shaped 4 128 (by omega) d.flattenStOf.wires.toList n wire
    found

/-- `find?` metadata transfer from module registers to program registers. -/
theorem toProgram_regs_find? (d : Loom.Hw.Design) (name : String) :
    ((d.toProgram).regs.find? (fun c => c.name == name)).map
        (fun c => (c.name, c.width)) =
      ((Compile.compile d).regs.find? (fun r => r.name == name)).map
        (fun r => (r.name, r.width)) := by
  rw [toProgram_regs d 128 16]
  exact flattenRegs_find?_meta (Compile.compile d).regs {} name

/-- `find?` metadata transfer from module memories to program memories. -/
theorem toProgram_mems_find? (d : Loom.Hw.Design) (name : String) :
    ((d.toProgram).mems.find? (fun c => c.name == name)).map
        (fun c => (c.name, c.addrWidth, c.dataWidth)) =
      ((Compile.compile d).mems.find? (fun mm => mm.name == name)).map
        (fun mm => (mm.name, mm.addrWidth, mm.dataWidth)) := by
  rw [toProgram_mems d 128 16]
  exact flattenMems_find?_meta (Compile.compile d).mems 128
    ((flattenRegs (Compile.compile d).regs).run {}).2 name

/-! ## Operand resolution: `OperandOk` → `refWidthBefore?` -/

/-- A resolvable flatten-state operand resolves in the constructed witness at
the same width. -/
theorem refWidthBefore?_of_operandOk (d : Loom.Hw.Design)
    (wf : d.flattenStOf.WF (Compile.compile d).regs (Compile.compile d).mems)
    {i : Nat} {name : String} {w' : Nat}
    (ok : OperandOk (Compile.compile d).regs d.flattenStOf.wires i name w') :
    Symbolic.refWidthBefore? d.toProgram d.indexedsOf d.tableOf i
      (operandRef name) = some w' := by
  cases ok with
  | inl wireCase =>
      obtain ⟨m, wire, hnum, hname, hlt, hfound, hwidth⟩ := wireCase
      have hop : operandRef name = .wire m := by
        simp [operandRef, hnum]
      have hlist : d.flattenStOf.wires.toList[m]? = some wire := by
        rw [Array.getElem?_toList]; exact hfound
      have hidxfound : d.toIndexedWires[m]? =
          some ⟨m, wire.width, indexedRhsOf wire.rhs⟩ := by
        rw [toIndexedWires_getElem?, hlist]; rfl
      have hidx := lookupIndexed?_toIndexedWires d hidxfound
      have hraw := lookupRaw?_toProgram d hlist
      have hrawname : wire.name = Symbolic.wireName m := wf.names m wire hfound
      rw [hop]
      simp [Symbolic.refWidthBefore?, hlt, hidx, hraw, guard,
        Symbolic.Ref.render, hrawname, hwidth]
  | inr regCase =>
      obtain ⟨hnum, r, hfind, hwidth⟩ := regCase
      have hop : operandRef name = .reg name := by
        simp [operandRef, hnum]
      have hmeta := toProgram_regs_find? d name
      rw [hfind] at hmeta
      cases hfindP : (d.toProgram).regs.find? (fun c => c.name == name) with
      | none => rw [hfindP] at hmeta; exact absurd hmeta (by simp)
      | some c =>
          rw [hfindP] at hmeta
          simp only [Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hmeta
          rw [hop]
          simp [Symbolic.refWidthBefore?, hnum, hfindP, guard, hmeta.2, hwidth]

/-! ## The `RhsOk` → `indexedRhsWellFormed` bridge -/

/-- **The core bridge**: each emitted right-hand side's flatten-state
obligations imply the release checker's per-node type check on the
translated node. -/
theorem indexedRhsWellFormed_of_rhsOk (d : Loom.Hw.Design)
    (wf : d.flattenStOf.WF (Compile.compile d).regs (Compile.compile d).mems)
    {i : Nat} {rhs : Rhs} {w : Nat}
    (ok : RhsOk (Compile.compile d).regs (Compile.compile d).mems
      d.flattenStOf.wires i rhs w) :
    Symbolic.indexedRhsWellFormed d.toProgram d.indexedsOf d.tableOf i w
      (indexedRhsOf rhs) = true := by
  cases rhs with
  | lit lw v =>
      have hlw : lw = w := ok
      subst hlw
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed]
  | ident value =>
      obtain ⟨w', op⟩ := ok
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf op]
  | memRead mem addr =>
      obtain ⟨header, hfind, hdata, hop⟩ := ok
      have haddr := refWidthBefore?_of_operandOk d wf hop
      have hmeta := toProgram_mems_find? d mem
      rw [hfind] at hmeta
      cases hfindP : (d.toProgram).mems.find? (fun c => c.name == mem) with
      | none => rw [hfindP] at hmeta; exact absurd hmeta (by simp)
      | some c =>
          rw [hfindP] at hmeta
          simp only [Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hmeta
          simp [indexedRhsOf, Symbolic.indexedRhsWellFormed, hfindP, haddr,
            hmeta.2.1, hmeta.2.2, hdata]
  | slice value hi lo =>
      obtain ⟨⟨w', op⟩, hle, heq⟩ := ok
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf op, hle, heq]
  | not value =>
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf ok]
  | bin op left right =>
      cases op <;> first
        | simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
            refWidthBefore?_of_operandOk d wf ok.1,
            refWidthBefore?_of_operandOk d wf ok.2]
        | (obtain ⟨hw, w', hl, hr⟩ := ok
           subst hw
           simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
             refWidthBefore?_of_operandOk d wf hl,
             refWidthBefore?_of_operandOk d wf hr])
  | slt left right =>
      obtain ⟨hw, w', hl, hr⟩ := ok
      subst hw
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf hl,
        refWidthBefore?_of_operandOk d wf hr]
  | mux c y n =>
      obtain ⟨hc, hy, hn⟩ := ok
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf hc,
        refWidthBefore?_of_operandOk d wf hy,
        refWidthBefore?_of_operandOk d wf hn]
  | sext amount value signBit =>
      obtain ⟨iw, op, hsign, hamount, hlt⟩ := ok
      simp [indexedRhsOf, Symbolic.indexedRhsWellFormed,
        refWidthBefore?_of_operandOk d wf op, hsign, hamount, hlt]

/-! ## The `matchesRaw` bridge -/

/-- Operand canonicality: a resolvable operand's translated reference renders
back to the operand string. -/
theorem operandRef_render {regs : List RegDef} {wires : Array Wire}
    {bound : Nat} {name : String} {w : Nat}
    (ok : OperandOk regs wires bound name w) :
    (operandRef name).render = name := by
  cases ok with
  | inl wireCase =>
      obtain ⟨m, wire, hnum, hname, -, -, -⟩ := wireCase
      subst hname
      simp [operandRef, wireNumber?_wireName, Symbolic.Ref.render]
  | inr regCase =>
      simp [operandRef, regCase.1, Symbolic.Ref.render]

/-- A flat wire whose operands are resolvable matches its own indexed
translation at any number. -/
theorem matchesRaw_of_rhsOk {regs : List RegDef} {mems : List MemDef}
    {wires : Array Wire} {bound : Nat} (i : Nat) (raw : Wire)
    (ok : RhsOk regs mems wires bound raw.rhs raw.width) :
    Symbolic.IndexedWire.matchesRaw i raw
      { number := i, width := raw.width, rhs := indexedRhsOf raw.rhs } =
      true := by
  obtain ⟨w, name, rhs⟩ := raw
  cases rhs with
  | lit lw v => simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf]
  | ident value =>
      obtain ⟨w', op⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render op]
  | memRead mem addr =>
      obtain ⟨header, -, -, op⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render op]
  | slice value hi lo =>
      obtain ⟨⟨w', op⟩, -, -⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render op]
  | not value =>
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render ok]
  | bin op left right =>
      cases op <;> first
        | simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
            operandRef_render ok.1, operandRef_render ok.2]
        | (obtain ⟨-, w', hl, hr⟩ := ok
           simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
             operandRef_render hl, operandRef_render hr])
  | slt left right =>
      obtain ⟨-, w', hl, hr⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render hl, operandRef_render hr]
  | mux c y n =>
      obtain ⟨hc, hy, hn⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render hc, operandRef_render hy, operandRef_render hn]
  | sext amount value signBit =>
      obtain ⟨iw, op, -, -, -⟩ := ok
      simp [Symbolic.IndexedWire.matchesRaw, indexedRhsOf,
        operandRef_render op]

/-! ## Assembly: the two wire-graph conjuncts -/

/-- Per-element well-formedness of the indexed view. -/
theorem toProgram_indexedWireWellFormedAt (d : Loom.Hw.Design)
    (wf : d.flattenStOf.WF (Compile.compile d).regs (Compile.compile d).mems)
    (i : Nat) (wire : Symbolic.IndexedWire)
    (found : d.toIndexedWires[i]? = some wire) :
    Symbolic.indexedWireWellFormedAt d.toProgram d.indexedsOf d.tableOf i
      wire = true := by
  have hcorr := toIndexedWires_getElem? d i
  rw [found] at hcorr
  obtain ⟨raw, hraw, hwire⟩ := Option.map_eq_some_iff.mp hcorr.symm
  subst hwire
  have harr : d.flattenStOf.wires[i]? = some raw := by
    rw [← Array.getElem?_toList]; exact hraw
  have hrhs := indexedRhsWellFormed_of_rhsOk d wf (wf.rhsOk i raw harr)
  have hlook := lookupIndexed?_toIndexedWires d found
  simp [Symbolic.indexedWireWellFormedAt, hlook, hrhs]

/-- **Well-formedness of the constructed wire graph**, conditional on one
kernel-reducible emission Boolean per design. -/
theorem toProgram_wireWellFormed_of_check (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true) :
    Symbolic.IndexedRopeWellFormed d.toProgram d.indexedsOf d.tableOf 0
      d.indexedsOf := by
  have wf : d.flattenStOf.WF (Compile.compile d).regs
      (Compile.compile d).mems :=
    flattenModule_wf (Compile.compile d) 128
      (moduleEmitOkB_sound (Compile.compile d) hemit)
  show Symbolic.IndexedRopeWellFormed d.toProgram d.indexedsOf d.tableOf 0
    (balancedRope ((listChunks (2 ^ 4)
      ((listChunks 128 d.toIndexedWires).map Rope.leaf)).map balancedRope))
  exact indexedRopeWellFormed_shaped d.toProgram d.indexedsOf d.tableOf 4 128
    (by omega) d.toIndexedWires
    (fun i wire h => toProgram_indexedWireWellFormedAt d wf i wire h)

/-- **The raw/indexed match of the constructed wire graph**, conditional on
the same emission Boolean (it supplies the operand-canonicality facts through
`FlattenSt.WF`). -/
theorem toProgram_wireMatches_of_check (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true) :
    Symbolic.IndexedRopeMatches 0 (d.toProgram).wires d.indexedsOf := by
  have wf : d.flattenStOf.WF (Compile.compile d).regs
      (Compile.compile d).mems :=
    flattenModule_wf (Compile.compile d) 128
      (moduleEmitOkB_sound (Compile.compile d) hemit)
  show Symbolic.IndexedRopeMatches 0
    (balancedRope ((listChunks (2 ^ 4)
      ((listChunks 128 d.flattenStOf.wires.toList).map Rope.leaf)).map
      balancedRope))
    (balancedRope ((listChunks (2 ^ 4)
      ((listChunks 128 d.toIndexedWires).map Rope.leaf)).map balancedRope))
  refine indexedRopeMatches_shaped 4 128 (by omega)
    d.flattenStOf.wires.toList d.toIndexedWires
    (toIndexedWires_length d).symm ?_
  intro i raw wire hr hw
  have hcorr := toIndexedWires_getElem? d i
  rw [hw, hr] at hcorr
  simp only [Option.map_some, Option.some.injEq] at hcorr
  subst hcorr
  exact matchesRaw_of_rhsOk i raw
    (wf.rhsOk i raw (by rw [← Array.getElem?_toList]; exact hr))

end Loom.Release.SSA
