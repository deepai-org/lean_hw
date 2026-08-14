-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgram
import Loom.Release.SymbolicSound

/-!
# Structural lemmas about `Design.toProgram`

Sorry-free bookkeeping facts about the constructed release witness: rope
shaping (`listChunks`/`balancedRope`) preserves contents, the flattening
recursions preserve declaration counts and metadata, and the observability
outputs of `d.toProgram` are exactly the compiler's `o_<reg>` views. These
discharge the easy conjuncts of `Symbolic.ModuleBehavior` for
`toProgram_denotes` (see `Loom/Release/ToProgramDenotes.lean`).
-/

namespace Loom.Release

/-! ## Rope contents -/

theorem Rope.length_flattenLists {α : Type} (rope : Rope (List α)) :
    rope.flattenLists.length = rope.listLength := by
  induction rope with
  | leaf values => rfl
  | node left right leftIH rightIH =>
      simp [Rope.flattenLists, Rope.listLength, leftIH, rightIH]

namespace SSA

/-! ## Chunking and balancing preserve contents -/

theorem listChunksGo_flatten {α : Type} {size : Nat} (positive : 0 < size) :
    ∀ (fuel : Nat) (items : List α), items.length ≤ fuel →
      (listChunksGo size fuel items).flatten = items
  | 0, [], _ => rfl
  | 0, _ :: _, bound => by simp at bound
  | _ + 1, [], _ => rfl
  | fuel + 1, item :: rest, bound => by
      rw [listChunksGo, List.flatten_cons,
        listChunksGo_flatten positive fuel ((item :: rest).drop size)
          (by simp only [List.length_drop, List.length_cons] at *; omega),
        List.take_append_drop]

/-- Chunking splits and only splits: the chunks flatten back to the list. -/
theorem listChunks_flatten {α : Type} (size : Nat) (items : List α) :
    (listChunks size items).flatten = items := by
  unfold listChunks
  split
  · simp
  · exact listChunksGo_flatten (by omega) items.length items (Nat.le_refl _)

theorem pairStep_flatten {α : Type} (items : List (Rope (List α))) :
    ((pairStep items).map Rope.flattenLists).flatten =
      (items.map Rope.flattenLists).flatten := by
  fun_induction pairStep items with
  | case1 one two rest ih =>
      simp [Rope.flattenLists, ih]
  | case2 => rfl

theorem pairStep_length_le {α : Type} (items : List (Rope α)) :
    (pairStep items).length ≤ items.length := by
  fun_induction pairStep items with
  | case1 one two rest ih => simp; omega
  | case2 => exact Nat.le_refl _

theorem balancedGo_flatten {α : Type} :
    ∀ (fuel : Nat) (items : List (Rope (List α))), items.length ≤ fuel →
      (balancedGo fuel items).flattenLists =
        (items.map Rope.flattenLists).flatten
  | fuel, [], _ => by simp only [balancedGo]; rfl
  | fuel, [single], _ => by simp [balancedGo]
  | 0, one :: two :: rest, bound => by simp at bound
  | fuel + 1, one :: two :: rest, bound => by
      have shorter : (pairStep (one :: two :: rest)).length ≤ fuel := by
        have := pairStep_length_le rest
        simp only [pairStep, List.length_cons] at *
        omega
      rw [balancedGo, balancedGo_flatten fuel _ shorter, pairStep_flatten]

/-- Balancing preserves leaf contents in order. -/
theorem balancedRope_flatten {α : Type} (items : List (Rope (List α))) :
    (balancedRope items).flattenLists =
      (items.map Rope.flattenLists).flatten :=
  balancedGo_flatten items.length items (Nat.le_refl _)

/-- The chunk-then-balance shape used by every witness rope flattens back to
the original list. -/
theorem balancedRope_chunks_flatten {α : Type} (size : Nat) (items : List α) :
    (balancedRope ((listChunks size items).map .leaf)).flattenLists =
      items := by
  rw [balancedRope_flatten, List.map_map]
  have : Rope.flattenLists ∘ (Rope.leaf : List α → Rope (List α)) = id := rfl
  rw [this, List.map_id, listChunks_flatten]

theorem balancedRope_chunks_listLength {α : Type} (size : Nat)
    (items : List α) :
    (balancedRope ((listChunks size items).map .leaf)).listLength =
      items.length := by
  rw [← Rope.length_flattenLists, balancedRope_chunks_flatten]

/-! ## The flattening recursions -/

open Loom.Hw Loom.Emit.MicroVerilog

@[simp] theorem flatten_reg (w : Nat) (name : String) :
    flatten (.reg w name) = pure name := rfl

theorem flattenRegs_run_cons (r : RegDef) (rest : List RegDef)
    (s : FlattenSt) :
    (flattenRegs (r :: rest)).run s =
      (({ name := r.name, width := r.width, init := r.init.toNat,
          next := ((flatten r.next).run s).1 } : Reg) ::
        ((flattenRegs rest).run ((flatten r.next).run s).2).1,
       ((flattenRegs rest).run ((flatten r.next).run s).2).2) := rfl

theorem length_flattenRegs (regs : List RegDef) (s : FlattenSt) :
    ((flattenRegs regs).run s).1.length = regs.length := by
  induction regs generalizing s with
  | nil => rfl
  | cons r rest ih => rw [flattenRegs_run_cons]; simp [ih]

/-- The flattened register list preserves each declaration's metadata. -/
theorem flattenRegs_meta (regs : List RegDef) (s : FlattenSt) :
    ((flattenRegs regs).run s).1.map (fun c => (c.name, c.width, c.init)) =
      regs.map (fun r => (r.name, r.width, r.init.toNat)) := by
  induction regs generalizing s with
  | nil => rfl
  | cons r rest ih => rw [flattenRegs_run_cons]; simp [ih]

theorem flattenMems_run_cons (mm : MemDef) (rest : List MemDef)
    (blockSize : Nat) (s : FlattenSt) :
    (flattenMems blockSize (mm :: rest)).run s =
      (({ name := mm.name, addrWidth := mm.addrWidth,
          dataWidth := mm.dataWidth,
          init := balancedRope ((listChunks blockSize
            ((List.range (2 ^ mm.addrWidth)).map fun a =>
              (mm.init a).toNat)).map .leaf),
          writes := ((flattenWrites mm.wrPorts).run s).1 } : Mem) ::
        ((flattenMems blockSize rest).run
          ((flattenWrites mm.wrPorts).run s).2).1,
       ((flattenMems blockSize rest).run
          ((flattenWrites mm.wrPorts).run s).2).2) := rfl

theorem length_flattenMems (mems : List MemDef) (blockSize : Nat)
    (s : FlattenSt) :
    ((flattenMems blockSize mems).run s).1.length = mems.length := by
  induction mems generalizing s with
  | nil => rfl
  | cons mm rest ih => rw [flattenMems_run_cons]; simp [ih]

theorem flattenOuts_run_cons (o : OutDef) (rest : List OutDef)
    (s : FlattenSt) :
    (flattenOuts (o :: rest)).run s =
      (({ name := o.name, width := o.width,
          value := ((flatten o.val).run s).1 } : Out) ::
        ((flattenOuts rest).run ((flatten o.val).run s).2).1,
       ((flattenOuts rest).run ((flatten o.val).run s).2).2) := rfl

/-- On the compiler's observability outputs — whose values are bare register
reads — flattening allocates nothing and copies the register names. -/
theorem flattenOuts_regOuts (regs : List Loom.Hw.RegDecl) (s : FlattenSt) :
    (flattenOuts (regs.map fun r =>
        ({ name := s!"o_{r.name}", width := r.width,
           val := .reg r.width r.name } : OutDef))).run s =
      (regs.map fun r =>
        ({ name := s!"o_{r.name}", width := r.width,
           value := r.name } : Out), s) := by
  induction regs generalizing s with
  | nil => rfl
  | cons r rest ih =>
      rw [List.map_cons, flattenOuts_run_cons]
      simp [ih]
      rfl

theorem flattenModule_run (m : Module) (blockSize : Nat) (s : FlattenSt) :
    (flattenModule m blockSize).run s =
      let a := (flattenRegs m.regs).run s
      let b := (flattenMems blockSize m.mems).run a.2
      let c := (flattenOuts m.outs).run b.2
      ((a.1, b.1, c.1), c.2) := rfl

/-! ## `toProgram` projections -/

theorem toProgram_name (d : Loom.Hw.Design) (blockSize chunkLeaves : Nat) :
    (d.toProgram blockSize chunkLeaves).name = d.name := rfl

theorem toProgram_regs (d : Loom.Hw.Design) (blockSize chunkLeaves : Nat) :
    (d.toProgram blockSize chunkLeaves).regs =
      ((flattenRegs (Compile.compile d).regs).run {}).1 := rfl

theorem toProgram_mems (d : Loom.Hw.Design) (blockSize chunkLeaves : Nat) :
    (d.toProgram blockSize chunkLeaves).mems =
      ((flattenMems blockSize (Compile.compile d).mems).run
        ((flattenRegs (Compile.compile d).regs).run {}).2).1 := rfl

theorem toProgram_regs_length (d : Loom.Hw.Design)
    (blockSize chunkLeaves : Nat) :
    (d.toProgram blockSize chunkLeaves).regs.length = d.regs.length := by
  rw [toProgram_regs, length_flattenRegs]
  simp [Compile.compile]

theorem toProgram_mems_length (d : Loom.Hw.Design)
    (blockSize chunkLeaves : Nat) :
    (d.toProgram blockSize chunkLeaves).mems.length = d.mems.length := by
  rw [toProgram_mems, length_flattenMems]
  simp [Compile.compile]

/-- The witness's outputs are exactly the compiler's observability views:
one `o_<reg>` per **exported** source register (D39 `Design.outputs`;
`d.exportedRegs` is `d.regs` for every design that declares no selection),
driven by the register name itself. -/
theorem toProgram_outs (d : Loom.Hw.Design) (blockSize chunkLeaves : Nat)
    (hcomb : d.combOutputs = []) :
    (d.toProgram blockSize chunkLeaves).outs =
      d.exportedRegs.map fun r =>
        ({ name := s!"o_{r.name}", width := r.width,
           value := r.name } : Out) := by
  show ((flattenOuts (Compile.compile d).outs).run _).1 = _
  have : (Compile.compile d).outs = d.exportedRegs.map fun r =>
      ({ name := s!"o_{r.name}", width := r.width,
         val := .reg r.width r.name } : OutDef) := by
    simp [Compile.compile, hcomb]
  rw [this, flattenOuts_regOuts]

theorem toProgram_outs_length (d : Loom.Hw.Design)
    (blockSize chunkLeaves : Nat) (hcomb : d.combOutputs = []) :
    (d.toProgram blockSize chunkLeaves).outs.length = d.exportedRegs.length := by
  rw [toProgram_outs d blockSize chunkLeaves hcomb, List.length_map]

/-! ## Count conjuncts of `ModuleBehavior` -/

theorem registersOf_listLength (d : Loom.Hw.Design) (blockSize : Nat) :
    (d.registersOf blockSize).listLength = d.regs.length := by
  unfold Loom.Hw.Design.registersOf
  rw [balancedRope_chunks_listLength]
  simp [toProgram_regs_length]

theorem outputsOf_listLength (d : Loom.Hw.Design) (blockSize : Nat) :
    (d.outputsOf blockSize).listLength = (d.toProgram).outs.length := by
  unfold Loom.Hw.Design.outputsOf
  rw [balancedRope_chunks_listLength, List.length_range]

/-! ## The output-behavior conjunct -/

open Loom.Release.Symbolic in
/-- A list that equals the consecutive indices from its own start is covered
by pointwise `OutputBehaviorAt` facts. -/
theorem outputBehaviorsFrom_of_range' (design : Loom.Hw.Design)
    (program : Program) (values : List Nat) (start : Nat)
    (consecutive : values = List.range' start values.length)
    (at_ : ∀ i, i ∈ values → OutputBehaviorAt design program i) :
    OutputBehaviorsFrom design program start values := by
  induction values generalizing start with
  | nil => exact .nil _
  | cons v rest ih =>
      have split : v :: rest = start :: List.range' (start + 1) rest.length := by
        simpa [List.range'_succ] using consecutive
      injection split with headEq tailEq
      subst headEq
      exact .cons rfl (at_ v List.mem_cons_self)
        (ih (v + 1) tailEq
          fun i mem => at_ i (List.mem_cons_of_mem _ mem))

open Loom.Release.Symbolic in
/-- Transfer from the flat statement to any rope whose leaves hold the
consecutive indices `start, start+1, …` in order. -/
theorem outputBehaviorRopeFrom_of_consecutive (design : Loom.Hw.Design)
    (program : Program) (rope : Rope (List Nat)) (start : Nat)
    (consecutive : rope.flattenLists = List.range' start rope.listLength)
    (at_ : ∀ i, i ∈ rope.flattenLists → OutputBehaviorAt design program i) :
    OutputBehaviorRopeFrom design program start rope := by
  induction rope generalizing start with
  | leaf values =>
      have flat : values = List.range' start values.length := consecutive
      exact .leaf (outputBehaviorsFrom_of_range' design program values start
        flat (fun i mem => at_ i mem))
  | node left right leftIH rightIH =>
      simp only [Rope.flattenLists, Rope.listLength] at consecutive at_
      rw [← List.range'_append_1] at consecutive
      have leftLen : left.flattenLists.length =
          (List.range' start left.listLength).length := by
        simp [Rope.length_flattenLists]
      obtain ⟨leftEq, rightEq⟩ := List.append_inj consecutive leftLen
      exact .node
        (leftIH start leftEq fun i mem => at_ i (List.mem_append_left _ mem))
        (rightIH (start + left.listLength) rightEq
          fun i mem => at_ i (List.mem_append_right _ mem))

open Loom.Release.Symbolic in
theorem toProgram_outputBehaviorAt (d : Loom.Hw.Design) (i : Nat)
    (hcomb : d.combOutputs = [])
    (bound : i < d.exportedRegs.length) :
    OutputBehaviorAt d (d.toProgram) i := by
  unfold OutputBehaviorAt
  rw [toProgram_outs d 128 16 hcomb]
  have found : d.exportedRegs[i]? = some d.exportedRegs[i] :=
    List.getElem?_eq_getElem bound
  simp [found]

open Loom.Release.Symbolic in
/-- The output conjunct of `ModuleBehavior` for the constructed witness. -/
theorem toProgram_outputBehavior (d : Loom.Hw.Design)
    (hcomb : d.combOutputs = []) :
    OutputBehaviorRopeFrom d d.toProgram 0 d.outputsOf := by
  apply outputBehaviorRopeFrom_of_consecutive
  · show (d.outputsOf).flattenLists = _
    rw [outputsOf_listLength]
    unfold Loom.Hw.Design.outputsOf
    rw [balancedRope_chunks_flatten, List.range_eq_range']
  · intro i mem
    apply toProgram_outputBehaviorAt d i hcomb
    have : i ∈ List.range (d.toProgram).outs.length := by
      unfold Loom.Hw.Design.outputsOf at mem
      rwa [balancedRope_chunks_flatten] at mem
    rw [← toProgram_outs_length d 128 16 hcomb]
    simpa using this

end SSA

end Loom.Release
