-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.FlattenMatches
import Loom.Release.ToProgramWellFormed

/-!
# The two semantic conjuncts of `toProgram_denotes`

Final assembly of the register and memory behavior of the constructed
release witness: every register root of `d.registersOf` semantically
denotes the verified compilation's next-state fold, and every memory root
of `d.memoriesOf` denotes its compiled initialization image and write
ports (`Compile.compilePort`), face by face.

Both theorems are conditional on the same three kernel-reducible design
Booleans that drive the wire-graph conjuncts: `moduleEmitOkB` (emission
obligations, supplying `FlattenSt.WF` and operand canonicality),
`moduleMatchOkB` (the matcher's width discipline), and `moduleNamesOkB`
(declared-name token discipline, D14). The semantic content is
`flattenModule_matches` (the flatten-soundness invariant's semantic half)
composed with `indexedExprMatches_raw` through the proved wire-graph rope
match `toProgram_wireMatches_of_check`; the bookkeeping is metadata and
render-roundtrip transport along the flattening traversal.
-/

namespace Loom.Release.SSA

open Loom.Hw Loom.Emit.MicroVerilog

/-! ## Traversal bookkeeping: lengths, metadata, render roundtrips -/

private theorem flattenWrites_run_cons {aw dw : Nat} (p : WritePort aw dw)
    (rest : List (WritePort aw dw)) (s : FlattenSt) :
    (flattenWrites (p :: rest)).run s =
      (({ en := ((flatten p.en).run s).1,
          addr := ((flatten p.addr).run ((flatten p.en).run s).2).1,
          data := ((flatten p.data).run
            ((flatten p.addr).run ((flatten p.en).run s).2).2).1 } : Write) ::
        ((flattenWrites rest).run ((flatten p.data).run
          ((flatten p.addr).run ((flatten p.en).run s).2).2).2).1,
       ((flattenWrites rest).run ((flatten p.data).run
          ((flatten p.addr).run ((flatten p.en).run s).2).2).2).2) := rfl

theorem length_flattenWrites {aw dw : Nat} (ports : List (WritePort aw dw))
    (s : FlattenSt) :
    ((flattenWrites ports).run s).1.length = ports.length := by
  induction ports generalizing s with
  | nil => rfl
  | cons p rest ih => rw [flattenWrites_run_cons]; simp [ih]

/-- Every register name `flattenRegs` hands back is operand-canonical: its
translated reference renders back to the stored string. The `OperandOk`
fact from `flatten_spec` at each head suffices — `operandRef_render` only
consumes the name-shape disjunction, which holds at any bound. -/
theorem flattenRegs_render (regs : List RegDef) (mems : List MemDef)
    (rs : List RegDef) (st : FlattenSt) (wf : st.WF regs mems)
    (hok : ∀ r ∈ rs, ExprEmitOk regs mems r.next) :
    ∀ (i : Nat) (out : Reg), ((flattenRegs rs).run st).1[i]? = some out →
      (operandRef out.next).render = out.next := by
  induction rs generalizing st with
  | nil =>
      intro i out h
      rw [show ((flattenRegs ([] : List RegDef)).run st).1 = [] from rfl] at h
      simp at h
  | cons r rest ih =>
      intro i out hout
      obtain ⟨wf1, -, op1⟩ := flatten_spec regs mems r.next st wf
        (hok r List.mem_cons_self)
      rw [flattenRegs_run_cons] at hout
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hout
          subst hout
          exact operandRef_render op1
      | succ n =>
          simp only [List.getElem?_cons_succ] at hout
          exact ih ((flatten r.next).run st).2 wf1
            (fun r' hr => hok r' (List.mem_cons_of_mem _ hr)) n out hout

/-- All three faces of every write `flattenWrites` hands back are
operand-canonical. -/
theorem flattenWrites_render (regs : List RegDef) (mems : List MemDef)
    {aw dw : Nat} (ports : List (WritePort aw dw)) (st : FlattenSt)
    (wf : st.WF regs mems)
    (hok : ∀ p ∈ ports, ExprEmitOk regs mems p.en ∧
      ExprEmitOk regs mems p.addr ∧ ExprEmitOk regs mems p.data) :
    ∀ (j : Nat) (ow : Write), ((flattenWrites ports).run st).1[j]? = some ow →
      (operandRef ow.en).render = ow.en ∧
      (operandRef ow.addr).render = ow.addr ∧
      (operandRef ow.data).render = ow.data := by
  induction ports generalizing st with
  | nil =>
      intro j ow h
      rw [show ((flattenWrites ([] : List (WritePort aw dw))).run st).1 = []
        from rfl] at h
      simp at h
  | cons p rest ih =>
      intro j ow how
      obtain ⟨okEn, okAddr, okData⟩ := hok p List.mem_cons_self
      obtain ⟨wf1, -, op1⟩ := flatten_spec regs mems p.en st wf okEn
      obtain ⟨wf2, -, op2⟩ := flatten_spec regs mems p.addr
        ((flatten p.en).run st).2 wf1 okAddr
      obtain ⟨wf3, -, op3⟩ := flatten_spec regs mems p.data
        ((flatten p.addr).run ((flatten p.en).run st).2).2 wf2 okData
      rw [flattenWrites_run_cons] at how
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at how
          subst how
          exact ⟨operandRef_render op1, operandRef_render op2,
            operandRef_render op3⟩
      | succ n =>
          simp only [List.getElem?_cons_succ] at how
          exact ih ((flatten p.data).run
            ((flatten p.addr).run ((flatten p.en).run st).2).2).2 wf3
            (fun p' hp => hok p' (List.mem_cons_of_mem _ hp)) n ow how

/-- All three faces of every write of every memory `flattenMems` hands back
are operand-canonical. -/
theorem flattenMems_render (regs : List RegDef) (mems : List MemDef)
    (blockSize : Nat) (ms : List MemDef) (st : FlattenSt) (wf : st.WF regs mems)
    (hok : ∀ mm ∈ ms, ∀ p ∈ mm.wrPorts, ExprEmitOk regs mems p.en ∧
      ExprEmitOk regs mems p.addr ∧ ExprEmitOk regs mems p.data) :
    ∀ (i : Nat) (out : Mem), ((flattenMems blockSize ms).run st).1[i]? = some out →
      ∀ (j : Nat) (ow : Write), out.writes[j]? = some ow →
        (operandRef ow.en).render = ow.en ∧
        (operandRef ow.addr).render = ow.addr ∧
        (operandRef ow.data).render = ow.data := by
  induction ms generalizing st with
  | nil =>
      intro i out h
      rw [show ((flattenMems blockSize ([] : List MemDef)).run st).1 = []
        from rfl] at h
      simp at h
  | cons mm rest ih =>
      intro i out hout
      obtain ⟨wfW, -⟩ := flattenWrites_spec regs mems mm.wrPorts st wf
        (hok mm List.mem_cons_self)
      rw [flattenMems_run_cons] at hout
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hout
          subst hout
          exact flattenWrites_render regs mems mm.wrPorts st wf
            (hok mm List.mem_cons_self)
      | succ n =>
          simp only [List.getElem?_cons_succ] at hout
          exact ih ((flattenWrites mm.wrPorts).run st).2 wfW
            (fun mm' hm => hok mm' (List.mem_cons_of_mem _ hm)) n out hout

/-- Pointwise shape of `flattenMems` output: metadata, the chunked
initialization image, and the write count are copied from the source
declaration. -/
theorem flattenMems_shape (blockSize : Nat) (ms : List MemDef)
    (st : FlattenSt) :
    ∀ (i : Nat) (out : Mem),
      ((flattenMems blockSize ms).run st).1[i]? = some out →
      ∃ src, ms[i]? = some src ∧ out.name = src.name ∧
        out.addrWidth = src.addrWidth ∧ out.dataWidth = src.dataWidth ∧
        out.init = balancedRope ((listChunks blockSize
          ((List.range (2 ^ src.addrWidth)).map fun a =>
            (src.init a).toNat)).map .leaf) ∧
        out.writes.length = src.wrPorts.length := by
  induction ms generalizing st with
  | nil =>
      intro i out h
      rw [show ((flattenMems blockSize ([] : List MemDef)).run st).1 = []
        from rfl] at h
      simp at h
  | cons mm rest ih =>
      intro i out hout
      rw [flattenMems_run_cons] at hout
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hout
          subst hout
          exact ⟨mm, rfl, rfl, rfl, rfl, rfl,
            length_flattenWrites mm.wrPorts st⟩
      | succ n =>
          simp only [List.getElem?_cons_succ] at hout
          exact ih ((flattenWrites mm.wrPorts).run st).2 n out hout

/-! ## Flat-list introduction rules for the memory predicates -/

open Loom.Release.Symbolic in
/-- Flat per-entry index and behavior facts cover a memory-root list at any
cumulative start. -/
theorem memoryBehaviorsFrom_of_forall (design : Loom.Hw.Design)
    (program : Program) (table : WireTable) :
    ∀ (block : List MemoryRoot) (start : Nat),
      (∀ (off : Nat) (entry : MemoryRoot), block[off]? = some entry →
        entry.index = start + off ∧
          MemoryBehaviorAt design program table (start + off) entry.init
            entry.ports) →
      MemoryBehaviorsFrom design program table start block
  | [], start, _ => .nil start
  | entry :: rest, start, h => by
      obtain ⟨hidx0, hbeh0⟩ := h 0 entry rfl
      rw [Nat.add_zero] at hidx0 hbeh0
      refine .cons hidx0 (by rw [hidx0]; exact hbeh0) ?_
      refine memoryBehaviorsFrom_of_forall design program table rest
        (start + 1) ?_
      intro off e he
      have := h (off + 1) e (by simpa using he)
      rwa [show start + (off + 1) = start + 1 + off by omega] at this

open Loom.Release.Symbolic in
/-- Flat per-entry index and behavior facts cover a port-root list at any
cumulative start. -/
theorem memoryPortBehaviorsFrom_of_forall (design : Loom.Hw.Design)
    (program : Program) (table : WireTable) (memoryIndex : Nat) :
    ∀ (block : List MemoryPortRoot) (start : Nat),
      (∀ (off : Nat) (entry : MemoryPortRoot), block[off]? = some entry →
        entry.index = start + off ∧
          MemoryPortBehaviorAt design program table memoryIndex (start + off)
            entry.refs) →
      MemoryPortBehaviorsFrom design program table memoryIndex start block
  | [], start, _ => .nil start
  | entry :: rest, start, h => by
      obtain ⟨hidx0, hbeh0⟩ := h 0 entry rfl
      rw [Nat.add_zero] at hidx0 hbeh0
      refine .cons hidx0 (by rw [hidx0]; exact hbeh0) ?_
      refine memoryPortBehaviorsFrom_of_forall design program table memoryIndex
        rest (start + 1) ?_
      intro off e he
      have := h (off + 1) e (by simpa using he)
      rwa [show start + (off + 1) = start + 1 + off by omega] at this

open Loom.Release.Symbolic in
/-- Pointwise image facts lift to the chunked-and-balanced initialization
rope: the `ropesSatisfyFrom` engine instantiated at
`MemoryInitBehaviorAtRope`. -/
theorem memoryInitBehaviorAtRope_balanced (design : Loom.Hw.Design)
    (memoryIndex : Nat) {blockSize : Nat} (positive : 0 < blockSize)
    (source : Loom.Hw.MemDecl)
    (found : design.mems[memoryIndex]? = some source) (values : List Nat)
    (h : ∀ (off : Nat) (b : Nat), values[off]? = some b →
      b = (source.init off).toNat) :
    MemoryInitBehaviorAtRope design memoryIndex 0
      (balancedRope ((listChunks blockSize values).map Rope.leaf)) := by
  have hleaf : ∀ (start : Nat) (block : List Nat),
      (∀ (off : Nat) (b : Nat), block[off]? = some b →
        b = (source.init (start + off)).toNat) →
      MemoryInitBehaviorAtRope design memoryIndex start (.leaf block) := by
    intro start block hb
    refine .leaf ?_
    simp only [found]
    intro index hlt
    have hidx : block[index]? = some block[index] :=
      List.getElem?_eq_getElem hlt
    rw [List.getD_eq_getElem?_getD, hidx, Option.getD_some]
    exact hb index block[index] hidx
  cases values with
  | nil =>
      rw [listChunks_nil positive, List.map_nil]
      show MemoryInitBehaviorAtRope design memoryIndex 0 (.leaf [])
      exact hleaf 0 [] (by intro off b hb; simp at hb)
  | cons x t =>
      refine ropesSatisfyFrom_balancedGo
        (P := MemoryInitBehaviorAtRope design memoryIndex)
        (fun _ _ _ hl hr => .node hl hr) _ 0 _ (Nat.le_refl _) ?_
        (ropesSatisfyFrom_chunks
          (Q := fun idx b => b = (source.init idx).toNat)
          (fun s block hb => hleaf s block hb)
          positive (x :: t).length (x :: t) (Nat.le_refl _) 0
          (fun off b hb => by simpa using h off b hb))
      rw [listChunks_cons positive, List.map_cons]
      exact List.cons_ne_nil _ _

/-! ## The memory witness roots -/

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

/-! ## Shared plumbing -/

/-- The faithfulness hypothesis of `flattenModule_matches` at the default
witness shape: the final flat array agrees with the indexed rope the
matcher navigates. -/
private theorem toProgram_faithful (d : Loom.Hw.Design) :
    ∀ (m : Nat) (wire : Wire),
      (((flattenModule (Compile.compile d) 128).run {}).2).wires[m]? =
        some wire →
      Symbolic.lookupIndexed? d.indexedsOf d.tableOf m =
        some ⟨m, wire.width, indexedRhsOf wire.rhs⟩ := by
  intro m wire h
  have hlist : d.flattenStOf.wires.toList[m]? = some wire := by
    rw [Array.getElem?_toList]; exact h
  have hidx : d.toIndexedWires[m]? =
      some ⟨m, wire.width, indexedRhsOf wire.rhs⟩ := by
    rw [toIndexedWires_getElem?, hlist]; rfl
  exact lookupIndexed?_toIndexedWires d hidx

/-! ## The register conjunct -/

/-- **The hard lemma, proved.** Every register root of the constructed
witness semantically denotes the verified compilation's next-state fold.
This single generic statement is what the per-design pipeline's 825
generated register theorems (the `hybrid registers` phase) instantiate at
one design; conditional only on the three kernel-reducible design
Booleans. -/
theorem toProgram_registerBehavior (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true)
    (hmw : moduleMatchOkB (Compile.compile d) = true)
    (hnames : moduleNamesOkB (Compile.compile d) = true) :
    Symbolic.RegisterBehaviorRopeFrom d d.toProgram d.tableOf 0
      d.registersOf := by
  have hok := moduleEmitOkB_sound (Compile.compile d) hemit
  obtain ⟨matRegs, -, -⟩ := flattenModule_matches (Compile.compile d) 128
    d.indexedsOf d.tableOf (toProgram_faithful d) hok hmw hnames
  have hropes := toProgram_wireMatches_of_check d hemit
  have hshape : d.registersOf = balancedRope ((listChunks 128
      ((d.toProgram).regs.zipIdx.map fun (reg, index) =>
        ({ index, root := operandRef reg.next } :
          Symbolic.RegisterRoot))).map .leaf) := rfl
  rw [hshape]
  refine registerBehaviorRopeFrom_shaped d d.toProgram d.tableOf 128
    (by omega) _ ?_ ?_
  · intro i entry h
    simp only [List.getElem?_map, List.getElem?_zipIdx] at h
    cases hreg : (d.toProgram).regs[i]? with
    | none => rw [hreg] at h; simp at h
    | some reg =>
        rw [hreg] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [← h]
        simp
  · intro i entry h
    simp only [List.getElem?_map, List.getElem?_zipIdx] at h
    cases hreg : (d.toProgram).regs[i]? with
    | none => rw [hreg] at h; simp at h
    | some reg =>
        rw [hreg] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [← h]
        -- Source register at the same index.
        have hib : i < (d.toProgram).regs.length := lt_of_getElem?_eq_some hreg
        have hlen : i < d.regs.length := by
          rw [← toProgram_regs_length d 128 16]; exact hib
        obtain ⟨source, hsrc⟩ : ∃ s, d.regs[i]? = some s :=
          ⟨_, List.getElem?_eq_getElem hlen⟩
        -- The compiled register at the same index.
        have hcsrc : (Compile.compile d).regs[i]? = some
            { name := source.name, width := source.width, init := source.init,
              next := d.rules.foldl
                (fun cur rl => Compile.nextReg source.name source.width
                  rl.body cur)
                (.reg source.width source.name) } := by
          simp only [Compile.compile, List.getElem?_map, hsrc, Option.map_some]
        -- Metadata transport.
        have hreg' : ((flattenRegs (Compile.compile d).regs).run {}).1[i]? =
            some reg := by
          rw [← toProgram_regs d 128 16]; exact hreg
        have hmeta := congrArg (fun l => l[i]?)
          (flattenRegs_meta (Compile.compile d).regs {})
        simp only [List.getElem?_map] at hmeta
        rw [hreg', hcsrc] at hmeta
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmeta
        -- Render roundtrip for the next-value name.
        have hrender := flattenRegs_render (Compile.compile d).regs
          (Compile.compile d).mems (Compile.compile d).regs {}
          (FlattenSt.WF.empty _ _) hok.1 i reg hreg'
        -- The semantic match against the compiled next-state fold.
        have hmatch := matRegs i reg _ hreg' hcsrc
        have hraw := Symbolic.indexedExprMatches_raw d.toProgram hropes
          d.tableOf _ _ hmatch
        simp only [Symbolic.RegisterBehaviorAt, hsrc, hreg]
        exact ⟨hmeta.1.symm, hmeta.2.1.symm, hmeta.2.2.symm, hrender.symm,
          hraw⟩

/-! ## The memory conjunct -/

/-- The memory conjunct: initialization images and write-port references of
the constructed witness denote the source image and `Compile.compilePort`,
port by port and face by face; conditional on the same three
kernel-reducible design Booleans. -/
theorem toProgram_memoryBehavior (d : Loom.Hw.Design)
    (hemit : moduleEmitOkB (Compile.compile d) = true)
    (hmw : moduleMatchOkB (Compile.compile d) = true)
    (hnames : moduleNamesOkB (Compile.compile d) = true) :
    Symbolic.MemoryBehaviorsFrom d d.toProgram d.tableOf 0 d.memoriesOf := by
  have hok := moduleEmitOkB_sound (Compile.compile d) hemit
  obtain ⟨-, matMems, -⟩ := flattenModule_matches (Compile.compile d) 128
    d.indexedsOf d.tableOf (toProgram_faithful d) hok hmw hnames
  have hropes := toProgram_wireMatches_of_check d hemit
  obtain ⟨wfR, -⟩ := flattenRegs_spec (Compile.compile d).regs
    (Compile.compile d).mems (Compile.compile d).regs {}
    (FlattenSt.WF.empty _ _) hok.1
  refine memoryBehaviorsFrom_of_forall d d.toProgram d.tableOf d.memoriesOf 0
    ?_
  intro i entry hentry
  unfold Loom.Hw.Design.memoriesOf at hentry
  simp only [List.getElem?_map, List.getElem?_zipIdx] at hentry
  cases hconc : (d.toProgram).mems[i]? with
  | none => rw [hconc] at hentry; simp at hentry
  | some concrete =>
      rw [hconc] at hentry
      simp only [Option.map_some, Option.some.injEq] at hentry
      rw [← hentry]
      simp only [Nat.zero_add]
      refine ⟨trivial, ?_⟩
      -- Source memory at the same index.
      have hib : i < (d.toProgram).mems.length := lt_of_getElem?_eq_some hconc
      have hlen : i < d.mems.length := by
        rw [← toProgram_mems_length d 128 16]; exact hib
      obtain ⟨source, hsrcM⟩ : ∃ s, d.mems[i]? = some s :=
        ⟨_, List.getElem?_eq_getElem hlen⟩
      -- The compiled memory at the same index.
      have hcsrc : (Compile.compile d).mems[i]? = some
          { name := source.name, addrWidth := source.addrWidth,
            dataWidth := source.dataWidth, init := source.init,
            wrPorts := (List.range (Compile.numPorts d source.name)).map
              fun p => Compile.compilePort d source.name source.addrWidth
                source.dataWidth p } := by
        simp only [Compile.compile, List.getElem?_map, hsrcM, Option.map_some]
      -- Shape facts through the flattening traversal.
      have hconc' : ((flattenMems 128 (Compile.compile d).mems).run
          ((flattenRegs (Compile.compile d).regs).run {}).2).1[i]? =
            some concrete := by
        rw [← toProgram_mems d 128 16]; exact hconc
      obtain ⟨src, hsrcC, hname, haw, hdw, hinit, hwlen⟩ :=
        flattenMems_shape 128 (Compile.compile d).mems
          ((flattenRegs (Compile.compile d).regs).run {}).2 i concrete hconc'
      rw [hcsrc] at hsrcC
      obtain rfl := Option.some.inj hsrcC
      refine Symbolic.memoryBehaviorAt_of_checks d d.toProgram d.tableOf i
        source concrete concrete.init _ hsrcM hconc hname.symm haw.symm
        hdw.symm rfl (by simp) ?_ ?_
      · -- The initialization image.
        rw [hinit]
        refine memoryInitBehaviorAtRope_balanced d i (by omega) source hsrcM _
          ?_
        intro off b hb
        rw [List.getElem?_map] at hb
        cases hr : (List.range (2 ^ source.addrWidth))[off]? with
        | none => rw [hr] at hb; simp at hb
        | some a =>
            rw [hr] at hb
            have hoff : off < 2 ^ source.addrWidth := by
              have := lt_of_getElem?_eq_some hr
              simpa using this
            rw [List.getElem?_range hoff] at hr
            obtain rfl := Option.some.inj hr
            simp only [Option.map_some, Option.some.injEq] at hb
            exact hb.symm
      · -- The write ports.
        refine memoryPortBehaviorsFrom_of_forall d d.toProgram d.tableOf i _
          0 ?_
        intro p pr hpr
        simp only [List.getElem?_map, List.getElem?_zipIdx] at hpr
        cases hw : concrete.writes[p]? with
        | none => rw [hw] at hpr; simp at hpr
        | some write =>
            rw [hw] at hpr
            simp only [Option.map_some, Option.some.injEq] at hpr
            rw [← hpr]
            simp only [Nat.zero_add]
            refine ⟨trivial, ?_⟩
            -- The compiled port at the same index.
            have hplt : p < Compile.numPorts d source.name := by
              have h1 : p < concrete.writes.length := lt_of_getElem?_eq_some hw
              rw [hwlen] at h1
              simpa using h1
            have hsp : ((List.range (Compile.numPorts d source.name)).map
                fun q => Compile.compilePort d source.name source.addrWidth
                  source.dataWidth q)[p]? =
                some (Compile.compilePort d source.name source.addrWidth
                  source.dataWidth p) := by
              rw [List.getElem?_map, List.getElem?_range hplt, Option.map_some]
            -- The semantic match on all three faces.
            have hmatch := matMems i concrete _ hconc' hcsrc p write
              (Compile.compilePort d source.name source.addrWidth
                source.dataWidth p) hw hsp
            -- Render roundtrips for the three faces.
            have hrender := flattenMems_render (Compile.compile d).regs
              (Compile.compile d).mems 128 (Compile.compile d).mems
              ((flattenRegs (Compile.compile d).regs).run {}).2 wfR hok.2.1
              i concrete hconc' p write hw
            exact Symbolic.memoryPortBehaviorAt_of_checks d d.toProgram
              d.tableOf i p source concrete write _ hsrcM hconc hw hname.symm
              haw.symm hdw.symm hrender.1.symm hrender.2.1.symm
              hrender.2.2.symm
              ⟨Symbolic.indexedExprMatches_raw d.toProgram hropes d.tableOf
                  _ _ hmatch.1,
                Symbolic.indexedExprMatches_raw d.toProgram hropes d.tableOf
                  _ _ hmatch.2.1,
                Symbolic.indexedExprMatches_raw d.toProgram hropes d.tableOf
                  _ _ hmatch.2.2⟩

/-! ## Axiom audit -/

#print axioms toProgram_registerBehavior
#print axioms toProgram_memoryBehavior

end Loom.Release.SSA
