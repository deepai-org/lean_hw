-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Std.Data.HashMap
import Loom.Hw.Compile
import Loom.Release.SymbolicCertificate

/-!
# The design's own release witness (`Design.toProgram`)

Today the concrete `SSA.Program` shipped with a release is produced *outside*
Lean: `scripts/gen_release_witness.py` regex-parses the printed Verilog back
into Lean literals, and its semantics are then re-established per node by the
certificate pipeline. This module closes that loop from the other side: it
constructs the same program directly from `Compile.compile d`, using the same
flattening discipline as the printer (`Print.pExprM`/`freshM`), so that
`program = d.toProgram` becomes a checkable data equality and the printed
artifact is, by definition, the verified compiler's output.

Faithfulness to the printer is the load-bearing property. `Print.freshM`
allocates `n0, n1, ...` in first-print order and hash-conses on
`(width, rendered RHS)`. Its pointer-identity memo is a pure optimization:
when a shared node is revisited, re-rendering it would rebuild the identical
key (operands resolve to the same canonical names bottom-up) and hit the CSE
table, returning the same name. The reference `flatten` below therefore
reproduces the printer's output with the CSE table alone. Like
`compile`/`compileImpl` and `print`/`printImpl`, a pointer-memoized
`@[implemented_by]` twin makes it executable on designs whose expression
DAGs would unfold exponentially as trees.

The traversal order is fixed by `printImpl`: every register's `next`, then
every memory's write ports (each `en`, `addr`, `data` in order), then every
output's value.
-/

namespace Loom.Release.SSA

open Loom.Hw Loom.Emit.MicroVerilog

/-! ## The flattening state -/

/-- Wire-allocation state mirroring `Print.MSt`: a counter, the wires emitted
so far, and the `(width, rendered RHS)` hash-consing table. The rendered RHS
key is the exact string the printer would emit, so allocation order and
sharing agree with the printed artifact by construction. -/
structure FlattenSt where
  wires : Array Wire := #[]
  next : Nat := 0
  cse : Std.HashMap (Nat × String) String := {}

/-- Mirror of `Print.freshM`, also recording the structured `Rhs`. -/
def freshWire (w : Nat) (key : String) (rhs : Rhs) :
    StateM FlattenSt String := do
  if let some name := (← get).cse[(w, key)]? then
    return name
  let st ← get
  let name := s!"n{st.next}"
  set { st with
        next := st.next + 1
        wires := st.wires.push { width := w, name, rhs }
        cse := st.cse.insert (w, key) name }
  pure name

/-- Flatten one µVerilog expression to SSA wires; returns the identifier
carrying its value. Cases correspond one-to-one with `Print.pExpr`, and each
rendered key string is byte-identical to that case's output. The `Rhs`
normalizations follow the release language: `zext` and width-preserving
`sext` have no constructor and land as `ident`; narrowing `sext` lands as
`slice`, exactly as the generator parses the printed text today. -/
def flatten : {w : Nat} → Emit.MicroVerilog.Expr w → StateM FlattenSt String
  | w, .lit v => freshWire w s!"{w}'d{v.toNat}" (.lit w v.toNat)
  | _, .reg _ n => pure n
  | dw, .memRead _ m addr => do
      let a ← flatten addr
      freshWire dw s!"{m}[{a}]" (.memRead m a)
  | w, .and a b => do
      let x ← flatten a; let y ← flatten b
      freshWire w s!"{x} & {y}" (.bin .and x y)
  | w, .or a b => do
      let x ← flatten a; let y ← flatten b
      freshWire w s!"{x} | {y}" (.bin .or x y)
  | w, .xor a b => do
      let x ← flatten a; let y ← flatten b
      freshWire w s!"{x} ^ {y}" (.bin .xor x y)
  | w, .not a => do
      let x ← flatten a
      freshWire w s!"~{x}" (.not x)
  | w, .add a b => do
      let x ← flatten a; let y ← flatten b
      freshWire w s!"{x} + {y}" (.bin .add x y)
  | w, .sub a b => do
      let x ← flatten a; let y ← flatten b
      freshWire w s!"{x} - {y}" (.bin .sub x y)
  | w, .shl a b => do
      let x ← flatten a; let y ← flatten b
      freshWire w s!"{x} << {y}" (.bin .shl x y)
  | w, .shr a b => do
      let x ← flatten a; let y ← flatten b
      freshWire w s!"{x} >> {y}" (.bin .shr x y)
  | _, .eq a b => do
      let x ← flatten a; let y ← flatten b
      freshWire 1 s!"{x} == {y}" (.bin .eq x y)
  | _, .ult a b => do
      let x ← flatten a; let y ← flatten b
      freshWire 1 s!"{x} < {y}" (.bin .ult x y)
  | _, .slt a b => do
      let x ← flatten a; let y ← flatten b
      freshWire 1 s!"$signed({x}) < $signed({y})" (.slt x y)
  | w, .mux c t f => do
      let cn ← flatten c; let tn ← flatten t; let fn ← flatten f
      freshWire w s!"{cn} ? {tn} : {fn}" (.mux cn tn fn)
  | _, @Emit.MicroVerilog.Expr.slice _ a lo w' => do
      let x ← flatten a
      freshWire w' s!"{x}[{lo + w' - 1}:{lo}]" (.slice x (lo + w' - 1) lo)
  | w', .zext a _ => do
      let x ← flatten a
      freshWire w' s!"{x}" (.ident x)
  | w', @Emit.MicroVerilog.Expr.sext w a _ => do
      let x ← flatten a
      let sb := "{" ++ toString (w' - w) ++ "{" ++ x ++ "[" ++
        toString (w - 1) ++ "]}}"
      if w' > w then
        freshWire w' ("{" ++ sb ++ ", " ++ x ++ "}") (.sext (w' - w) x (w - 1))
      else if w' = w then
        freshWire w' s!"{x}" (.ident x)
      else
        freshWire w' s!"{x}[{w'-1}:0]" (.slice x (w' - 1) 0)

/-! ## Rope shaping

The generated witness fixes the rope shapes: wire leaves of `blockSize`,
grouped `chunkLeaves` leaves per balanced chunk tree, chunk trees composed
by the same pairing; memory images chunked at `blockSize` and balanced.
`balancedRope` is the Lean transcription of the generator's `balanced`:
repeatedly pair adjacent elements left to right, promoting an odd trailing
element unchanged. -/

private def listChunksGo {α : Type} (size : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, items@(_ :: _) =>
      items.take size :: listChunksGo size fuel (items.drop size)

/-- Split a list into consecutive chunks of `size` (last may be short). The
list length is sufficient fuel: every round consumes at least one element. -/
def listChunks {α : Type} (size : Nat) (items : List α) : List (List α) :=
  if size = 0 then [items] else listChunksGo size items.length items

private def pairStep {α : Type} : List (Rope α) → List (Rope α)
  | one :: two :: rest => .node one two :: pairStep rest
  | short => short

private def balancedGo {α : Type} [Inhabited α] : Nat → List (Rope α) → Rope α
  | _, [] => .leaf default
  | _, [single] => single
  | 0, one :: _ :: _ => one
  | fuel + 1, one :: two :: rest => balancedGo fuel (pairStep (one :: two :: rest))

/-- The generator's `balanced`: pair adjacent trees until one remains,
promoting an odd trailing element unchanged. Each round at least halves a
multi-element list, so the list length is sufficient fuel; an empty input
yields `.leaf default` (the generator never produces one). -/
def balancedRope {α : Type} [Inhabited α] (items : List (Rope α)) : Rope α :=
  balancedGo items.length items

/-- Wire rope with the generated three-level shape: leaves of `blockSize`,
balanced chunk trees of `chunkLeaves` leaves, balanced root over chunks. -/
def shapeWireRope (blockSize chunkLeaves : Nat) (wires : List Wire) :
    Rope (List Wire) :=
  let leaves := (listChunks blockSize wires).map Rope.leaf
  balancedRope ((listChunks chunkLeaves leaves).map balancedRope)

/-! ## The constructor -/

/-- The release witness as the verified compiler's own output.

`d.toProgram` is definitionally the flattening of `Compile.compile d` in the
printer's traversal order, shaped into the generated witness's rope layout.
The generator-independence goal is the equality `program = d.toProgram`
against the parsed witness, after which the parsing layer stops being part
of anything's trust story. -/
def _root_.Loom.Hw.Design.toProgram (d : Loom.Hw.Design)
    (blockSize : Nat := 128) (chunkLeaves : Nat := 16) : Program :=
  let m := Compile.compile d
  let build : StateM FlattenSt (List Reg × List Mem × List Out) := do
    let mut regs : Array Reg := #[]
    for r in m.regs do
      let nw ← flatten r.next
      regs := regs.push
        { name := r.name, width := r.width, init := r.init.toNat, next := nw }
    let mut mems : Array Mem := #[]
    for mm in m.mems do
      let mut writes : Array Write := #[]
      for p in mm.wrPorts do
        let en ← flatten p.en
        let addr ← flatten p.addr
        let data ← flatten p.data
        writes := writes.push { en, addr, data }
      let image := (List.range (2 ^ mm.addrWidth)).map fun a =>
        (mm.init a).toNat
      mems := mems.push
        { name := mm.name, addrWidth := mm.addrWidth,
          dataWidth := mm.dataWidth,
          init := balancedRope ((listChunks blockSize image).map .leaf),
          writes := writes.toList }
    let mut outs : Array Out := #[]
    for o in m.outs do
      let v ← flatten o.val
      outs := outs.push { name := o.name, width := o.width, value := v }
    pure (regs.toList, mems.toList, outs.toList)
  let ((regs, mems, outs), st) := build.run {}
  { name := m.name
    regs
    mems
    wires := shapeWireRope blockSize chunkLeaves st.wires.toList
    outs }

/-! ## Fast execution (pointer-memoized; same output)

`flatten` walks the expression as a tree, so designs whose expression DAGs
carry heavy sharing (LNP64-µ's pointer-doubling circuits) unfold
exponentially. As with `print`/`printImpl`, the twin below adds a
pointer-identity memo. It is extensionally equal to the reference: a
revisited shared node would re-render the identical `(width, key)` (operands
resolve to the same canonical names bottom-up) and hit the CSE table,
returning the same name — the memo only skips that redundant walk. -/

private structure FlattenMSt where
  wires : Array Wire := #[]
  next : Nat := 0
  cse : Std.HashMap (Nat × String) String := {}
  memo : Std.HashMap USize String := {}

private def freshWireM (w : Nat) (key : String) (rhs : Rhs) :
    StateM FlattenMSt String := do
  if let some name := (← get).cse[(w, key)]? then
    return name
  let st ← get
  let name := s!"n{st.next}"
  set { st with
        next := st.next + 1
        wires := st.wires.push { width := w, name, rhs }
        cse := st.cse.insert (w, key) name }
  pure name

mutual

private unsafe def flattenMGo :
    {w : Nat} → Emit.MicroVerilog.Expr w → StateM FlattenMSt String
  | w, .lit v => freshWireM w s!"{w}'d{v.toNat}" (.lit w v.toNat)
  | _, .reg _ n => pure n
  | dw, .memRead _ m addr => do
      let a ← flattenM addr
      freshWireM dw s!"{m}[{a}]" (.memRead m a)
  | w, .and a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM w s!"{x} & {y}" (.bin .and x y)
  | w, .or a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM w s!"{x} | {y}" (.bin .or x y)
  | w, .xor a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM w s!"{x} ^ {y}" (.bin .xor x y)
  | w, .not a => do
      let x ← flattenM a
      freshWireM w s!"~{x}" (.not x)
  | w, .add a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM w s!"{x} + {y}" (.bin .add x y)
  | w, .sub a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM w s!"{x} - {y}" (.bin .sub x y)
  | w, .shl a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM w s!"{x} << {y}" (.bin .shl x y)
  | w, .shr a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM w s!"{x} >> {y}" (.bin .shr x y)
  | _, .eq a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM 1 s!"{x} == {y}" (.bin .eq x y)
  | _, .ult a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM 1 s!"{x} < {y}" (.bin .ult x y)
  | _, .slt a b => do
      let x ← flattenM a; let y ← flattenM b
      freshWireM 1 s!"$signed({x}) < $signed({y})" (.slt x y)
  | w, .mux c t f => do
      let cn ← flattenM c; let tn ← flattenM t; let fn ← flattenM f
      freshWireM w s!"{cn} ? {tn} : {fn}" (.mux cn tn fn)
  | _, @Emit.MicroVerilog.Expr.slice _ a lo w' => do
      let x ← flattenM a
      freshWireM w' s!"{x}[{lo + w' - 1}:{lo}]" (.slice x (lo + w' - 1) lo)
  | w', .zext a _ => do
      let x ← flattenM a
      freshWireM w' s!"{x}" (.ident x)
  | w', @Emit.MicroVerilog.Expr.sext w a _ => do
      let x ← flattenM a
      let sb := "{" ++ toString (w' - w) ++ "{" ++ x ++ "[" ++
        toString (w - 1) ++ "]}}"
      if w' > w then
        freshWireM w' ("{" ++ sb ++ ", " ++ x ++ "}") (.sext (w' - w) x (w - 1))
      else if w' = w then
        freshWireM w' s!"{x}" (.ident x)
      else
        freshWireM w' s!"{x}[{w'-1}:0]" (.slice x (w' - 1) 0)

private unsafe def flattenM {w : Nat} (e : Emit.MicroVerilog.Expr w) :
    StateM FlattenMSt String := do
  let k := ptrAddrUnsafe e
  if let some name := (← get).memo[k]? then
    return name
  let name ← flattenMGo e
  modify fun st => { st with memo := st.memo.insert k name }
  return name

end

/-- Run the printer-order traversal with the memoized flattener. -/
private unsafe def flattenModuleImpl (m : Module) (blockSize : Nat) :
    (List Reg × List Mem × List Out) × FlattenMSt :=
  (build.run {})
where
  build : StateM FlattenMSt (List Reg × List Mem × List Out) := do
    let mut regs : Array Reg := #[]
    for r in m.regs do
      let nw ← flattenM r.next
      regs := regs.push
        { name := r.name, width := r.width, init := r.init.toNat, next := nw }
    let mut mems : Array Mem := #[]
    for mm in m.mems do
      let mut writes : Array Write := #[]
      for p in mm.wrPorts do
        let en ← flattenM p.en
        let addr ← flattenM p.addr
        let data ← flattenM p.data
        writes := writes.push { en, addr, data }
      let image := (List.range (2 ^ mm.addrWidth)).map fun a =>
        (mm.init a).toNat
      mems := mems.push
        { name := mm.name, addrWidth := mm.addrWidth,
          dataWidth := mm.dataWidth,
          init := balancedRope ((listChunks blockSize image).map .leaf),
          writes := writes.toList }
    let mut outs : Array Out := #[]
    for o in m.outs do
      let v ← flattenM o.val
      outs := outs.push { name := o.name, width := o.width, value := v }
    pure (regs.toList, mems.toList, outs.toList)

private unsafe def toProgramImpl (d : Loom.Hw.Design)
    (blockSize : Nat := 128) (chunkLeaves : Nat := 16) : Program :=
  let m := Compile.compile d
  let ((regs, mems, outs), st) := flattenModuleImpl m blockSize
  { name := m.name
    regs
    mems
    outs
    wires := shapeWireRope blockSize chunkLeaves st.wires.toList }

attribute [implemented_by toProgramImpl] Loom.Hw.Design.toProgram

/-! ## Derived certificate roots

The remaining `ModuleBehavior` arguments are deterministic projections of
the same construction. -/

/-- The reference for an SSA operand: numbered wires by their canonical
name, anything else as a register read, matching the generator. -/
def operandRef (name : String) : Symbolic.Ref :=
  match Symbolic.wireNumber? name with
  | some number => .wire number
  | none => .reg name

/-- String-free view of one structured RHS. -/
def indexedRhsOf : Rhs → Symbolic.IndexedRhs
  | .lit width value => .lit width value
  | .ident name => .ident (operandRef name)
  | .memRead mem addr => .memRead mem (operandRef addr)
  | .slice value hi lo => .slice (operandRef value) hi lo
  | .not value => .not (operandRef value)
  | .bin op left right => .bin op (operandRef left) (operandRef right)
  | .slt left right => .slt (operandRef left) (operandRef right)
  | .mux c y n => .mux (operandRef c) (operandRef y) (operandRef n)
  | .sext amount value signBit => .sext amount (operandRef value) signBit

/-- The flat, numbered wire list underlying `d.toProgram`. -/
def _root_.Loom.Hw.Design.toIndexedWires (d : Loom.Hw.Design) :
    List Symbolic.IndexedWire :=
  let m := Compile.compile d
  let build : StateM FlattenSt Unit := do
    for r in m.regs do
      _ ← flatten r.next
    for mm in m.mems do
      for p in mm.wrPorts do
        _ ← flatten p.en
        _ ← flatten p.addr
        _ ← flatten p.data
    for o in m.outs do
      _ ← flatten o.val
  let st := (build.run {}).2
  st.wires.toList.zipIdx.map fun (wire, number) =>
    { number, width := wire.width, rhs := indexedRhsOf wire.rhs }

private unsafe def toIndexedWiresImpl (d : Loom.Hw.Design) :
    List Symbolic.IndexedWire :=
  let (_, st) := flattenModuleImpl (Compile.compile d) 128
  st.wires.toList.zipIdx.map fun (wire, number) =>
    { number, width := wire.width, rhs := indexedRhsOf wire.rhs }

attribute [implemented_by toIndexedWiresImpl] Loom.Hw.Design.toIndexedWires

/-- Indexed wires in the witness rope shape. -/
def _root_.Loom.Hw.Design.indexedsOf (d : Loom.Hw.Design)
    (blockSize : Nat := 128) (chunkLeaves : Nat := 16) :
    Rope (List Symbolic.IndexedWire) :=
  let leaves := (listChunks blockSize d.toIndexedWires).map Rope.leaf
  balancedRope ((listChunks chunkLeaves leaves).map balancedRope)

/-- The flat wire table for the same shape. -/
def _root_.Loom.Hw.Design.tableOf (d : Loom.Hw.Design)
    (blockSize : Nat := 128) : Symbolic.WireTable :=
  { leafSize := blockSize
    leafCount := (d.toIndexedWires.length + blockSize - 1) / blockSize }

/-- One register root per declaration: the reference carrying its next
value in `d.toProgram`. -/
def _root_.Loom.Hw.Design.registersOf (d : Loom.Hw.Design)
    (blockSize : Nat := 128) : Rope (List Symbolic.RegisterRoot) :=
  let entries := (d.toProgram).regs.zipIdx.map fun (reg, index) =>
    ({ index, root := operandRef reg.next } : Symbolic.RegisterRoot)
  balancedRope ((listChunks blockSize entries).map .leaf)

/-- Output indices in rope shape (`OutputBehaviorAt` fixes the content). -/
def _root_.Loom.Hw.Design.outputsOf (d : Loom.Hw.Design)
    (blockSize : Nat := 128) : Rope (List Nat) :=
  let indices := List.range (d.toProgram).outs.length
  balancedRope ((listChunks blockSize indices).map .leaf)

end Loom.Release.SSA
