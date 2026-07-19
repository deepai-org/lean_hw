-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SSA
import Loom.Hw.Compile
import Loom.Hw.FootprintCover

/-!
# Symbolic SSA release certificates

The total SSA elaborator expands every named wire into a typed expression.
That is convenient for small programs, but a full LNP64-µ witness creates an
enormous kernel term. This module validates the same graph symbolically:
operands remain names, and generator-supplied rope addresses provide bounded
random access to their defining wires.

The address table is untrusted proof data. Every lookup checks both the rope
address and the wire name, so a stale, permuted, or malicious table entry can
only make validation fail.
-/

namespace Loom.Release.Symbolic

open Loom.Release.SSA

/-- A concrete operand is either a source register or a numbered SSA wire. -/
inductive Ref where
  | reg (name : String)
  | wire (number : Nat)
  deriving Repr, DecidableEq

def Ref.render : Ref → String
  | .reg name => name
  | .wire number => s!"n{number}"

/-- Decode the deliberately tiny release-witness naming convention. -/
def wireNumber? (name : String) : Option Nat := do
  guard (name.startsWith "n")
  (name.drop 1).toNat?

/-- String-free certificate view of an SSA right-hand side. -/
inductive IndexedRhs where
  | lit (width value : Nat)
  | ident (value : Ref)
  | memRead (mem : String) (address : Ref)
  | slice (value : Ref) (hi lo : Nat)
  | not (value : Ref)
  | bin (op : BinOp) (left right : Ref)
  | slt (left right : Ref)
  | mux (condition yes no : Ref)
  | sext (amount : Nat) (value : Ref) (signBit : Nat)
  deriving Repr, DecidableEq

structure IndexedWire where
  number : Nat
  width : Nat
  rhs : IndexedRhs
  deriving Repr, DecidableEq

/-- A small balanced random-access view of one generated wire block.  The
cached left size makes lookup logarithmic; `WellFormed` proves that the cache
agrees with the canonical list view used by the existing soundness theorems. -/
inductive LookupTree (α : Type) where
  | leaf (value : α)
  | node (leftSize : Nat) (left right : LookupTree α)

def LookupTree.toList {α : Type} : LookupTree α → List α
  | .leaf value => [value]
  | .node _ left right => left.toList ++ right.toList

def LookupTree.get? {α : Type} : LookupTree α → Nat → Option α
  | .leaf value, 0 => some value
  | .leaf _, _ + 1 => none
  | .node leftSize left right, index =>
      if index < leftSize then left.get? index
      else right.get? (index - leftSize)

inductive LookupTree.WellFormed {α : Type} : LookupTree α → Prop where
  | leaf {value : α} : WellFormed (.leaf value)
  | node {leftSize : Nat} {left right : LookupTree α}
      (size : leftSize = left.toList.length)
      (leftOk : WellFormed left) (rightOk : WellFormed right) :
      WellFormed (.node leftSize left right)

theorem LookupTree.get?_eq_getElem?_toList
    {α : Type} {tree : LookupTree α}
    (wellFormed : tree.WellFormed) (index : Nat) :
    tree.get? index = tree.toList[index]? := by
  induction wellFormed generalizing index with
  | leaf => cases index <;> rfl
  | node size leftOk rightOk leftIH rightIH =>
      cases size
      simp only [get?, toList]
      split
      · rename_i inLeft
        rw [leftIH, List.getElem?_append_left inLeft]
      · rename_i notInLeft
        rw [rightIH, List.getElem?_append_right (Nat.le_of_not_gt notInLeft)]

/-- Check the indexed view against the exact raw witness node. This is run
once per bounded wire leaf; later semantic checks never parse identifiers. -/
def IndexedWire.matchesRaw (number : Nat) (raw : Wire)
    (indexed : IndexedWire) : Bool :=
  indexed.number == number &&
  raw.name == (Ref.wire number).render && raw.width == indexed.width &&
  match raw.rhs, indexed.rhs with
  | .lit w v, .lit w' v' => w == w' && v == v'
  | .ident value, .ident value' => value == value'.render
  | .memRead mem address, .memRead mem' address' =>
      mem == mem' && address == address'.render
  | .slice value hi lo, .slice value' hi' lo' =>
      value == value'.render && hi == hi' && lo == lo'
  | .not value, .not value' => value == value'.render
  | .bin op left right, .bin op' left' right' =>
      op == op' && left == left'.render && right == right'.render
  | .slt left right, .slt left' right' =>
      left == left'.render && right == right'.render
  | .mux condition yes no, .mux condition' yes' no' =>
      condition == condition'.render && yes == yes'.render && no == no'.render
  | .sext amount value signBit, .sext amount' value' signBit' =>
      amount == amount' && value == value'.render && signBit == signBit'
  | _, _ => false

def indexedBlockMatches : Nat → List Wire → List IndexedWire → Bool
  | _, [], [] => true
  | number, raw :: raws, indexed :: indexeds =>
      indexed.matchesRaw number raw &&
        indexedBlockMatches (number + 1) raws indexeds
  | _, _, _ => false

/-- Balanced proof that the indexed graph is exactly the string-free view of
the raw rendered wire rope, with globally correct wire numbering. -/
inductive IndexedRopeMatches : Nat → Rope (List Wire) →
    Rope (List IndexedWire) → Prop where
  | leaf {start raws indexed}
      (accepted : indexedBlockMatches start raws indexed = true) :
      IndexedRopeMatches start (.leaf raws) (.leaf indexed)
  | node {start rawLeft rawRight indexedLeft indexedRight}
      (left : IndexedRopeMatches start rawLeft indexedLeft)
      (right : IndexedRopeMatches (start + rawLeft.listLength)
        rawRight indexedRight) :
      IndexedRopeMatches start (.node rawLeft rawRight)
        (.node indexedLeft indexedRight)

/-- Compact layout proof data for fixed-size wire leaves. Only one path per
leaf is stored; the numeric SSA suffix determines the leaf and offset.
The last leaf may be shorter. -/
structure WireTable where
  leafSize : Nat
  leafCount : Nat
  deriving Repr, DecidableEq

private def balancedPathAux : Nat → Nat → Nat → Option (List Bool)
  | 0, _, _ => none
  | _ + 1, 0, _ => none
  | _ + 1, 1, 0 => some []
  | _ + 1, 1, _ => none
  | fuel + 1, count, index => do
      let parent ← balancedPathAux fuel ((count + 1) / 2) (index / 2)
      if count % 2 == 1 && index + 1 == count then pure parent
      else pure (parent ++ [index % 2 == 1])

/-- Compute the root-to-leaf path induced by the pairwise balanced rope
constructor used by release generation. -/
def balancedPath? (count index : Nat) : Option (List Bool) := do
  guard (index < count)
  balancedPathAux (count + 1) count index

def lookupIndexed? (wires : Rope (List IndexedWire)) (table : WireTable)
    (number : Nat) : Option IndexedWire := do
  guard (table.leafSize > 0)
  let path ← balancedPath? table.leafCount (number / table.leafSize)
  let wire ← wires.resolve? ⟨path, number % table.leafSize⟩
  guard (wire.number == number)
  pure wire

/-- Resolve a numbered wire from separately checked path and leaf facts.
This is the constant-time proof interface used by large generated
certificates: the global rope path is checked once per leaf, while individual
wire uses only reduce a bounded leaf lookup. -/
theorem lookupIndexed_of_resolve
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {number : Nat} {path : List Bool} {wire : IndexedWire}
    (positive : table.leafSize > 0)
    (pathFound : balancedPath? table.leafCount
      (number / table.leafSize) = some path)
    (resolved : wires.resolve? ⟨path, number % table.leafSize⟩ = some wire)
    (numberEq : wire.number = number) :
    lookupIndexed? wires table number = some wire := by
  simp [lookupIndexed?, positive, pathFound, resolved, numberEq, guard]

/-- Resolve the declared width of an operand while checking one numbered SSA
wire. Wire operands must point strictly backward, which simultaneously makes
the graph acyclic and matches the sequential concrete elaborator. -/
def refWidthBefore? (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (current : Nat) : Ref → Option Nat
  | .reg name =>
      do
        guard (wireNumber? name).isNone
        pure (← program.regs.find? fun reg => reg.name == name).width
  | .wire number => do
      guard (number < current)
      pure (← lookupIndexed? wires table number).width

/-- Whole-node type check for the concrete SSA subset. This mirrors
`SSA.Rhs.elaborate`, but retains only widths and bounded numeric lookups, so it
can be kernel-checked on a full artifact without constructing expanded
expression trees. -/
def indexedRhsWellFormed (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (number resultWidth : Nat) : IndexedRhs → Bool
  | .lit literalWidth _ => literalWidth == resultWidth
  | .ident value => (refWidthBefore? program wires table number value).isSome
  | .memRead mem address =>
      match program.mems.find? (fun candidate => candidate.name == mem),
          refWidthBefore? program wires table number address with
      | some header, some addressWidth =>
          header.addrWidth == addressWidth && header.dataWidth == resultWidth
      | _, _ => false
  | .slice value hi lo =>
      (refWidthBefore? program wires table number value).isSome &&
        lo ≤ hi && hi + 1 - lo == resultWidth
  | .not value =>
      refWidthBefore? program wires table number value == some resultWidth
  | .bin op left right =>
      match op with
      | .and | .or | .xor | .add | .sub | .shl | .shr =>
          refWidthBefore? program wires table number left == some resultWidth &&
            refWidthBefore? program wires table number right == some resultWidth
      | .eq | .ult =>
          resultWidth == 1 &&
            match refWidthBefore? program wires table number left,
                refWidthBefore? program wires table number right with
            | some leftWidth, some rightWidth => leftWidth == rightWidth
            | _, _ => false
  | .slt left right =>
      resultWidth == 1 &&
        match refWidthBefore? program wires table number left,
            refWidthBefore? program wires table number right with
        | some leftWidth, some rightWidth => leftWidth == rightWidth
        | _, _ => false
  | .mux condition yes no =>
      refWidthBefore? program wires table number condition == some 1 &&
        refWidthBefore? program wires table number yes == some resultWidth &&
        refWidthBefore? program wires table number no == some resultWidth
  | .sext amount value signBit =>
      match refWidthBefore? program wires table number value with
      | some inputWidth => signBit + 1 == inputWidth &&
          inputWidth + amount == resultWidth && inputWidth < resultWidth
      | none => false

def indexedWireWellFormedAt (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (number : Nat) (wire : IndexedWire) : Bool :=
  wire.number == number &&
    lookupIndexed? wires table number == some wire &&
    indexedRhsWellFormed program wires table number wire.width wire.rhs

def indexedSemanticBlockMatches (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable) :
    Nat → List IndexedWire → Bool
  | _, [] => true
  | number, wire :: rest =>
      indexedWireWellFormedAt program wires table number wire &&
        indexedSemanticBlockMatches program wires table (number + 1) rest

/-- Balanced evidence that every rendered SSA assignment is well-typed and
only references a source register or a strictly earlier numbered wire. -/
inductive IndexedRopeWellFormed (program : Program)
    (allWires : Rope (List IndexedWire)) (table : WireTable) :
    Nat → Rope (List IndexedWire) → Prop where
  | leaf {start wires}
      (accepted : indexedSemanticBlockMatches program allWires table
        start wires = true) :
      IndexedRopeWellFormed program allWires table start (.leaf wires)
  | node {start left right}
      (leftProof : IndexedRopeWellFormed program allWires table start left)
      (rightProof : IndexedRopeWellFormed program allWires table
        (start + left.listLength) right) :
      IndexedRopeWellFormed program allWires table start (.node left right)

/-- String-free structural comparison with the reference compiler expression.
Shared SSA nodes may be revisited, but each visit performs only bounded rope
navigation and constructor/Nat comparisons. -/
def indexedExprMatches (wires : Rope (List IndexedWire)) (table : WireTable) :
    {w : Nat} → Loom.Emit.MicroVerilog.Expr w → Ref → Bool
  | _, .reg _ sourceName, .reg actualName => sourceName == actualName
  | _, .reg .., .wire _ => false
  | _, .lit _, .reg _ => false
  | w, .lit value, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .lit literalWidth actualValue⟩ =>
          actualWidth == w && literalWidth == w && actualValue == value.toNat
      | _ => false

  | _, .memRead .., .reg _ => false
  | w, .memRead _ mem address, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .memRead actualMem actualAddress⟩ =>
          actualWidth == w && actualMem == mem &&
            indexedExprMatches wires table address actualAddress
      | _ => false
  | _, .and .., .reg _ | _, .or .., .reg _ | _, .xor .., .reg _
  | _, .not _, .reg _ | _, .add .., .reg _ | _, .sub .., .reg _
  | _, .shl .., .reg _ | _, .shr .., .reg _ | _, .eq .., .reg _
  | _, .ult .., .reg _ | _, .slt .., .reg _ | _, .mux .., .reg _
  | _, .slice .., .reg _ | _, .zext .., .reg _ | _, .sext .., .reg _ => false
  | w, .and left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .bin .and actualLeft actualRight⟩ =>
          actualWidth == w && indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | w, .or left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .bin .or actualLeft actualRight⟩ =>
          actualWidth == w && indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | w, .xor left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .bin .xor actualLeft actualRight⟩ =>
          actualWidth == w && indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | w, .not value, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .not actual⟩ =>
          actualWidth == w && indexedExprMatches wires table value actual
      | _ => false
  | w, .add left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .bin .add actualLeft actualRight⟩ =>
          actualWidth == w && indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | w, .sub left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .bin .sub actualLeft actualRight⟩ =>
          actualWidth == w && indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | w, .shl left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .bin .shl actualLeft actualRight⟩ =>
          actualWidth == w && indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | w, .shr left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .bin .shr actualLeft actualRight⟩ =>
          actualWidth == w && indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | _, .eq left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, 1, .bin .eq actualLeft actualRight⟩ =>
          indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | _, .ult left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, 1, .bin .ult actualLeft actualRight⟩ =>
          indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | _, .slt left right, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, 1, .slt actualLeft actualRight⟩ =>
          indexedExprMatches wires table left actualLeft &&
            indexedExprMatches wires table right actualRight
      | _ => false
  | w, .mux condition yes no, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .mux actualCondition actualYes actualNo⟩ =>
          actualWidth == w &&
            indexedExprMatches wires table condition actualCondition &&
            indexedExprMatches wires table yes actualYes &&
            indexedExprMatches wires table no actualNo
      | _ => false
  | w, .slice value lo _, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .slice actualValue hi actualLo⟩ =>
          actualWidth == w && actualLo == lo && hi == lo + w - 1 &&
            indexedExprMatches wires table value actualValue
      | _ => false
  | w, @Loom.Emit.MicroVerilog.Expr.zext inputWidth value _, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .ident actual⟩ =>
          actualWidth == w && inputWidth ≤ w &&
            indexedExprMatches wires table value actual
      | _ => false
  | w, @Loom.Emit.MicroVerilog.Expr.sext inputWidth value _, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .sext amount actual signBit⟩ =>
          actualWidth == w && inputWidth < w && amount == w - inputWidth &&
            signBit + 1 == inputWidth &&
            indexedExprMatches wires table value actual
      | _ => false

/-- A proof DAG for one expression check.  Every constructor checks only the
outer SSA wire and refers to child evidence as theorem constants.  This is
extensionally the same check as `indexedExprMatches`, but it preserves sharing
in large generated source expressions instead of repeatedly normalizing them
as trees. -/
inductive IndexedExprEvidence (wires : Rope (List IndexedWire))
    (table : WireTable) :
    {width : Nat} → Loom.Emit.MicroVerilog.Expr width → Ref → Prop where
  | reg (width : Nat) (name : String) :
      IndexedExprEvidence wires table (.reg width name) (.reg name)
  | lit {width : Nat} {value : BitVec width} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .lit width value.toNat⟩) :
      IndexedExprEvidence wires table (.lit value) (.wire number)
  | memRead {addressWidth dataWidth : Nat} {memory : String}
      {address : Loom.Emit.MicroVerilog.Expr addressWidth}
      {addressRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, dataWidth, .memRead memory addressRef⟩)
      (addressEvidence : IndexedExprEvidence wires table address addressRef) :
      IndexedExprEvidence wires table (.memRead dataWidth memory address)
        (.wire number)
  | and {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .bin .and leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.and left right) (.wire number)
  | or {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .bin .or leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.or left right) (.wire number)
  | xor {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .bin .xor leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.xor left right) (.wire number)
  | not {width : Nat} {value : Loom.Emit.MicroVerilog.Expr width}
      {valueRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .not valueRef⟩)
      (valueEvidence : IndexedExprEvidence wires table value valueRef) :
      IndexedExprEvidence wires table (.not value) (.wire number)
  | add {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .bin .add leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.add left right) (.wire number)
  | sub {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .bin .sub leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.sub left right) (.wire number)
  | shl {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .bin .shl leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.shl left right) (.wire number)
  | shr {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .bin .shr leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.shr left right) (.wire number)
  | eq {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, 1, .bin .eq leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.eq left right) (.wire number)
  | ult {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, 1, .bin .ult leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.ult left right) (.wire number)
  | slt {width : Nat} {left right : Loom.Emit.MicroVerilog.Expr width}
      {leftRef rightRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, 1, .slt leftRef rightRef⟩)
      (leftEvidence : IndexedExprEvidence wires table left leftRef)
      (rightEvidence : IndexedExprEvidence wires table right rightRef) :
      IndexedExprEvidence wires table (.slt left right) (.wire number)
  | mux {width : Nat} {condition : Loom.Emit.MicroVerilog.Expr 1}
      {yes no : Loom.Emit.MicroVerilog.Expr width}
      {conditionRef yesRef noRef : Ref} {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .mux conditionRef yesRef noRef⟩)
      (conditionEvidence : IndexedExprEvidence wires table condition conditionRef)
      (yesEvidence : IndexedExprEvidence wires table yes yesRef)
      (noEvidence : IndexedExprEvidence wires table no noRef) :
      IndexedExprEvidence wires table (.mux condition yes no) (.wire number)
  | slice {inputWidth width lo : Nat}
      {value : Loom.Emit.MicroVerilog.Expr inputWidth} {valueRef : Ref}
      {number : Nat}
      (found : lookupIndexed? wires table number = some
        ⟨number, width, .slice valueRef (lo + width - 1) lo⟩)
      (valueEvidence : IndexedExprEvidence wires table value valueRef) :
      IndexedExprEvidence wires table (.slice value lo width) (.wire number)
  | zext {inputWidth width : Nat}
      {value : Loom.Emit.MicroVerilog.Expr inputWidth} {valueRef : Ref}
      {number : Nat}
      (found : lookupIndexed? wires table number =
        some ⟨number, width, .ident valueRef⟩)
      (widthAccepted : inputWidth ≤ width)
      (valueEvidence : IndexedExprEvidence wires table value valueRef) :
      IndexedExprEvidence wires table (.zext value width) (.wire number)
  | sext {inputWidth width : Nat}
      {value : Loom.Emit.MicroVerilog.Expr inputWidth} {valueRef : Ref}
      {number : Nat}
      (found : lookupIndexed? wires table number = some
        ⟨number, width, .sext (width - inputWidth) valueRef
          (inputWidth - 1)⟩)
      (inputPositive : 0 < inputWidth)
      (widthAccepted : inputWidth < width)
      (valueEvidence : IndexedExprEvidence wires table value valueRef) :
      IndexedExprEvidence wires table (.sext value width) (.wire number)

theorem IndexedExprEvidence.accepted
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {width : Nat} {expression : Loom.Emit.MicroVerilog.Expr width} {reference : Ref}
    (evidence : IndexedExprEvidence wires table expression reference) :
    indexedExprMatches wires table expression reference = true := by
  induction evidence <;> simp_all [indexedExprMatches]
  omega

/-- Three structural SSA references denoting one memory write-port value. -/
structure PortRefs where
  en : Ref
  addr : Ref
  data : Ref
  deriving Repr, DecidableEq

inductive NextRegCert where
  | same
  | write
  | seq (mid : Option Ref) (left right : NextRegCert)
  | ite (thenCert elseCert : NextRegCert)
  deriving Repr, DecidableEq

inductive NextRulesCert where
  | nil
  | cons (mid : Option Ref) (head : NextRegCert) (tail : NextRulesCert)
  deriving Repr, DecidableEq

/-- Structural evidence that an action cannot write one register. Generated
release proofs compose this evidence as named constants, avoiding kernel
normalization of a whole processor action merely to justify a `.same` node. -/
inductive NoRegWrite (register : String) (width : Nat) : Loom.Hw.Act → Prop
  | skip : NoRegWrite register width .skip
  | seq {left right} : NoRegWrite register width left →
      NoRegWrite register width right →
      NoRegWrite register width (.seq left right)
  | ite {guard thenAction elseAction} :
      NoRegWrite register width thenAction →
      NoRegWrite register width elseAction →
      NoRegWrite register width (.ite guard thenAction elseAction)
  | writeName {actualWidth name} (value : Loom.Hw.Expr actualWidth)
      (different : name ≠ register) :
      NoRegWrite register width (.write actualWidth name value)
  | writeWidth {actualWidth} (value : Loom.Hw.Expr actualWidth)
      (different : actualWidth ≠ width) :
      NoRegWrite register width (.write actualWidth register value)
  | memWrite {addressWidth dataWidth name port}
      (address : Loom.Hw.Expr addressWidth) (value : Loom.Hw.Expr dataWidth) :
      NoRegWrite register width
        (.memWrite addressWidth dataWidth name port address value)

theorem NoRegWrite.not_mem {register : String} {width : Nat}
    {action : Loom.Hw.Act} (h : NoRegWrite register width action) :
    (register, width) ∉ action.regWrites := by
  induction h with
  | skip => simp [Loom.Hw.Act.regWrites]
  | seq _ _ left right =>
      simp [Loom.Hw.Act.regWrites, left, right]
  | ite _ _ thenProof elseProof =>
      simp [Loom.Hw.Act.regWrites, thenProof, elseProof]
  | writeName _ different =>
      simp only [Loom.Hw.Act.regWrites, List.mem_singleton, Prod.mk.injEq,
        not_and]
      intro sameName _
      exact different sameName.symm
  | writeWidth _ different =>
      simp only [Loom.Hw.Act.regWrites, List.mem_singleton, Prod.mk.injEq,
        true_and]
      exact fun sameWidth => different sameWidth.symm
  | memWrite => simp [Loom.Hw.Act.regWrites]

theorem NoRegWrite.of_not_mem (register : String) (width : Nat) :
    ∀ action : Loom.Hw.Act, (register, width) ∉ action.regWrites →
      NoRegWrite register width action
  | .skip, _ => .skip
  | .seq left right, h => by
      simp only [Loom.Hw.Act.regWrites, List.mem_append, not_or] at h
      exact .seq (of_not_mem register width left h.1)
        (of_not_mem register width right h.2)
  | .ite _ thenAction elseAction, h => by
      simp only [Loom.Hw.Act.regWrites, List.mem_append, not_or] at h
      exact .ite (of_not_mem register width thenAction h.1)
        (of_not_mem register width elseAction h.2)
  | .write actualWidth name value, h => by
      by_cases hname : name = register
      · subst name
        apply NoRegWrite.writeWidth value
        intro sameWidth
        subst actualWidth
        exact h (by simp [Loom.Hw.Act.regWrites])
      · exact NoRegWrite.writeName value hname
  | .memWrite _ _ _ _ address value, _ => NoRegWrite.memWrite address value

theorem NoRegWrite.writesRegB_eq_false {register : String} {width : Nat}
    {action : Loom.Hw.Act} (h : NoRegWrite register width action) :
    Loom.Hw.Compile.writesRegB register width action = false := by
  exact (Loom.Hw.Compile.writesRegB_eq_false_iff register width action).2
    h.not_mem

/-- Structural evidence that an action cannot write one concrete memory port.
This is the memory analogue of `NoRegWrite`; its tree-shaped proofs let the
release checker justify `.same` nodes without reducing an entire action. -/
inductive NoPortWrite (memory : String) (port : Nat) : Loom.Hw.Act → Prop
  | skip : NoPortWrite memory port .skip
  | seq {left right} : NoPortWrite memory port left →
      NoPortWrite memory port right →
      NoPortWrite memory port (.seq left right)
  | ite {guard thenAction elseAction} :
      NoPortWrite memory port thenAction →
      NoPortWrite memory port elseAction →
      NoPortWrite memory port (.ite guard thenAction elseAction)
  | write {width name} (value : Loom.Hw.Expr width) :
      NoPortWrite memory port (.write width name value)
  | memWriteName {addressWidth dataWidth name actualPort}
      (address : Loom.Hw.Expr addressWidth) (value : Loom.Hw.Expr dataWidth)
      (different : name ≠ memory) :
      NoPortWrite memory port
        (.memWrite addressWidth dataWidth name actualPort address value)
  | memWritePort {addressWidth dataWidth actualPort}
      (address : Loom.Hw.Expr addressWidth) (value : Loom.Hw.Expr dataWidth)
      (different : actualPort ≠ port) :
      NoPortWrite memory port
        (.memWrite addressWidth dataWidth memory actualPort address value)

theorem NoPortWrite.writesPortB_eq_false {memory : String} {port : Nat}
    {action : Loom.Hw.Act} (h : NoPortWrite memory port action) :
    Loom.Hw.Compile.writesPortB memory port action = false := by
  induction h with
  | skip => simp [Loom.Hw.Compile.writesPortB, Loom.Hw.Compile.portTrace]
  | seq _ _ left right | ite _ _ left right =>
      rw [Loom.Hw.Compile.writesPortB, decide_eq_false_iff_not]
      simp only [Loom.Hw.Compile.portTrace, List.mem_append, not_or]
      constructor
      · simpa [Loom.Hw.Compile.writesPortB] using left
      · simpa [Loom.Hw.Compile.writesPortB] using right
  | write => simp [Loom.Hw.Compile.writesPortB, Loom.Hw.Compile.portTrace]
  | memWriteName _ _ different =>
      simp [Loom.Hw.Compile.writesPortB, Loom.Hw.Compile.portTrace, different]
  | memWritePort _ _ different =>
      have different' : port ≠ _ := fun same => different same.symm
      simp [Loom.Hw.Compile.writesPortB, Loom.Hw.Compile.portTrace, different']

/-- Structural evidence that an action contains a write to a concrete memory
port. It lets conditional certificate nodes establish their pruning guard
without normalizing the surrounding processor action. -/
inductive HasPortWrite (memory : String) (port : Nat) : Loom.Hw.Act → Prop
  | seqLeft {left right} : HasPortWrite memory port left →
      HasPortWrite memory port (.seq left right)
  | seqRight {left right} : HasPortWrite memory port right →
      HasPortWrite memory port (.seq left right)
  | iteThen {guard thenAction elseAction} :
      HasPortWrite memory port thenAction →
      HasPortWrite memory port (.ite guard thenAction elseAction)
  | iteElse {guard thenAction elseAction} :
      HasPortWrite memory port elseAction →
      HasPortWrite memory port (.ite guard thenAction elseAction)
  | memWrite {addressWidth dataWidth}
      (address : Loom.Hw.Expr addressWidth) (value : Loom.Hw.Expr dataWidth) :
      HasPortWrite memory port
        (.memWrite addressWidth dataWidth memory port address value)

theorem HasPortWrite.writesPortB_eq_true {memory : String} {port : Nat}
    {action : Loom.Hw.Act} (h : HasPortWrite memory port action) :
    Loom.Hw.Compile.writesPortB memory port action = true := by
  induction h with
  | seqLeft _ | iteThen _ =>
      simp_all [Loom.Hw.Compile.writesPortB, Loom.Hw.Compile.portTrace]
  | seqRight _ | iteElse _ =>
      simp_all [Loom.Hw.Compile.writesPortB, Loom.Hw.Compile.portTrace]
  | memWrite =>
      simp [Loom.Hw.Compile.writesPortB, Loom.Hw.Compile.portTrace]

/-- Validate one source action's contribution to a register root without
materializing `Compile.nextReg`. -/
def nextRegMatches (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) : Loom.Hw.Act → Option Ref → Ref →
      NextRegCert → Bool
  | .skip, some current, out, .same => current == out
  | .seq left right, current, out, .seq mid leftCert rightCert =>
      match mid with
      | some mid =>
          nextRegMatches wires table register width left current mid leftCert &&
            nextRegMatches wires table register width right (some mid) out rightCert
      | none =>
          nextRegMatches wires table register width right none out rightCert
  | .seq left right, some current, out, .same =>
      !Loom.Hw.Compile.writesRegB register width (.seq left right) &&
        current == out
  | .ite guard thenAction elseAction, current, .wire number,
      .ite thenCert elseCert =>
      if Loom.Hw.Compile.writesRegB register width thenAction ||
          Loom.Hw.Compile.writesRegB register width elseAction then
        match lookupIndexed? wires table number with
        | some ⟨_, actualWidth, .mux guardRef thenRef elseRef⟩ =>
            actualWidth == width &&
              indexedExprMatches wires table
                (Loom.Hw.Compile.compileExpr guard) guardRef &&
              nextRegMatches wires table register width thenAction current
                thenRef thenCert &&
              nextRegMatches wires table register width elseAction current
                elseRef elseCert
        | _ => false
      else false
  | .ite _ thenAction elseAction, some current, out, .same =>
      !(Loom.Hw.Compile.writesRegB register width thenAction ||
        Loom.Hw.Compile.writesRegB register width elseAction) && current == out
  | .write actualWidth actualRegister value, current, out, cert =>
      if actualRegister = register then
        if h : actualWidth = width then
          match cert with
          | .write => indexedExprMatches wires table
              (Loom.Hw.Compile.compileExpr (h ▸ value)) out
          | _ => false
        else match current with
          | some current => cert == .same && current == out
          | none => false
      else match current with
        | some current => cert == .same && current == out
        | none => false
  | .memWrite .., some current, out, .same => current == out
  | _, _, _, _ => false

/-- Validate the ordered rule fold for one register. -/
def nextRulesMatches (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) : List Loom.Hw.Rule → Option Ref → Ref →
      NextRulesCert → Bool
  | [], some current, out, .nil => current == out
  | rule :: rules, current, out, .cons mid head tail =>
      match mid with
      | some mid =>
          nextRegMatches wires table register width rule.body current mid head &&
            nextRulesMatches wires table register width rules (some mid) out tail
      | none =>
          nextRulesMatches wires table register width rules none out tail
  | _, _, _, _ => false

/-! ## Shared register-write footprints

The baseline checker asks `writesRegB` while checking every register.  On a
large shared action DAG that repeats the same source traversal hundreds of
times.  The definitions below separate one shared coverage check per rule
from the cheap per-register lookup. -/

/-- One over-approximating list of register keys per source rule. -/
abbrev RuleRegFootprints := List (List (String × Nat))

/-- Check all rule footprints once.  This function is deliberately separate
from `nextRulesMatchesCovered`, so a generated named theorem can be reused by
every register certificate without reopening its proof. -/
def ruleRegFootprintsCoverB : List Loom.Hw.Rule → RuleRegFootprints → Bool
  | [], [] => true
  | rule :: rules, covered :: rest =>
      rule.body.regWritesCoveredB covered &&
        ruleRegFootprintsCoverB rules rest
  | _, _ => false

/-- Validate one action using a previously checked write over-approximation.
When the register is absent, only the small literal footprint and the `.same`
certificate are inspected; the source action is not traversed. -/
def nextRegMatchesCovered (wires : Rope (List IndexedWire))
    (table : WireTable) (covered : List (String × Nat))
    (register : String) (width : Nat) (action : Loom.Hw.Act)
    (current : Option Ref) (out : Ref) (cert : NextRegCert) : Bool :=
  if covered.elem (register, width) then
    nextRegMatches wires table register width action current out cert
  else
    match current, cert with
    | some current, .same => current == out
    | _, _ => false

theorem nextRegMatchesCovered_of_present
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (covered : List (String × Nat)) (register : String) (width : Nat)
    (action : Loom.Hw.Act) (current : Option Ref) (out : Ref)
    (cert : NextRegCert)
    (present : covered.elem (register, width) = true)
    (accepted : nextRegMatches wires table register width action current out
      cert = true) :
    nextRegMatchesCovered wires table covered register width action current
      out cert = true := by
  have member : (register, width) ∈ covered :=
    List.mem_of_elem_eq_true present
  simp [nextRegMatchesCovered, member, accepted]

/-- Register-rule validation using shared, prechecked rule footprints. -/
def nextRulesMatchesCovered (wires : Rope (List IndexedWire))
    (table : WireTable) (register : String) (width : Nat) :
    List Loom.Hw.Rule → RuleRegFootprints → Option Ref → Ref →
      NextRulesCert → Bool
  | [], [], some current, out, .nil => current == out
  | rule :: rules, covered :: rest, current, out,
      .cons mid head tail =>
      match mid with
      | some mid =>
          nextRegMatchesCovered wires table covered register width rule.body
              current mid head &&
            nextRulesMatchesCovered wires table register width rules rest
              (some mid) out tail
      | none =>
          nextRulesMatchesCovered wires table register width rules rest none
            out tail
  | _, _, _, _, _ => false

theorem nextRulesMatchesCovered_nil
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (current out : Ref)
    (same : current = out) :
    nextRulesMatchesCovered wires table register width [] []
      (some current) out .nil = true := by
  simp [nextRulesMatchesCovered, same]

theorem nextRulesMatchesCovered_cons_named
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (rule : Loom.Hw.Rule)
    (rules : List Loom.Hw.Rule) (covered : List (String × Nat))
    (rest : RuleRegFootprints) (current : Option Ref) (mid out : Ref)
    (head : NextRegCert) (tail : NextRulesCert)
    (headAccepted : nextRegMatchesCovered wires table covered register width
      rule.body current mid head = true)
    (tailAccepted : nextRulesMatchesCovered wires table register width rules
      rest (some mid) out tail = true) :
    nextRulesMatchesCovered wires table register width (rule :: rules)
      (covered :: rest) current out (.cons (some mid) head tail) = true := by
  simp only [nextRulesMatchesCovered, headAccepted, tailAccepted,
    Bool.true_and]

theorem nextRulesMatchesCovered_cons_discard
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (rule : Loom.Hw.Rule)
    (rules : List Loom.Hw.Rule) (covered : List (String × Nat))
    (rest : RuleRegFootprints) (current : Option Ref) (out : Ref)
    (head : NextRegCert) (tail : NextRulesCert)
    (tailAccepted : nextRulesMatchesCovered wires table register width rules
      rest none out tail = true) :
    nextRulesMatchesCovered wires table register width (rule :: rules)
      (covered :: rest) current out (.cons none head tail) = true := by
  simpa only [nextRulesMatchesCovered] using tailAccepted

/-! ## Structural memory-port certificates -/

/-- String-free proof data for one `Compile.memPort` action fold. -/
inductive NextPortCert where
  | same
  | write
  | seq (mid : PortRefs) (left right : NextPortCert)
  | ite (guard : Ref) (thenPort elsePort : PortRefs)
      (thenCert elseCert : NextPortCert)
  deriving Repr, DecidableEq

/-- String-free proof data for an ordered memory-port rule fold. -/
inductive NextPortRulesCert where
  | nil
  | cons (mid : PortRefs) (head : NextPortCert) (tail : NextPortRulesCert)
  deriving Repr, DecidableEq

/-- Check that one result root is exactly the SSA mux of three supplied
references. -/
def indexedMuxRootMatches (wires : Rope (List IndexedWire))
    (table : WireTable) (width : Nat) (condition yes no out : Ref) : Bool :=
  match out with
  | .wire number =>
      match lookupIndexed? wires table number with
      | some indexed =>
          indexed.width == width &&
            indexed.rhs == .mux condition yes no
      | none => false
  | .reg _ => false

/-- Check the three output muxes introduced by `Compile.memPort` for a
conditional write. -/
def indexedPortMuxMatches (wires : Rope (List IndexedWire))
    (table : WireTable) (addressWidth dataWidth : Nat) (guard : Ref)
    (thenPort elsePort out : PortRefs) : Bool :=
  indexedMuxRootMatches wires table 1 guard thenPort.en elsePort.en out.en &&
  indexedMuxRootMatches wires table addressWidth guard thenPort.addr
    elsePort.addr out.addr &&
  indexedMuxRootMatches wires table dataWidth guard thenPort.data
    elsePort.data out.data

/-- Validate one source action's contribution to a concrete memory write
port without materializing `Compile.memPort`. -/
def nextPortMatches (wires : Rope (List IndexedWire)) (table : WireTable)
    (memory : String) (addressWidth dataWidth port : Nat) :
      Loom.Hw.Act → PortRefs → PortRefs → NextPortCert → Bool
  | .skip, current, out, .same => current == out
  | .seq left right, current, out, .seq mid leftCert rightCert =>
      nextPortMatches wires table memory addressWidth dataWidth port left
          current mid leftCert &&
        nextPortMatches wires table memory addressWidth dataWidth port right
          mid out rightCert
  | .seq left right, current, out, .same =>
      !Loom.Hw.Compile.writesPortB memory port (.seq left right) &&
        current == out
  | .ite guard thenAction elseAction, current, out,
      .ite guardRef thenPort elsePort thenCert elseCert =>
      if Loom.Hw.Compile.writesPortB memory port thenAction ||
          Loom.Hw.Compile.writesPortB memory port elseAction then
        indexedExprMatches wires table
            (Loom.Hw.Compile.compileExpr guard) guardRef &&
          nextPortMatches wires table memory addressWidth dataWidth port
            thenAction current thenPort thenCert &&
          nextPortMatches wires table memory addressWidth dataWidth port
            elseAction current elsePort elseCert &&
          indexedPortMuxMatches wires table addressWidth dataWidth guardRef
            thenPort elsePort out
      else false
  | .ite _ thenAction elseAction, current, out, .same =>
      !(Loom.Hw.Compile.writesPortB memory port thenAction ||
        Loom.Hw.Compile.writesPortB memory port elseAction) && current == out
  | .memWrite actualAddressWidth actualDataWidth actualMemory actualPort
      address value, current, out, cert =>
      if _samePort : actualMemory = memory ∧ actualPort = port then
        if sameWidths : actualAddressWidth = addressWidth ∧
            actualDataWidth = dataWidth then
          match cert with
          | .write =>
              indexedExprMatches wires table (.lit (BitVec.ofNat 1 1)) out.en &&
              indexedExprMatches wires table
                (Loom.Hw.Compile.compileExpr (sameWidths.1 ▸ address)) out.addr &&
              indexedExprMatches wires table
                (Loom.Hw.Compile.compileExpr (sameWidths.2 ▸ value)) out.data
          | _ => false
        else cert == .same && current == out
      else cert == .same && current == out
  | .write .., current, out, .same => current == out
  | _, _, _, _ => false

/-- Validate an ordered rule fold for one concrete memory write port. -/
def nextPortRulesMatches (wires : Rope (List IndexedWire))
    (table : WireTable) (memory : String) (addressWidth dataWidth port : Nat) :
      List Loom.Hw.Rule → PortRefs → PortRefs → NextPortRulesCert → Bool
  | [], current, out, .nil => current == out
  | rule :: rules, current, out, .cons mid head tail =>
      nextPortMatches wires table memory addressWidth dataWidth port rule.body
          current mid head &&
        nextPortRulesMatches wires table memory addressWidth dataWidth port rules
          mid out tail
  | _, _, _, _ => false

/-! ## Compositional acceptance

These lemmas are deliberately small. Generated release modules give every
large child check its own named theorem and use the lemmas below to compose
parents without unfolding or normalizing the child proofs again. -/

theorem nextRegMatches_same_of_noWrite
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (action : Loom.Hw.Act)
    (current : Ref) (h : NoRegWrite register width action) :
    nextRegMatches wires table register width action (some current) current
      .same = true := by
  cases h with
  | skip => simp [nextRegMatches]
  | seq leftProof rightProof =>
      simp [nextRegMatches,
        (NoRegWrite.seq leftProof rightProof).writesRegB_eq_false]
  | ite thenProof elseProof =>
      simp [nextRegMatches, thenProof.writesRegB_eq_false,
        elseProof.writesRegB_eq_false]
  | writeName value different =>
      simp [nextRegMatches, different]
  | writeWidth value different =>
      simp [nextRegMatches, different]
  | memWrite => simp [nextRegMatches]

/-- Compact Boolean-facing form of `nextRegMatches_same_of_noWrite`.
Release elaboration can kernel-reduce the direct structural write test and
reuse this generic theorem instead of materializing a `NoRegWrite` proof tree
for every register/action pair. -/
theorem nextRegMatches_same_of_writesRegB_false
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (action : Loom.Hw.Act)
    (current : Ref)
    (h : Loom.Hw.Compile.writesRegB register width action = false) :
    nextRegMatches wires table register width action (some current) current
      .same = true := by
  apply nextRegMatches_same_of_noWrite
  exact NoRegWrite.of_not_mem register width action
    ((Loom.Hw.Compile.writesRegB_eq_false_iff register width action).1 h)

theorem nextRegMatches_seq_named
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (left right : Loom.Hw.Act)
    (current : Option Ref) (mid out : Ref) (leftCert rightCert : NextRegCert)
    (hleft : nextRegMatches wires table register width left current mid
      leftCert = true)
    (hright : nextRegMatches wires table register width right (some mid) out
      rightCert = true) :
    nextRegMatches wires table register width (.seq left right) current out
      (.seq (some mid) leftCert rightCert) = true := by
  simp only [nextRegMatches, hleft, hright, Bool.true_and]

theorem nextRegMatches_seq_discard
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (left right : Loom.Hw.Act)
    (current : Option Ref) (out : Ref) (leftCert rightCert : NextRegCert)
    (hright : nextRegMatches wires table register width right none out
      rightCert = true) :
    nextRegMatches wires table register width (.seq left right) current out
      (.seq none leftCert rightCert) = true := by
  simpa only [nextRegMatches] using hright

theorem nextRegMatches_ite_written
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (guard : Loom.Hw.Expr 1)
    (thenAction elseAction : Loom.Hw.Act) (current : Option Ref)
    (number : Nat) (guardRef thenRef elseRef : Ref)
    (thenCert elseCert : NextRegCert)
    (hwrites : (Loom.Hw.Compile.writesRegB register width thenAction ||
      Loom.Hw.Compile.writesRegB register width elseAction) = true)
    (hlookup : lookupIndexed? wires table number = some
      { number := number, width := width,
        rhs := .mux guardRef thenRef elseRef })
    (hguard : indexedExprMatches wires table
      (Loom.Hw.Compile.compileExpr guard) guardRef = true)
    (hthen : nextRegMatches wires table register width thenAction current
      thenRef thenCert = true)
    (helse : nextRegMatches wires table register width elseAction current
      elseRef elseCert = true) :
    nextRegMatches wires table register width
      (.ite guard thenAction elseAction) current (.wire number)
      (.ite thenCert elseCert) = true := by
  simp [nextRegMatches, hwrites, hlookup, hguard, hthen, helse]

theorem nextRulesMatches_nil
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (current out : Ref)
    (hcurrent : current = out) :
    nextRulesMatches wires table register width [] (some current) out .nil = true := by
  subst out
  simp only [nextRulesMatches, beq_self_eq_true]

theorem nextRulesMatches_cons_named
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (rule : Loom.Hw.Rule)
    (rules : List Loom.Hw.Rule) (current : Option Ref) (mid out : Ref)
    (head : NextRegCert) (tail : NextRulesCert)
    (hhead : nextRegMatches wires table register width rule.body current mid
      head = true)
    (htail : nextRulesMatches wires table register width rules (some mid) out
      tail = true) :
    nextRulesMatches wires table register width (rule :: rules) current out
      (.cons (some mid) head tail) = true := by
  simp only [nextRulesMatches, hhead, htail, Bool.true_and]

theorem nextRulesMatches_cons_discard
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (register : String) (width : Nat) (rule : Loom.Hw.Rule)
    (rules : List Loom.Hw.Rule) (current : Option Ref) (out : Ref)
    (head : NextRegCert) (tail : NextRulesCert)
    (htail : nextRulesMatches wires table register width rules none out tail = true) :
    nextRulesMatches wires table register width (rule :: rules) current out
      (.cons none head tail) = true := by
  simpa only [nextRulesMatches] using htail

theorem nextPortMatches_same_of_noWrite
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (memory : String) (addressWidth dataWidth port : Nat)
    (action : Loom.Hw.Act) (current : PortRefs)
    (h : NoPortWrite memory port action) :
    nextPortMatches wires table memory addressWidth dataWidth port action
      current current .same = true := by
  cases h with
  | skip => simp [nextPortMatches]
  | seq leftProof rightProof =>
      simp [nextPortMatches,
        (NoPortWrite.seq leftProof rightProof).writesPortB_eq_false]
  | ite thenProof elseProof =>
      simp [nextPortMatches, thenProof.writesPortB_eq_false,
        elseProof.writesPortB_eq_false]
  | write => simp [nextPortMatches]
  | memWriteName address value different =>
      simp [nextPortMatches, different]
  | memWritePort address value different =>
      simp [nextPortMatches, different]

theorem nextPortMatches_seq_named
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (memory : String) (addressWidth dataWidth port : Nat)
    (left right : Loom.Hw.Act) (current mid out : PortRefs)
    (leftCert rightCert : NextPortCert)
    (hleft : nextPortMatches wires table memory addressWidth dataWidth port left
      current mid leftCert = true)
    (hright : nextPortMatches wires table memory addressWidth dataWidth port right
      mid out rightCert = true) :
    nextPortMatches wires table memory addressWidth dataWidth port
      (.seq left right) current out (.seq mid leftCert rightCert) = true := by
  simp only [nextPortMatches, hleft, hright, Bool.true_and]

theorem nextPortMatches_ite_written
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (memory : String) (addressWidth dataWidth port : Nat)
    (guard : Loom.Hw.Expr 1) (thenAction elseAction : Loom.Hw.Act)
    (current out : PortRefs) (guardRef : Ref) (thenPort elsePort : PortRefs)
    (thenCert elseCert : NextPortCert)
    (hwrites : (Loom.Hw.Compile.writesPortB memory port thenAction ||
      Loom.Hw.Compile.writesPortB memory port elseAction) = true)
    (hguard : indexedExprMatches wires table
      (Loom.Hw.Compile.compileExpr guard) guardRef = true)
    (hthen : nextPortMatches wires table memory addressWidth dataWidth port
      thenAction current thenPort thenCert = true)
    (helse : nextPortMatches wires table memory addressWidth dataWidth port
      elseAction current elsePort elseCert = true)
    (hmux : indexedPortMuxMatches wires table addressWidth dataWidth guardRef
      thenPort elsePort out = true) :
    nextPortMatches wires table memory addressWidth dataWidth port
      (.ite guard thenAction elseAction) current out
      (.ite guardRef thenPort elsePort thenCert elseCert) = true := by
  simp [nextPortMatches, hwrites, hguard, hthen, helse, hmux]

theorem nextPortRulesMatches_nil
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (memory : String) (addressWidth dataWidth port : Nat) (current : PortRefs) :
    nextPortRulesMatches wires table memory addressWidth dataWidth port []
      current current .nil = true := by
  simp only [nextPortRulesMatches, beq_self_eq_true]

theorem nextPortRulesMatches_cons_named
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (memory : String) (addressWidth dataWidth port : Nat)
    (rule : Loom.Hw.Rule) (rules : List Loom.Hw.Rule)
    (current mid out : PortRefs) (head : NextPortCert)
    (tail : NextPortRulesCert)
    (hhead : nextPortMatches wires table memory addressWidth dataWidth port
      rule.body current mid head = true)
    (htail : nextPortRulesMatches wires table memory addressWidth dataWidth port
      rules mid out tail = true) :
    nextPortRulesMatches wires table memory addressWidth dataWidth port
      (rule :: rules) current out (.cons mid head tail) = true := by
  simp only [nextPortRulesMatches, hhead, htail, Bool.true_and]


/-- Resolve an SSA wire in logarithmic rope depth without constructing its
expanded µVerilog expression. All generator-provided information is checked. -/
def lookupWire? (program : Program) (table : WireTable)
    (name : String) : Option Wire := do
  let number ← wireNumber? name
  guard (table.leafSize > 0)
  let path ← balancedPath? table.leafCount (number / table.leafSize)
  let reference : Rope.Ref := ⟨path, number % table.leafSize⟩
  let wire ← program.wires.resolve? reference
  guard (wire.name == name)
  pure wire

private def lookupReg? (program : Program) (name : String) : Option Reg :=
  program.regs.find? fun reg => reg.name == name

private def nameWidth? (program : Program) (table : WireTable)
    (name : String) : Option Nat :=
  match lookupReg? program name with
  | some reg => some reg.width
  | none => (lookupWire? program table name).map (·.width)

/-- Evaluate a named concrete SSA expression against a source-shaped state,
without constructing an expression AST. Fuel bounds graph traversal; release
checks separately establish that every wire only names lower-numbered wires. -/
def evalNameFuel (program : Program) (table : WireTable)
    (state : Loom.Emit.MicroVerilog.St) : (fuel : Nat) → (name : String) →
      (width : Nat) → Option (BitVec width)
  | 0, _, _ => none
  | fuel + 1, name, width =>
    match lookupReg? program name with
    | some reg =>
        if h : reg.width = width then some (h ▸ state.regs name reg.width)
        else none
    | none => do
      let wire ← lookupWire? program table name
      guard (wire.width == width)
      let evalAt (operand : String) (operandWidth : Nat) :=
        evalNameFuel program table state fuel operand operandWidth
      let evalAny (operand : String) : Option (Sigma BitVec) := do
        let operandWidth ← nameWidth? program table operand
        pure ⟨operandWidth, ← evalAt operand operandWidth⟩
      match wire.rhs with
      | .lit actualWidth value => do
          guard (actualWidth == width)
          pure (BitVec.ofNat width value)
      | .ident source => do
          let ⟨_, value⟩ ← evalAny source
          pure (value.setWidth width)
      | .memRead mem address => do
          let header ← program.mems.find? fun candidate => candidate.name == mem
          guard (header.dataWidth == width)
          let address ← evalAt address header.addrWidth
          pure (state.mems mem address.toNat width)
      | .slice source hi lo => do
          guard (lo ≤ hi && hi + 1 - lo == width)
          let ⟨_, value⟩ ← evalAny source
          pure (value.extractLsb' lo width)
      | .not source => pure (~~~(← evalAt source width))
      | .bin op left right =>
          match op with
          | .and => pure ((← evalAt left width) &&& (← evalAt right width))
          | .or => pure ((← evalAt left width) ||| (← evalAt right width))
          | .xor => pure ((← evalAt left width) ^^^ (← evalAt right width))
          | .add => pure ((← evalAt left width) + (← evalAt right width))
          | .sub => pure ((← evalAt left width) - (← evalAt right width))
          | .shl => pure ((← evalAt left width) <<< (← evalAt right width).toNat)
          | .shr => pure ((← evalAt left width) >>> (← evalAt right width).toNat)
          | .eq => do
              if h : width = 1 then do
                let operandWidth ← nameWidth? program table left
                let leftValue ← evalAt left operandWidth
                let rightValue ← evalAt right operandWidth
                pure (h.symm ▸ if leftValue = rightValue then 1#1 else 0#1)
              else none
          | .ult => do
              if h : width = 1 then do
                let operandWidth ← nameWidth? program table left
                let leftValue ← evalAt left operandWidth
                let rightValue ← evalAt right operandWidth
                pure (h.symm ▸ if leftValue.ult rightValue then 1#1 else 0#1)
              else none
      | .slt left right => do
          if h : width = 1 then do
            let operandWidth ← nameWidth? program table left
            let leftValue ← evalAt left operandWidth
            let rightValue ← evalAt right operandWidth
            pure (h.symm ▸ if leftValue.slt rightValue then 1#1 else 0#1)
          else none
      | .mux condition yes no => do
          let conditionValue ← evalAt condition 1
          if conditionValue = 1#1 then evalAt yes width else evalAt no width
      | .sext amount source signBit => do
          let ⟨sourceWidth, value⟩ ← evalAny source
          guard (signBit + 1 == sourceWidth && sourceWidth + amount == width &&
            sourceWidth < width)
          pure (value.signExtend width)

/-- Successful symbolic lookup always returns a wire bearing the requested
name. This is the first local soundness fact used by the graph checker. -/
theorem lookupWire_name (program : Program) (table : WireTable)
    (name : String) (wire : Wire)
    (h : lookupWire? program table name = some wire) : wire.name = name := by
  unfold lookupWire? at h
  cases hnumber : wireNumber? name with
  | none => simp [hnumber] at h
  | some number =>
    by_cases hsize : table.leafSize > 0
    · cases hpath : balancedPath? table.leafCount
          (number / table.leafSize) with
      | none => simp [hnumber, hsize, hpath] at h
      | some path =>
        cases hwire : program.wires.resolve?
            ⟨path, number % table.leafSize⟩ with
        | none => simp [hnumber, hsize, hpath, hwire] at h
        | some actual =>
          by_cases hname : actual.name = name
          · simp [hnumber, hsize, hpath, hwire, guard, beq_iff_eq, hname] at h
            subst wire
            exact hname
          · simp [hnumber, hsize, hpath, hwire, guard, beq_iff_eq, hname] at h
            change (none : Option Wire) = some wire at h
            contradiction
    · simp [hnumber, hsize] at h
      change (none : Option Wire) = some wire at h
      contradiction

private def wireRhs? (program : Program) (table : WireTable)
    (name : String) (width : Nat) : Option Rhs := do
  let wire ← lookupWire? program table name
  guard (wire.width == width)
  pure wire.rhs

/-- Check a source EDSL expression directly against the named SSA graph.
Unlike `Program.elaborateEnv`, this never constructs an expanded µVerilog
expression. Recursion follows the source expression, while every concrete
edge is re-read from a checked rope address. -/
def exprMatches (program : Program) (table : WireTable) :
    {w : Nat} → Loom.Emit.MicroVerilog.Expr w → String → Bool
  | _, .reg _ sourceName, name => sourceName == name
  | w, .lit value, name =>
      match wireRhs? program table name w with
      | some (.lit actualWidth actualValue) =>
          actualWidth == w && actualValue == value.toNat
      | _ => false
  | w, .memRead _ mem address, name =>
      match wireRhs? program table name w with
      | some (.memRead actualMem actualAddress) =>
          actualMem == mem && exprMatches program table address actualAddress
      | _ => false
  | w, .and left right, name =>
      match wireRhs? program table name w with
      | some (.bin .and actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | w, .or left right, name =>
      match wireRhs? program table name w with
      | some (.bin .or actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | w, .xor left right, name =>
      match wireRhs? program table name w with
      | some (.bin .xor actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | w, .not value, name =>
      match wireRhs? program table name w with
      | some (.not actual) => exprMatches program table value actual
      | _ => false
  | w, .add left right, name =>
      match wireRhs? program table name w with
      | some (.bin .add actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | w, .sub left right, name =>
      match wireRhs? program table name w with
      | some (.bin .sub actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | w, .shl left right, name =>
      match wireRhs? program table name w with
      | some (.bin .shl actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | w, .shr left right, name =>
      match wireRhs? program table name w with
      | some (.bin .shr actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | _, .eq left right, name =>
      match wireRhs? program table name 1 with
      | some (.bin .eq actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | _, .ult left right, name =>
      match wireRhs? program table name 1 with
      | some (.bin .ult actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | _, .slt left right, name =>
      match wireRhs? program table name 1 with
      | some (.slt actualLeft actualRight) =>
          exprMatches program table left actualLeft &&
            exprMatches program table right actualRight
      | _ => false
  | w, .mux guard yes no, name =>
      match wireRhs? program table name w with
      | some (.mux actualGuard actualYes actualNo) =>
          exprMatches program table guard actualGuard &&
            exprMatches program table yes actualYes &&
            exprMatches program table no actualNo
      | _ => false
  | w, .slice value lo _, name =>
      match wireRhs? program table name w with
      | some (.slice actualValue hi actualLo) =>
          actualLo == lo && hi == lo + w - 1 &&
            exprMatches program table value actualValue
      | _ => false
  | w, @Loom.Emit.MicroVerilog.Expr.zext inputWidth value _, name =>
      match wireRhs? program table name w with
      | some (.ident actual) =>
          inputWidth ≤ w && exprMatches program table value actual
      | _ => false
  | w, @Loom.Emit.MicroVerilog.Expr.sext inputWidth value _, name =>
      match wireRhs? program table name w with
      | some (.sext amount actual signBit) =>
          inputWidth < w && amount == w - inputWidth &&
            signBit + 1 == inputWidth &&
            exprMatches program table value actual
      | _ => false

/-- Check one concrete register declaration and its named next-state root
against the reference source-design fold. This is independently decidable per
register, enabling bounded generated proof modules. -/
def registerMatchesAt (design : Loom.Hw.Design) (program : Program)
    (table : WireTable) (index : Nat) : Bool :=
  match design.regs[index]?, program.regs[index]? with
  | some source, some concrete =>
      source.name == concrete.name && source.width == concrete.width &&
      source.init.toNat == concrete.init &&
      exprMatches program table
        (design.rules.foldl
          (fun current rule => Loom.Hw.Compile.nextReg source.name
            source.width rule.body current)
          (.reg source.width source.name)) concrete.next
  | _, _ => false

/-- Numeric-reference form of `registerMatchesAt`, used by full artifacts. -/
def indexedRegisterMatchesAt (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (index : Nat) (root : Ref) : Bool :=
  match design.regs[index]?, program.regs[index]? with
  | some source, some concrete =>
      source.name == concrete.name && source.width == concrete.width &&
      source.init.toNat == concrete.init && concrete.next == root.render &&
      indexedExprMatches wires table
        (design.rules.foldl
          (fun current rule => Loom.Hw.Compile.nextReg source.name
            source.width rule.body current)
          (.reg source.width source.name)) root
  | _, _ => false

def indexedRegisterMetadataMatchesAt (design : Loom.Hw.Design)
    (program : Program) (index : Nat) (root : Ref) : Bool :=
  match design.regs[index]?, program.regs[index]? with
  | some source, some concrete =>
      source.name == concrete.name && source.width == concrete.width &&
      source.init.toNat == concrete.init && concrete.next == root.render
  | _, _ => false

structure RegisterRoot where
  index : Nat
  root : Ref
  deriving Repr, DecidableEq

def RegisterRoot.accepted (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (entry : RegisterRoot) : Bool :=
  indexedRegisterMatchesAt design program wires table entry.index entry.root

def registerRootsAccepted (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable) :
    List RegisterRoot → Bool
  | [] => true
  | root :: roots => root.accepted design program wires table &&
      registerRootsAccepted design program wires table roots

theorem registerRootsAccepted_head (design : Loom.Hw.Design)
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (root : RegisterRoot) (roots : List RegisterRoot)
    (h : registerRootsAccepted design program wires table (root :: roots) = true) :
    root.accepted design program wires table = true := by
  simp only [registerRootsAccepted, Bool.and_eq_true] at h
  exact h.1

theorem registerRootsAccepted_tail (design : Loom.Hw.Design)
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (root : RegisterRoot) (roots : List RegisterRoot)
    (h : registerRootsAccepted design program wires table (root :: roots) = true) :
    registerRootsAccepted design program wires table roots = true := by
  simp only [registerRootsAccepted, Bool.and_eq_true] at h
  exact h.2

/-- Check one concrete memory write port against the corresponding reference
compiler port, using only numeric SSA references. -/
def indexedMemoryPortMatchesAt (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (memoryIndex portIndex : Nat) (refs : PortRefs) : Bool :=
  match design.mems[memoryIndex]?, program.mems[memoryIndex]? with
  | some source, some concrete =>
      match concrete.writes[portIndex]? with
      | some write =>
          let compiled := Loom.Hw.Compile.compilePort design source.name
            source.addrWidth source.dataWidth portIndex
          source.name == concrete.name &&
          source.addrWidth == concrete.addrWidth &&
          source.dataWidth == concrete.dataWidth &&
          write.en == refs.en.render && write.addr == refs.addr.render &&
          write.data == refs.data.render &&
          indexedExprMatches wires table compiled.en refs.en &&
          indexedExprMatches wires table compiled.addr refs.addr &&
          indexedExprMatches wires table compiled.data refs.data
      | none => false
  | _, _ => false

/-- Check one bounded initialization leaf against the source memory function. -/
def memoryInitBlockMatches (source : Loom.Hw.MemDecl) (start : Nat) :
    List Nat → Bool
  | [] => true
  | value :: values => value == (source.init start).toNat &&
      memoryInitBlockMatches source (start + 1) values

/-- Metadata and complete initialized address space of one memory. -/
def indexedMemoryMatchesAt (design : Loom.Hw.Design) (program : Program)
    (memoryIndex : Nat) : Bool :=
  match design.mems[memoryIndex]?, program.mems[memoryIndex]? with
  | some source, some concrete =>
      source.name == concrete.name &&
      source.addrWidth == concrete.addrWidth &&
      source.dataWidth == concrete.dataWidth &&
      concrete.init.listLength == 2 ^ source.addrWidth &&
      concrete.writes.length == Loom.Hw.Compile.numPorts design source.name
  | _, _ => false

end Loom.Release.Symbolic
