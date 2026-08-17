-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Chan
import Loom.Hw.Declarations
import Loom.Core.Word

/-!
# Typed packed hardware values

`HwPacked` relates an ordinary Lean value to one exact-width hardware word.
The wrappers in this module are an authoring facade only: they lower directly
to Loom's existing `Expr`, `Reg`, `Mem`, `Chan`, and declaration types.

Layouts have no implicit padding. `PackedLayout` checks the
declaration-order/MSB-first convention; the core `PackedField` descriptor
records the resulting LSB offset and carries its static bounds proof.
-/

namespace Loom.Hw

universe u

/-- A semantic Lean value with one canonical packed hardware representation. -/
class HwPacked (α : Type u) where
  width : Nat
  pack : α → BitVec width
  unpack : BitVec width → α
  unpack_pack : ∀ value, unpack (pack value) = value
  pack_unpack : ∀ bits, pack (unpack bits) = bits

namespace HwPacked

/-- Fixed-width bit vectors are already canonical packed values. -/
instance (w : Nat) : HwPacked (BitVec w) where
  width := w
  pack := id
  unpack := id
  unpack_pack := by intro; rfl
  pack_unpack := by intro; rfl

@[simp] theorem width_bitVec (w : Nat) :
    HwPacked.width (BitVec w) = w := rfl

end HwPacked

/-- A packed value in combinational hardware. -/
structure PackedExpr (α : Type u) [HwPacked α] where
  bits : Expr (HwPacked.width α)

namespace PackedExpr

variable {α : Type u} [HwPacked α]

def fromBits (bits : Expr (HwPacked.width α)) : PackedExpr α := ⟨bits⟩

def ofValue (value : α) : PackedExpr α := ⟨.lit (HwPacked.pack value)⟩

/-- Interpret evaluated packed bits as their semantic Lean value. -/
def eval (value : PackedExpr α) (σ : St) : α :=
  HwPacked.unpack (value.bits.eval σ)

/-- Packed equality is exact bit equality. -/
def eq (left right : PackedExpr α) : Expr 1 := .eq left.bits right.bits

end PackedExpr

/-- A checked static field coordinate within a packed value. `lo` is
LSB-indexed and comes from the no-padding, MSB-first declaration layout.
Core fields themselves are scalar bit vectors. -/
structure PackedField (α : Type u) [HwPacked α] (fieldWidth : Nat) where
  name : String
  lo : Nat
  inBounds : lo + fieldWidth ≤ HwPacked.width α

namespace PackedField

variable {α : Type u} [HwPacked α] {fieldWidth : Nat}

/-- Read a field using the existing static slice expression. -/
def read (field : PackedField α fieldWidth) (value : PackedExpr α) :
    Expr fieldWidth :=
  .slice value.bits field.lo fieldWidth

/-- Extract a field from a semantic value using exactly the hardware layout. -/
def get (field : PackedField α fieldWidth) (value : α) : BitVec fieldWidth :=
  Loom.Word.extract field.lo fieldWidth (HwPacked.pack value)

theorem read_eval (field : PackedField α fieldWidth) (value : PackedExpr α)
    (state : St) :
    (field.read value).eval state = field.get (value.eval state) := by
  simp [read, get, PackedExpr.eval, Expr.eval, Loom.Word.extract,
    HwPacked.pack_unpack]

/-- Checked constructor for programmatic layouts. Generated layouts normally
carry the proof directly, while dynamic clients receive a named error. -/
def checked (name : String) (lo fieldWidth : Nat) :
    Except String (PackedField α fieldWidth) :=
  if inBounds : lo + fieldWidth ≤ HwPacked.width α then
    Except.ok ⟨name, lo, inBounds⟩
  else
    Except.error <| s!"packed field `{name}` [{lo + fieldWidth - 1}:{lo}] exceeds " ++
      s!"{HwPacked.width α}-bit value"

end PackedField

/-- A checked coordinate whose value is itself a packed semantic type.  Nested
packed records remain one flat bit vector in hardware; this descriptor retains
the semantic child type only at the authoring/proof boundary. -/
structure PackedSubfield (α : Type u) [HwPacked α]
    (β : Type u) [HwPacked β] where
  name : String
  lo : Nat
  inBounds : lo + HwPacked.width β ≤ HwPacked.width α

namespace PackedSubfield

variable {α : Type u} [HwPacked α] {β : Type u} [HwPacked β]

/-- Read a nested packed value by slicing its flat representation. -/
def read (field : PackedSubfield α β) (value : PackedExpr α) : PackedExpr β :=
  .fromBits (.slice value.bits field.lo (HwPacked.width β))

/-- Extract and decode a nested packed value from a semantic parent value. -/
def get (field : PackedSubfield α β) (value : α) : β :=
  HwPacked.unpack <| Loom.Word.extract field.lo (HwPacked.width β)
    (HwPacked.pack value)

theorem read_eval (field : PackedSubfield α β) (value : PackedExpr α)
    (state : St) :
    (field.read value).eval state = field.get (value.eval state) := by
  simp [read, get, PackedExpr.eval, Expr.eval, Loom.Word.extract,
    PackedExpr.fromBits, HwPacked.pack_unpack]

/-- View a nested coordinate as its underlying flat bit slice. -/
def bitsField (field : PackedSubfield α β) :
    PackedField α (HwPacked.width β) :=
  ⟨field.name, field.lo, field.inBounds⟩

/-- Compose a nested coordinate with one scalar child coordinate. -/
def childField {fieldWidth : Nat} (outer : PackedSubfield α β)
    (inner : PackedField β fieldWidth) : PackedField α fieldWidth where
  name := outer.name ++ "." ++ inner.name
  lo := outer.lo + inner.lo
  inBounds := by
    have innerBound := inner.inBounds
    have outerBound := outer.inBounds
    omega

/-- Compose two nested coordinates without changing the flat hardware word. -/
def childSubfield {γ : Type u} [HwPacked γ]
    (outer : PackedSubfield α β) (inner : PackedSubfield β γ) :
    PackedSubfield α γ where
  name := outer.name ++ "." ++ inner.name
  lo := outer.lo + inner.lo
  inBounds := by
    have innerBound := inner.inBounds
    have outerBound := outer.inBounds
    omega

end PackedSubfield

/-- A semantic record projection tied to its exact packed coordinate. Generated
record declarations produce one member per named field; the agreement law
prevents a field name or Lean projection from drifting away from the packed
layout used by hardware reads and writes. -/
structure PackedMember (α : Type u) [HwPacked α] (fieldWidth : Nat) where
  field : PackedField α fieldWidth
  project : α → BitVec fieldWidth
  project_eq_get : ∀ value, project value = field.get value

namespace PackedMember

variable {α : Type u} [HwPacked α] {fieldWidth : Nat}

def name (member : PackedMember α fieldWidth) : String := member.field.name

def read (member : PackedMember α fieldWidth) (value : PackedExpr α) :
    Expr fieldWidth :=
  member.field.read value

@[simp] theorem get_eq_project (member : PackedMember α fieldWidth)
    (value : α) : member.field.get value = member.project value :=
  (member.project_eq_get value).symm

end PackedMember

namespace PackedExpr

variable {α : Type u} [HwPacked α]

/-- Replace one statically bounded field while preserving all other bits.
This is a combinational record update; register field assignment uses the
same insertion algebra through `Act.writeSlice`. -/
def setField {fieldWidth : Nat} (value : PackedExpr α)
    (field : PackedField α fieldWidth) (replacement : Expr fieldWidth) :
    PackedExpr α :=
  let mask : BitVec (HwPacked.width α) :=
    (BitVec.allOnes fieldWidth).setWidth (HwPacked.width α) <<< field.lo
  ⟨.or (.and value.bits (.not (.lit mask)))
    (.shl (.zext replacement (HwPacked.width α))
      (.lit (BitVec.ofNat (HwPacked.width α) field.lo)))⟩

theorem setField_eval_bits {fieldWidth : Nat} (value : PackedExpr α)
    (field : PackedField α fieldWidth) (replacement : Expr fieldWidth)
    (state : St) :
    (value.setField field replacement).bits.eval state =
      Loom.Word.insert field.lo (replacement.eval state)
        (value.bits.eval state) := by
  have loFits : field.lo < 2 ^ HwPacked.width α := by
    have bound := field.inBounds
    have loLe : field.lo ≤ HwPacked.width α := by omega
    exact lt_of_le_of_lt loLe Nat.lt_two_pow_self
  simp [setField, Expr.eval, Loom.Word.insert, Nat.mod_eq_of_lt loFits]

def setMember {fieldWidth : Nat} (value : PackedExpr α)
    (member : PackedMember α fieldWidth) (replacement : Expr fieldWidth) :
    PackedExpr α :=
  value.setField member.field replacement

/-- Replace a whole nested packed field while preserving the parent's other
bits. -/
def setSubfield {β : Type u} [HwPacked β] (value : PackedExpr α)
    (field : PackedSubfield α β) (replacement : PackedExpr β) : PackedExpr α :=
  value.setField field.bitsField replacement.bits

end PackedExpr

/-- One top-level field span in a packed declaration. A nested semantic field
occupies its child's complete flat width. Coordinates are LSB-indexed, while
declaration order is recorded separately by `PackedLayout`. -/
structure PackedSpan where
  name : String
  width : Nat
  lo : Nat
  deriving Repr, DecidableEq

namespace PackedSpan

/-- Two field spans do not overlap. -/
def Disjoint (left right : PackedSpan) : Prop :=
  left.lo + left.width ≤ right.lo ∨ right.lo + right.width ≤ left.lo

instance : DecidableRel Disjoint := fun left right =>
  decidable_of_iff
    (left.lo + left.width ≤ right.lo ∨
      right.lo + right.width ≤ left.lo) (Iff.rfl)

end PackedSpan

/-- The collective layout contract for one packed type. Besides unique names
and static bounds, it records complete no-padding coverage and the canonical
first-field-most-significant placement. Syntax generation may create this
proof object, but all downstream users consume only these checked facts. -/
structure PackedLayout (α : Type u) [HwPacked α] where
  fields : List PackedSpan
  namesUnique : (fields.map (·.name)).Nodup
  inBounds : ∀ field ∈ fields,
    field.lo + field.width ≤ HwPacked.width α
  disjoint : fields.Pairwise PackedSpan.Disjoint
  complete : fields.foldr (fun field total => field.width + total) 0 =
    HwPacked.width α
  msbFirst : ∀ (index : Nat) (inRange : index < fields.length),
    (fields[index]'inRange).lo =
      (fields.drop (index + 1)).foldr
        (fun field total => field.width + total) 0

namespace PackedLayout

variable {α : Type u} [HwPacked α]

/-- Obtain the typed static field coordinate at one declaration index. -/
def fieldAt (layout : PackedLayout α) (index : Fin layout.fields.length) :
    PackedField α (layout.fields.get index).width :=
  let span := layout.fields.get index
  { name := span.name
    lo := span.lo
    inBounds := layout.inBounds span (List.get_mem layout.fields index) }

/-- Locate a field index for diagnostics and dynamic tooling. Generated source
normally refers to its statically named `fieldAt` projection directly. -/
def findIndex? (layout : PackedLayout α) (name : String) : Option Nat :=
  layout.fields.findIdx? (fun field => field.name = name)

end PackedLayout

/-- The one canonical checked layout associated with a packed semantic type.
Declaration front ends may supply this instance beside `HwPacked`; core
clients can therefore discover field geometry without duplicating it. -/
class HwPackedLayout (α : Type u) [HwPacked α] where
  layout : PackedLayout α

namespace HwPackedLayout

variable {α : Type u} [HwPacked α] [HwPackedLayout α]

def fieldAt (index : Fin (layout (α := α)).fields.length) :
    PackedField α ((layout (α := α)).fields.get index).width :=
  (layout (α := α)).fieldAt index

def findIndex? (name : String) : Option Nat :=
  (layout (α := α)).findIndex? name

end HwPackedLayout

/-- A width-indexed field list for constructing a packed expression. Each
`cons` places its expression above the remaining fields, so declaration order
is MSB-first by construction and introduces no padding. -/
inductive PackedFields : Nat → Type where
  | nil : PackedFields 0
  | cons {headWidth tailWidth : Nat} (head : Expr headWidth)
      (tail : PackedFields tailWidth) : PackedFields (headWidth + tailWidth)

namespace PackedFields

def bits : {width : Nat} → PackedFields width → Expr width
  | _, .nil => .lit 0#0
  | _, .cons head tail => Expr.concat head tail.bits

end PackedFields

namespace PackedExpr

variable {α : Type u} [HwPacked α]

/-- Build a packed value from an exactly width-matched, MSB-first field list. -/
def ofFields (fields : PackedFields (HwPacked.width α)) : PackedExpr α :=
  ⟨fields.bits⟩

end PackedExpr

/-- A register containing one packed value. -/
structure PackedReg (α : Type u) [HwPacked α] where
  bits : Reg (HwPacked.width α)
  deriving Repr

namespace PackedReg

variable {α : Type u} [HwPacked α]

def named (name : String) : PackedReg α := ⟨⟨name⟩⟩
def name (reg : PackedReg α) : String := reg.bits.name
def rd (reg : PackedReg α) : PackedExpr α := ⟨reg.bits.rd⟩
def set (reg : PackedReg α) (value : PackedExpr α) : Act := reg.bits.set value.bits
def setValue (reg : PackedReg α) (value : α) : Act := reg.set (.ofValue value)

def decl (reg : PackedReg α) (init : α) : RegDecl :=
  reg.bits.decl (HwPacked.pack init)

/-- A bounded partial packed-register update. The RHS remains a pre-cycle
read; preserved bits come from the current ordered-write accumulator. -/
def setField {fieldWidth : Nat} (reg : PackedReg α)
    (field : PackedField α fieldWidth) (value : Expr fieldWidth) : Act :=
  .writeSlice (HwPacked.width α) reg.name field.lo fieldWidth
    field.inBounds value

def setMember {fieldWidth : Nat} (reg : PackedReg α)
    (member : PackedMember α fieldWidth) (value : Expr fieldWidth) : Act :=
  reg.setField member.field value

/-- Assign a whole nested packed field with one bounded `writeSlice`. -/
def setSubfield {β : Type u} [HwPacked β] (reg : PackedReg α)
    (field : PackedSubfield α β) (value : PackedExpr β) : Act :=
  reg.setField field.bitsField value.bits

instance : CoeHead (PackedReg α) (PackedExpr α) := ⟨rd⟩

end PackedReg

/-- An immutable environment-owned packed input handle. It deliberately does
not expose `Reg.set`; read and declaration are its complete hardware API. -/
structure PackedInput (α : Type u) [HwPacked α] where
  name : String
  deriving Repr

namespace PackedInput

variable {α : Type u} [HwPacked α]

def named (name : String) : PackedInput α := ⟨name⟩

def rd (input : PackedInput α) : PackedExpr α :=
  ⟨.reg (HwPacked.width α) input.name⟩

def decl (input : PackedInput α) : InputDecl :=
  ⟨input.name, HwPacked.width α⟩

/-- Bind one semantic value to this input using the same canonical packer used
by registers, memories, channels, and observations. -/
def bind (input : PackedInput α) (value : α) : InputBinding :=
  InputBinding.of (Reg.mk input.name) (HwPacked.pack value)

instance : CoeHead (PackedInput α) (PackedExpr α) := ⟨rd⟩

end PackedInput

/-- A typed same-cycle output. Keeping the semantic type on the authoring
handle prevents two unrelated equal-width packed records from being confused;
`decl` is the sole erasure point to Loom's scalar `CombOutput`. -/
structure PackedOutput (α : Type u) [HwPacked α] where
  name : String
  value : PackedExpr α

namespace PackedOutput

variable {α : Type u} [HwPacked α]

def named (name : String) (value : PackedExpr α) : PackedOutput α :=
  ⟨name, value⟩

def decl (output : PackedOutput α) : CombOutput :=
  ⟨output.name, HwPacked.width α, output.value.bits⟩

def evalState (output : PackedOutput α) (state : St) : α :=
  output.value.eval state

/-- Observe this output through the ordinary open-design input installation
path, then recover its semantic packed value. -/
def evalOpen (output : PackedOutput α) (design : Design) (inputs : InEnv)
    (state : St) : α :=
  HwPacked.unpack (design.evalCombOutput inputs state output.decl)

end PackedOutput

/-- A memory whose element is one packed value. V1 intentionally offers only
whole-element writes; field writes would require a memory read-modify-write
and explicit port contract. -/
structure PackedMem (aw : Nat) (α : Type u) [HwPacked α] where
  bits : Mem aw (HwPacked.width α)
  deriving Repr

namespace PackedMem

variable {aw : Nat} {α : Type u} [HwPacked α]

def named (name : String) : PackedMem aw α := ⟨⟨name⟩⟩
def name (mem : PackedMem aw α) : String := mem.bits.name
def rd (mem : PackedMem aw α) (addr : Expr aw) : PackedExpr α :=
  ⟨mem.bits.rd addr⟩
def write (mem : PackedMem aw α) (port : Nat) (addr : Expr aw)
    (value : PackedExpr α) : Act :=
  mem.bits.write port addr value.bits
def writeValue (mem : PackedMem aw α) (port : Nat) (addr : Expr aw)
    (value : α) : Act :=
  mem.write port addr (.ofValue value)
def decl (mem : PackedMem aw α) (init : Nat → α) : MemDecl :=
  mem.bits.decl (fun address => HwPacked.pack (init address))

end PackedMem

/-- A channel carrying one packed value over the unchanged scalar channel
implementation and CDC realization machinery. -/
structure PackedChan (α : Type u) [HwPacked α] where
  bits : Chan (HwPacked.width α)
  deriving Repr

namespace PackedChan

variable {α : Type u} [HwPacked α]

def named (name : String) (depth : Nat := 1)
    (policy : FullCoTickPolicy := .exchange) : PackedChan α :=
  ⟨⟨name, depth, policy⟩⟩
def canEnq (channel : PackedChan α) : Expr 1 := channel.bits.canEnq
def enq (channel : PackedChan α) (value : PackedExpr α) : Act :=
  channel.bits.enq value.bits
def enqValue (channel : PackedChan α) (value : α) : Act :=
  channel.enq (.ofValue value)
def canDeq (channel : PackedChan α) : Expr 1 := channel.bits.canDeq
def deq (channel : PackedChan α) : PackedExpr α := ⟨channel.bits.deq⟩
def pop (channel : PackedChan α) : Act := channel.bits.pop
def withSource (channel : PackedChan α) (design : Design) : Design :=
  channel.bits.withSource design
def withSink (channel : PackedChan α) (design : Design) : Design :=
  channel.bits.withSink design

end PackedChan

namespace Declarations

/-- Add packed state while deriving reset bits from the canonical packer. -/
def addPackedReg {α : Type u} [HwPacked α] (decls : Declarations)
    (reg : PackedReg α) (init : α) (exported : Bool := false) : Declarations :=
  { decls with
    regs := decls.regs ++ [reg.decl init]
    outputs := if exported then decls.outputs ++ [reg.name] else decls.outputs }

def addPackedInput {α : Type u} [HwPacked α] (decls : Declarations)
    (input : PackedInput α) : Declarations :=
  { decls with inputs := decls.inputs ++ [input.decl] }

def addPackedCombOutput {α : Type u} [HwPacked α] (decls : Declarations)
    (name : String) (value : PackedExpr α) : Declarations :=
  decls.addCombOutput name value.bits

def addPackedOutput {α : Type u} [HwPacked α] (decls : Declarations)
    (output : PackedOutput α) : Declarations :=
  { decls with combOutputs := decls.combOutputs ++ [output.decl] }

def addPackedMem {aw : Nat} {α : Type u} [HwPacked α]
    (decls : Declarations) (mem : PackedMem aw α) (init : Nat → α)
    (syncRead : Bool := false) (ackInit : Bool := false) : Declarations :=
  decls.addMem mem.bits (fun address => HwPacked.pack (init address))
    syncRead ackInit

end Declarations

end Loom.Hw
