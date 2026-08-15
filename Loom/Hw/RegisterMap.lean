-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component

/-!
# Typed register maps

A register map is ordinary verified-library data. Typed entries prevent direct
reads or writes that their access policy forbids; an erased dependent
declaration then drives bus decode, reset declarations, documentation, and
software constants from the same source.
-/

namespace Loom.Hw

universe u

namespace RegisterMap

inductive Access where
  | readOnly
  | writeOnly
  | readWrite
  deriving Repr, DecidableEq, BEq

namespace Access

def readable : Access → Bool
  | .readOnly | .readWrite => true
  | .writeOnly => false

def writable : Access → Bool
  | .writeOnly | .readWrite => true
  | .readOnly => false

end Access

/-- Evidence required by the typed entry read API. -/
class CanRead (access : Access) : Prop where
  allowed : access.readable = true

/-- Evidence required by the typed entry write API. -/
class CanWrite (access : Access) : Prop where
  allowed : access.writable = true

instance : CanRead .readOnly := ⟨rfl⟩
instance : CanRead .readWrite := ⟨rfl⟩
instance : CanWrite .writeOnly := ⟨rfl⟩
instance : CanWrite .readWrite := ⟨rfl⟩

inductive WriteBehavior where
  | replace
  | oneToClear
  | oneToSet
  deriving Repr, DecidableEq, BEq

inductive ReadBehavior where
  | observe
  | clear
  deriving Repr, DecidableEq, BEq

/-- One semantically typed software-visible register. -/
structure Entry (access : Access) (addressWidth dataWidth : Nat)
    (α : Type u) [HwPacked α] where
  name : String
  address : BitVec addressWidth
  register : Reg (HwPacked.width α)
  reset : α
  fits : HwPacked.width α ≤ dataWidth
  writeBehavior : WriteBehavior := .replace
  readBehavior : ReadBehavior := .observe

namespace Entry

def read {access : Access} {addressWidth dataWidth : Nat}
    {α : Type u} [HwPacked α] [CanRead access]
    (entry : Entry access addressWidth dataWidth α) : PackedExpr α :=
  ⟨entry.register.rd⟩

private def writtenValue {width : Nat} (behavior : WriteBehavior)
    (current incoming : Expr width) : Expr width :=
  match behavior with
  | .replace => incoming
  | .oneToClear => .and current (.not incoming)
  | .oneToSet => .or current incoming

def write {access : Access} {addressWidth dataWidth : Nat}
    {α : Type u} [HwPacked α] [CanWrite access]
    (entry : Entry access addressWidth dataWidth α)
    (value : PackedExpr α) : Act :=
  entry.register.set
    (writtenValue entry.writeBehavior entry.register.rd value.bits)

end Entry

/-- Erased dependent entry used by generators. Width remains dependent in the
reset value and register handle, so decode cannot accidentally write a value
of a different width. -/
structure Decl (addressWidth dataWidth : Nat) where
  name : String
  address : BitVec addressWidth
  width : Nat
  register : Reg width
  reset : BitVec width
  fits : width ≤ dataWidth
  access : Access
  writeBehavior : WriteBehavior
  readBehavior : ReadBehavior

def Entry.decl {access : Access} {addressWidth dataWidth : Nat}
    {α : Type u} [HwPacked α]
    (entry : Entry access addressWidth dataWidth α) : Decl addressWidth dataWidth :=
  { name := entry.name
    address := entry.address
    width := HwPacked.width α
    register := entry.register
    reset := HwPacked.pack entry.reset
    fits := entry.fits
    access
    writeBehavior := entry.writeBehavior
    readBehavior := entry.readBehavior }

structure Map (addressWidth dataWidth : Nat) where
  name : String
  entries : List (Decl addressWidth dataWidth)

namespace Map

def locallyValidB {addressWidth dataWidth : Nat}
    (map : Map addressWidth dataWidth) : Bool :=
  let names := map.entries.map (·.name)
  let registerNames := map.entries.map (·.register.name)
  let addresses := map.entries.map (·.address)
  !map.name.isEmpty &&
    map.entries.all (fun entry =>
      !entry.name.isEmpty && !entry.register.name.isEmpty && entry.width > 0) &&
    names.eraseDups.length == names.length &&
    registerNames.eraseDups.length == registerNames.length &&
    addresses.eraseDups.length == addresses.length

def declarations {addressWidth dataWidth : Nat}
    (map : Map addressWidth dataWidth) : List RegDecl :=
  map.entries.map fun entry => entry.register.decl entry.reset

private def selected {addressWidth dataWidth : Nat}
    (address : Expr addressWidth) (entry : Decl addressWidth dataWidth) : Expr 1 :=
  .eq address (.lit entry.address)

structure ReadResult (dataWidth : Nat) where
  hit : Expr 1
  data : Expr dataWidth

/-- Combinational read decode. Write-only entries do not hit. Narrow entries
are zero-extended; the single declaration fixes that policy. -/
def decodeRead {addressWidth dataWidth : Nat}
    (map : Map addressWidth dataWidth) (address : Expr addressWidth) :
    ReadResult dataWidth :=
  let readable := map.entries.filter (·.access.readable)
  let hit := orTree <| readable.map (selected address)
  let data := readable.foldr (fun entry fallback =>
    .mux (selected address entry)
      (.zext entry.register.rd dataWidth) fallback) (.lit 0)
  ⟨hit, data⟩

private def busWrite {addressWidth dataWidth : Nat}
    (address : Expr addressWidth) (data : Expr dataWidth)
    (entry : Decl addressWidth dataWidth) : Act :=
  let incoming : Expr entry.width := .slice data 0 entry.width
  let value := Entry.writtenValue entry.writeBehavior entry.register.rd incoming
  .ite (selected address entry) (entry.register.set value) .skip

/-- Decode one accepted bus write. Address uniqueness makes at most one entry
eligible; write-only entries are naturally included. -/
def decodeWrite {addressWidth dataWidth : Nat}
    (map : Map addressWidth dataWidth) (accepted : Expr 1)
    (address : Expr addressWidth) (data : Expr dataWidth) : Act :=
  .ite accepted
    (actSeq <| (map.entries.filter (·.access.writable)).map
      (busWrite address data)) .skip

/-- Apply clear-on-read side effects for one accepted read. -/
def decodeReadEffects {addressWidth dataWidth : Nat}
    (map : Map addressWidth dataWidth) (accepted : Expr 1)
    (address : Expr addressWidth) : Act :=
  .ite accepted
    (actSeq <| (map.entries.filter fun entry =>
      entry.access.readable && entry.readBehavior == .clear).map fun entry =>
        .ite (selected address entry) (entry.register.set (.lit 0)) .skip)
    .skip

/-- One bus event. Read side effects occur first and a simultaneous write wins
explicitly, matching the returned `Act.seq` order. -/
def transact {addressWidth dataWidth : Nat}
    (map : Map addressWidth dataWidth)
    (readAccepted writeAccepted : Expr 1)
    (address : Expr addressWidth) (writeData : Expr dataWidth) : Act :=
  .seq (map.decodeReadEffects readAccepted address)
    (map.decodeWrite writeAccepted address writeData)

structure SoftwareConstant where
  name : String
  address : Nat
  deriving Repr, DecidableEq, BEq

def softwareConstants {addressWidth dataWidth : Nat}
    (map : Map addressWidth dataWidth) : List SoftwareConstant :=
  map.entries.map fun entry => ⟨entry.name, entry.address.toNat⟩

private def accessName : Access → String
  | .readOnly => "read-only"
  | .writeOnly => "write-only"
  | .readWrite => "read/write"

private def writeBehaviorName : WriteBehavior → String
  | .replace => "replace"
  | .oneToClear => "one-to-clear"
  | .oneToSet => "one-to-set"

private def readBehaviorName : ReadBehavior → String
  | .observe => "observe"
  | .clear => "clear-on-read"

/-- Stable Markdown generated from the same entries as hardware decode. -/
def markdown {addressWidth dataWidth : Nat}
    (map : Map addressWidth dataWidth) : String :=
  "# Register map `" ++ map.name ++ "`\n\n" ++
    "| Name | Address | Width | Access | Write | Read |\n" ++
    "| --- | ---: | ---: | --- | --- | --- |\n" ++
    String.intercalate "\n" (map.entries.map fun entry =>
      s!"| `{entry.name}` | 0x{Nat.toDigits 16 entry.address.toNat |> String.ofList} | {entry.width} | {accessName entry.access} | {writeBehaviorName entry.writeBehavior} | {readBehaviorName entry.readBehavior} |") ++
    "\n"

end Map

end RegisterMap

end Loom.Hw
