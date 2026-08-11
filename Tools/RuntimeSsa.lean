-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate

/-!
# Compact runtime SSA input

The kernel-facing release witness is intentionally large and declarative.
Untrusted certificate generation instead reads this compact JSON projection,
avoiding native compilation of the generated Lean root.
-/

namespace Tools.RuntimeSsa

open Loom.Release

structure Rhs where
  op : String
  strings : Array String
  nums : Array Nat
  deriving Inhabited

structure Wire where
  name : String
  width : Nat
  rhs : Rhs
  deriving Inhabited

structure Reg where
  name : String
  width : Nat
  init : Nat
  next : String

structure Program where
  name : String
  regs : Array Reg
  wires : Array Wire

def ref? (name : String) : Option Loom.Release.Symbolic.Ref :=
  match Loom.Release.Symbolic.wireNumber? name with
  | some number => some (.wire number)
  | none => some (.reg name)

private def binaryOp? : String → Option Loom.Release.SSA.BinOp
  | "and" => some .and | "or" => some .or | "xor" => some .xor
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul
  | "udiv" => some .udiv | "urem" => some .urem | "shl" => some .shl
  | "shr" => some .shr | "eq" => some .eq | "ult" => some .ult
  | _ => none

def Rhs.toIndexed? (rhs : Rhs) : Option Loom.Release.Symbolic.IndexedRhs := do
  match rhs.op, rhs.strings.toList, rhs.nums.toList with
  | "lit", [], [width, value] => pure (.lit width value)
  | "ident", [value], [] => pure (.ident (← ref? value))
  | "memRead", [memory, address], [] =>
      pure (.memRead memory (← ref? address))
  | "slice", [value], [hi, lo] => pure (.slice (← ref? value) hi lo)
  | "not", [value], [] => pure (.not (← ref? value))
  | "slt", [left, right], [] => pure (.slt (← ref? left) (← ref? right))
  | "mux", [guard, yes, no], [] =>
      pure (.mux (← ref? guard) (← ref? yes) (← ref? no))
  | "sext", [value], [amount, signBit] =>
      pure (.sext amount (← ref? value) signBit)
  | op, [left, right], [] =>
      pure (.bin (← binaryOp? op) (← ref? left) (← ref? right))
  | _, _, _ => none

private def commaStrings (text : String) : Array String :=
  if text.isEmpty then #[] else text.splitOn "," |>.toArray

private def commaNats (text : String) : Option (Array Nat) := do
  if text.isEmpty then return #[]
  text.splitOn "," |>.mapM String.toNat? |>.map List.toArray

private inductive Entry where
  | reg (value : Reg)
  | wire (value : Wire)

private def parseFields (fields : Array String) : Except String Entry :=
  match fields.toList with
  | ["R", name, width, init, next] => do
      let some width := width.toNat? | throw "bad register width"
      let some init := init.toNat? | throw "bad register init"
      pure (.reg { name, width, init, next })
  | ["W", name, width, op, strings, nums] => do
      let some width := width.toNat? | throw "bad wire width"
      let some nums := commaNats nums | throw "bad wire numbers"
      pure (.wire
        { name, width, rhs := { op, strings := commaStrings strings, nums } })
  | _ => throw "bad runtime SSA record"

def load (path : System.FilePath) : IO Program := do
  let contents ← IO.FS.readBinFile path
  let mut index := 0
  let mut fieldStart := 0
  let mut fields : Array String := #[]
  let mut name := ""
  let mut sawHeader := false
  let mut regs := #[]
  let mut wires := #[]
  while index < contents.size do
    let byte := contents[index]!
    if byte == 9 || byte == 59 || byte == 10 then
      fields := fields.push (String.fromUTF8!
        (contents.extract fieldStart index))
      index := index + 1
      fieldStart := index
      if byte != 9 then
        if !sawHeader then
          if fields.size == 2 && fields[0]! == "LOOM_SSA_V1" then
            name := fields[1]!
            sawHeader := true
          else throw (IO.userError "invalid runtime SSA header")
        else
          match parseFields fields with
          | .ok (.reg value) => regs := regs.push value
          | .ok (.wire value) => wires := wires.push value
          | .error message => throw (IO.userError message)
        fields := #[]
    else index := index + 1
  unless sawHeader do throw (IO.userError "empty runtime SSA")
  pure { name, regs, wires }

end Tools.RuntimeSsa
