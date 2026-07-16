-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SSA
import Loom.Hw.Compile

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

/-- Compact layout proof data for fixed-size wire leaves. Only one path per
leaf is stored; the numeric SSA suffix determines the leaf and offset.
The last leaf may be shorter. -/
structure WireTable where
  leafSize : Nat
  paths : Array (List Bool)
  deriving Repr, DecidableEq

/-- Decode the deliberately tiny release-witness naming convention. -/
def wireNumber? (name : String) : Option Nat := do
  guard (name.startsWith "n")
  (name.drop 1).toNat?

/-- Resolve an SSA wire in logarithmic rope depth without constructing its
expanded µVerilog expression. All generator-provided information is checked. -/
def lookupWire? (program : Program) (table : WireTable)
    (name : String) : Option Wire := do
  let number ← wireNumber? name
  guard (table.leafSize > 0)
  let path ← table.paths[number / table.leafSize]?
  let reference : Rope.Ref := ⟨path, number % table.leafSize⟩
  let wire ← program.wires.resolve? reference
  guard (wire.name == name)
  pure wire

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
    · cases hpath : table.paths[number / table.leafSize]? with
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
    {w : Nat} → Loom.Hw.Expr w → String → Bool
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
  | w, @Loom.Hw.Expr.zext inputWidth value _, name =>
      match wireRhs? program table name w with
      | some (.ident actual) =>
          inputWidth ≤ w && exprMatches program table value actual
      | _ => false
  | w, @Loom.Hw.Expr.sext inputWidth value _, name =>
      match wireRhs? program table name w with
      | some (.sext amount actual signBit) =>
          inputWidth < w && amount == w - inputWidth &&
            signBit + 1 == inputWidth &&
            exprMatches program table value actual
      | _ => false

end Loom.Release.Symbolic
