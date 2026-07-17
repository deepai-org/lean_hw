-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate

/-!
# Structural elaboration of symbolic SSA witnesses

This elaborator is keyed by `Ref`, not rendered strings. The raw/indexed rope
certificate separately proves that every structural reference renders to the
exact identifier present in the shipped text. Keeping semantic lookup
structural removes decimal parsing, string-map shadowing, and generator naming
conventions from the proof of behavior.
-/

namespace Loom.Release.Symbolic

open Loom.Release.SSA
open Loom.Emit.MicroVerilog

/-- A typed semantic environment for source registers and numbered SSA wires. -/
abbrev SemanticEnv := Ref → Option (Sigma Expr)

/-- Resolve a structural reference at an expected width. -/
def SemanticEnv.resolveAt (env : SemanticEnv) (reference : Ref)
    (width : Nat) : Option (Expr width) := do
  let ⟨actualWidth, value⟩ ← env reference
  if h : actualWidth = width then pure (h ▸ value) else none

/-- Initial environment containing source-register expressions only. -/
def SemanticEnv.initial (program : Program) : SemanticEnv
  | .reg name =>
      match program.regs.find? (fun reg => reg.name == name) with
      | some reg => some ⟨reg.width, .reg reg.width name⟩
      | none => none
  | .wire _ => none

/-- Add one numbered SSA value without affecting the disjoint register
namespace or any other wire number. -/
def SemanticEnv.insertWire (env : SemanticEnv) (number width : Nat)
    (value : Expr width) : SemanticEnv :=
  fun reference =>
    if reference = .wire number then some ⟨width, value⟩ else env reference

private def semanticBinSame (env : SemanticEnv) (width : Nat)
    (left right : Ref) (make : Expr width → Expr width → Expr width) :
    Option (Expr width) := do
  pure (make (← env.resolveAt left width) (← env.resolveAt right width))

private def semanticComparison (env : SemanticEnv) (resultWidth : Nat)
    (left right : Ref) (make : {width : Nat} → Expr width → Expr width → Expr 1) :
    Option (Expr resultWidth) := do
  guard (resultWidth == 1)
  let ⟨operandWidth, leftValue⟩ ← env left
  let rightValue ← env.resolveAt right operandWidth
  if h : (1 : Nat) = resultWidth then
    pure (h ▸ make leftValue rightValue)
  else none

/-- Elaborate one indexed RHS using structural references only. -/
def IndexedRhs.elaborate (program : Program) (env : SemanticEnv)
    (resultWidth : Nat) : IndexedRhs → Option (Expr resultWidth)
  | .lit literalWidth value => do
      guard (literalWidth == resultWidth)
      pure (.lit (BitVec.ofNat resultWidth value))
  | .ident reference => do
      let ⟨_, value⟩ ← env reference
      pure (.zext value resultWidth)
  | .memRead mem address => do
      let header ← program.mems.find? (fun candidate => candidate.name == mem)
      let address ← env.resolveAt address header.addrWidth
      if h : header.dataWidth = resultWidth then
        pure (h ▸ Expr.memRead header.dataWidth mem address)
      else none
  | .slice value hi lo => do
      guard (lo ≤ hi && hi + 1 - lo == resultWidth)
      let ⟨_, input⟩ ← env value
      pure (.slice input lo resultWidth)
  | .not value => do
      pure (.not (← env.resolveAt value resultWidth))
  | .bin op left right =>
      match op with
      | .and => semanticBinSame env resultWidth left right .and
      | .or => semanticBinSame env resultWidth left right .or
      | .xor => semanticBinSame env resultWidth left right .xor
      | .add => semanticBinSame env resultWidth left right .add
      | .sub => semanticBinSame env resultWidth left right .sub
      | .shl => semanticBinSame env resultWidth left right .shl
      | .shr => semanticBinSame env resultWidth left right .shr
      | .eq => semanticComparison env resultWidth left right (fun a b => .eq a b)
      | .ult => semanticComparison env resultWidth left right (fun a b => .ult a b)
  | .slt left right =>
      semanticComparison env resultWidth left right (fun a b => .slt a b)
  | .mux condition yes no => do
      pure (.mux (← env.resolveAt condition 1)
        (← env.resolveAt yes resultWidth) (← env.resolveAt no resultWidth))
  | .sext amount value signBit => do
      let ⟨inputWidth, input⟩ ← env value
      guard (signBit + 1 == inputWidth && inputWidth + amount == resultWidth &&
        inputWidth < resultWidth)
      pure (.sext input resultWidth)

/-- Elaborate a sequential leaf of numbered assignments. -/
def elaborateIndexedBlock (program : Program) :
    List IndexedWire → SemanticEnv → Option SemanticEnv
  | [], env => some env
  | wire :: rest, env => do
      let value ← wire.rhs.elaborate program env wire.width
      elaborateIndexedBlock program rest
        (env.insertWire wire.number wire.width value)

/-- Elaborate a balanced wire rope from left to right. -/
def elaborateIndexedRope (program : Program) :
    Rope (List IndexedWire) → SemanticEnv → Option SemanticEnv
  | .leaf wires, env => elaborateIndexedBlock program wires env
  | .node left right, env => do
      let env ← elaborateIndexedRope program left env
      elaborateIndexedRope program right env

/-- Build the complete structural semantic environment for a witness. -/
def elaborateIndexedEnv (program : Program)
    (wires : Rope (List IndexedWire)) : Option SemanticEnv :=
  elaborateIndexedRope program wires (SemanticEnv.initial program)

end Loom.Release.Symbolic
