-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile

/-!
# Whole-register compilation

`Compile.nextReg` presents compilation one register at a time.  That is a
convenient reference definition, but a release checker which follows that
presentation traverses the same action once for every register.  This module
transposes the definition: an action transforms the complete environment of
next-value expressions in one structural pass.

The pointwise theorem at the end is the bridge back to the established
compiler.  A finite, indexed release checker can refine `nextRegs`; it does
not need to validate hundreds of independent `nextReg` traversals.
-/

namespace Loom.Hw.Compile

open Loom.Hw

/-- A symbolic next-value for every register name and width. -/
abbrev RegExprEnv := (name : String) → (width : Nat) → MV.Expr width

/-- Replace one well-typed entry in a symbolic register environment. -/
def RegExprEnv.set (env : RegExprEnv) (name : String) {width : Nat}
    (value : MV.Expr width) : RegExprEnv :=
  fun actualName actualWidth =>
    if actualName = name then
      if h : width = actualWidth then h ▸ value
      else env actualName actualWidth
    else env actualName actualWidth

/-- Compile an action over all register next-values simultaneously.

The result is extensionally the family of `nextReg` computations, but this
form exposes the shared action traversal needed by the release validator.
Memory writes do not affect this register environment. -/
def nextRegs : Act → RegExprEnv → RegExprEnv
  | .skip, current => current
  | .seq left right, current => nextRegs right (nextRegs left current)
  | .ite guard thenAction elseAction, current =>
      let thenRegs := nextRegs thenAction current
      let elseRegs := nextRegs elseAction current
      fun name width =>
        if writesRegB name width thenAction ||
            writesRegB name width elseAction then
          .mux (compileExpr guard) (thenRegs name width)
            (elseRegs name width)
        else current name width
  | .write _ name value, current =>
      current.set name (compileExpr value)
  | .writeSlice width name lo _ _ value, current =>
      current.set name (insertExpr lo (compileExpr value) (current name width))
  | .memWrite .., current => current

/-- The whole-environment action compiler agrees pointwise with the existing
reference compiler. -/
theorem nextRegs_apply (action : Act) (current : RegExprEnv)
    (name : String) (width : Nat) :
    nextRegs action current name width =
      nextReg name width action (current name width) := by
  induction action generalizing current with
  | skip => rfl
  | seq left right leftIH rightIH =>
      simp only [nextRegs, nextReg]
      rw [rightIH, leftIH]
  | ite guard thenAction elseAction thenIH elseIH =>
      simp only [nextRegs, nextReg]
      split
      · simp only [thenIH, elseIH]
      · rfl
  | write actualWidth actualName value =>
      by_cases nameEq : actualName = name
      · subst actualName
        simp [nextRegs, nextReg, RegExprEnv.set]
      · have reverseNameEq : name ≠ actualName := fun equal => nameEq equal.symm
        simp [nextRegs, nextReg, RegExprEnv.set, nameEq, reverseNameEq]
  | writeSlice actualWidth actualName lo fieldWidth inBounds value =>
      by_cases nameEq : actualName = name
      · subst actualName
        by_cases widthEq : actualWidth = width
        · subst width
          simp [nextRegs, nextReg, RegExprEnv.set]
        · simp [nextRegs, nextReg, RegExprEnv.set, widthEq]
      · have reverseNameEq : name ≠ actualName := fun equal => nameEq equal.symm
        simp [nextRegs, nextReg, RegExprEnv.set, nameEq, reverseNameEq]
  | memWrite => rfl

/-- Compile an ordered rule list over the entire symbolic register state. -/
def nextRuleRegs (rules : List Rule) (current : RegExprEnv) : RegExprEnv :=
  rules.foldl (fun state rule => nextRegs rule.body state) current

/-- Pointwise agreement also holds for the ordered rule fold used by
`Compile.compile`. -/
theorem nextRuleRegs_apply (rules : List Rule) (current : RegExprEnv)
    (name : String) (width : Nat) :
    nextRuleRegs rules current name width =
      rules.foldl
        (fun value rule => nextReg name width rule.body value)
        (current name width) := by
  induction rules generalizing current with
  | nil => rfl
  | cons rule rules ih =>
      simp only [nextRuleRegs, List.foldl_cons]
      change nextRuleRegs rules (nextRegs rule.body current) name width = _
      rw [ih, nextRegs_apply]

/-- Initial symbolic state used by the reference compiler. -/
def initialRegExprs : RegExprEnv := fun name width => .reg width name

/-- The whole-state root for a source register is definitionally connected
to the next expression stored by `Compile.compile`. -/
theorem compiledRegisterRoot (design : Design) (source : RegDecl) :
    nextRuleRegs design.rules initialRegExprs source.name source.width =
      design.rules.foldl
        (fun value rule => nextReg source.name source.width rule.body value)
        (.reg source.width source.name) :=
  nextRuleRegs_apply design.rules initialRegExprs source.name source.width

end Loom.Hw.Compile
