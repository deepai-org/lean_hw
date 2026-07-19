-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CompileWhole

/-!
# Shared register-update plans

A `RegPlan` retains only the writes and conditionals relevant to one register.
`Plans` constructs all of those projections together during one traversal of
the source action.  Release validation can therefore check this shared plan
once and validate each concrete SSA root against a small plan, without walking
the complete processor action again.
-/

namespace Loom.Hw.Compile

open Loom.Hw

set_option maxRecDepth 10000

/-- The source-level fragment that determines one register's next value. -/
inductive RegPlan (width : Nat) where
  | same
  | write (value : Loom.Hw.Expr width)
  | seq (left right : RegPlan width)
  | ite (guard : Loom.Hw.Expr 1) (thenPlan elsePlan : RegPlan width)

namespace RegPlan

/-- Interpret a register plan through the established expression compiler. -/
def apply {width : Nat} : RegPlan width → MV.Expr width → MV.Expr width
  | .same, current => current
  | .write value, _ => compileExpr value
  | .seq left right, current => right.apply (left.apply current)
  | .ite guard thenPlan elsePlan, current =>
      .mux (compileExpr guard) (thenPlan.apply current)
        (elsePlan.apply current)

/-- Smart sequential composition, eliminating identity fragments. -/
def compose {width : Nat} : RegPlan width → RegPlan width → RegPlan width
  | .same, right => right
  | left, .same => left
  | left, right => .seq left right

/-- Smart conditional construction matching `nextReg`'s pruning rule. -/
def branch {width : Nat} (guard : Loom.Hw.Expr 1) :
    RegPlan width → RegPlan width → RegPlan width
  | .same, .same => .same
  | thenPlan, elsePlan => .ite guard thenPlan elsePlan

/-- Whether a plan contains any write. -/
def active {width : Nat} : RegPlan width → Bool
  | .same => false
  | _ => true

/-- The conventional single-register projection, used only to state and prove
the correspondence theorem.  Release computation uses `Plans.ofAction`. -/
def ofAction (name : String) (width : Nat) : Act → RegPlan width
  | .skip => .same
  | .seq left right =>
      (ofAction name width left).compose (ofAction name width right)
  | .ite guard thenAction elseAction =>
      branch guard (ofAction name width thenAction)
        (ofAction name width elseAction)
  | .write actualWidth actualName value =>
      if actualName = name then
        if h : actualWidth = width then .write (h ▸ value) else .same
      else .same
  | .memWrite .. => .same

theorem apply_compose {width : Nat} (left right : RegPlan width)
    (current : MV.Expr width) :
    (left.compose right).apply current = right.apply (left.apply current) := by
  cases left <;> cases right <;> rfl

theorem apply_branch {width : Nat} (guard : Loom.Hw.Expr 1)
    (thenPlan elsePlan : RegPlan width) (current : MV.Expr width) :
    (branch guard thenPlan elsePlan).apply current =
      if thenPlan.active || elsePlan.active then
        .mux (compileExpr guard) (thenPlan.apply current)
          (elsePlan.apply current)
      else current := by
  cases thenPlan <;> cases elsePlan <;> rfl

theorem active_ofAction (action : Act) (name : String) (width : Nat) :
    (ofAction name width action).active = writesRegB name width action := by
  induction action with
  | skip | memWrite => rfl
  | seq left right leftIH rightIH =>
      cases leftPlan : ofAction name width left <;>
        cases rightPlan : ofAction name width right <;>
        simp_all [ofAction, compose, active, writesRegB]
  | ite guard thenAction elseAction thenIH elseIH =>
      cases thenPlan : ofAction name width thenAction <;>
        cases elsePlan : ofAction name width elseAction <;>
        simp_all [ofAction, branch, active, writesRegB]
  | write actualWidth actualName value =>
      by_cases nameEq : actualName = name
      · subst actualName
        by_cases widthEq : actualWidth = width <;>
          simp [ofAction, active, writesRegB, widthEq]
      · simp [ofAction, active, writesRegB, nameEq]

/-- A projected plan denotes exactly the established `nextReg` compiler. -/
theorem apply_ofAction (action : Act) (name : String) (width : Nat)
    (current : MV.Expr width) :
    (ofAction name width action).apply current =
      nextReg name width action current := by
  induction action generalizing current with
  | skip => rfl
  | seq left right leftIH rightIH =>
      simp only [ofAction, apply_compose, nextReg]
      rw [rightIH, leftIH]
  | ite guard thenAction elseAction thenIH elseIH =>
      simp only [ofAction, apply_branch, nextReg]
      rw [active_ofAction thenAction name width,
        active_ofAction elseAction name width, thenIH, elseIH]
  | write actualWidth actualName value =>
      by_cases nameEq : actualName = name
      · subst actualName
        by_cases widthEq : actualWidth = width
        · subst actualWidth
          simp [ofAction, nextReg, apply]
        · simp [ofAction, nextReg, apply, widthEq]
      · simp [ofAction, nextReg, apply, nameEq]
  | memWrite => rfl

end RegPlan

/-- A width-indexed register plan for every declaration, in declaration
order. -/
inductive Plans : List RegDecl → Type where
  | nil : Plans []
  | cons {register : RegDecl} {registers : List RegDecl}
      (head : RegPlan register.width) (tail : Plans registers) :
      Plans (register :: registers)

namespace Plans

def same : (registers : List RegDecl) → Plans registers
  | [] => .nil
  | _ :: registers => .cons .same (same registers)

def compose : {registers : List RegDecl} →
    Plans registers → Plans registers → Plans registers
  | [], .nil, .nil => .nil
  | _ :: _, .cons left lefts, .cons right rights =>
      .cons (left.compose right) (compose lefts rights)

def branch (guard : Loom.Hw.Expr 1) : {registers : List RegDecl} →
    Plans registers → Plans registers → Plans registers
  | [], .nil, .nil => .nil
  | _ :: _, .cons thenPlan thenPlans, .cons elsePlan elsePlans =>
      .cons (RegPlan.branch guard thenPlan elsePlan)
        (branch guard thenPlans elsePlans)

def write (actualWidth : Nat) (actualName : String)
    (value : Loom.Hw.Expr actualWidth) :
    (registers : List RegDecl) → Plans registers
  | [] => .nil
  | register :: registers =>
      if actualName = register.name then
        if widthEq : actualWidth = register.width then
          .cons (.write (widthEq ▸ value)) (write actualWidth actualName value registers)
        else .cons .same (write actualWidth actualName value registers)
      else .cons .same (write actualWidth actualName value registers)

/-- Construct every register projection in one source-action traversal. -/
def ofAction (registers : List RegDecl) : Act → Plans registers
  | .skip => same registers
  | .seq left right =>
      (ofAction registers left).compose (ofAction registers right)
  | .ite guard thenAction elseAction =>
      branch guard (ofAction registers thenAction) (ofAction registers elseAction)
  | .write width name value => write width name value registers
  | .memWrite .. => same registers

/-- Pointwise specification of an action-wide plan. -/
def Projects (action : Act) : {registers : List RegDecl} → Plans registers → Prop
  | [], .nil => True
  | register :: _, .cons head tail =>
      head = RegPlan.ofAction register.name register.width action ∧
        Projects action tail

private theorem projects_same (registers : List RegDecl) :
    Projects .skip (same registers) := by
  induction registers with
  | nil => trivial
  | cons register registers ih => exact ⟨rfl, ih⟩

private theorem projects_memWrite (aw dw : Nat) (memory : String) (port : Nat)
    (address : Loom.Hw.Expr aw) (value : Loom.Hw.Expr dw)
    (registers : List RegDecl) :
    Projects (.memWrite aw dw memory port address value) (same registers) := by
  induction registers with
  | nil => trivial
  | cons register registers ih => exact ⟨rfl, ih⟩

private theorem projects_compose (left right : Act) {registers : List RegDecl}
    {leftPlans rightPlans : Plans registers}
    (leftProjects : Projects left leftPlans)
    (rightProjects : Projects right rightPlans) :
    Projects (.seq left right) (leftPlans.compose rightPlans) := by
  induction registers with
  | nil => cases leftPlans; cases rightPlans; trivial
  | cons register registers ih =>
      cases leftPlans with
      | cons leftHead leftTail =>
        cases rightPlans with
        | cons rightHead rightTail =>
          rw [leftProjects.1, rightProjects.1]
          exact ⟨rfl, ih leftProjects.2 rightProjects.2⟩

private theorem projects_branch (guard : Loom.Hw.Expr 1)
    (thenAction elseAction : Act) {registers : List RegDecl}
    {thenPlans elsePlans : Plans registers}
    (thenProjects : Projects thenAction thenPlans)
    (elseProjects : Projects elseAction elsePlans) :
    Projects (.ite guard thenAction elseAction)
      (branch guard thenPlans elsePlans) := by
  induction registers with
  | nil => cases thenPlans; cases elsePlans; trivial
  | cons register registers ih =>
      cases thenPlans with
      | cons thenHead thenTail =>
        cases elsePlans with
        | cons elseHead elseTail =>
          rw [thenProjects.1, elseProjects.1]
          exact ⟨rfl, ih thenProjects.2 elseProjects.2⟩

private theorem projects_write (actualWidth : Nat) (actualName : String)
    (value : Loom.Hw.Expr actualWidth) (registers : List RegDecl) :
    Projects (.write actualWidth actualName value)
      (write actualWidth actualName value registers) := by
  induction registers with
  | nil => trivial
  | cons register registers ih =>
      by_cases nameEq : actualName = register.name
      · subst actualName
        by_cases widthEq : actualWidth = register.width
        · subst actualWidth
          simp [write, Projects, RegPlan.ofAction, ih]
        · simp [write, Projects, RegPlan.ofAction, widthEq, ih]
      · simp [write, Projects, RegPlan.ofAction, nameEq, ih]

/-- The shared construction computes all conventional projections exactly. -/
theorem ofAction_projects (registers : List RegDecl) (action : Act) :
    Projects action (ofAction registers action) := by
  induction action with
  | skip => exact projects_same registers
  | seq left right leftIH rightIH =>
      exact projects_compose left right leftIH rightIH
  | ite guard thenAction elseAction thenIH elseIH =>
      exact projects_branch guard thenAction elseAction thenIH elseIH
  | write width name value => exact projects_write width name value registers
  | memWrite aw dw memory port address value =>
      exact projects_memWrite aw dw memory port address value registers

end Plans

end Loom.Hw.Compile
