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

/-- Forget a cached concrete spelling when looking up semantic wire identity. -/
def SemanticEnv.get (env : SemanticEnv) : Ref → Option (Sigma Expr)
  | .namedWire number _ => env (.wire number)
  | reference => env reference

/-- Resolve a structural reference at an expected width. -/
def SemanticEnv.resolveAt (env : SemanticEnv) (reference : Ref)
    (width : Nat) : Option (Expr width) := do
  let ⟨actualWidth, value⟩ ← env.get reference
  if h : actualWidth = width then pure (h ▸ value) else none

/-- Initial environment containing source-register expressions only. -/
def SemanticEnv.initial (program : Program) : SemanticEnv
  | .reg name =>
      match program.regs.find? (fun reg => reg.name == name) with
      | some reg => some ⟨reg.width, .reg reg.width name⟩
      | none => none
  | .wire _ => none
  | .namedWire _ _ => none

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
  let ⟨operandWidth, leftValue⟩ ← env.get left
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
      let ⟨_, value⟩ ← env.get reference
      pure (.zext value resultWidth)
  | .memRead mem address => do
      let header ← program.mems.find? (fun candidate => candidate.name == mem)
      let address ← env.resolveAt address header.addrWidth
      if h : header.dataWidth = resultWidth then
        pure (h ▸ Expr.memRead header.dataWidth mem address)
      else none
  | .slice value hi lo => do
      guard (lo ≤ hi && hi + 1 - lo == resultWidth)
      let ⟨_, input⟩ ← env.get value
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
      | .mul => semanticBinSame env resultWidth left right .mul
      | .udiv => semanticBinSame env resultWidth left right .udiv
      | .urem => semanticBinSame env resultWidth left right .urem
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
      let ⟨inputWidth, input⟩ ← env.get value
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

/-! ## Soundness infrastructure -/

private theorem semanticOptionFailure {α : Type} :
    (failure : Option α) = none := rfl

private theorem indexedSemanticBlock_get_number
    {program : Program} {allWires : Rope (List IndexedWire)}
    {table : WireTable} {start : Nat} {block : List IndexedWire}
    (accepted : indexedSemanticBlockMatches program allWires table start block =
      true) (index : Nat) (wire : IndexedWire)
    (found : block[index]? = some wire) :
    wire.number = start + index := by
  induction block generalizing start index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [indexedSemanticBlockMatches, Bool.and_eq_true] at accepted
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst wire
          have numberEq : head.number = start := by
            have parts : (head.number = start ∧
                lookupIndexed? allWires table start = some head) ∧
                indexedRhsWellFormed program allWires table start head.width
                  head.rhs = true := by
              simpa only [indexedWireWellFormedAt, Bool.and_eq_true, beq_iff_eq]
                using accepted.1
            exact parts.1.1
          simpa using numberEq
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have numberEq := ih accepted.2 index found
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using numberEq

private theorem IndexedRopeWellFormed.resolve_number_lt
    {program : Program} {allWires : Rope (List IndexedWire)}
    {table : WireTable} {start : Nat} {rope : Rope (List IndexedWire)}
    (hwellFormed : IndexedRopeWellFormed program allWires table start rope)
    (reference : Rope.Ref) (wire : IndexedWire)
    (found : rope.resolve? reference = some wire) :
    wire.number < start + rope.listLength := by
  induction hwellFormed generalizing reference wire with
  | leaf accepted =>
      rcases reference with ⟨path, index⟩
      cases path with
      | nil =>
          simp only [Rope.resolve_leaf] at found
          have numberEq := indexedSemanticBlock_get_number accepted index wire found
          have indexLt : index < List.length _ :=
            (List.getElem?_eq_some_iff.mp found).choose
          rw [numberEq]
          exact Nat.add_lt_add_left indexLt _
      | cons step path => simp [Rope.resolve?] at found
  | @node nodeStart left right leftProof rightProof leftIH rightIH =>
      rcases reference with ⟨path, index⟩
      cases path with
      | nil => simp [Rope.resolve?] at found
      | cons step path =>
          cases step with
          | false =>
              simp only [Rope.resolve_node_left] at found
              have leftLt := leftIH ⟨path, index⟩ wire found
              have leftLe : nodeStart + left.listLength ≤
                  nodeStart + (left.listLength + right.listLength) :=
                Nat.add_le_add_left (Nat.le_add_right _ _) _
              exact Nat.lt_of_lt_of_le leftLt leftLe
          | true =>
              simp only [Rope.resolve_node_right] at found
              simpa [Rope.listLength, Nat.add_assoc] using
                rightIH ⟨path, index⟩ wire found

private theorem lookupIndexed_number_lt
    {program : Program} {wires : Rope (List IndexedWire)} {table : WireTable}
    (hwellFormed : IndexedRopeWellFormed program wires table 0 wires)
    (number : Nat) (wire : IndexedWire)
    (found : lookupIndexed? wires table number = some wire) :
    number < wires.listLength := by
  unfold lookupIndexed? at found
  by_cases size : table.leafSize > 0
  · simp only [size, Option.bind_eq_bind] at found
    cases pathEq : balancedPath? table.leafCount
        (number / table.leafSize) with
    | none => simp [pathEq] at found
    | some path =>
        simp only [pathEq, Option.bind_some] at found
        cases wireEq : wires.resolve? ⟨path, number % table.leafSize⟩ with
        | none => simp [wireEq] at found
        | some actual =>
            simp only [wireEq, Option.bind_some] at found
            by_cases numberEq : actual.number = number
            · simp [guard, numberEq] at found
              subst wire
              have actualLt := hwellFormed.resolve_number_lt
                ⟨path, number % table.leafSize⟩ actual wireEq
              simpa [numberEq] using actualLt
            · exfalso
              simp [guard, semanticOptionFailure, beq_iff_eq, numberEq] at found
  · exfalso
    simp [guard, semanticOptionFailure, size] at found

private theorem indexedExprMatches_lookup
    (wires : Rope (List IndexedWire)) (table : WireTable)
    {width : Nat} (expr : Expr width) (number : Nat)
    (matchOk : indexedExprMatches wires table expr (.wire number) = true) :
    ∃ wire, lookupIndexed? wires table number = some wire ∧
      wire.width = width := by
  cases lookup : lookupIndexed? wires table number with
  | none => cases expr <;> simp [indexedExprMatches, lookup] at matchOk
  | some wire =>
      refine ⟨wire, rfl, ?_⟩
      cases expr <;> simp only [indexedExprMatches, lookup] at matchOk
      all_goals try simp at matchOk
      all_goals split at matchOk <;> simp_all

private theorem indexedExprMatches_named_eq_wire
    (wires : Rope (List IndexedWire)) (table : WireTable)
    {width : Nat} (expr : Expr width) (number : Nat) (name : String) :
    indexedExprMatches wires table expr (.namedWire number name) =
      indexedExprMatches wires table expr (.wire number) := by
  cases expr <;> rfl

/-- The semantic environment resolves exactly the widths accepted by the
bounded whole-graph checker before wire `current`. -/
def IndexedEnvResolvesBefore (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (current : Nat) (env : SemanticEnv) : Prop :=
  ∀ reference width,
    refWidthBefore? program wires table current reference = some width →
    ∃ value : Expr width, env.resolveAt reference width = some value

/-- Every register occurrence in an expression agrees with the concrete
program declaration. The indexed graph checker deliberately compares only
structural expression shape; this predicate supplies the source-side typing
fact needed to make register leaves exact. -/
def ExprRegistersValid (program : Program) :
    {width : Nat} → Expr width → Prop
  | width, .reg _ name =>
      ∃ reg, program.regs.find? (fun candidate => candidate.name == name) =
        some reg ∧ reg.width = width ∧ wireNumber? name = none
  | _, .lit _ => True
  | _, .memRead _ _ address => ExprRegistersValid program address
  | _, .and left right | _, .or left right | _, .xor left right
  | _, .add left right | _, .sub left right | _, .mul left right
  | _, .udiv left right | _, .urem left right | _, .shl left right
  | _, .shr left right | _, .eq left right | _, .ult left right
  | _, .slt left right =>
      ExprRegistersValid program left ∧ ExprRegistersValid program right
  | _, .not value | _, .slice value _ _ | _, .zext value _
  | _, .sext value _ => ExprRegistersValid program value
  | _, .mux condition yes no =>
      ExprRegistersValid program condition ∧
        ExprRegistersValid program yes ∧ ExprRegistersValid program no

/-- Source-EDSL expression form of register validity. -/
def HwExprRegistersValid (program : Program) :
    {width : Nat} → Loom.Hw.Expr width → Prop
  | width, .reg _ name =>
      ∃ reg, program.regs.find? (fun candidate => candidate.name == name) =
        some reg ∧ reg.width = width ∧ wireNumber? name = none
  | _, .lit _ => True
  | _, .memRead _ _ address => HwExprRegistersValid program address
  | _, .and left right | _, .or left right | _, .xor left right
  | _, .add left right | _, .sub left right | _, .mul left right
  | _, .udiv left right | _, .urem left right | _, .shl left right
  | _, .shr left right | _, .eq left right | _, .ult left right
  | _, .slt left right =>
      HwExprRegistersValid program left ∧ HwExprRegistersValid program right
  | _, .not value | _, .slice value _ _ | _, .zext value _
  | _, .sext value _ => HwExprRegistersValid program value
  | _, .mux condition yes no =>
      HwExprRegistersValid program condition ∧
        HwExprRegistersValid program yes ∧ HwExprRegistersValid program no

/-- Every register read made by an action is declared at its intrinsic width. -/
def ActRegistersValid (program : Program) : Loom.Hw.Act → Prop
  | .skip => True
  | .seq left right =>
      ActRegistersValid program left ∧ ActRegistersValid program right
  | .ite condition yes no =>
      HwExprRegistersValid program condition ∧
        ActRegistersValid program yes ∧ ActRegistersValid program no
  | .write _ _ value => HwExprRegistersValid program value
  | .memWrite _ _ _ _ address value =>
      HwExprRegistersValid program address ∧ HwExprRegistersValid program value

/-- Source-level read discipline needed by the release elaboration theorem.
It is intentionally separate from compiler correctness's write discipline. -/
structure DesignReadsValid (design : Loom.Hw.Design) (program : Program) : Prop where
  register : ∀ source ∈ design.regs,
    ∃ concrete,
      program.regs.find? (fun candidate => candidate.name == source.name) =
        some concrete ∧ concrete.width = source.width ∧
        wireNumber? source.name = none
  rule : ∀ rule ∈ design.rules, ActRegistersValid program rule.body

/-- Exact validity of one source register declaration. -/
def SourceRegisterValid (program : Program) (source : Loom.Hw.RegDecl) : Prop :=
  ∃ concrete,
    program.regs.find? (fun candidate => candidate.name == source.name) =
      some concrete ∧ concrete.width = source.width ∧
      wireNumber? source.name = none

/-- A typed register-read leaf supplies the corresponding source declaration
certificate without another lookup reduction. -/
theorem SourceRegisterValid.ofHwReg {program : Program}
    (source : Loom.Hw.RegDecl)
    (valid : HwExprRegistersValid program
      (.reg source.width source.name)) :
    SourceRegisterValid program source := by
  simpa [HwExprRegistersValid, SourceRegisterValid] using valid

/-- A compositional certificate for the source register declarations. Unlike
`List.all`, its proof can be assembled from separately named leaf theorems. -/
def SourceRegistersValid (program : Program) : List Loom.Hw.RegDecl → Prop
  | [] => True
  | source :: rest =>
      SourceRegisterValid program source ∧ SourceRegistersValid program rest

/-- A compositional certificate for all rule-body reads. -/
def RulesRegistersValid (program : Program) : List Loom.Hw.Rule → Prop
  | [] => True
  | rule :: rest =>
      ActRegistersValid program rule.body ∧ RulesRegistersValid program rest

theorem SourceRegistersValid.all {program : Program} {sources : List Loom.Hw.RegDecl}
    (valid : SourceRegistersValid program sources) :
    ∀ source ∈ sources,
      ∃ concrete,
        program.regs.find? (fun candidate => candidate.name == source.name) =
          some concrete ∧ concrete.width = source.width ∧
          wireNumber? source.name = none := by
  induction sources with
  | nil => simp
  | cons head tail ih =>
      intro source member
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using valid.1
      | inr member => exact ih valid.2 source member

theorem RulesRegistersValid.all {program : Program} {rules : List Loom.Hw.Rule}
    (valid : RulesRegistersValid program rules) :
    ∀ rule ∈ rules, ActRegistersValid program rule.body := by
  induction rules with
  | nil => simp
  | cons head tail ih =>
      intro rule member
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using valid.1
      | inr member => exact ih valid.2 rule member

/-- Assemble the public read-discipline proposition from compositional list
certificates. -/
theorem DesignReadsValid.ofLists {design : Loom.Hw.Design} {program : Program}
    (registers : SourceRegistersValid program design.regs)
    (rules : RulesRegistersValid program design.rules) :
    DesignReadsValid design program :=
  ⟨registers.all, rules.all⟩

/-- Executable source-expression read check. -/
def hwExprRegistersValidB (program : Program) :
    {width : Nat} → Loom.Hw.Expr width → Bool
  | width, .reg _ name =>
      match program.regs.find? (fun candidate => candidate.name == name) with
      | some reg => reg.width == width && (wireNumber? name).isNone
      | none => false
  | _, .lit _ => true
  | _, .memRead _ _ address => hwExprRegistersValidB program address
  | _, .and left right | _, .or left right | _, .xor left right
  | _, .add left right | _, .sub left right | _, .mul left right
  | _, .udiv left right | _, .urem left right | _, .shl left right
  | _, .shr left right | _, .eq left right | _, .ult left right
  | _, .slt left right =>
      hwExprRegistersValidB program left && hwExprRegistersValidB program right
  | _, .not value | _, .slice value _ _ | _, .zext value _
  | _, .sext value _ => hwExprRegistersValidB program value
  | _, .mux condition yes no =>
      hwExprRegistersValidB program condition &&
        hwExprRegistersValidB program yes && hwExprRegistersValidB program no

/-- Executable action read check. -/
def actRegistersValidB (program : Program) : Loom.Hw.Act → Bool
  | .skip => true
  | .seq left right =>
      actRegistersValidB program left && actRegistersValidB program right
  | .ite condition yes no =>
      hwExprRegistersValidB program condition &&
        actRegistersValidB program yes && actRegistersValidB program no
  | .write _ _ value => hwExprRegistersValidB program value
  | .memWrite _ _ _ _ address value =>
      hwExprRegistersValidB program address && hwExprRegistersValidB program value

/-- Executable check for one source register declaration. -/
def sourceRegisterValidB (program : Program)
    (source : Loom.Hw.RegDecl) : Bool :=
  match program.regs.find? (fun candidate => candidate.name == source.name) with
  | some concrete => concrete.width == source.width &&
      (wireNumber? source.name).isNone
  | none => false

theorem sourceRegisterValidB_sound {program : Program} (source : Loom.Hw.RegDecl)
    (accepted : sourceRegisterValidB program source = true) :
    SourceRegisterValid program source := by
  unfold sourceRegisterValidB at accepted
  unfold SourceRegisterValid
  cases found : program.regs.find? (fun candidate =>
      candidate.name == source.name) with
  | none => simp [found] at accepted
  | some concrete =>
      simp only [found, Bool.and_eq_true, beq_iff_eq,
        Option.isNone_iff_eq_none] at accepted
      exact ⟨concrete, rfl, accepted.1, accepted.2⟩

/-- One bounded Boolean whose soundness yields the complete source read
discipline used by exact release elaboration. -/
def designRegisterReadsValidB (design : Loom.Hw.Design) (program : Program) : Bool :=
  design.regs.all (sourceRegisterValidB program)

theorem designRegisterReadsValidB_sound {design : Loom.Hw.Design} {program : Program}
    (accepted : designRegisterReadsValidB design program = true) :
    ∀ source ∈ design.regs, SourceRegisterValid program source := by
  simp only [designRegisterReadsValidB, List.all_eq_true] at accepted
  intro source member
  exact sourceRegisterValidB_sound source (accepted source member)

def designReadsValidB (design : Loom.Hw.Design) (program : Program) : Bool :=
  designRegisterReadsValidB design program &&
    design.rules.all (fun rule => actRegistersValidB program rule.body)

theorem hwExprRegistersValidB_sound {program : Program} {width : Nat}
    (expr : Loom.Hw.Expr width)
    (accepted : hwExprRegistersValidB program expr = true) :
    HwExprRegistersValid program expr := by
  induction expr <;> simp_all [hwExprRegistersValidB, HwExprRegistersValid,
    Bool.and_eq_true]
  case reg width name =>
    cases found : program.regs.find? (fun candidate => candidate.name == name) with
    | none => simp [found] at accepted
    | some reg =>
        simp only [found, Bool.and_eq_true, beq_iff_eq,
          Option.isNone_iff_eq_none] at accepted
        exact ⟨reg, rfl, accepted.1, accepted.2⟩

theorem actRegistersValidB_sound {program : Program} (action : Loom.Hw.Act)
    (accepted : actRegistersValidB program action = true) :
    ActRegistersValid program action := by
  induction action <;> simp_all [actRegistersValidB, ActRegistersValid,
    Bool.and_eq_true, hwExprRegistersValidB_sound]

theorem designReadsValidB_sound {design : Loom.Hw.Design} {program : Program}
    (accepted : designReadsValidB design program = true) :
    DesignReadsValid design program := by
  simp only [designReadsValidB, Bool.and_eq_true, List.all_eq_true] at accepted
  constructor
  · intro source sourceMem
    exact designRegisterReadsValidB_sound accepted.1 source sourceMem
  · intro rule ruleMem
    exact actRegistersValidB_sound rule.body (accepted.2 rule ruleMem)

/-- Structural compilation preserves source register validity. -/
theorem compileExpr_registersValid {program : Program} {width : Nat}
    (expr : Loom.Hw.Expr width) (valid : HwExprRegistersValid program expr) :
    ExprRegistersValid program (Loom.Hw.Compile.compileExpr expr) := by
  induction expr <;> simp_all [HwExprRegistersValid, ExprRegistersValid,
    Loom.Hw.Compile.compileExpr]

/-- Folding one valid action into a valid next-register expression preserves
register validity. -/
theorem nextReg_registersValid {program : Program} (register : String)
    (width : Nat) (action : Loom.Hw.Act) (current : Expr width)
    (actionValid : ActRegistersValid program action)
    (currentValid : ExprRegistersValid program current) :
    ExprRegistersValid program
      (Loom.Hw.Compile.nextReg register width action current) := by
  induction action generalizing current with
  | skip => exact currentValid
  | seq left right leftIH rightIH =>
      exact rightIH _ actionValid.2 (leftIH _ actionValid.1 currentValid)
  | ite condition yes no yesIH noIH =>
      simp only [Loom.Hw.Compile.nextReg]
      split
      · exact ⟨compileExpr_registersValid condition actionValid.1,
          yesIH _ actionValid.2.1 currentValid,
          noIH _ actionValid.2.2 currentValid⟩
      · exact currentValid
  | write actualWidth actualName value =>
      simp only [Loom.Hw.Compile.nextReg]
      split
      · split
        next widthEq =>
          cases widthEq
          exact compileExpr_registersValid value actionValid
        · exact currentValid
      · exact currentValid
  | memWrite => exact currentValid

/-- The ordered rule fold used for a compiled register preserves register
validity when every rule action is valid. -/
theorem nextRules_registersValid {program : Program} (register : String)
    (width : Nat) (rules : List Loom.Hw.Rule) (current : Expr width)
    (rulesValid : ∀ rule ∈ rules, ActRegistersValid program rule.body)
    (currentValid : ExprRegistersValid program current) :
    ExprRegistersValid program
      (rules.foldl (fun value rule => Loom.Hw.Compile.nextReg register width
        rule.body value) current) := by
  induction rules generalizing current with
  | nil => exact currentValid
  | cons rule rules ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro tail tailMem
        exact rulesValid tail (by simp [tailMem])
      · exact nextReg_registersValid register width rule.body current
          (rulesValid rule (by simp)) currentValid

/-- Register-read validity for all three expressions of a compiled memory
write port. -/
def PortRegistersValid (program : Program) {addressWidth dataWidth : Nat}
    (port : Loom.Hw.Compile.Port addressWidth dataWidth) : Prop :=
  ExprRegistersValid program port.en ∧
    ExprRegistersValid program port.addr ∧
    ExprRegistersValid program port.data

/-- Folding one valid source action into a valid memory port preserves the
register-read discipline. -/
theorem memPort_registersValid {program : Program} (memory : String)
    (addressWidth dataWidth portIndex : Nat) (action : Loom.Hw.Act)
    (current : Loom.Hw.Compile.Port addressWidth dataWidth)
    (actionValid : ActRegistersValid program action)
    (currentValid : PortRegistersValid program current) :
    PortRegistersValid program
      (Loom.Hw.Compile.memPort memory addressWidth dataWidth portIndex action
        current) := by
  induction action generalizing current with
  | skip => exact currentValid
  | seq left right leftIH rightIH =>
      exact rightIH _ actionValid.2 (leftIH _ actionValid.1 currentValid)
  | ite condition yes no yesIH noIH =>
      simp only [Loom.Hw.Compile.memPort]
      split
      · let yesPort := Loom.Hw.Compile.memPort memory addressWidth dataWidth
          portIndex yes current
        let noPort := Loom.Hw.Compile.memPort memory addressWidth dataWidth
          portIndex no current
        have conditionValid := compileExpr_registersValid condition actionValid.1
        have yesValid : PortRegistersValid program yesPort :=
          yesIH _ actionValid.2.1 currentValid
        have noValid : PortRegistersValid program noPort :=
          noIH _ actionValid.2.2 currentValid
        exact ⟨⟨conditionValid, yesValid.1, noValid.1⟩,
          ⟨conditionValid, yesValid.2.1, noValid.2.1⟩,
          ⟨conditionValid, yesValid.2.2, noValid.2.2⟩⟩
      · exact currentValid
  | write => exact currentValid
  | memWrite actualAddressWidth actualDataWidth actualMemory actualPort
      address value =>
      simp only [Loom.Hw.Compile.memPort]
      split
      · split
        next widths =>
          rcases widths with ⟨addressWidthEq, dataWidthEq⟩
          cases addressWidthEq
          cases dataWidthEq
          exact ⟨trivial,
            compileExpr_registersValid address actionValid.1,
            compileExpr_registersValid value actionValid.2⟩
        · exact currentValid
      · exact currentValid

/-- Folding a valid rule list into one memory port preserves validity. -/
theorem portRules_registersValid {program : Program} (memory : String)
    (addressWidth dataWidth portIndex : Nat) (rules : List Loom.Hw.Rule)
    (current : Loom.Hw.Compile.Port addressWidth dataWidth)
    (rulesValid : ∀ rule ∈ rules, ActRegistersValid program rule.body)
    (currentValid : PortRegistersValid program current) :
    PortRegistersValid program
      (rules.foldl (fun port rule => Loom.Hw.Compile.memPort memory
        addressWidth dataWidth portIndex rule.body port) current) := by
  induction rules generalizing current with
  | nil => exact currentValid
  | cons rule rules ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro tail tailMem
        exact rulesValid tail (by simp [tailMem])
      · exact memPort_registersValid memory addressWidth dataWidth portIndex
          rule.body current (rulesValid rule (by simp)) currentValid

/-- Every reference compiler memory port satisfies the release elaborator's
register-validity premise under the source read discipline. -/
theorem compilePort_registersValid {design : Loom.Hw.Design}
    {program : Program} (readsValid : DesignReadsValid design program)
    (memory : String) (addressWidth dataWidth portIndex : Nat) :
    PortRegistersValid program
      (Loom.Hw.Compile.compilePort design memory addressWidth dataWidth
        portIndex) := by
  apply portRules_registersValid memory addressWidth dataWidth portIndex
    design.rules
  · exact readsValid.rule
  · exact ⟨trivial, trivial, trivial⟩

/-- The reference compiler's next-state expression for any declared source
register satisfies the release elaborator's register-validity premise. -/
theorem registerNext_registersValid {design : Loom.Hw.Design}
    {program : Program} (readsValid : DesignReadsValid design program)
    (source : Loom.Hw.RegDecl) (sourceMem : source ∈ design.regs) :
    ExprRegistersValid program
      (design.rules.foldl
        (fun current rule => Loom.Hw.Compile.nextReg source.name source.width
          rule.body current)
        (.reg source.width source.name)) := by
  apply nextRules_registersValid source.name source.width design.rules
  · exact readsValid.rule
  · obtain ⟨concrete, found, widthEq, notWire⟩ :=
      readsValid.register source sourceMem
    exact ⟨concrete, found, widthEq, notWire⟩

/-- Every well-typed compiler expression accepted for an in-scope structural
reference resolves to that exact intrinsically typed expression. -/
def IndexedEnvModelsBefore (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (current : Nat) (env : SemanticEnv) : Prop :=
  ∀ {width : Nat} (expr : Expr width) (reference : Ref),
    ExprRegistersValid program expr →
    indexedExprMatches wires table expr reference = true →
    refWidthBefore? program wires table current reference = some width →
    env.resolveAt reference width = some expr

private theorem indexedModels_current_eq
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (left right : Nat) (env : SemanticEnv) (equal : left = right)
    (hmodels : IndexedEnvModelsBefore program wires table left env) :
    IndexedEnvModelsBefore program wires table right env := by
  subst right
  exact hmodels

private theorem semanticEntry_of_resolveAt
    (env : SemanticEnv) (reference : Ref) (width : Nat) (value : Expr width)
    (accepted : env.resolveAt reference width = some value) :
    env.get reference = some ⟨width, value⟩ := by
  unfold SemanticEnv.resolveAt at accepted
  cases found : env.get reference with
  | none => simp [found] at accepted
  | some entry =>
      obtain ⟨actual, raw⟩ := entry
      by_cases widthEq : actual = width
      · subst actual
        simp [found] at accepted
        subst value
        rfl
      · simp [found, widthEq] at accepted

private theorem semanticBinSame_of_resolveAt
    (env : SemanticEnv) (width : Nat) (leftRef rightRef : Ref)
    (make : Expr width → Expr width → Expr width) (left right : Expr width)
    (leftEq : env.resolveAt leftRef width = some left)
    (rightEq : env.resolveAt rightRef width = some right) :
    semanticBinSame env width leftRef rightRef make = some (make left right) := by
  simp [semanticBinSame, leftEq, rightEq]

private theorem semanticComparison_of_resolveAt
    (env : SemanticEnv) (leftRef rightRef : Ref) (width : Nat)
    (make : {w : Nat} → Expr w → Expr w → Expr 1)
    (left right : Expr width)
    (leftEntry : env.get leftRef = some ⟨width, left⟩)
    (rightEq : env.resolveAt rightRef width = some right) :
    semanticComparison env 1 leftRef rightRef make = some (make left right) := by
  simp [semanticComparison, guard, leftEntry, rightEq]

/-- A successful node check is sufficient for structural elaboration under
any environment satisfying the earlier-reference invariant. -/
theorem indexedRhsWellFormed_elaborate_isSome
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (number resultWidth : Nat) (rhs : IndexedRhs) (env : SemanticEnv)
    (henv : IndexedEnvResolvesBefore program wires table number env)
    (accepted : indexedRhsWellFormed program wires table number resultWidth rhs =
      true) :
    ∃ value : Expr resultWidth, rhs.elaborate program env resultWidth = some value := by
  cases rhs with
  | lit literalWidth value =>
      simp only [indexedRhsWellFormed, beq_iff_eq] at accepted
      subst literalWidth
      exact ⟨.lit (BitVec.ofNat resultWidth value), by
        simp [IndexedRhs.elaborate, guard]⟩
  | ident reference =>
      cases found : refWidthBefore? program wires table number reference with
      | none => simp [indexedRhsWellFormed, found] at accepted
      | some inputWidth =>
          obtain ⟨value, valueEq⟩ := henv reference inputWidth found
          have entryEq := semanticEntry_of_resolveAt env reference inputWidth value valueEq
          exact ⟨.zext value resultWidth, by
            simp [IndexedRhs.elaborate, entryEq]⟩
  | memRead mem addressRef =>
      simp only [indexedRhsWellFormed] at accepted
      cases headerFound : program.mems.find? (fun candidate => candidate.name == mem) with
      | none => simp [headerFound] at accepted
      | some header =>
          cases addressFound : refWidthBefore? program wires table number addressRef with
          | none => simp [headerFound, addressFound] at accepted
          | some addressWidth =>
              simp only [headerFound, addressFound, Bool.and_eq_true,
                beq_iff_eq] at accepted
              rcases accepted with ⟨rfl, rfl⟩
              obtain ⟨address, addressEq⟩ :=
                henv addressRef header.addrWidth addressFound
              exact ⟨.memRead header.dataWidth mem address, by
                simp [IndexedRhs.elaborate, headerFound, addressEq]⟩
  | slice valueRef hi lo =>
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at accepted
      cases valueFound : refWidthBefore? program wires table number valueRef with
      | none => simp [valueFound] at accepted
      | some inputWidth =>
          obtain ⟨value, valueEq⟩ := henv valueRef inputWidth valueFound
          have entryEq := semanticEntry_of_resolveAt env valueRef inputWidth value valueEq
          exact ⟨.slice value lo resultWidth, by
            simp [IndexedRhs.elaborate, guard, entryEq, accepted.1.2, accepted.2]⟩
  | not valueRef =>
      have found := beq_iff_eq.mp accepted
      obtain ⟨value, valueEq⟩ := henv valueRef resultWidth found
      exact ⟨.not value, by simp [IndexedRhs.elaborate, valueEq]⟩
  | bin op leftRef rightRef =>
      cases op with
      | and | or | xor | add | sub | mul | udiv | urem | shl | shr =>
          simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at accepted
          obtain ⟨left, leftEq⟩ := henv leftRef resultWidth accepted.1
          obtain ⟨right, rightEq⟩ := henv rightRef resultWidth accepted.2
          first
          | exact ⟨.and left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.or left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.xor left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.add left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.sub left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.mul left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.udiv left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.urem left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.shl left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.shr left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
      | eq | ult =>
          simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at accepted
          cases leftFound : refWidthBefore? program wires table number leftRef with
          | none => simp [leftFound] at accepted
          | some operandWidth =>
              cases rightFound : refWidthBefore? program wires table number rightRef with
              | none => simp [leftFound, rightFound] at accepted
              | some rightWidth =>
                  simp only [leftFound, rightFound, beq_iff_eq] at accepted
                  rcases accepted with ⟨rfl, rfl⟩
                  obtain ⟨left, leftEq⟩ := henv leftRef operandWidth leftFound
                  obtain ⟨right, rightEq⟩ := henv rightRef operandWidth rightFound
                  have leftEntry := semanticEntry_of_resolveAt env leftRef operandWidth left leftEq
                  first
                  | exact ⟨.eq left right,
                      semanticComparison_of_resolveAt _ _ _ _ _ _ _ leftEntry rightEq⟩
                  | exact ⟨.ult left right,
                      semanticComparison_of_resolveAt _ _ _ _ _ _ _ leftEntry rightEq⟩
  | slt leftRef rightRef =>
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at accepted
      cases leftFound : refWidthBefore? program wires table number leftRef with
      | none => simp [leftFound] at accepted
      | some operandWidth =>
          cases rightFound : refWidthBefore? program wires table number rightRef with
          | none => simp [leftFound, rightFound] at accepted
          | some rightWidth =>
              simp only [leftFound, rightFound, beq_iff_eq] at accepted
              rcases accepted with ⟨rfl, rfl⟩
              obtain ⟨left, leftEq⟩ := henv leftRef operandWidth leftFound
              obtain ⟨right, rightEq⟩ := henv rightRef operandWidth rightFound
              have leftEntry := semanticEntry_of_resolveAt env leftRef operandWidth left leftEq
              exact ⟨.slt left right,
                semanticComparison_of_resolveAt _ _ _ _ _ _ _ leftEntry rightEq⟩
  | mux conditionRef yesRef noRef =>
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at accepted
      obtain ⟨condition, conditionEq⟩ := henv conditionRef 1 accepted.1.1
      obtain ⟨yes, yesEq⟩ := henv yesRef resultWidth accepted.1.2
      obtain ⟨no, noEq⟩ := henv noRef resultWidth accepted.2
      exact ⟨.mux condition yes no, by
        simp [IndexedRhs.elaborate, conditionEq, yesEq, noEq]⟩
  | sext amount valueRef signBit =>
      simp only [indexedRhsWellFormed] at accepted
      cases valueFound : refWidthBefore? program wires table number valueRef with
      | none => simp [valueFound] at accepted
      | some inputWidth =>
          simp only [valueFound, Bool.and_eq_true, beq_iff_eq,
            decide_eq_true_eq] at accepted
          obtain ⟨value, valueEq⟩ := henv valueRef inputWidth valueFound
          have entryEq := semanticEntry_of_resolveAt env valueRef inputWidth value valueEq
          exact ⟨.sext value resultWidth, by
            simp [IndexedRhs.elaborate, guard, entryEq, accepted.1.1,
              accepted.1.2, accepted.2]⟩

theorem semanticInitial_resolvesBefore
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable) :
    IndexedEnvResolvesBefore program wires table 0
      (SemanticEnv.initial program) := by
  intro reference width accepted
  cases reference with
  | reg name =>
      unfold refWidthBefore? at accepted
      cases notWire : wireNumber? name with
      | some number =>
          simp only [notWire, Option.isNone_some, guard] at accepted
          rw [semanticOptionFailure] at accepted
          simp at accepted
      | none =>
          cases found : program.regs.find? (fun reg => reg.name == name) with
          | none => simp [notWire, found, guard] at accepted
          | some reg =>
              have widthEq : reg.width = width := by
                simpa [notWire, found, guard] using accepted
              subst width
              exact ⟨.reg reg.width name, by
                simp [SemanticEnv.resolveAt, SemanticEnv.get,
                  SemanticEnv.initial, found]⟩
  | wire number =>
      unfold refWidthBefore? at accepted
      have notEarlier : ¬number < 0 := Nat.not_lt_zero number
      simp only [notEarlier, guard] at accepted
      rw [semanticOptionFailure] at accepted
      simp at accepted
  | namedWire number name =>
      unfold refWidthBefore? at accepted
      have notEarlier : ¬number < 0 := Nat.not_lt_zero number
      simp only [notEarlier, guard] at accepted
      rw [semanticOptionFailure] at accepted
      simp at accepted

theorem semanticInitial_modelsBefore
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable) :
    IndexedEnvModelsBefore program wires table 0
      (SemanticEnv.initial program) := by
  intro width expr reference valid matchOk inScope
  cases reference with
  | wire number =>
      unfold refWidthBefore? at inScope
      have notEarlier : ¬number < 0 := Nat.not_lt_zero number
      simp only [notEarlier, guard] at inScope
      rw [semanticOptionFailure] at inScope
      simp at inScope
  | namedWire number name =>
      unfold refWidthBefore? at inScope
      have notEarlier : ¬number < 0 := Nat.not_lt_zero number
      simp only [notEarlier, guard] at inScope
      rw [semanticOptionFailure] at inScope
      simp at inScope
  | reg actualName =>
      cases expr <;> simp [indexedExprMatches] at matchOk
      case reg sourceName =>
        subst actualName
        rcases valid with ⟨source, sourceFound, sourceWidth, sourceNotWire⟩
        unfold refWidthBefore? at inScope
        cases found : program.regs.find? (fun reg => reg.name == sourceName) with
        | none => simp [sourceNotWire, found, guard] at inScope
        | some reg =>
            have widthEq : reg.width = width := by
              simpa [sourceNotWire, found, guard] using inScope
            subst width
            have sourceEq : source = reg := by
              simpa [found] using sourceFound.symm
            subst source
            simp [SemanticEnv.resolveAt, SemanticEnv.get,
              SemanticEnv.initial, found]

private theorem refWidthBefore_wire_previous
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current number width : Nat) (different : number ≠ current)
    (accepted : refWidthBefore? program wires table (current + 1) (.wire number) =
      some width) :
    refWidthBefore? program wires table current (.wire number) = some width := by
  have earlierSucc : number < current + 1 := by
    by_cases earlier : number < current + 1
    · exact earlier
    · unfold refWidthBefore? at accepted
      simp only [earlier, guard] at accepted
      rw [semanticOptionFailure] at accepted
      simp at accepted
  have le : number ≤ current := Nat.le_of_lt_succ earlierSucc
  have earlier : number < current := Nat.lt_of_le_of_ne le different
  unfold refWidthBefore? at accepted ⊢
  simp only [earlierSucc, earlier, guard] at accepted ⊢
  exact accepted

private theorem refWidthBefore_wire_lookup_width
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current number width : Nat) (wire : IndexedWire)
    (lookup : lookupIndexed? wires table number = some wire)
    (accepted : refWidthBefore? program wires table current (.wire number) =
      some width) : wire.width = width := by
  unfold refWidthBefore? at accepted
  by_cases earlier : number < current
  · cases rawFound : lookupRaw? program.wires table number with
    | none => simp [earlier, lookup, rawFound, guard] at accepted
    | some raw =>
        by_cases nameEq : raw.name = (Ref.wire number).render
        · simpa [earlier, lookup, rawFound, nameEq, guard] using accepted
        · simp [earlier, lookup, rawFound, nameEq, guard,
            semanticOptionFailure] at accepted
  · simp [earlier, guard, semanticOptionFailure] at accepted

private theorem refWidthBefore_named_previous
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current number width : Nat) (name : String) (different : number ≠ current)
    (accepted : refWidthBefore? program wires table (current + 1)
      (.namedWire number name) = some width) :
    refWidthBefore? program wires table current (.namedWire number name) =
      some width := by
  have earlierSucc : number < current + 1 := by
    by_cases earlier : number < current + 1
    · exact earlier
    · simp [refWidthBefore?, earlier, guard, semanticOptionFailure] at accepted
  have earlier : number < current :=
    Nat.lt_of_le_of_ne (Nat.le_of_lt_succ earlierSucc) different
  unfold refWidthBefore? at accepted ⊢
  simp only [earlierSucc, earlier, guard] at accepted ⊢
  exact accepted

private theorem refWidthBefore_named_lookup_width
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current number width : Nat) (name : String) (wire : IndexedWire)
    (lookup : lookupIndexed? wires table number = some wire)
    (accepted : refWidthBefore? program wires table current
      (.namedWire number name) = some width) : wire.width = width := by
  unfold refWidthBefore? at accepted
  by_cases earlier : number < current
  · cases rawFound : lookupRaw? program.wires table number with
    | none => simp [earlier, lookup, rawFound, guard] at accepted
    | some raw =>
        by_cases nameEq : raw.name = name
        · simpa [earlier, lookup, rawFound, nameEq, guard] using accepted
        · simp [earlier, lookup, rawFound, nameEq, guard,
            semanticOptionFailure] at accepted
  · simp [earlier, guard, semanticOptionFailure] at accepted

private theorem indexedModels_insertWire_previous
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current wireWidth : Nat) (value : Expr wireWidth) (env : SemanticEnv)
    (hmodels : IndexedEnvModelsBefore program wires table current env) :
    IndexedEnvModelsBefore program wires table current
      (env.insertWire current wireWidth value) := by
  intro width expr reference valid matchOk inScope
  have resolved := hmodels expr reference valid matchOk inScope
  cases reference with
  | reg name =>
      unfold SemanticEnv.resolveAt at resolved ⊢
      simpa [SemanticEnv.insertWire] using resolved
  | wire number =>
      have different : number ≠ current := by
        intro same
        subst number
        unfold refWidthBefore? at inScope
        have notEarlier : ¬current < current := Nat.lt_irrefl current
        simp only [notEarlier, guard] at inScope
        rw [semanticOptionFailure] at inScope
        simp at inScope
      have refNe : Ref.wire number ≠ Ref.wire current := by
        intro same
        cases same
        exact different rfl
      unfold SemanticEnv.resolveAt at resolved ⊢
      simpa [SemanticEnv.get, SemanticEnv.insertWire, refNe] using resolved
  | namedWire number name =>
      have different : number ≠ current := by
        intro same
        subst number
        unfold refWidthBefore? at inScope
        have notEarlier : ¬current < current := Nat.lt_irrefl current
        simp only [notEarlier, guard] at inScope
        rw [semanticOptionFailure] at inScope
        simp at inScope
      have resolved := hmodels expr (.namedWire number name) valid matchOk inScope
      unfold SemanticEnv.resolveAt at resolved ⊢
      simp only [SemanticEnv.get]
      simpa [SemanticEnv.get, SemanticEnv.insertWire, different] using resolved

private theorem indexedExprMatches_refWidth
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current actualWidth : Nat) {width : Nat} (expr : Expr width)
    (reference : Ref) (valid : ExprRegistersValid program expr)
    (matchOk : indexedExprMatches wires table expr reference = true)
    (found : refWidthBefore? program wires table current reference =
      some actualWidth) :
    actualWidth = width := by
  cases reference with
  | reg actualName =>
      cases expr <;> simp [indexedExprMatches] at matchOk
      case reg sourceName =>
        subst actualName
        rcases valid with ⟨reg, regFound, regWidth, regNotWire⟩
        simp only [refWidthBefore?] at found
        simp [regNotWire, regFound, guard] at found
        exact found.symm.trans regWidth
  | wire number =>
      obtain ⟨wire, lookup, wireWidth⟩ :=
        indexedExprMatches_lookup wires table expr number matchOk
      unfold refWidthBefore? at found
      by_cases earlier : number < current
      · cases rawFound : lookupRaw? program.wires table number with
        | none => simp [earlier, lookup, rawFound, guard] at found
        | some raw =>
            by_cases nameEq : raw.name = (Ref.wire number).render
            · have actualEq : wire.width = actualWidth := by
                simpa [earlier, lookup, rawFound, nameEq, guard] using found
              exact actualEq.symm.trans wireWidth
            · simp [earlier, lookup, rawFound, nameEq, guard,
                semanticOptionFailure] at found
      · simp [earlier, guard, semanticOptionFailure] at found
  | namedWire number name =>
      have wireMatch : indexedExprMatches wires table expr (.wire number) =
          true := by
        rw [indexedExprMatches_named_eq_wire] at matchOk
        exact matchOk
      obtain ⟨wire, lookup, wireWidth⟩ :=
        indexedExprMatches_lookup wires table expr number wireMatch
      unfold refWidthBefore? at found
      by_cases earlier : number < current
      · cases rawFound : lookupRaw? program.wires table number with
        | none => simp [earlier, lookup, rawFound, guard] at found
        | some raw =>
            by_cases nameEq : raw.name = name
            · have actualEq : wire.width = actualWidth := by
                simpa [earlier, lookup, rawFound, nameEq, guard] using found
              exact actualEq.symm.trans wireWidth
            · simp [earlier, lookup, rawFound, nameEq, guard,
                semanticOptionFailure] at found
      · simp [earlier, guard, semanticOptionFailure] at found

private theorem indexedModels_resolve
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current : Nat) (env : SemanticEnv)
    (hmodels : IndexedEnvModelsBefore program wires table current env)
    {width actualWidth : Nat} (expr : Expr width) (reference : Ref)
    (valid : ExprRegistersValid program expr)
    (matchOk : indexedExprMatches wires table expr reference = true)
    (found : refWidthBefore? program wires table current reference =
      some actualWidth) :
    env.resolveAt reference width = some expr := by
  have widthEq := indexedExprMatches_refWidth program wires table current
    actualWidth expr reference valid matchOk found
  subst actualWidth
  exact hmodels expr reference valid matchOk found

private theorem indexedExprMatches_current_elaborate
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current : Nat) (env : SemanticEnv)
    (hmodels : IndexedEnvModelsBefore program wires table current env)
    {width : Nat} (expr : Expr width) (wire : IndexedWire)
    (valid : ExprRegistersValid program expr)
    (wireOk : indexedWireWellFormedAt program wires table current wire = true)
    (matchOk : indexedExprMatches wires table expr (.wire current) = true) :
    ∃ widthEq : wire.width = width,
      wire.rhs.elaborate program env wire.width =
        some (widthEq.symm ▸ expr) := by
  rcases wire with ⟨wireNumber, wireWidth, rhs⟩
  simp only [indexedWireWellFormedAt, Bool.and_eq_true, beq_iff_eq] at wireOk
  rcases wireOk with ⟨⟨numberEq, lookupEq⟩, rhsOk⟩
  subst wireNumber
  cases expr <;> cases rhs <;>
    simp [indexedExprMatches, lookupEq] at matchOk
  case lit.lit value literalWidth actualValue =>
    rcases matchOk with ⟨⟨widthEq, literalWidthEq⟩, valueEq⟩
    subst wireWidth
    subst literalWidth
    subst actualValue
    exact ⟨rfl, by simp [IndexedRhs.elaborate, guard]⟩
  case memRead.memRead mem addressWidth address memRef addressRef =>
    rcases matchOk with ⟨⟨widthEq, memEq⟩, addressMatch⟩
    subst wireWidth
    subst memRef
    simp only [indexedRhsWellFormed] at rhsOk
    cases headerFound : program.mems.find? (fun candidate =>
        candidate.name == mem) with
    | none => simp [headerFound] at rhsOk
    | some header =>
        cases addressFound : refWidthBefore? program wires table current
            addressRef with
        | none => simp [headerFound, addressFound] at rhsOk
        | some actualAddressWidth =>
            simp only [headerFound, addressFound, Bool.and_eq_true,
              beq_iff_eq] at rhsOk
            have actualEq := indexedExprMatches_refWidth program wires table
              current actualAddressWidth address addressRef valid addressMatch
                addressFound
            have addressEq := indexedModels_resolve program wires table current
              env hmodels address addressRef valid addressMatch addressFound
            have headerAddressEq : header.addrWidth = addressWidth :=
              rhsOk.1.trans actualEq
            have headerDataEq : header.dataWidth = width := rhsOk.2
            rcases header with ⟨headerName, headerAddrWidth,
              headerDataWidth, headerInit, headerWrites⟩
            simp only at headerAddressEq headerDataEq
            subst headerAddrWidth
            subst headerDataWidth
            exact ⟨rfl, by
              simp [IndexedRhs.elaborate, headerFound, addressEq]⟩
  case not.not value valueRef =>
    rcases matchOk with ⟨widthEq, valueMatch⟩
    subst wireWidth
    have valueScope : refWidthBefore? program wires table current valueRef =
        some width := beq_iff_eq.mp rhsOk
    have valueEq := hmodels value valueRef valid valueMatch valueScope
    exact ⟨rfl, by simp [IndexedRhs.elaborate, valueEq]⟩
  case and.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case and =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case or.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case or =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case xor.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case xor =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case add.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case add =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case sub.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case sub =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case mul.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case mul =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case udiv.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case udiv =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case urem.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case urem =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case shl.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case shl =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case shr.bin left right op leftRef rightRef =>
    cases op <;> simp at matchOk
    case shr =>
      rcases matchOk with ⟨⟨widthEq, leftMatch⟩, rightMatch⟩
      subst wireWidth
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
      have leftEq := indexedModels_resolve program wires table current env
        hmodels left leftRef valid.1 leftMatch rhsOk.1
      have rightEq := indexedModels_resolve program wires table current env
        hmodels right rightRef valid.2 rightMatch rhsOk.2
      exact ⟨rfl, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
  case eq.bin left right op leftRef rightRef =>
    cases op <;> try simp at matchOk
    case eq =>
      split at matchOk
      next matchEq =>
        cases matchEq
        simp only [Bool.and_eq_true] at matchOk
        simp only [indexedRhsWellFormed] at rhsOk
        cases leftFound : refWidthBefore? program wires table current leftRef with
        | none => simp [leftFound] at rhsOk
        | some operandWidth =>
            cases rightFound : refWidthBefore? program wires table current
                rightRef with
            | none => simp [leftFound, rightFound] at rhsOk
            | some rightWidth =>
                simp only [leftFound, rightFound] at rhsOk
                have operandEq : operandWidth = rightWidth :=
                  beq_iff_eq.mp rhsOk
                subst rightWidth
                have leftEq := indexedModels_resolve program wires table
                  current env hmodels left leftRef valid.1 matchOk.1 leftFound
                have rightEq := indexedModels_resolve program wires table
                  current env hmodels right rightRef valid.2 matchOk.2 rightFound
                have leftEntry := semanticEntry_of_resolveAt env leftRef _ _ leftEq
                exact ⟨rfl, semanticComparison_of_resolveAt _ _ _ _ _ _ _
                  leftEntry rightEq⟩
      next mismatch => simp at matchOk
  case ult.bin left right op leftRef rightRef =>
    cases op <;> try simp at matchOk
    case ult =>
      split at matchOk
      next matchEq =>
        cases matchEq
        simp only [Bool.and_eq_true] at matchOk
        simp only [indexedRhsWellFormed] at rhsOk
        cases leftFound : refWidthBefore? program wires table current leftRef with
        | none => simp [leftFound] at rhsOk
        | some operandWidth =>
            cases rightFound : refWidthBefore? program wires table current
                rightRef with
            | none => simp [leftFound, rightFound] at rhsOk
            | some rightWidth =>
                simp only [leftFound, rightFound] at rhsOk
                have operandEq : operandWidth = rightWidth :=
                  beq_iff_eq.mp rhsOk
                subst rightWidth
                have leftEq := indexedModels_resolve program wires table
                  current env hmodels left leftRef valid.1 matchOk.1 leftFound
                have rightEq := indexedModels_resolve program wires table
                  current env hmodels right rightRef valid.2 matchOk.2 rightFound
                have leftEntry := semanticEntry_of_resolveAt env leftRef _ _ leftEq
                exact ⟨rfl, semanticComparison_of_resolveAt _ _ _ _ _ _ _
                  leftEntry rightEq⟩
      next mismatch => simp at matchOk
  case slt.slt left right leftRef rightRef =>
    split at matchOk
    next matchEq =>
      cases matchEq
      simp only [Bool.and_eq_true] at matchOk
      simp only [indexedRhsWellFormed] at rhsOk
      cases leftFound : refWidthBefore? program wires table current leftRef with
      | none => simp [leftFound] at rhsOk
      | some operandWidth =>
          cases rightFound : refWidthBefore? program wires table current
              rightRef with
          | none => simp [leftFound, rightFound] at rhsOk
          | some rightWidth =>
              simp only [leftFound, rightFound] at rhsOk
              have operandEq : operandWidth = rightWidth :=
                beq_iff_eq.mp (by simpa using rhsOk)
              subst rightWidth
              have leftEq := indexedModels_resolve program wires table current
                env hmodels left leftRef valid.1 matchOk.1 leftFound
              have rightEq := indexedModels_resolve program wires table current
                env hmodels right rightRef valid.2 matchOk.2 rightFound
              have leftEntry := semanticEntry_of_resolveAt env leftRef _ _ leftEq
              exact ⟨rfl, semanticComparison_of_resolveAt _ _ _ _ _ _ _
                leftEntry rightEq⟩
    next mismatch => simp at matchOk
  case mux.mux condition yes no conditionRef yesRef noRef =>
    rcases matchOk with ⟨⟨⟨widthEq, conditionMatch⟩, yesMatch⟩, noMatch⟩
    subst wireWidth
    rcases valid with ⟨conditionValid, yesValid, noValid⟩
    simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at rhsOk
    have conditionEq := indexedModels_resolve program wires table current env
      hmodels condition conditionRef conditionValid conditionMatch rhsOk.1.1
    have yesEq := indexedModels_resolve program wires table current env
      hmodels yes yesRef yesValid yesMatch rhsOk.1.2
    have noEq := indexedModels_resolve program wires table current env
      hmodels no noRef noValid noMatch rhsOk.2
    exact ⟨rfl, by
      simp [IndexedRhs.elaborate, conditionEq, yesEq, noEq]⟩
  case slice.slice value lo valueRef hi actualLo =>
    rcases matchOk with ⟨⟨⟨widthEq, loEq⟩, hiEq⟩, valueMatch⟩
    subst wireWidth
    subst actualLo
    subst hi
    simp only [indexedRhsWellFormed, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at rhsOk
    cases valueFound : refWidthBefore? program wires table current valueRef with
    | none => simp [valueFound] at rhsOk
    | some inputWidth =>
        have valueEq := indexedModels_resolve program wires table current env
          hmodels value valueRef valid valueMatch valueFound
        have valueEntry := semanticEntry_of_resolveAt env valueRef _ _ valueEq
        exact ⟨rfl, by
          simp [IndexedRhs.elaborate, guard, valueEntry, rhsOk]⟩
  case zext.ident value valueRef =>
    rcases matchOk with ⟨⟨widthEq, inputLe⟩, valueMatch⟩
    subst wireWidth
    simp only [indexedRhsWellFormed] at rhsOk
    cases valueFound : refWidthBefore? program wires table current valueRef with
    | none => simp [valueFound] at rhsOk
    | some inputWidth =>
        have valueEq := indexedModels_resolve program wires table current env
          hmodels value valueRef valid valueMatch valueFound
        have valueEntry := semanticEntry_of_resolveAt env valueRef _ _ valueEq
        exact ⟨rfl, by
          simp [IndexedRhs.elaborate, valueEntry]⟩
  case sext.sext value amount valueRef signBit =>
    rcases matchOk with
      ⟨⟨⟨⟨widthEq, inputLt⟩, amountEq⟩, signBitEq⟩, valueMatch⟩
    subst wireWidth
    simp only [indexedRhsWellFormed] at rhsOk
    cases valueFound : refWidthBefore? program wires table current valueRef with
    | none => simp [valueFound] at rhsOk
    | some actualInputWidth =>
        simp only [valueFound, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at rhsOk
        have actualEq := indexedExprMatches_refWidth program wires table current
          actualInputWidth value valueRef valid valueMatch valueFound
        subst actualInputWidth
        have valueEq := hmodels value valueRef valid valueMatch valueFound
        have valueEntry := semanticEntry_of_resolveAt env valueRef _ _ valueEq
        exact ⟨rfl, by
          simp [IndexedRhs.elaborate, guard, valueEntry, rhsOk]⟩

/-- Elaborating one accepted numbered wire extends the semantic environment
invariant from `current` to `current + 1`. -/
theorem elaborateIndexedWire_preserves
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current : Nat) (wire : IndexedWire) (env : SemanticEnv)
    (henv : IndexedEnvResolvesBefore program wires table current env)
    (accepted : indexedWireWellFormedAt program wires table current wire = true) :
    ∃ value : Expr wire.width,
      wire.rhs.elaborate program env wire.width = some value ∧
      IndexedEnvResolvesBefore program wires table (current + 1)
        (env.insertWire wire.number wire.width value) := by
  simp only [indexedWireWellFormedAt, Bool.and_eq_true, beq_iff_eq] at accepted
  have numberEq : wire.number = current := accepted.1.1
  have lookupEq : lookupIndexed? wires table current = some wire := accepted.1.2
  obtain ⟨value, valueEq⟩ := indexedRhsWellFormed_elaborate_isSome
    program wires table current wire.width wire.rhs env henv accepted.2
  rw [numberEq]
  refine ⟨value, valueEq, ?_⟩
  intro reference width found
  cases reference with
  | reg name =>
      have previous : refWidthBefore? program wires table current (.reg name) =
          some width := by
        simpa [refWidthBefore?] using found
      obtain ⟨resolved, resolvedEq⟩ := henv (.reg name) width previous
      exact ⟨resolved, by
        simpa [SemanticEnv.insertWire] using resolvedEq⟩
  | wire number =>
      by_cases same : number = current
      · subst number
        have widthEq : wire.width = width := by
          exact refWidthBefore_wire_lookup_width program wires table
            (current + 1) current width wire lookupEq found
        subst width
        exact ⟨value, by
          simp [SemanticEnv.get, SemanticEnv.insertWire,
            SemanticEnv.resolveAt]⟩
      · have previous := refWidthBefore_wire_previous program wires table
          current number width same found
        obtain ⟨resolved, resolvedEq⟩ := henv (.wire number) width previous
        have refNe : Ref.wire number ≠ Ref.wire current := by
          intro equal
          cases equal
          exact same rfl
        exact ⟨resolved, by
          unfold SemanticEnv.resolveAt at resolvedEq ⊢
          simpa [SemanticEnv.get, SemanticEnv.insertWire, refNe]
            using resolvedEq⟩
  | namedWire number name =>
      by_cases same : number = current
      · subst number
        have widthEq : wire.width = width :=
          refWidthBefore_named_lookup_width program wires table
            (current + 1) current width name wire lookupEq found
        subst width
        exact ⟨value, by
          simp [SemanticEnv.get, SemanticEnv.insertWire,
            SemanticEnv.resolveAt]⟩
      · have previous := refWidthBefore_named_previous program wires table
          current number width name same found
        obtain ⟨resolved, resolvedEq⟩ :=
          henv (.namedWire number name) width previous
        exact ⟨resolved, by
          unfold SemanticEnv.resolveAt at resolvedEq ⊢
          simpa [SemanticEnv.get, SemanticEnv.insertWire, same]
            using resolvedEq⟩

/-- One accepted assignment preserves both type resolution and exact
compiler-expression correspondence. -/
theorem elaborateIndexedWire_preservesModels
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (current : Nat) (wire : IndexedWire) (env : SemanticEnv)
    (henv : IndexedEnvResolvesBefore program wires table current env)
    (hmodels : IndexedEnvModelsBefore program wires table current env)
    (accepted : indexedWireWellFormedAt program wires table current wire = true) :
    ∃ value : Expr wire.width,
      wire.rhs.elaborate program env wire.width = some value ∧
      IndexedEnvResolvesBefore program wires table (current + 1)
        (env.insertWire wire.number wire.width value) ∧
      IndexedEnvModelsBefore program wires table (current + 1)
        (env.insertWire wire.number wire.width value) := by
  obtain ⟨value, valueEq, nextEnv⟩ := elaborateIndexedWire_preserves
    program wires table current wire env henv accepted
  have numberEq : wire.number = current := by
    have parts : (wire.number = current ∧
        lookupIndexed? wires table current = some wire) ∧
        indexedRhsWellFormed program wires table current wire.width wire.rhs =
          true := by
      simpa only [indexedWireWellFormedAt, Bool.and_eq_true, beq_iff_eq]
        using accepted
    exact parts.1.1
  refine ⟨value, valueEq, nextEnv, ?_⟩
  intro width expr reference valid matchOk inScope
  cases reference with
  | reg name =>
      have previous : refWidthBefore? program wires table current (.reg name) =
          some width := by
        simpa [refWidthBefore?] using inScope
      have resolved := hmodels expr (.reg name) valid matchOk previous
      unfold SemanticEnv.resolveAt at resolved ⊢
      simpa [SemanticEnv.insertWire] using resolved
  | wire number =>
      by_cases same : number = current
      · subst number
        obtain ⟨widthEq, exactEq⟩ := indexedExprMatches_current_elaborate
          program wires table current env hmodels expr wire valid accepted matchOk
        cases widthEq
        have exactEq' : wire.rhs.elaborate program env wire.width =
            some expr := by simpa using exactEq
        have valueIsExpr : value = expr := by
          rw [valueEq] at exactEq'
          exact Option.some.inj exactEq'
        subst value
        rw [numberEq]
        simp [SemanticEnv.get, SemanticEnv.insertWire,
          SemanticEnv.resolveAt]
      · have previous := refWidthBefore_wire_previous program wires table
          current number width same inScope
        have resolved := hmodels expr (.wire number) valid matchOk previous
        have refNe : Ref.wire number ≠ Ref.wire wire.number := by
          rw [numberEq]
          intro equal
          cases equal
          exact same rfl
        unfold SemanticEnv.resolveAt at resolved ⊢
        simpa [SemanticEnv.get, SemanticEnv.insertWire, refNe] using resolved
  | namedWire number name =>
      by_cases same : number = current
      · subst number
        have wireMatch : indexedExprMatches wires table expr (.wire current) =
            true := by
          rw [indexedExprMatches_named_eq_wire] at matchOk
          exact matchOk
        obtain ⟨widthEq, exactEq⟩ := indexedExprMatches_current_elaborate
          program wires table current env hmodels expr wire valid accepted wireMatch
        cases widthEq
        have exactEq' : wire.rhs.elaborate program env wire.width =
            some expr := by simpa using exactEq
        have valueIsExpr : value = expr := by
          rw [valueEq] at exactEq'
          exact Option.some.inj exactEq'
        subst value
        rw [numberEq]
        simp [SemanticEnv.get, SemanticEnv.insertWire,
          SemanticEnv.resolveAt]
      · have previous := refWidthBefore_named_previous program wires table
          current number width name same inScope
        have resolved := hmodels expr (.namedWire number name) valid matchOk previous
        have differentWire : number ≠ wire.number := by simpa [numberEq] using same
        unfold SemanticEnv.resolveAt at resolved ⊢
        simpa [SemanticEnv.get, SemanticEnv.insertWire, differentWire]
          using resolved

/-- Elaborating an accepted sequential leaf preserves the lookup invariant
through every numbered assignment in the leaf. -/
theorem elaborateIndexedBlock_preserves
    (program : Program) (allWires : Rope (List IndexedWire))
    (table : WireTable) (start : Nat) (block : List IndexedWire)
    (env : SemanticEnv)
    (henv : IndexedEnvResolvesBefore program allWires table start env)
    (accepted : indexedSemanticBlockMatches program allWires table start block =
      true) :
    ∃ out,
      elaborateIndexedBlock program block env = some out ∧
      IndexedEnvResolvesBefore program allWires table
        (start + block.length) out := by
  induction block generalizing start env with
  | nil =>
      exact ⟨env, rfl, by simpa using henv⟩
  | cons wire rest ih =>
      simp only [indexedSemanticBlockMatches, Bool.and_eq_true] at accepted
      obtain ⟨value, valueEq, nextEnv⟩ := elaborateIndexedWire_preserves
        program allWires table start wire env henv accepted.1
      obtain ⟨out, outEq, outEnv⟩ := ih
        (start := start + 1)
        (env := env.insertWire wire.number wire.width value)
        nextEnv accepted.2
      refine ⟨out, ?_, ?_⟩
      · simp [elaborateIndexedBlock, valueEq, outEq]
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outEnv

/-- Exact expression correspondence composes through a sequential leaf. -/
theorem elaborateIndexedBlock_preservesModels
    (program : Program) (allWires : Rope (List IndexedWire))
    (table : WireTable) (start : Nat) (block : List IndexedWire)
    (env : SemanticEnv)
    (henv : IndexedEnvResolvesBefore program allWires table start env)
    (hmodels : IndexedEnvModelsBefore program allWires table start env)
    (accepted : indexedSemanticBlockMatches program allWires table start block =
      true) :
    ∃ out,
      elaborateIndexedBlock program block env = some out ∧
      IndexedEnvResolvesBefore program allWires table
        (start + block.length) out ∧
      IndexedEnvModelsBefore program allWires table
        (start + block.length) out := by
  induction block generalizing start env with
  | nil =>
      exact ⟨env, rfl, by simpa using henv,
        indexedModels_current_eq program allWires table _ _ env
          (by simp) hmodels⟩
  | cons wire rest ih =>
      simp only [indexedSemanticBlockMatches, Bool.and_eq_true] at accepted
      obtain ⟨value, valueEq, nextEnv, nextModels⟩ :=
        elaborateIndexedWire_preservesModels program allWires table start wire
          env henv hmodels accepted.1
      obtain ⟨out, outEq, outEnv, outModels⟩ := ih
        (start := start + 1)
        (env := env.insertWire wire.number wire.width value)
        nextEnv nextModels accepted.2
      refine ⟨out, ?_, ?_, ?_⟩
      · simp [elaborateIndexedBlock, valueEq, outEq]
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outEnv
      · apply indexedModels_current_eq program allWires table
          ((start + 1) + rest.length) (start + (wire :: rest).length) out
        · simp [Nat.add_comm, Nat.add_left_comm]
        · exact outModels

/-- Balanced well-formedness evidence is sufficient for elaborating the
corresponding rope while preserving all earlier structural references. -/
theorem elaborateIndexedRope_preserves
    (program : Program) (allWires : Rope (List IndexedWire))
    (table : WireTable) (start : Nat) (rope : Rope (List IndexedWire))
    (env : SemanticEnv)
    (hwellFormed : IndexedRopeWellFormed program allWires table start rope)
    (henv : IndexedEnvResolvesBefore program allWires table start env) :
    ∃ out,
      elaborateIndexedRope program rope env = some out ∧
      IndexedEnvResolvesBefore program allWires table
        (start + rope.listLength) out := by
  induction hwellFormed generalizing env with
  | leaf accepted =>
      simpa [elaborateIndexedRope, Rope.listLength] using
        elaborateIndexedBlock_preserves program allWires table _ _ env
          henv accepted
  | @node start left right leftProof rightProof leftIH rightIH =>
      obtain ⟨leftEnv, leftEq, leftInv⟩ := leftIH env henv
      obtain ⟨out, outEq, outInv⟩ := rightIH leftEnv leftInv
      refine ⟨out, ?_, ?_⟩
      · simp [elaborateIndexedRope, leftEq, outEq]
      · simpa [Rope.listLength, Nat.add_assoc] using outInv

/-- Exact expression correspondence composes across balanced rope nodes. -/
theorem elaborateIndexedRope_preservesModels
    (program : Program) (allWires : Rope (List IndexedWire))
    (table : WireTable) (start : Nat) (rope : Rope (List IndexedWire))
    (env : SemanticEnv)
    (hwellFormed : IndexedRopeWellFormed program allWires table start rope)
    (henv : IndexedEnvResolvesBefore program allWires table start env)
    (hmodels : IndexedEnvModelsBefore program allWires table start env) :
    ∃ out,
      elaborateIndexedRope program rope env = some out ∧
      IndexedEnvResolvesBefore program allWires table
        (start + rope.listLength) out ∧
      IndexedEnvModelsBefore program allWires table
        (start + rope.listLength) out := by
  induction hwellFormed generalizing env with
  | leaf accepted =>
      simpa [elaborateIndexedRope, Rope.listLength] using
        elaborateIndexedBlock_preservesModels program allWires table _ _ env
          henv hmodels accepted
  | @node start left right leftProof rightProof leftIH rightIH =>
      obtain ⟨leftEnv, leftEq, leftInv, leftModels⟩ :=
        leftIH env henv hmodels
      obtain ⟨out, outEq, outInv, outModels⟩ :=
        rightIH leftEnv leftInv leftModels
      refine ⟨out, ?_, ?_, ?_⟩
      · simp [elaborateIndexedRope, leftEq, outEq]
      · simpa [Rope.listLength, Nat.add_assoc] using outInv
      · apply indexedModels_current_eq program allWires table
          ((start + left.listLength) + right.listLength)
          (start + (Rope.node left right).listLength) out
        · simp [Rope.listLength, Nat.add_assoc]
        · exact outModels

/-- A whole-graph certificate guarantees that the structural SSA elaborator
constructs a complete typed environment. -/
theorem elaborateIndexedEnv_isSome
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (hwellFormed : IndexedRopeWellFormed program wires table 0 wires) :
    ∃ env,
      elaborateIndexedEnv program wires = some env ∧
      IndexedEnvResolvesBefore program wires table wires.listLength env := by
  obtain ⟨env, envEq, henv⟩ := elaborateIndexedRope_preserves
    program wires table 0 wires (SemanticEnv.initial program) hwellFormed
      (semanticInitial_resolvesBefore program wires table)
  exact ⟨env, envEq, by simpa using henv⟩

/-- Whole-graph elaboration yields an environment in which every accepted,
register-well-typed compiler expression resolves to the exact expression. -/
theorem elaborateIndexedEnv_models
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (hwellFormed : IndexedRopeWellFormed program wires table 0 wires) :
    ∃ env,
      elaborateIndexedEnv program wires = some env ∧
      IndexedEnvResolvesBefore program wires table wires.listLength env ∧
      IndexedEnvModelsBefore program wires table wires.listLength env := by
  obtain ⟨env, envEq, henv, hmodels⟩ := elaborateIndexedRope_preservesModels
    program wires table 0 wires (SemanticEnv.initial program) hwellFormed
      (semanticInitial_resolvesBefore program wires table)
      (semanticInitial_modelsBefore program wires table)
  exact ⟨env, envEq, by simpa using henv,
    indexedModels_current_eq program wires table (0 + wires.listLength)
      wires.listLength env (by simp) hmodels⟩

/-- An accepted expression root is in scope after every well-formed SSA wire
has been elaborated. -/
theorem indexedExprMatches_inScope
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (_hwellFormed : IndexedRopeWellFormed program wires table 0 wires)
    {width : Nat} (expr : Expr width) (reference : Ref)
    (_valid : ExprRegistersValid program expr)
    (_matchOk : indexedExprMatches wires table expr reference = true)
    (scope : refWidthBefore? program wires table wires.listLength reference =
      some width) :
    refWidthBefore? program wires table wires.listLength reference =
      some width := scope

/-- The whole-graph certificate turns an accepted, well-typed symbolic root
into exact equality with the corresponding reference-compiler expression. -/
theorem elaborateIndexedEnv_resolves
    (program : Program) (wires : Rope (List IndexedWire)) (table : WireTable)
    (hwellFormed : IndexedRopeWellFormed program wires table 0 wires)
    {width : Nat} (expr : Expr width) (reference : Ref)
    (valid : ExprRegistersValid program expr)
    (matchOk : indexedExprMatches wires table expr reference = true)
    (scope : refWidthBefore? program wires table wires.listLength reference =
      some width) :
    ∃ env,
      elaborateIndexedEnv program wires = some env ∧
      env.resolveAt reference width = some expr := by
  obtain ⟨env, envEq, _, hmodels⟩ := elaborateIndexedEnv_models
    program wires table hwellFormed
  have inScope := indexedExprMatches_inScope program wires table hwellFormed
    expr reference valid matchOk scope
  exact ⟨env, envEq, hmodels expr reference valid matchOk inScope⟩

/-- An accepted concrete register root resolves exactly to the reference
compiler's ordered next-state fold. -/
theorem indexedRegisterMatchesAt_resolves
    (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (readsValid : DesignReadsValid design program)
    (hwellFormed : IndexedRopeWellFormed program wires table 0 wires)
    (index : Nat) (source : Loom.Hw.RegDecl) (root : Ref)
    (sourceFound : design.regs[index]? = some source)
    (accepted : indexedRegisterMatchesAt design program wires table index root =
      true) :
    ∃ env,
      elaborateIndexedEnv program wires = some env ∧
      env.resolveAt root source.width = some
        (design.rules.foldl
          (fun current rule => Loom.Hw.Compile.nextReg source.name source.width
            rule.body current)
          (.reg source.width source.name)) := by
  cases concreteFound : program.regs[index]? with
  | none => simp [indexedRegisterMatchesAt, sourceFound, concreteFound] at accepted
  | some concrete =>
      simp only [indexedRegisterMatchesAt, sourceFound, concreteFound,
        Bool.and_eq_true, beq_iff_eq] at accepted
      have sourceMem : source ∈ design.regs := by
        obtain ⟨inBounds, atIndex⟩ :=
          List.getElem?_eq_some_iff.mp sourceFound
        rw [← atIndex]
        exact List.getElem_mem inBounds
      have valid := registerNext_registersValid readsValid source sourceMem
      exact elaborateIndexedEnv_resolves program wires table hwellFormed _ root
        valid accepted.2 accepted.1.2

/-- Accepted concrete memory-port roots resolve exactly to all three
expressions of the reference compiler port. -/
theorem indexedMemoryPortMatchesAt_resolves
    (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (readsValid : DesignReadsValid design program)
    (hwellFormed : IndexedRopeWellFormed program wires table 0 wires)
    (memoryIndex portIndex : Nat) (source : Loom.Hw.MemDecl)
    (refs : PortRefs) (sourceFound : design.mems[memoryIndex]? = some source)
    (accepted : indexedMemoryPortMatchesAt design program wires table
      memoryIndex portIndex refs = true) :
    let compiled := Loom.Hw.Compile.compilePort design source.name
      source.addrWidth source.dataWidth portIndex
    ∃ env,
      elaborateIndexedEnv program wires = some env ∧
      env.resolveAt refs.en 1 = some compiled.en ∧
      env.resolveAt refs.addr source.addrWidth = some compiled.addr ∧
      env.resolveAt refs.data source.dataWidth = some compiled.data := by
  cases concreteFound : program.mems[memoryIndex]? with
  | none =>
      simp [indexedMemoryPortMatchesAt, sourceFound, concreteFound] at accepted
  | some concrete =>
      cases writeFound : concrete.writes[portIndex]? with
      | none =>
          simp [indexedMemoryPortMatchesAt, sourceFound, concreteFound,
            writeFound] at accepted
      | some write =>
          simp only [indexedMemoryPortMatchesAt, sourceFound, concreteFound,
            writeFound, Bool.and_eq_true, beq_iff_eq] at accepted
          let compiled := Loom.Hw.Compile.compilePort design source.name
            source.addrWidth source.dataWidth portIndex
          have valid : PortRegistersValid program compiled :=
            compilePort_registersValid readsValid source.name source.addrWidth
              source.dataWidth portIndex
          obtain ⟨env, envEq, _, hmodels⟩ := elaborateIndexedEnv_models
            program wires table hwellFormed
          have enScope := indexedExprMatches_inScope program wires table
            hwellFormed compiled.en refs.en valid.1 accepted.1.1.2
              accepted.1.1.1.1.1.2
          have addrScope := indexedExprMatches_inScope program wires table
            hwellFormed compiled.addr refs.addr valid.2.1 accepted.1.2
              accepted.1.1.1.1.2
          have dataScope := indexedExprMatches_inScope program wires table
            hwellFormed compiled.data refs.data valid.2.2 accepted.2
              accepted.1.1.1.2
          exact ⟨env, envEq,
            hmodels compiled.en refs.en valid.1 accepted.1.1.2 enScope,
            hmodels compiled.addr refs.addr valid.2.1 accepted.1.2 addrScope,
            hmodels compiled.data refs.data valid.2.2 accepted.2 dataScope⟩

end Loom.Release.Symbolic
