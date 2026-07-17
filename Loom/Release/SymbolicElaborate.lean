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

/-! ## Soundness infrastructure -/

private theorem semanticOptionFailure {α : Type} :
    (failure : Option α) = none := rfl

/-- The semantic environment resolves exactly the widths accepted by the
bounded whole-graph checker before wire `current`. -/
def IndexedEnvResolvesBefore (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (current : Nat) (env : SemanticEnv) : Prop :=
  ∀ reference width,
    refWidthBefore? program wires table current reference = some width →
    ∃ value : Expr width, env.resolveAt reference width = some value

private theorem semanticEntry_of_resolveAt
    (env : SemanticEnv) (reference : Ref) (width : Nat) (value : Expr width)
    (accepted : env.resolveAt reference width = some value) :
    env reference = some ⟨width, value⟩ := by
  unfold SemanticEnv.resolveAt at accepted
  cases found : env reference with
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
    (leftEntry : env leftRef = some ⟨width, left⟩)
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
      | and | or | xor | add | sub | shl | shr =>
          simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at accepted
          obtain ⟨left, leftEq⟩ := henv leftRef resultWidth accepted.1
          obtain ⟨right, rightEq⟩ := henv rightRef resultWidth accepted.2
          first
          | exact ⟨.and left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.or left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.xor left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.add left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
          | exact ⟨.sub left right, semanticBinSame_of_resolveAt _ _ _ _ _ _ _ leftEq rightEq⟩
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
                simp [SemanticEnv.resolveAt, SemanticEnv.initial, found]⟩
  | wire number =>
      unfold refWidthBefore? at accepted
      have notEarlier : ¬number < 0 := Nat.not_lt_zero number
      simp only [notEarlier, guard] at accepted
      rw [semanticOptionFailure] at accepted
      simp at accepted

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
          unfold refWidthBefore? at found
          simpa [guard, lookupEq] using found
        subst width
        exact ⟨value, by
          simp [SemanticEnv.insertWire, SemanticEnv.resolveAt]⟩
      · have previous := refWidthBefore_wire_previous program wires table
          current number width same found
        obtain ⟨resolved, resolvedEq⟩ := henv (.wire number) width previous
        have refNe : Ref.wire number ≠ Ref.wire current := by
          intro equal
          cases equal
          exact same rfl
        exact ⟨resolved, by
          unfold SemanticEnv.resolveAt at resolvedEq ⊢
          simpa [SemanticEnv.insertWire, refNe] using resolvedEq⟩

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

end Loom.Release.Symbolic
