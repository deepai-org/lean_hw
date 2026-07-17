-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate

/-!
# Soundness of symbolic SSA certificates

This module proves that the bounded indexed checker denotes the raw concrete
SSA witness. The proofs quantify over arbitrary generator output and table
paths; no generator invariant is assumed.
-/

namespace Loom.Release.Symbolic

open Loom.Release.SSA

private theorem optionFailure {α : Type} : (failure : Option α) = none := rfl

theorem indexedBlockMatches_get
    {start : Nat} {raws : List Wire} {indexeds : List IndexedWire}
    (accepted : indexedBlockMatches start raws indexeds = true) :
    ∀ (index : Nat) (indexed : IndexedWire), indexeds[index]? = some indexed →
      ∃ raw, raws[index]? = some raw ∧
        indexed.matchesRaw indexed.number raw = true := by
  induction raws generalizing start indexeds with
  | nil =>
      intro index indexed found
      cases indexeds <;> simp [indexedBlockMatches] at accepted found
  | cons raw raws ih =>
      cases indexeds with
      | nil => simp [indexedBlockMatches] at accepted
      | cons indexedHead indexedTail =>
        rw [indexedBlockMatches] at accepted
        have parts : indexedHead.matchesRaw start raw = true ∧
            indexedBlockMatches (start + 1) raws indexedTail = true := by
          simpa only [Bool.and_eq_true] using accepted
        intro index indexed found
        cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst indexed
            have numberEq : indexedHead.number = start := by
              have numberTrue := parts.1
              simp only [IndexedWire.matchesRaw, Bool.and_eq_true] at numberTrue
              exact beq_iff_eq.mp numberTrue.1.1.1
            refine ⟨raw, rfl, ?_⟩
            simpa only [numberEq] using parts.1
        | succ index =>
            simp only [List.getElem?_cons_succ] at found
            exact ih parts.2 index indexed found

theorem IndexedRopeMatches.resolve
    {start : Nat} {raws : Rope (List Wire)}
    {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches start raws indexeds) :
    ∀ (reference : Rope.Ref) (indexed : IndexedWire),
      indexeds.resolve? reference = some indexed →
      ∃ raw, raws.resolve? reference = some raw ∧
        indexed.matchesRaw indexed.number raw = true := by
  induction hmatches with
  | leaf accepted =>
      intro reference indexed found
      cases reference with
      | mk path offset =>
        cases path with
        | nil =>
            simp only [Rope.resolve_leaf] at found ⊢
            exact indexedBlockMatches_get accepted offset indexed found
        | cons step path =>
            simp [Rope.resolve?] at found
  | node left right leftIH rightIH =>
      intro reference indexed found
      cases reference with
      | mk path offset =>
        cases path with
        | nil => simp [Rope.resolve?] at found
        | cons step path =>
            cases step with
            | false =>
                simp only [Rope.resolve_node_left] at found ⊢
                exact leftIH ⟨path, offset⟩ indexed found
            | true =>
                simp only [Rope.resolve_node_right] at found ⊢
                exact rightIH ⟨path, offset⟩ indexed found

theorem lookupIndexed_resolvesRaw
    {raws : Rope (List Wire)} {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 raws indexeds)
    (table : WireTable) (number : Nat) (indexed : IndexedWire)
    (found : lookupIndexed? indexeds table number = some indexed) :
    ∃ path raw,
      table.paths[number / table.leafSize]? = some path ∧
      raws.resolve? ⟨path, number % table.leafSize⟩ = some raw ∧
      indexed.matchesRaw number raw = true := by
  unfold lookupIndexed? at found
  by_cases size : table.leafSize > 0
  · simp only [size, Option.bind_eq_bind] at found
    cases pathEq : table.paths[number / table.leafSize]? with
    | none => simp [pathEq] at found
    | some path =>
      simp only [pathEq, Option.bind_some] at found
      cases indexedEq : indexeds.resolve? ⟨path, number % table.leafSize⟩ with
      | none => simp [indexedEq] at found
      | some actual =>
        simp only [indexedEq, Option.bind_some] at found
        by_cases numberEq : actual.number = number
        · simp [guard, numberEq] at found
          subst indexed
          obtain ⟨raw, rawEq, rawMatch⟩ :=
            hmatches.resolve ⟨path, number % table.leafSize⟩ actual indexedEq
          refine ⟨path, raw, rfl, rawEq, ?_⟩
          simpa only [numberEq] using rawMatch
        · exfalso
          simp [guard, optionFailure, beq_iff_eq, numberEq] at found
  · exfalso
    simp [guard, optionFailure, size] at found

/-- A raw witness wire is physically present at the table address for its
number and bears the canonical numbered identifier. -/
def RawWireAt (program : Program) (table : WireTable)
    (number : Nat) (raw : Wire) : Prop :=
  ∃ path,
    table.paths[number / table.leafSize]? = some path ∧
    program.wires.resolve? ⟨path, number % table.leafSize⟩ = some raw ∧
    raw.name = (Ref.wire number).render

theorem lookupIndexed_rawWireAt
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (number : Nat) (indexed : IndexedWire)
    (found : lookupIndexed? indexeds table number = some indexed) :
    ∃ raw, RawWireAt program table number raw ∧
      indexed.matchesRaw number raw = true := by
  obtain ⟨path, raw, pathEq, rawEq, rawMatch⟩ :=
    lookupIndexed_resolvesRaw hmatches table number indexed found
  have nameEq : raw.name = (Ref.wire number).render := by
    have parts := rawMatch
    simp only [IndexedWire.matchesRaw, Bool.and_eq_true] at parts
    exact beq_iff_eq.mp parts.1.1.2
  exact ⟨raw, ⟨path, pathEq, rawEq, nameEq⟩, rawMatch⟩

def IndexedRhs.toRaw : IndexedRhs → Rhs
  | .lit width value => .lit width value
  | .ident value => .ident value.render
  | .memRead mem address => .memRead mem address.render
  | .slice value hi lo => .slice value.render hi lo
  | .not value => .not value.render
  | .bin op left right => .bin op left.render right.render
  | .slt left right => .slt left.render right.render
  | .mux condition yes no => .mux condition.render yes.render no.render
  | .sext amount value signBit => .sext amount value.render signBit

theorem IndexedWire.matchesRaw_width_rhs
    {number : Nat} {raw : Wire} {indexed : IndexedWire}
    (accepted : indexed.matchesRaw number raw = true) :
    raw.width = indexed.width ∧ raw.rhs = indexed.rhs.toRaw := by
  rcases raw with ⟨rawWidth, rawName, rawRhs⟩
  rcases indexed with ⟨indexedNumber, indexedWidth, indexedRhs⟩
  cases rawRhs <;> cases indexedRhs <;>
    simp_all [IndexedWire.matchesRaw, IndexedRhs.toRaw, Bool.and_eq_true,
      beq_iff_eq]

/-- Declarative meaning of a source µVerilog expression in the raw concrete
SSA graph. This relation contains no indexed witness data. -/
inductive RawExprMatches (program : Program) (table : WireTable) :
    {width : Nat} → Loom.Emit.MicroVerilog.Expr width → Ref → Prop
  | reg (width : Nat) (name : String) :
      RawExprMatches program table (.reg width name) (.reg name)
  | lit {width value number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .lit width value.toNat →
      RawExprMatches program table (.lit value) (.wire number)
  | memRead {addressWidth dataWidth mem address addressRef number raw} :
      RawWireAt program table number raw → raw.width = dataWidth →
      raw.rhs = .memRead mem addressRef.render →
      RawExprMatches program table address addressRef →
      RawExprMatches program table
        (.memRead dataWidth mem (address : Loom.Emit.MicroVerilog.Expr addressWidth))
        (.wire number)
  | and {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .and leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.and left right) (.wire number)
  | or {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .or leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.or left right) (.wire number)
  | xor {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .xor leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.xor left right) (.wire number)
  | not {width value valueRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .not valueRef.render →
      RawExprMatches program table value valueRef →
      RawExprMatches program table (.not value) (.wire number)
  | add {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .add leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.add left right) (.wire number)
  | sub {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .sub leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.sub left right) (.wire number)
  | shl {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .shl leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.shl left right) (.wire number)
  | shr {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .shr leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.shr left right) (.wire number)
  | eq {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = 1 →
      raw.rhs = .bin .eq leftRef.render rightRef.render →
      RawExprMatches program table (left : Loom.Emit.MicroVerilog.Expr width) leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.eq left right) (.wire number)
  | ult {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = 1 →
      raw.rhs = .bin .ult leftRef.render rightRef.render →
      RawExprMatches program table (left : Loom.Emit.MicroVerilog.Expr width) leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.ult left right) (.wire number)
  | slt {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = 1 →
      raw.rhs = .slt leftRef.render rightRef.render →
      RawExprMatches program table (left : Loom.Emit.MicroVerilog.Expr width) leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.slt left right) (.wire number)
  | mux {width condition yes no conditionRef yesRef noRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .mux conditionRef.render yesRef.render noRef.render →
      RawExprMatches program table condition conditionRef →
      RawExprMatches program table yes yesRef →
      RawExprMatches program table no noRef →
      RawExprMatches program table (.mux condition yes no) (.wire number)
  | slice {inputWidth width value lo valueRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .slice valueRef.render (lo + width - 1) lo →
      RawExprMatches program table
        (value : Loom.Emit.MicroVerilog.Expr inputWidth) valueRef →
      RawExprMatches program table (.slice value lo width) (.wire number)
  | zext {inputWidth width value valueRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .ident valueRef.render → inputWidth ≤ width →
      RawExprMatches program table value valueRef →
      RawExprMatches program table (.zext value width) (.wire number)
  | sext {inputWidth width value valueRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .sext (width - inputWidth) valueRef.render (inputWidth - 1) →
      inputWidth < width → RawExprMatches program table value valueRef →
      RawExprMatches program table (.sext value width) (.wire number)

/-- Acceptance by the indexed expression checker is sound for arbitrary
indexed ropes and address tables: it produces a derivation solely about the
raw concrete SSA program. -/
theorem indexedExprMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) {width : Nat}
    (expr : Loom.Emit.MicroVerilog.Expr width) (reference : Ref)
    (accepted : indexedExprMatches indexeds table expr reference = true) :
    RawExprMatches program table expr reference := by
  induction expr generalizing reference with
  | reg width name =>
      cases reference with
      | reg actual =>
          simp only [indexedExprMatches, beq_iff_eq] at accepted
          subst actual
          exact .reg width name
      | wire number => simp [indexedExprMatches] at accepted
  | lit value =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case lit literalWidth actualValue =>
                obtain ⟨raw, rawAt, rawMatch⟩ :=
                  lookupIndexed_rawWireAt program hmatches table number
                    ⟨indexedNumber, actualWidth, .lit literalWidth actualValue⟩ found
                obtain ⟨widthEq, rhsEq⟩ :=
                  IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .lit literalWidth actualValue⟩) rawMatch
                exact .lit rawAt (widthEq.trans accepted.1.1)
                  (rhsEq.trans (by simp [IndexedRhs.toRaw, accepted.1.2,
                    accepted.2]))
  | memRead dataWidth mem address addressIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case memRead actualMem actualAddress =>
                obtain ⟨raw, rawAt, rawMatch⟩ :=
                  lookupIndexed_rawWireAt program hmatches table number
                    ⟨indexedNumber, actualWidth, .memRead actualMem actualAddress⟩ found
                obtain ⟨widthEq, rhsEq⟩ :=
                  IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .memRead actualMem actualAddress⟩) rawMatch
                exact .memRead rawAt (widthEq.trans accepted.1.1)
                  (rhsEq.trans (by simp [IndexedRhs.toRaw, accepted.1.2]))
                  (addressIH actualAddress accepted.2)
  | and left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case and =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .and actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ :=
                    IndexedWire.matchesRaw_width_rhs
                      (indexed := ⟨indexedNumber, actualWidth,
                        .bin .and actualLeft actualRight⟩) rawMatch
                  exact .and rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2)
                    (rightIH actualRight accepted.2)
  | or left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case or =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .or actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ :=
                    IndexedWire.matchesRaw_width_rhs
                      (indexed := ⟨indexedNumber, actualWidth,
                        .bin .or actualLeft actualRight⟩) rawMatch
                  exact .or rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2)
                    (rightIH actualRight accepted.2)
  | xor left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case xor =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .xor actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ :=
                    IndexedWire.matchesRaw_width_rhs
                      (indexed := ⟨indexedNumber, actualWidth,
                        .bin .xor actualLeft actualRight⟩) rawMatch
                  exact .xor rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2)
                    (rightIH actualRight accepted.2)
  | not value valueIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case not actual =>
                obtain ⟨raw, rawAt, rawMatch⟩ :=
                  lookupIndexed_rawWireAt program hmatches table number
                    ⟨indexedNumber, actualWidth, .not actual⟩ found
                obtain ⟨widthEq, rhsEq⟩ :=
                  IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth, .not actual⟩) rawMatch
                exact .not rawAt (widthEq.trans accepted.1) rhsEq
                  (valueIH actual accepted.2)
  | add left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case add =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .add actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .add actualLeft actualRight⟩) rawMatch
                  exact .add rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
  | sub left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case sub =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .sub actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .sub actualLeft actualRight⟩) rawMatch
                  exact .sub rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
  | shl left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case shl =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .shl actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .shl actualLeft actualRight⟩) rawMatch
                  exact .shl rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
  | shr left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case shr =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .shr actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .shr actualLeft actualRight⟩) rawMatch
                  exact .shr rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
  | eq left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                split at accepted
                next matchEq =>
                  cases matchEq
                  simp only [Bool.and_eq_true] at accepted
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, 1, .bin .eq actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, 1,
                      .bin .eq actualLeft actualRight⟩) rawMatch
                  exact .eq rawAt widthEq rhsEq
                    (leftIH actualLeft accepted.1) (rightIH actualRight accepted.2)
                next mismatch => simp at accepted
  | ult left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                split at accepted
                next matchEq =>
                  cases matchEq
                  simp only [Bool.and_eq_true] at accepted
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, 1, .bin .ult actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, 1,
                      .bin .ult actualLeft actualRight⟩) rawMatch
                  exact .ult rawAt widthEq rhsEq
                    (leftIH actualLeft accepted.1) (rightIH actualRight accepted.2)
                next mismatch => simp at accepted
  | slt left right leftIH rightIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case slt actualLeft actualRight =>
                split at accepted
                next matchEq =>
                  cases matchEq
                  simp only [Bool.and_eq_true] at accepted
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, 1, .slt actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, 1,
                      .slt actualLeft actualRight⟩) rawMatch
                  exact .slt rawAt widthEq rhsEq
                    (leftIH actualLeft accepted.1) (rightIH actualRight accepted.2)
                next mismatch => simp at accepted
  | mux condition yes no conditionIH yesIH noIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case mux actualCondition actualYes actualNo =>
                obtain ⟨raw, rawAt, rawMatch⟩ :=
                  lookupIndexed_rawWireAt program hmatches table number
                    ⟨indexedNumber, actualWidth,
                      .mux actualCondition actualYes actualNo⟩ found
                obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                  (indexed := ⟨indexedNumber, actualWidth,
                    .mux actualCondition actualYes actualNo⟩) rawMatch
                exact .mux rawAt (widthEq.trans accepted.1.1.1) rhsEq
                  (conditionIH actualCondition accepted.1.1.2)
                  (yesIH actualYes accepted.1.2) (noIH actualNo accepted.2)
  | slice value lo width valueIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case slice actualValue hi actualLo =>
                obtain ⟨raw, rawAt, rawMatch⟩ :=
                  lookupIndexed_rawWireAt program hmatches table number
                    ⟨indexedNumber, actualWidth,
                      .slice actualValue hi actualLo⟩ found
                obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                  (indexed := ⟨indexedNumber, actualWidth,
                    .slice actualValue hi actualLo⟩) rawMatch
                exact .slice rawAt (widthEq.trans accepted.1.1.1)
                  (rhsEq.trans (by simp [IndexedRhs.toRaw, accepted.1.1.2,
                    accepted.1.2]))
                  (valueIH actualValue accepted.2)
  | zext value width valueIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case ident actual =>
                obtain ⟨raw, rawAt, rawMatch⟩ :=
                  lookupIndexed_rawWireAt program hmatches table number
                    ⟨indexedNumber, actualWidth, .ident actual⟩ found
                obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                  (indexed := ⟨indexedNumber, actualWidth, .ident actual⟩) rawMatch
                exact .zext rawAt (widthEq.trans accepted.1.1) rhsEq
                  accepted.1.2 (valueIH actual accepted.2)
  | @sext inputWidth value width valueIH =>
      cases reference with
      | reg name => simp [indexedExprMatches] at accepted
      | wire number =>
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case sext amount actual signBit =>
                obtain ⟨raw, rawAt, rawMatch⟩ :=
                  lookupIndexed_rawWireAt program hmatches table number
                    ⟨indexedNumber, actualWidth, .sext amount actual signBit⟩ found
                obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                  (indexed := ⟨indexedNumber, actualWidth,
                    .sext amount actual signBit⟩) rawMatch
                have signEq : signBit = inputWidth - 1 := by omega
                exact .sext rawAt (widthEq.trans accepted.1.1.1.1)
                  (by simpa [IndexedRhs.toRaw, accepted.1.1.2, signEq]
                    using rhsEq)
                  accepted.1.1.1.2 (valueIH actual accepted.2)

end Loom.Release.Symbolic
