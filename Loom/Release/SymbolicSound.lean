-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate
import Std.Data.TreeMap.Lemmas

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

theorem indexedBlockMatches_getRaw
    {start : Nat} {raws : List Wire} {indexeds : List IndexedWire}
    (accepted : indexedBlockMatches start raws indexeds = true) :
    ∀ (index : Nat) (raw : Wire), raws[index]? = some raw →
      ∃ indexed, indexeds[index]? = some indexed ∧
        indexed.matchesRaw indexed.number raw = true := by
  induction raws generalizing start indexeds with
  | nil =>
      intro index raw found
      simp at found
  | cons rawHead rawTail ih =>
      cases indexeds with
      | nil => simp [indexedBlockMatches] at accepted
      | cons indexedHead indexedTail =>
          rw [indexedBlockMatches] at accepted
          have parts : indexedHead.matchesRaw start rawHead = true ∧
              indexedBlockMatches (start + 1) rawTail indexedTail = true := by
            simpa only [Bool.and_eq_true] using accepted
          intro index raw found
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst raw
              have numberEq : indexedHead.number = start := by
                have numberTrue := parts.1
                simp only [IndexedWire.matchesRaw, Bool.and_eq_true] at numberTrue
                exact beq_iff_eq.mp numberTrue.1.1.1
              exact ⟨indexedHead, rfl, by simpa only [numberEq] using parts.1⟩
          | succ index =>
              simp only [List.getElem?_cons_succ] at found
              exact ih parts.2 index raw found

theorem IndexedRopeMatches.resolveRaw
    {start : Nat} {raws : Rope (List Wire)}
    {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches start raws indexeds) :
    ∀ (reference : Rope.Ref) (raw : Wire),
      raws.resolve? reference = some raw →
      ∃ indexed, indexeds.resolve? reference = some indexed ∧
        indexed.matchesRaw indexed.number raw = true := by
  induction hmatches with
  | leaf accepted =>
      intro reference raw found
      cases reference with
      | mk path offset =>
          cases path with
          | nil =>
              simp only [Rope.resolve_leaf] at found ⊢
              exact indexedBlockMatches_getRaw accepted offset raw found
          | cons step path => simp [Rope.resolve?] at found
  | node left right leftIH rightIH =>
      intro reference raw found
      cases reference with
      | mk path offset =>
          cases path with
          | nil => simp [Rope.resolve?] at found
          | cons step path =>
              cases step with
              | false =>
                  simp only [Rope.resolve_node_left] at found ⊢
                  exact leftIH ⟨path, offset⟩ raw found
              | true =>
                  simp only [Rope.resolve_node_right] at found ⊢
                  exact rightIH ⟨path, offset⟩ raw found

theorem indexedSemanticBlock_get
    {program : Program} {allWires : Rope (List IndexedWire)}
    {table : WireTable} {start : Nat} {wires : List IndexedWire}
    (accepted : indexedSemanticBlockMatches program allWires table start wires =
      true) :
    ∀ (index : Nat) (wire : IndexedWire), wires[index]? = some wire →
      indexedWireWellFormedAt program allWires table wire.number wire = true := by
  induction wires generalizing start with
  | nil => intro index wire found; simp at found
  | cons head tail ih =>
      rw [indexedSemanticBlockMatches] at accepted
      have parts : indexedWireWellFormedAt program allWires table start head = true ∧
          indexedSemanticBlockMatches program allWires table (start + 1) tail =
            true := by
        simpa only [Bool.and_eq_true] using accepted
      intro index wire found
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst wire
          have numberEq : head.number = start := by
            have numberTrue := parts.1
            simp only [indexedWireWellFormedAt, Bool.and_eq_true] at numberTrue
            exact beq_iff_eq.mp numberTrue.1.1
          simpa only [numberEq] using parts.1
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          exact ih parts.2 index wire found

theorem IndexedRopeWellFormed.resolve
    {program : Program} {allWires : Rope (List IndexedWire)}
    {table : WireTable} {start : Nat} {wires : Rope (List IndexedWire)}
    (hwellFormed : IndexedRopeWellFormed program allWires table start wires) :
    ∀ (reference : Rope.Ref) (wire : IndexedWire),
      wires.resolve? reference = some wire →
      indexedWireWellFormedAt program allWires table wire.number wire = true := by
  induction hwellFormed with
  | leaf accepted =>
      intro reference wire found
      cases reference with
      | mk path offset =>
          cases path with
          | nil =>
              simp only [Rope.resolve_leaf] at found
              exact indexedSemanticBlock_get accepted offset wire found
          | cons step path => simp [Rope.resolve?] at found
  | node leftProof rightProof leftIH rightIH =>
      intro reference wire found
      cases reference with
      | mk path offset =>
          cases path with
          | nil => simp [Rope.resolve?] at found
          | cons step path =>
              cases step with
              | false =>
                  simp only [Rope.resolve_node_left] at found
                  exact leftIH ⟨path, offset⟩ wire found
              | true =>
                  simp only [Rope.resolve_node_right] at found
                  exact rightIH ⟨path, offset⟩ wire found

theorem lookupIndexed_wellFormed
    {program : Program} {wires : Rope (List IndexedWire)}
    {table : WireTable}
    (hwellFormed : IndexedRopeWellFormed program wires table 0 wires)
    (number : Nat) (indexed : IndexedWire)
    (found : lookupIndexed? wires table number = some indexed) :
    indexedWireWellFormedAt program wires table number indexed = true := by
  unfold lookupIndexed? at found
  by_cases size : table.leafSize > 0
  · simp only [size, Option.bind_eq_bind] at found
    cases pathEq : table.paths[number / table.leafSize]? with
    | none => simp [pathEq] at found
    | some path =>
        simp only [pathEq, Option.bind_some] at found
        cases indexedEq : wires.resolve? ⟨path, number % table.leafSize⟩ with
        | none => simp [indexedEq] at found
        | some actual =>
            simp only [indexedEq, Option.bind_some] at found
            by_cases numberEq : actual.number = number
            · simp [guard, numberEq] at found
              subst indexed
              have accepted := hwellFormed.resolve
                ⟨path, number % table.leafSize⟩ actual indexedEq
              simpa only [numberEq] using accepted
            · exfalso
              simp [guard, optionFailure, beq_iff_eq, numberEq] at found
  · exfalso
    simp [guard, optionFailure, size] at found

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

/-- Declarative width resolution for an operand of wire `current`. Unlike the
Boolean checker, this proposition mentions only the raw program and records
the strict topological order of numbered wire references. -/
inductive RawRefWidth (program : Program) (table : WireTable)
    (current : Nat) : Ref → Nat → Prop
  | reg {name concrete}
      (notWire : wireNumber? name = none)
      (found : program.regs.find? (fun reg => reg.name == name) = some concrete) :
      RawRefWidth program table current (.reg name) concrete.width
  | wire {number raw}
      (earlier : number < current) (located : RawWireAt program table number raw) :
      RawRefWidth program table current (.wire number) raw.width

theorem refWidthBefore_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (current : Nat) (reference : Ref) (width : Nat)
    (accepted : refWidthBefore? program indexeds table current reference =
      some width) :
    RawRefWidth program table current reference width := by
  cases reference with
  | reg name =>
      unfold refWidthBefore? at accepted
      cases notWire : wireNumber? name with
      | some number =>
          simp only [notWire, Option.isNone_some, guard] at accepted
          rw [optionFailure] at accepted
          simp at accepted
      | none =>
          cases found : program.regs.find? (fun reg => reg.name == name) with
          | none => simp [notWire, found] at accepted
          | some concrete =>
              simp only [notWire, Option.isNone_none, guard,
                Option.bind_eq_bind, found, Option.bind_some] at accepted
              have widthEq : concrete.width = width := by
                simpa [guard, optionFailure] using accepted
              subst width
              exact .reg notWire found
  | wire number =>
      unfold refWidthBefore? at accepted
      by_cases earlier : number < current
      · simp only [earlier, guard, Option.bind_eq_bind] at accepted
        cases found : lookupIndexed? indexeds table number with
        | none => simp [found] at accepted
        | some indexed =>
            simp [found] at accepted
            subst width
            obtain ⟨raw, rawAt, rawMatch⟩ :=
              lookupIndexed_rawWireAt program hmatches table number indexed found
            obtain ⟨widthEq, _⟩ := IndexedWire.matchesRaw_width_rhs rawMatch
            rw [← widthEq]
            exact .wire earlier rawAt
      · simp only [earlier, guard] at accepted
        rw [optionFailure] at accepted
        simp at accepted

/-- Raw, generator-independent typing judgment corresponding to
`SSA.Rhs.elaborate`. -/
inductive RawRhsWellFormed (program : Program) (table : WireTable)
    (number resultWidth : Nat) : Rhs → Prop
  | lit {value} : RawRhsWellFormed program table number resultWidth
      (.lit resultWidth value)
  | ident {value inputWidth} :
      RawRefWidth program table number value inputWidth →
      RawRhsWellFormed program table number resultWidth (.ident value.render)
  | memRead {mem address header} :
      program.mems.find? (fun candidate => candidate.name == mem) = some header →
      RawRefWidth program table number address header.addrWidth →
      header.dataWidth = resultWidth →
      RawRhsWellFormed program table number resultWidth
        (.memRead mem address.render)
  | slice {value inputWidth hi lo} :
      RawRefWidth program table number value inputWidth → lo ≤ hi →
      hi + 1 - lo = resultWidth →
      RawRhsWellFormed program table number resultWidth
        (.slice value.render hi lo)
  | not {value} :
      RawRefWidth program table number value resultWidth →
      RawRhsWellFormed program table number resultWidth (.not value.render)
  | binSame {op left right} :
      (op = .and ∨ op = .or ∨ op = .xor ∨ op = .add ∨ op = .sub ∨
        op = .shl ∨ op = .shr) →
      RawRefWidth program table number left resultWidth →
      RawRefWidth program table number right resultWidth →
      RawRhsWellFormed program table number resultWidth
        (.bin op left.render right.render)
  | comparison {op left right operandWidth} :
      (op = .eq ∨ op = .ult) → resultWidth = 1 →
      RawRefWidth program table number left operandWidth →
      RawRefWidth program table number right operandWidth →
      RawRhsWellFormed program table number resultWidth
        (.bin op left.render right.render)
  | slt {left right operandWidth} : resultWidth = 1 →
      RawRefWidth program table number left operandWidth →
      RawRefWidth program table number right operandWidth →
      RawRhsWellFormed program table number resultWidth
        (.slt left.render right.render)
  | mux {condition yes no} :
      RawRefWidth program table number condition 1 →
      RawRefWidth program table number yes resultWidth →
      RawRefWidth program table number no resultWidth →
      RawRhsWellFormed program table number resultWidth
        (.mux condition.render yes.render no.render)
  | sext {amount value signBit inputWidth} :
      RawRefWidth program table number value inputWidth →
      signBit + 1 = inputWidth → inputWidth + amount = resultWidth →
      inputWidth < resultWidth →
      RawRhsWellFormed program table number resultWidth
        (.sext amount value.render signBit)

theorem refWidthBefore_isSome_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (current : Nat) (reference : Ref)
    (accepted : (refWidthBefore? program indexeds table current reference).isSome =
      true) :
    ∃ width, RawRefWidth program table current reference width := by
  cases found : refWidthBefore? program indexeds table current reference with
  | none => simp [found] at accepted
  | some width => exact ⟨width,
      refWidthBefore_raw program hmatches table current reference width found⟩

theorem indexedRhsWellFormed_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (number resultWidth : Nat) (rhs : IndexedRhs)
    (accepted : indexedRhsWellFormed program indexeds table number
      resultWidth rhs = true) :
    RawRhsWellFormed program table number resultWidth rhs.toRaw := by
  cases rhs with
  | lit literalWidth value =>
      simp only [indexedRhsWellFormed, beq_iff_eq] at accepted
      subst literalWidth
      exact .lit
  | ident value =>
      obtain ⟨inputWidth, valueWellFormed⟩ :=
        refWidthBefore_isSome_raw program hmatches table number value accepted
      exact .ident valueWellFormed
  | memRead mem address =>
      simp only [indexedRhsWellFormed] at accepted
      cases headerFound : program.mems.find?
          (fun candidate => candidate.name == mem) with
      | none => simp [headerFound] at accepted
      | some header =>
          cases addressFound : refWidthBefore? program indexeds table number
              address with
          | none => simp [headerFound, addressFound] at accepted
          | some addressWidth =>
              simp only [headerFound, addressFound, Bool.and_eq_true,
                beq_iff_eq] at accepted
              exact .memRead headerFound
                (accepted.1 ▸ refWidthBefore_raw program hmatches table number
                  address addressWidth addressFound)
                accepted.2
  | slice value hi lo =>
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at accepted
      obtain ⟨inputWidth, valueWellFormed⟩ :=
        refWidthBefore_isSome_raw program hmatches table number value
          accepted.1.1
      exact .slice valueWellFormed accepted.1.2 accepted.2
  | not value =>
      exact .not (refWidthBefore_raw program hmatches table number value
        resultWidth (beq_iff_eq.mp accepted))
  | bin op left right =>
      cases op with
      | and | or | xor | add | sub | shl | shr =>
          simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq]
            at accepted
          exact .binSame (by simp) (refWidthBefore_raw program hmatches table
            number left resultWidth accepted.1)
            (refWidthBefore_raw program hmatches table number right resultWidth
              accepted.2)
      | eq | ult =>
          simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq]
            at accepted
          cases leftFound : refWidthBefore? program indexeds table number left with
          | none => simp [leftFound] at accepted
          | some leftWidth =>
              cases rightFound : refWidthBefore? program indexeds table number right with
              | none => simp [leftFound, rightFound] at accepted
              | some rightWidth =>
                  simp only [leftFound, rightFound, beq_iff_eq] at accepted
                  exact .comparison (by simp) accepted.1
                    (refWidthBefore_raw program hmatches table number left
                      leftWidth leftFound)
                    (accepted.2 ▸ refWidthBefore_raw program hmatches table number
                      right rightWidth rightFound)
  | slt left right =>
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at accepted
      cases leftFound : refWidthBefore? program indexeds table number left with
      | none => simp [leftFound] at accepted
      | some leftWidth =>
          cases rightFound : refWidthBefore? program indexeds table number right with
          | none => simp [leftFound, rightFound] at accepted
          | some rightWidth =>
              simp only [leftFound, rightFound, beq_iff_eq] at accepted
              exact .slt accepted.1
                (refWidthBefore_raw program hmatches table number left leftWidth
                  leftFound)
                (accepted.2 ▸ refWidthBefore_raw program hmatches table number
                  right rightWidth rightFound)
  | mux condition yes no =>
      simp only [indexedRhsWellFormed, Bool.and_eq_true, beq_iff_eq] at accepted
      exact .mux
        (refWidthBefore_raw program hmatches table number condition 1
          accepted.1.1)
        (refWidthBefore_raw program hmatches table number yes resultWidth
          accepted.1.2)
        (refWidthBefore_raw program hmatches table number no resultWidth accepted.2)
  | sext amount value signBit =>
      simp only [indexedRhsWellFormed] at accepted
      cases valueFound : refWidthBefore? program indexeds table number value with
      | none => simp [valueFound] at accepted
      | some inputWidth =>
          simp only [valueFound, Bool.and_eq_true, beq_iff_eq,
            decide_eq_true_eq] at accepted
          exact .sext (refWidthBefore_raw program hmatches table number value
            inputWidth valueFound) accepted.1.1 accepted.1.2 accepted.2

theorem indexedWireWellFormedAt_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (number : Nat) (indexed : IndexedWire) (raw : Wire)
    (wellFormed : indexedWireWellFormedAt program indexeds table number indexed =
      true)
    (rawMatches : indexed.matchesRaw number raw = true) :
    RawRhsWellFormed program table number raw.width raw.rhs := by
  simp only [indexedWireWellFormedAt, Bool.and_eq_true, beq_iff_eq]
    at wellFormed
  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs rawMatches
  have semantic := indexedRhsWellFormed_raw program hmatches table number
    indexed.width indexed.rhs wellFormed.2
  rw [← widthEq, ← rhsEq] at semantic
  exact semantic

/-- Every bounded numeric lookup accepted by a whole-graph certificate denotes
a well-typed assignment in the raw rendered program. -/
theorem lookupIndexed_rawWellFormed
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable)
    (hwellFormed : IndexedRopeWellFormed program indexeds table 0 indexeds)
    (number : Nat) (indexed : IndexedWire)
    (found : lookupIndexed? indexeds table number = some indexed) :
    ∃ raw, RawWireAt program table number raw ∧
      RawRhsWellFormed program table number raw.width raw.rhs := by
  obtain ⟨raw, rawAt, rawMatches⟩ :=
    lookupIndexed_rawWireAt program hmatches table number indexed found
  have wellFormed := lookupIndexed_wellFormed hwellFormed number indexed found
  exact ⟨raw, rawAt, indexedWireWellFormedAt_raw program hmatches table number
    indexed raw wellFormed rawMatches⟩

/-- Environment invariant used to prove total concrete elaboration. Every
source register or earlier wire admitted by the raw typing judgment resolves
at its declared width. -/
def EnvResolvesBefore (program : Program) (table : WireTable)
    (current : Nat) (env : Env) : Prop :=
  ∀ reference width, RawRefWidth program table current reference width →
    ∃ value : Loom.Emit.MicroVerilog.Expr width,
      resolveAt (program.regs.map fun reg => ⟨reg.name, reg.width⟩) env
        reference.render width = some value

private theorem resolveAny_of_resolveAt
    (regs : List RegHdr) (env : Env) (name : String) (width : Nat)
    (value : Loom.Emit.MicroVerilog.Expr width)
    (accepted : resolveAt regs env name width = some value) :
    resolveAny regs env name = some ⟨width, value⟩ := by
  unfold resolveAt at accepted
  cases found : resolveAny regs env name with
  | none => simp [found] at accepted
  | some entry =>
      obtain ⟨actual, raw⟩ := entry
      by_cases widthEq : actual = width
      · subst actual
        simp [found] at accepted
        subst value
        rfl
      · simp [found, widthEq] at accepted

private theorem resolveAny_insert_of_ne
    (regs : List RegHdr) (env : Env) (insertedName name : String)
    (entry : Sigma Loom.Emit.MicroVerilog.Expr)
    (different : insertedName ≠ name) :
    resolveAny regs (env.insert insertedName entry) name =
      resolveAny regs env name := by
  unfold resolveAny
  simp [Std.TreeMap.getElem?_insert, different]

private theorem resolveAt_insert_of_ne
    (regs : List RegHdr) (env : Env) (insertedName name : String)
    (entry : Sigma Loom.Emit.MicroVerilog.Expr) (width : Nat)
    (different : insertedName ≠ name) :
    resolveAt regs (env.insert insertedName entry) name width =
      resolveAt regs env name width := by
  unfold resolveAt
  rw [resolveAny_insert_of_ne regs env insertedName name entry different]

private theorem binSame_of_resolveAt
    (regs : List RegHdr) (env : Env) (width : Nat) (leftName rightName : String)
    (make : Loom.Emit.MicroVerilog.Expr width →
      Loom.Emit.MicroVerilog.Expr width → Loom.Emit.MicroVerilog.Expr width)
    (left right : Loom.Emit.MicroVerilog.Expr width)
    (leftEq : resolveAt regs env leftName width = some left)
    (rightEq : resolveAt regs env rightName width = some right) :
    binSame regs env width leftName rightName make = some (make left right) := by
  simp [Loom.Release.SSA.binSame, leftEq, rightEq]

private theorem comparison_of_resolveAt
    (regs : List RegHdr) (env : Env) (leftName rightName : String)
    (width : Nat) (make : {w : Nat} → Loom.Emit.MicroVerilog.Expr w →
      Loom.Emit.MicroVerilog.Expr w → Loom.Emit.MicroVerilog.Expr 1)
    (left right : Loom.Emit.MicroVerilog.Expr width)
    (leftAny : resolveAny regs env leftName = some ⟨width, left⟩)
    (rightEq : resolveAt regs env rightName width = some right) :
    comparison regs env 1 leftName rightName make = some (make left right) := by
  simp [Loom.Release.SSA.comparison, guard, leftAny, rightEq]

theorem RawRhsWellFormed.elaborate_isSome
    {program : Program} {table : WireTable} {number resultWidth : Nat}
    {rhs : Rhs} (hraw : RawRhsWellFormed program table number resultWidth rhs)
    (env : Env) (henv : EnvResolvesBefore program table number env) :
    ∃ value : Loom.Emit.MicroVerilog.Expr resultWidth,
      rhs.elaborate (program.regs.map fun reg => ⟨reg.name, reg.width⟩)
        (program.mems.map fun mem => ⟨mem.name, mem.addrWidth, mem.dataWidth⟩)
        env resultWidth = some value := by
  induction hraw with
  | lit =>
      rename_i value
      exact ⟨.lit (BitVec.ofNat resultWidth value), by
        simp [Rhs.elaborate, guard]⟩
  | ident referenceWellFormed =>
      obtain ⟨resolved, resolvedEq⟩ := henv _ _ referenceWellFormed
      have rawEq := resolveAny_of_resolveAt _ _ _ _ _ resolvedEq
      exact ⟨.zext resolved resultWidth, by simp [Rhs.elaborate, rawEq]⟩
  | memRead headerFound addressWellFormed dataWidthEq =>
      rename_i mem addressRef header
      subst resultWidth
      obtain ⟨address, addressEq⟩ := henv _ _ addressWellFormed
      have mappedHeader :
          (program.mems.map fun mem =>
            (⟨mem.name, mem.addrWidth, mem.dataWidth⟩ : MemHdr)).find?
              (fun candidate => candidate.name == mem) =
            some ⟨header.name, header.addrWidth, header.dataWidth⟩ := by
        simp [List.find?_map, Function.comp_def, headerFound]
      exact ⟨.memRead header.dataWidth mem address, by
        simp [Rhs.elaborate, mappedHeader, addressEq]⟩
  | slice valueWellFormed loLeHi widthEq =>
      rename_i valueRef inputWidth hi lo
      obtain ⟨resolved, resolvedEq⟩ := henv _ _ valueWellFormed
      have rawEq := resolveAny_of_resolveAt _ _ _ _ _ resolvedEq
      exact ⟨.slice resolved lo resultWidth, by
        simp [Rhs.elaborate, guard, loLeHi, widthEq, rawEq]⟩
  | not valueWellFormed =>
      obtain ⟨resolved, resolvedEq⟩ := henv _ _ valueWellFormed
      exact ⟨.not resolved, by simp [Rhs.elaborate, resolvedEq]⟩
  | binSame operatorSupported leftWellFormed rightWellFormed =>
      obtain ⟨left, leftEq⟩ := henv _ _ leftWellFormed
      obtain ⟨right, rightEq⟩ := henv _ _ rightWellFormed
      rcases operatorSupported with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨.and left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
      · refine ⟨.or left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
      · refine ⟨.xor left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
      · refine ⟨.add left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
      · refine ⟨.sub left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
      · refine ⟨.shl left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
      · refine ⟨.shr left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
  | comparison operatorSupported resultIsOne leftWellFormed rightWellFormed =>
      subst resultIsOne
      obtain ⟨left, leftEq⟩ := henv _ _ leftWellFormed
      obtain ⟨right, rightEq⟩ := henv _ _ rightWellFormed
      have rawLeftEq := resolveAny_of_resolveAt _ _ _ _ _ leftEq
      rcases operatorSupported with rfl | rfl
      · refine ⟨.eq left right, ?_⟩
        exact comparison_of_resolveAt _ _ _ _ _ _ _ _ rawLeftEq rightEq
      · refine ⟨.ult left right, ?_⟩
        exact comparison_of_resolveAt _ _ _ _ _ _ _ _ rawLeftEq rightEq
  | slt resultIsOne leftWellFormed rightWellFormed =>
      subst resultIsOne
      obtain ⟨left, leftEq⟩ := henv _ _ leftWellFormed
      obtain ⟨right, rightEq⟩ := henv _ _ rightWellFormed
      have rawLeftEq := resolveAny_of_resolveAt _ _ _ _ _ leftEq
      refine ⟨.slt left right, ?_⟩
      exact comparison_of_resolveAt _ _ _ _ _ _ _ _ rawLeftEq rightEq
  | mux conditionWellFormed yesWellFormed noWellFormed =>
      obtain ⟨condition, conditionEq⟩ := henv _ _ conditionWellFormed
      obtain ⟨yes, yesEq⟩ := henv _ _ yesWellFormed
      obtain ⟨no, noEq⟩ := henv _ _ noWellFormed
      exact ⟨.mux condition yes no, by
        simp [Rhs.elaborate, conditionEq, yesEq, noEq]⟩
  | sext valueWellFormed signBitEq amountEq inputLt =>
      rename_i amount valueRef signBit inputWidth
      obtain ⟨resolved, resolvedEq⟩ := henv _ _ valueWellFormed
      have rawEq := resolveAny_of_resolveAt _ _ _ _ _ resolvedEq
      exact ⟨.sext resolved resultWidth, by
        simp [Rhs.elaborate, guard, rawEq, signBitEq, amountEq, inputLt]⟩

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

/-- Meaning of the optional symbolic accumulator used while checking an
action. `none` deliberately imposes no premise: a successful certificate
must then establish an output independent of the discarded accumulator. -/
def RawCurrentMatches (program : Program) (table : WireTable) {width : Nat}
    (expr : Loom.Emit.MicroVerilog.Expr width) : Option Ref → Prop
  | some reference => RawExprMatches program table expr reference
  | none => True

private theorem nextReg_eq_of_no_write (register : String) (width : Nat) :
    ∀ (action : Loom.Hw.Act) (cur : Loom.Emit.MicroVerilog.Expr width),
      Loom.Hw.Compile.writesRegB register width action = false →
      Loom.Hw.Compile.nextReg register width action cur = cur := by
  intro action
  induction action with
  | skip => intro _ _; rfl
  | seq left right leftIH rightIH =>
      intro cur accepted
      have notMem : (register, width) ∉ (left.seq right).regWrites := by
        simpa [Loom.Hw.Compile.writesRegB] using accepted
      simp only [Loom.Hw.Act.regWrites, List.mem_append, not_or] at notMem
      rw [Loom.Hw.Compile.nextReg,
        rightIH _ (by simpa [Loom.Hw.Compile.writesRegB] using notMem.2),
        leftIH _ (by simpa [Loom.Hw.Compile.writesRegB] using notMem.1)]
  | ite guard thenAction elseAction thenIH elseIH =>
      intro cur accepted
      have notMem :
          (register, width) ∉ (Loom.Hw.Act.ite guard thenAction elseAction).regWrites := by
        simpa [Loom.Hw.Compile.writesRegB] using accepted
      simp only [Loom.Hw.Act.regWrites, List.mem_append, not_or] at notMem
      rw [Loom.Hw.Compile.nextReg, if_neg]
      simp [Loom.Hw.Compile.writesRegB, notMem]
  | write actualWidth name value =>
      intro cur accepted
      have notMem :
          (register, width) ∉ (Loom.Hw.Act.write actualWidth name value).regWrites := by
        simpa [Loom.Hw.Compile.writesRegB] using accepted
      simp only [Loom.Hw.Compile.nextReg]
      by_cases sameName : name = register
      · rw [if_pos sameName]
        have differentWidth : actualWidth ≠ width := by
          intro sameWidth
          exact notMem (by simp [Loom.Hw.Act.regWrites, sameName, sameWidth])
        rw [dif_neg differentWidth]
      · rw [if_neg sameName]
  | memWrite => intro _ _; rfl

/-- Soundness of the symbolic action checker against the reference
`Compile.nextReg` function. -/
theorem nextRegMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (register : String) (width : Nat) :
    ∀ (action : Loom.Hw.Act) (current : Option Ref) (out : Ref)
      (cert : NextRegCert),
      nextRegMatches indexeds table register width action current out cert = true →
      ∀ cur : Loom.Emit.MicroVerilog.Expr width,
        RawCurrentMatches program table cur current →
        RawExprMatches program table
          (Loom.Hw.Compile.nextReg register width action cur) out := by
  intro action
  induction action <;> intro current out cert accepted cur currentMatches
  · cases current <;> cases cert <;>
      simp [nextRegMatches] at accepted
    subst out
    simpa [Loom.Hw.Compile.nextReg] using currentMatches
  · rename_i left right leftIH rightIH
    cases cert with
    | seq mid leftCert rightCert =>
        cases mid with
        | none =>
            simp only [nextRegMatches] at accepted
            simpa only [Loom.Hw.Compile.nextReg] using
              rightIH none out rightCert accepted
                (Loom.Hw.Compile.nextReg register width left cur) trivial
        | some mid =>
            simp only [nextRegMatches, Bool.and_eq_true] at accepted
            have leftMatches := leftIH current mid leftCert accepted.1 cur currentMatches
            simpa only [Loom.Hw.Compile.nextReg] using
              rightIH (some mid) out rightCert accepted.2
                (Loom.Hw.Compile.nextReg register width left cur) leftMatches
    | same =>
        cases current with
        | none => simp [nextRegMatches] at accepted
        | some current =>
            simp only [nextRegMatches, Bool.and_eq_true, beq_iff_eq] at accepted
            rw [← accepted.2]
            rw [nextReg_eq_of_no_write register width
              (.seq left right) cur (by simpa using accepted.1)]
            exact currentMatches
    | write => simp [nextRegMatches] at accepted
    | ite thenCert elseCert => simp [nextRegMatches] at accepted
  · rename_i guard thenAction elseAction thenIH elseIH
    by_cases writes : Loom.Hw.Compile.writesRegB register width thenAction ||
        Loom.Hw.Compile.writesRegB register width elseAction
    · cases cert with
      | ite thenCert elseCert =>
          cases out with
          | reg name => simp [nextRegMatches] at accepted
          | wire number =>
              simp only [nextRegMatches, writes, if_true] at accepted
              cases found : lookupIndexed? indexeds table number with
              | none => simp [found] at accepted
              | some indexed =>
                  obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
                  cases rhs <;> simp [found] at accepted
                  next guardRef thenRef elseRef =>
                    obtain ⟨raw, rawAt, rawMatch⟩ :=
                      lookupIndexed_rawWireAt program hmatches table number
                        ⟨indexedNumber, actualWidth,
                          .mux guardRef thenRef elseRef⟩ found
                    obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                      (indexed := ⟨indexedNumber, actualWidth,
                        .mux guardRef thenRef elseRef⟩) rawMatch
                    rw [Loom.Hw.Compile.nextReg, if_pos writes]
                    exact .mux rawAt (widthEq.trans accepted.1.1.1) rhsEq
                      (indexedExprMatches_raw program hmatches table _ _
                        accepted.1.1.2)
                      (thenIH current thenRef thenCert accepted.1.2 cur currentMatches)
                      (elseIH current elseRef elseCert accepted.2 cur currentMatches)
      | same => cases current <;> simp [nextRegMatches, writes] at accepted
      | write => simp [nextRegMatches] at accepted
      | seq mid leftCert rightCert => simp [nextRegMatches] at accepted
    · cases cert with
      | same =>
          have writesFalse :
              (Loom.Hw.Compile.writesRegB register width thenAction ||
                Loom.Hw.Compile.writesRegB register width elseAction) = false := by
            cases value : (Loom.Hw.Compile.writesRegB register width thenAction ||
              Loom.Hw.Compile.writesRegB register width elseAction) <;> simp_all
          cases current with
          | none => simp [nextRegMatches] at accepted
          | some current =>
              have currentEq : current = out := by
                simpa [nextRegMatches, writesFalse] using accepted
              rw [← currentEq]
              rw [Loom.Hw.Compile.nextReg, writesFalse]
              exact currentMatches
      | ite thenCert elseCert =>
          have writesFalse :
              (Loom.Hw.Compile.writesRegB register width thenAction ||
                Loom.Hw.Compile.writesRegB register width elseAction) = false := by
            cases value : (Loom.Hw.Compile.writesRegB register width thenAction ||
              Loom.Hw.Compile.writesRegB register width elseAction) <;> simp_all
          cases out <;> simp [nextRegMatches, writesFalse] at accepted
      | write => simp [nextRegMatches] at accepted
      | seq mid leftCert rightCert => simp [nextRegMatches] at accepted
  · rename_i actualWidth actualRegister value
    by_cases sameRegister : actualRegister = register
    · by_cases sameWidth : actualWidth = width
      · subst actualRegister
        subst actualWidth
        cases cert with
        | write =>
            simp only [nextRegMatches, if_pos, dif_pos] at accepted
            rw [Loom.Hw.Compile.nextReg, if_pos rfl, dif_pos rfl]
            exact indexedExprMatches_raw program hmatches table _ _ accepted
        | same => simp [nextRegMatches] at accepted
        | seq mid leftCert rightCert => simp [nextRegMatches] at accepted
        | ite thenCert elseCert => simp [nextRegMatches] at accepted
      · cases current <;> cases cert <;>
          simp [nextRegMatches, Loom.Hw.Compile.nextReg,
            sameRegister, sameWidth] at accepted ⊢
        subst out
        exact currentMatches
    · cases current <;> cases cert <;>
        simp [nextRegMatches, Loom.Hw.Compile.nextReg,
          sameRegister] at accepted ⊢
      subst out
      exact currentMatches
  · cases current <;> cases cert <;>
      simp [nextRegMatches] at accepted
    subst out
    simpa [Loom.Hw.Compile.nextReg] using currentMatches

/-- Soundness of the ordered scheduler fold used to construct a compiled
register's next-state expression. -/
theorem nextRulesMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (register : String) (width : Nat) :
    ∀ (rules : List Loom.Hw.Rule) (current : Option Ref) (out : Ref)
      (cert : NextRulesCert),
      nextRulesMatches indexeds table register width rules current out cert = true →
      ∀ cur : Loom.Emit.MicroVerilog.Expr width,
        RawCurrentMatches program table cur current →
        RawExprMatches program table
          (rules.foldl (fun acc rule =>
            Loom.Hw.Compile.nextReg register width rule.body acc) cur) out := by
  intro rules
  induction rules with
  | nil =>
      intro current out cert accepted cur currentMatches
      cases current <;> cases cert <;> simp [nextRulesMatches] at accepted
      rw [← accepted]
      exact currentMatches
  | cons rule rules rulesIH =>
      intro current out cert accepted cur currentMatches
      cases cert with
      | nil => simp [nextRulesMatches] at accepted
      | cons mid head tail =>
          cases mid with
          | none =>
              simp only [nextRulesMatches] at accepted
              simpa only [List.foldl_cons] using
                rulesIH none out tail accepted
                  (Loom.Hw.Compile.nextReg register width rule.body cur) trivial
          | some mid =>
              simp only [nextRulesMatches, Bool.and_eq_true] at accepted
              have headMatches := nextRegMatches_raw program hmatches table
                register width rule.body current mid head accepted.1 cur currentMatches
              simpa only [List.foldl_cons] using
                rulesIH (some mid) out tail accepted.2
                  (Loom.Hw.Compile.nextReg register width rule.body cur) headMatches

end Loom.Release.Symbolic
