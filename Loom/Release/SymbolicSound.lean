-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate
import Loom.Release.SymbolicElaborate
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
              exact beq_iff_eq.mp numberTrue.1.1
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
                exact beq_iff_eq.mp numberTrue.1.1
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

/-- Extract an exact global lookup from an already checked 128-wire semantic
block.  Release action certificates use this lemma to reuse the one full-wire
validation pass instead of navigating the global rope again for every mux
join. -/
theorem indexedSemanticBlock_lookup
    {program : Program} {allWires : Rope (List IndexedWire)}
    {table : WireTable} {start offset : Nat} {wires : List IndexedWire}
    {wire : IndexedWire}
    (accepted : indexedSemanticBlockMatches program allWires table start wires =
      true)
    (found : wires[offset]? = some wire) :
    lookupIndexed? allWires table wire.number = some wire := by
  have wellFormed := indexedSemanticBlock_get accepted offset wire found
  simp only [indexedWireWellFormedAt, Bool.and_eq_true, beq_iff_eq] at wellFormed
  exact wellFormed.1.2

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
    cases pathEq : balancedPath? table.leafCount
        (number / table.leafSize) with
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
      balancedPath? table.leafCount (number / table.leafSize) = some path ∧
      raws.resolve? ⟨path, number % table.leafSize⟩ = some raw ∧
      indexed.matchesRaw number raw = true := by
  unfold lookupIndexed? at found
  by_cases size : table.leafSize > 0
  · simp only [size, Option.bind_eq_bind] at found
    cases pathEq : balancedPath? table.leafCount
        (number / table.leafSize) with
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
numeric position. Textual-name consistency is checked separately for each
operand, so the proof does not depend on a particular naming convention. -/
def RawWireAt (program : Program) (table : WireTable)
    (number : Nat) (raw : Wire) : Prop :=
  ∃ path,
    balancedPath? table.leafCount (number / table.leafSize) = some path ∧
    program.wires.resolve? ⟨path, number % table.leafSize⟩ = some raw

theorem RawWireAt.lookupRaw {program : Program} {table : WireTable}
    {number : Nat} {raw : Wire} (located : RawWireAt program table number raw)
    (positive : table.leafSize > 0) :
    lookupRaw? program.wires table number = some raw := by
  rcases located with ⟨path, pathEq, rawEq⟩
  simp [lookupRaw?, positive, pathEq, rawEq, guard]

theorem lookupIndexed_rawWireAt
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (number : Nat) (indexed : IndexedWire)
    (found : lookupIndexed? indexeds table number = some indexed) :
    ∃ raw, RawWireAt program table number raw ∧
      indexed.matchesRaw number raw = true := by
  obtain ⟨path, raw, pathEq, rawEq, rawMatch⟩ :=
    lookupIndexed_resolvesRaw hmatches table number indexed found
  exact ⟨raw, ⟨path, pathEq, rawEq⟩, rawMatch⟩

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
      (earlier : number < current) (located : RawWireAt program table number raw)
      (nameEq : raw.name = (Ref.wire number).render) :
      RawRefWidth program table current (.wire number) raw.width
  | namedWire {number name raw}
      (earlier : number < current) (located : RawWireAt program table number raw)
      (nameEq : raw.name = name) :
      RawRefWidth program table current (.namedWire number name) raw.width

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
            simp only [found, Option.bind_some] at accepted
            cases rawFound : lookupRaw? program.wires table number with
            | none => simp [rawFound] at accepted
            | some checkedRaw =>
              simp only [rawFound, Option.bind_some] at accepted
              have nameEq : checkedRaw.name = (Ref.wire number).render := by
                by_cases equal : checkedRaw.name = (Ref.wire number).render
                · exact equal
                · exfalso
                  simp [equal, optionFailure] at accepted
              have widthEq : indexed.width = width := by
                simpa [guard, nameEq] using accepted
              have positive : table.leafSize > 0 := by
                by_cases positive : table.leafSize > 0
                · exact positive
                · exfalso
                  simp [lookupRaw?, guard, positive, optionFailure] at rawFound
              obtain ⟨raw, rawAt, rawMatch⟩ :=
                lookupIndexed_rawWireAt program hmatches table number indexed found
              have sameRaw : raw = checkedRaw := by
                rw [rawAt.lookupRaw positive] at rawFound
                exact Option.some.inj rawFound
              subst checkedRaw
              obtain ⟨rawWidthEq, _⟩ := IndexedWire.matchesRaw_width_rhs rawMatch
              rw [← widthEq, ← rawWidthEq]
              exact .wire earlier rawAt nameEq
      · simp only [earlier, guard] at accepted
        exfalso
        simp [optionFailure] at accepted
  | namedWire number name =>
      unfold refWidthBefore? at accepted
      by_cases earlier : number < current
      · simp only [earlier, guard, Option.bind_eq_bind] at accepted
        cases found : lookupIndexed? indexeds table number with
        | none => simp [found] at accepted
        | some indexed =>
            simp only [found, Option.bind_some] at accepted
            cases rawFound : lookupRaw? program.wires table number with
            | none => simp [rawFound] at accepted
            | some checkedRaw =>
              simp only [rawFound, Option.bind_some] at accepted
              have nameEq : checkedRaw.name = name := by
                by_cases equal : checkedRaw.name = name
                · exact equal
                · exfalso
                  simp [equal, optionFailure] at accepted
              have widthEq : indexed.width = width := by
                simpa [guard, nameEq] using accepted
              have positive : table.leafSize > 0 := by
                by_cases positive : table.leafSize > 0
                · exact positive
                · exfalso
                  simp [lookupRaw?, guard, positive, optionFailure] at rawFound
              obtain ⟨raw, rawAt, rawMatch⟩ :=
                lookupIndexed_rawWireAt program hmatches table number indexed found
              have sameRaw : raw = checkedRaw := by
                rw [rawAt.lookupRaw positive] at rawFound
                exact Option.some.inj rawFound
              subst checkedRaw
              obtain ⟨rawWidthEq, _⟩ := IndexedWire.matchesRaw_width_rhs rawMatch
              rw [← widthEq, ← rawWidthEq]
              exact .namedWire earlier rawAt nameEq
      · simp only [earlier, guard] at accepted
        exfalso
        simp [optionFailure] at accepted

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
        op = .mul ∨ op = .udiv ∨ op = .urem ∨ op = .shl ∨ op = .shr) →
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
      | and | or | xor | add | sub | mul | udiv | urem | shl | shr =>
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
      rcases operatorSupported with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · refine ⟨.mul left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
      · refine ⟨.udiv left right, ?_⟩
        exact binSame_of_resolveAt _ _ _ _ _ _ _ _ leftEq rightEq
      · refine ⟨.urem left right, ?_⟩
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
  | named {width : Nat} {expr : Loom.Emit.MicroVerilog.Expr width}
      {number : Nat} {name : String} :
      RawExprMatches program table expr (.wire number) →
      RawExprMatches program table expr (.namedWire number name)
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
  | mul {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .mul leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.mul left right) (.wire number)
  | udiv {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .udiv leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.udiv left right) (.wire number)
  | urem {width left right leftRef rightRef number raw} :
      RawWireAt program table number raw → raw.width = width →
      raw.rhs = .bin .urem leftRef.render rightRef.render →
      RawExprMatches program table left leftRef →
      RawExprMatches program table right rightRef →
      RawExprMatches program table (.urem left right) (.wire number)
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
      | namedWire number name => simp [indexedExprMatches] at accepted
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
  | mul left right leftIH rightIH =>
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
                case mul =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .mul actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .mul actualLeft actualRight⟩) rawMatch
                  exact .mul rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
      | namedWire number name =>
          apply RawExprMatches.named
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case mul =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .mul actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .mul actualLeft actualRight⟩) rawMatch
                  exact .mul rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
  | udiv left right leftIH rightIH =>
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
                case udiv =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .udiv actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .udiv actualLeft actualRight⟩) rawMatch
                  exact .udiv rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
      | namedWire number name =>
          apply RawExprMatches.named
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case udiv =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .udiv actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .udiv actualLeft actualRight⟩) rawMatch
                  exact .udiv rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
  | urem left right leftIH rightIH =>
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
                case urem =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .urem actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .urem actualLeft actualRight⟩) rawMatch
                  exact .urem rawAt (widthEq.trans accepted.1.1) rhsEq
                    (leftIH actualLeft accepted.1.2) (rightIH actualRight accepted.2)
      | namedWire number name =>
          apply RawExprMatches.named
          cases found : lookupIndexed? indexeds table number with
          | none => simp [indexedExprMatches, found] at accepted
          | some indexed =>
              obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
              cases rhs <;> simp [indexedExprMatches, found] at accepted
              case bin op actualLeft actualRight =>
                cases op <;> simp at accepted
                case urem =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth, .bin .urem actualLeft actualRight⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .bin .urem actualLeft actualRight⟩) rawMatch
                  exact .urem rawAt (widthEq.trans accepted.1.1) rhsEq
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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
      | namedWire number name =>
          apply RawExprMatches.named
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

/-- Soundness of the distinguished-current half of slice insertion. -/
private theorem indexedInsertClear_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) {width : Nat} (mask : BitVec width)
    (currentExpr : Loom.Emit.MicroVerilog.Expr width) (current cleared : Ref)
    (currentMatches : RawExprMatches program table currentExpr current)
    (accepted :
      (match lookupRef? indexeds table cleared with
      | some ⟨_, clearWidth, .bin .and actualCurrent negMask⟩ =>
          clearWidth == width && actualCurrent == current &&
            indexedExprMatches indexeds table (.not (.lit mask)) negMask
      | _ => false) = true) :
    RawExprMatches program table (.and currentExpr (.not (.lit mask))) cleared := by
  cases cleared with
  | reg name => simp [lookupRef?] at accepted
  | wire number =>
      cases found : lookupIndexed? indexeds table number with
      | none => simp [lookupRef?, found] at accepted
      | some indexed =>
          obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
          cases rhs <;> simp [lookupRef?, found] at accepted
          next op actualCurrent negMask =>
            cases op <;> simp at accepted
            obtain ⟨raw, rawAt, rawMatch⟩ :=
              lookupIndexed_rawWireAt program hmatches table number
                ⟨indexedNumber, actualWidth, .bin .and actualCurrent negMask⟩ found
            obtain ⟨widthEq, rhsEq⟩ :=
              IndexedWire.matchesRaw_width_rhs rawMatch
            exact .and rawAt (widthEq.trans accepted.1.1)
              (by simpa [IndexedRhs.toRaw] using rhsEq)
              (accepted.1.2 ▸ currentMatches)
              (indexedExprMatches_raw program hmatches table _ _ accepted.2)
  | namedWire number name =>
      apply RawExprMatches.named
      cases found : lookupIndexed? indexeds table number with
      | none => simp [lookupRef?, found] at accepted
      | some indexed =>
          obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
          cases rhs <;> simp [lookupRef?, found] at accepted
          next op actualCurrent negMask =>
            cases op <;> simp at accepted
            obtain ⟨raw, rawAt, rawMatch⟩ :=
              lookupIndexed_rawWireAt program hmatches table number
                ⟨indexedNumber, actualWidth, .bin .and actualCurrent negMask⟩ found
            obtain ⟨widthEq, rhsEq⟩ :=
              IndexedWire.matchesRaw_width_rhs rawMatch
            exact .and rawAt (widthEq.trans accepted.1.1)
              (by simpa [IndexedRhs.toRaw] using rhsEq)
              (accepted.1.2 ▸ currentMatches)
              (indexedExprMatches_raw program hmatches table _ _ accepted.2)

/-- The insertion checker denotes the compiler's exact mask graph. -/
theorem indexedInsertMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) {width fieldWidth : Nat} (lo : Nat)
    (value : Loom.Hw.Expr fieldWidth)
    (currentExpr : Loom.Emit.MicroVerilog.Expr width) (current out : Ref)
    (currentMatches : RawExprMatches program table currentExpr current)
    (accepted : indexedInsertMatches indexeds table width lo fieldWidth value
      current out = true) :
    RawExprMatches program table
      (Loom.Hw.Compile.insertExpr lo
        (Loom.Hw.Compile.compileExpr value) currentExpr) out := by
  cases out with
  | reg name => simp [indexedInsertMatches] at accepted
  | namedWire number name => simp [indexedInsertMatches] at accepted
  | wire number =>
      cases found : lookupIndexed? indexeds table number with
      | none => simp [indexedInsertMatches, found] at accepted
      | some indexed =>
          obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
          cases rhs <;> simp [indexedInsertMatches, found] at accepted
          next op cleared shiftedRef =>
            cases op <;> simp at accepted
            obtain ⟨raw, rawAt, rawMatch⟩ :=
              lookupIndexed_rawWireAt program hmatches table number
                ⟨indexedNumber, actualWidth, .bin .or cleared shiftedRef⟩ found
            obtain ⟨widthEq, rhsEq⟩ :=
              IndexedWire.matchesRaw_width_rhs rawMatch
            unfold Loom.Hw.Compile.insertExpr
            exact .or rawAt (widthEq.trans accepted.1.1)
              (by simpa [IndexedRhs.toRaw] using rhsEq)
              (indexedInsertClear_raw program hmatches table _ currentExpr
                current cleared currentMatches accepted.1.2)
              (indexedExprMatches_raw program hmatches table _ _ accepted.2)
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
        exact (Loom.Hw.Compile.writesRegB_eq_false_iff register width _).1
          accepted
      simp only [Loom.Hw.Act.regWrites, List.mem_append, not_or] at notMem
      rw [Loom.Hw.Compile.nextReg,
        rightIH _ ((Loom.Hw.Compile.writesRegB_eq_false_iff register width _).2
          notMem.2),
        leftIH _ ((Loom.Hw.Compile.writesRegB_eq_false_iff register width _).2
          notMem.1)]
  | ite guard thenAction elseAction thenIH elseIH =>
      intro cur accepted
      have notMem :
          (register, width) ∉ (Loom.Hw.Act.ite guard thenAction elseAction).regWrites := by
        exact (Loom.Hw.Compile.writesRegB_eq_false_iff register width _).1
          accepted
      simp only [Loom.Hw.Act.regWrites, List.mem_append, not_or] at notMem
      rw [Loom.Hw.Compile.nextReg, if_neg]
      · simp [(Loom.Hw.Compile.writesRegB_eq_false_iff register width _).2
            notMem.1,
          (Loom.Hw.Compile.writesRegB_eq_false_iff register width _).2
            notMem.2]
  | write actualWidth name value =>
      intro cur accepted
      have notMem :
          (register, width) ∉ (Loom.Hw.Act.write actualWidth name value).regWrites := by
        exact (Loom.Hw.Compile.writesRegB_eq_false_iff register width _).1
          accepted
      simp only [Loom.Hw.Compile.nextReg]
      by_cases sameName : name = register
      · rw [if_pos sameName]
        have differentWidth : actualWidth ≠ width := by
          intro sameWidth
          exact notMem (by simp [Loom.Hw.Act.regWrites, sameName, sameWidth])
        rw [dif_neg differentWidth]
      · rw [if_neg sameName]
  | writeSlice actualWidth name lo fieldWidth inBounds value =>
      intro cur accepted
      have notMem : (register, width) ∉
          (Loom.Hw.Act.writeSlice actualWidth name lo fieldWidth inBounds value).regWrites := by
        exact (Loom.Hw.Compile.writesRegB_eq_false_iff register width _).1 accepted
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
    | write | writeSlice => simp [nextRegMatches] at accepted
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
          | namedWire number name =>
              simp [nextRegMatches] at accepted
      | same => cases current <;> simp [nextRegMatches, writes] at accepted
      | write | writeSlice => simp [nextRegMatches] at accepted
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
      | write | writeSlice => simp [nextRegMatches] at accepted
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
        | writeSlice => simp [nextRegMatches] at accepted
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
  · rename_i actualWidth actualRegister lo fieldWidth inBounds value
    by_cases sameRegister : actualRegister = register
    · by_cases sameWidth : actualWidth = width
      · subst actualRegister
        subst actualWidth
        cases cert with
        | writeSlice =>
            cases current with
            | none => simp [nextRegMatches] at accepted
            | some current =>
                simp only [nextRegMatches, if_pos, dif_pos] at accepted
                rw [Loom.Hw.Compile.nextReg, if_pos rfl, dif_pos rfl]
                exact indexedInsertMatches_raw program hmatches table lo value
                  cur current out currentMatches accepted
        | same => simp [nextRegMatches] at accepted
        | write => simp [nextRegMatches] at accepted
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

/-- Soundness of the fast path that consults a shared action-write
over-approximation instead of traversing an unchanged action per register. -/
theorem nextRegMatchesCovered_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (covered : List (String × Nat))
    (register : String) (width : Nat) (action : Loom.Hw.Act)
    (coverage : action.regWritesCoveredB covered = true)
    (current : Option Ref) (out : Ref) (cert : NextRegCert)
    (accepted : nextRegMatchesCovered indexeds table covered register width
      action current out cert = true) :
    ∀ cur : Loom.Emit.MicroVerilog.Expr width,
      RawCurrentMatches program table cur current →
      RawExprMatches program table
        (Loom.Hw.Compile.nextReg register width action cur) out := by
  intro cur currentMatches
  by_cases present : (register, width) ∈ covered
  · simp [nextRegMatchesCovered, present] at accepted
    exact nextRegMatches_raw program hmatches table register width action
      current out cert accepted cur currentMatches
  · have noWrite :
        Loom.Hw.Compile.writesRegB register width action = false := by
      rw [Loom.Hw.Compile.writesRegB_eq_false_iff]
      exact Loom.Hw.Act.not_mem_regWrites_of_covered coverage present
    simp [nextRegMatchesCovered, present] at accepted
    cases current with
    | none => cases cert <;> simp at accepted
    | some current =>
        cases cert <;> simp at accepted
        subst out
        rw [nextReg_eq_of_no_write register width action cur noWrite]
        exact currentMatches

/-- Soundness of ordered register-rule checking with one shared footprint
coverage theorem for the whole rule list. -/
theorem nextRulesMatchesCovered_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (register : String) (width : Nat) :
    ∀ (rules : List Loom.Hw.Rule) (footprints : RuleRegFootprints)
      (current : Option Ref) (out : Ref) (cert : NextRulesCert),
      ruleRegFootprintsCoverB rules footprints = true →
      nextRulesMatchesCovered indexeds table register width rules footprints
        current out cert = true →
      ∀ cur : Loom.Emit.MicroVerilog.Expr width,
        RawCurrentMatches program table cur current →
        RawExprMatches program table
          (rules.foldl (fun acc rule =>
            Loom.Hw.Compile.nextReg register width rule.body acc) cur) out := by
  intro rules
  induction rules with
  | nil =>
      intro footprints current out cert coverage accepted cur currentMatches
      cases footprints <;> cases current <;> cases cert <;>
        simp [ruleRegFootprintsCoverB, nextRulesMatchesCovered] at coverage accepted
      subst out
      exact currentMatches
  | cons rule rules rulesIH =>
      intro footprints current out cert coverage accepted cur currentMatches
      cases footprints with
      | nil => simp [ruleRegFootprintsCoverB] at coverage
      | cons covered rest =>
          simp only [ruleRegFootprintsCoverB, Bool.and_eq_true] at coverage
          cases cert with
          | nil => simp [nextRulesMatchesCovered] at accepted
          | cons mid head tail =>
              cases mid with
              | none =>
                  simp only [nextRulesMatchesCovered] at accepted
                  simpa only [List.foldl_cons] using
                    rulesIH rest none out tail coverage.2 accepted
                      (Loom.Hw.Compile.nextReg register width rule.body cur)
                      trivial
              | some mid =>
                  simp only [nextRulesMatchesCovered, Bool.and_eq_true] at accepted
                  have headMatches := nextRegMatchesCovered_raw program hmatches
                    table covered register width rule.body coverage.1 current mid
                    head accepted.1 cur currentMatches
                  simpa only [List.foldl_cons] using
                    rulesIH rest (some mid) out tail coverage.2 accepted.2
                      (Loom.Hw.Compile.nextReg register width rule.body cur)
                      headMatches

/-! ## Memory-port checker soundness -/

/-- Declarative meaning of three concrete SSA roots as one typed compiler
memory-port value. -/
def RawPortMatches (program : Program) (table : WireTable) {addressWidth
    dataWidth : Nat} (port : Loom.Hw.Compile.Port addressWidth dataWidth)
    (refs : PortRefs) : Prop :=
  RawExprMatches program table port.en refs.en ∧
  RawExprMatches program table port.addr refs.addr ∧
  RawExprMatches program table port.data refs.data

/-- A structural mux-root check is sound when its three operand references
already denote the corresponding source expressions. -/
theorem indexedMuxRootMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) {width : Nat}
    (condition : Loom.Emit.MicroVerilog.Expr 1)
    (yes no : Loom.Emit.MicroVerilog.Expr width)
    (conditionRef yesRef noRef out : Ref)
    (accepted : indexedMuxRootMatches indexeds table width conditionRef yesRef
      noRef out = true)
    (conditionMatches : RawExprMatches program table condition conditionRef)
    (yesMatches : RawExprMatches program table yes yesRef)
    (noMatches : RawExprMatches program table no noRef) :
    RawExprMatches program table (.mux condition yes no) out := by
  cases out with
  | reg name => simp [indexedMuxRootMatches] at accepted
  | wire number =>
      cases found : lookupIndexed? indexeds table number with
      | none => simp [indexedMuxRootMatches, found] at accepted
      | some indexed =>
          obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
          cases rhs <;> simp [indexedMuxRootMatches, found] at accepted
          case mux actualCondition actualYes actualNo =>
            obtain ⟨raw, rawAt, rawMatch⟩ :=
              lookupIndexed_rawWireAt program hmatches table number
                ⟨indexedNumber, actualWidth,
                  .mux actualCondition actualYes actualNo⟩ found
            obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
              (indexed := ⟨indexedNumber, actualWidth,
                .mux actualCondition actualYes actualNo⟩) rawMatch
            rcases accepted with ⟨actualWidthEq, rhsMatches⟩
            have rhsRefs :
                (actualCondition, actualYes, actualNo) =
                  (conditionRef, yesRef, noRef) := by
              simpa using rhsMatches
            cases rhsRefs
            exact .mux rawAt (widthEq.trans actualWidthEq) rhsEq
              conditionMatches yesMatches noMatches
  | namedWire number name =>
      apply RawExprMatches.named
      cases found : lookupIndexed? indexeds table number with
      | none => simp [indexedMuxRootMatches, found] at accepted
      | some indexed =>
          obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
          cases rhs <;> simp [indexedMuxRootMatches, found] at accepted
          case mux actualCondition actualYes actualNo =>
            obtain ⟨raw, rawAt, rawMatch⟩ :=
              lookupIndexed_rawWireAt program hmatches table number
                ⟨indexedNumber, actualWidth,
                  .mux actualCondition actualYes actualNo⟩ found
            obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
              (indexed := ⟨indexedNumber, actualWidth,
                .mux actualCondition actualYes actualNo⟩) rawMatch
            rcases accepted with ⟨actualWidthEq, rhsMatches⟩
            have rhsRefs :
                (actualCondition, actualYes, actualNo) =
                  (conditionRef, yesRef, noRef) := by
              simpa using rhsMatches
            cases rhsRefs
            exact .mux rawAt (widthEq.trans actualWidthEq) rhsEq
              conditionMatches yesMatches noMatches

/-- Three accepted mux roots construct the exact conditional compiler port. -/
theorem indexedPortMuxMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) {addressWidth dataWidth : Nat}
    (guard : Loom.Emit.MicroVerilog.Expr 1)
    (thenPort elsePort : Loom.Hw.Compile.Port addressWidth dataWidth)
    (guardRef : Ref) (thenRefs elseRefs out : PortRefs)
    (accepted : indexedPortMuxMatches indexeds table addressWidth dataWidth
      guardRef thenRefs elseRefs out = true)
    (guardMatches : RawExprMatches program table guard guardRef)
    (thenMatches : RawPortMatches program table thenPort thenRefs)
    (elseMatches : RawPortMatches program table elsePort elseRefs) :
    RawPortMatches program table
      { en := .mux guard thenPort.en elsePort.en
        addr := .mux guard thenPort.addr elsePort.addr
        data := .mux guard thenPort.data elsePort.data } out := by
  simp only [indexedPortMuxMatches, Bool.and_eq_true] at accepted
  exact ⟨indexedMuxRootMatches_raw program hmatches table guard thenPort.en
      elsePort.en guardRef thenRefs.en elseRefs.en out.en accepted.1.1
      guardMatches thenMatches.1 elseMatches.1,
    indexedMuxRootMatches_raw program hmatches table guard thenPort.addr
      elsePort.addr guardRef thenRefs.addr elseRefs.addr out.addr accepted.1.2
      guardMatches thenMatches.2.1 elseMatches.2.1,
    indexedMuxRootMatches_raw program hmatches table guard thenPort.data
      elsePort.data guardRef thenRefs.data elseRefs.data out.data accepted.2
      guardMatches thenMatches.2.2 elseMatches.2.2⟩

private theorem memPort_eq_of_no_write (memory : String)
    (addressWidth dataWidth port : Nat) :
    ∀ (action : Loom.Hw.Act)
      (current : Loom.Hw.Compile.Port addressWidth dataWidth),
      Loom.Hw.Compile.writesPortB memory port action = false →
      Loom.Hw.Compile.memPort memory addressWidth dataWidth port action current =
        current := by
  intro action
  induction action with
  | skip => intro _ _; rfl
  | seq left right leftIH rightIH =>
      intro current accepted
      have notMem : port ∉ Loom.Hw.Compile.portTrace memory (.seq left right) := by
        simpa [Loom.Hw.Compile.writesPortB] using accepted
      simp only [Loom.Hw.Compile.portTrace, List.mem_append, not_or] at notMem
      rw [Loom.Hw.Compile.memPort,
        rightIH _ (by simpa [Loom.Hw.Compile.writesPortB] using notMem.2),
        leftIH _ (by simpa [Loom.Hw.Compile.writesPortB] using notMem.1)]
  | ite guard thenAction elseAction thenIH elseIH =>
      intro current accepted
      have notMem : port ∉ Loom.Hw.Compile.portTrace memory
          (.ite guard thenAction elseAction) := by
        simpa [Loom.Hw.Compile.writesPortB] using accepted
      simp only [Loom.Hw.Compile.portTrace, List.mem_append, not_or] at notMem
      rw [Loom.Hw.Compile.memPort, if_neg]
      simp [Loom.Hw.Compile.writesPortB, notMem]
  | write | writeSlice => intro _ _; rfl
  | memWrite actualAddressWidth actualDataWidth actualMemory actualPort
      address value =>
      intro current accepted
      have notMem : port ∉ Loom.Hw.Compile.portTrace memory
          (.memWrite actualAddressWidth actualDataWidth actualMemory actualPort
            address value) := by
        simpa [Loom.Hw.Compile.writesPortB] using accepted
      simp only [Loom.Hw.Compile.memPort]
      by_cases samePort : actualMemory = memory ∧ actualPort = port
      · exact False.elim (notMem (by simp [Loom.Hw.Compile.portTrace, samePort]))
      · rw [if_neg samePort]

/-- Soundness of the string-free symbolic action checker against the
reference `Compile.memPort` function. -/
theorem nextPortMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (memory : String)
    (addressWidth dataWidth port : Nat) :
    ∀ (action : Loom.Hw.Act) (current out : PortRefs) (cert : NextPortCert),
      nextPortMatches indexeds table memory addressWidth dataWidth port action
        current out cert = true →
      ∀ currentPort : Loom.Hw.Compile.Port addressWidth dataWidth,
        RawPortMatches program table currentPort current →
        RawPortMatches program table
          (Loom.Hw.Compile.memPort memory addressWidth dataWidth port action
            currentPort) out := by
  intro action
  induction action <;> intro current out cert accepted currentPort currentMatches
  · cases cert <;> simp [nextPortMatches] at accepted
    subst out
    simpa [Loom.Hw.Compile.memPort] using currentMatches
  · rename_i left right leftIH rightIH
    cases cert with
    | seq mid leftCert rightCert =>
        simp only [nextPortMatches, Bool.and_eq_true] at accepted
        have leftMatches := leftIH current mid leftCert accepted.1
          currentPort currentMatches
        simpa only [Loom.Hw.Compile.memPort] using
          rightIH mid out rightCert accepted.2
            (Loom.Hw.Compile.memPort memory addressWidth dataWidth port left
              currentPort) leftMatches
    | same =>
        simp only [nextPortMatches, Bool.and_eq_true, beq_iff_eq] at accepted
        rw [← accepted.2]
        have writesFalse :
            Loom.Hw.Compile.writesPortB memory port (.seq left right) = false := by
          cases found : Loom.Hw.Compile.writesPortB memory port (.seq left right) <;>
            simp_all
        rw [memPort_eq_of_no_write memory addressWidth dataWidth port
          (.seq left right) currentPort writesFalse]
        exact currentMatches
    | _ => simp [nextPortMatches] at accepted
  · rename_i guard thenAction elseAction thenIH elseIH
    by_cases writes : Loom.Hw.Compile.writesPortB memory port thenAction ||
        Loom.Hw.Compile.writesPortB memory port elseAction
    · cases cert with
      | ite guardRef thenRefs elseRefs thenCert elseCert =>
          simp only [nextPortMatches, writes, if_true, Bool.and_eq_true]
            at accepted
          have guardMatches := indexedExprMatches_raw program hmatches table
            (Loom.Hw.Compile.compileExpr guard) guardRef accepted.1.1.1
          have thenMatches := thenIH current thenRefs thenCert accepted.1.1.2
            currentPort currentMatches
          have elseMatches := elseIH current elseRefs elseCert accepted.1.2
            currentPort currentMatches
          rw [Loom.Hw.Compile.memPort, if_pos writes]
          exact indexedPortMuxMatches_raw program hmatches table
            (Loom.Hw.Compile.compileExpr guard)
            (Loom.Hw.Compile.memPort memory addressWidth dataWidth port
              thenAction currentPort)
            (Loom.Hw.Compile.memPort memory addressWidth dataWidth port
              elseAction currentPort)
            guardRef thenRefs elseRefs out accepted.2 guardMatches
            thenMatches elseMatches
      | _ => simp [nextPortMatches, writes] at accepted
    · cases cert with
      | same =>
          simp only [nextPortMatches, writes, Bool.not_false,
            Bool.true_and, beq_iff_eq] at accepted
          rw [← accepted]
          rw [Loom.Hw.Compile.memPort, if_neg writes]
          exact currentMatches
      | _ => simp [nextPortMatches, writes] at accepted
  · cases cert <;> simp [nextPortMatches] at accepted
    subst out
    exact currentMatches
  · cases cert <;> simp [nextPortMatches] at accepted
    subst out
    exact currentMatches
  · rename_i actualAddressWidth actualDataWidth actualMemory actualPort
      address value
    by_cases samePort : actualMemory = memory ∧ actualPort = port
    · by_cases sameWidths : actualAddressWidth = addressWidth ∧
          actualDataWidth = dataWidth
      · rcases samePort with ⟨rfl, rfl⟩
        rcases sameWidths with ⟨rfl, rfl⟩
        cases cert with
        | write =>
            simp [nextPortMatches] at accepted
            simp only [Loom.Hw.Compile.memPort]
            exact ⟨indexedExprMatches_raw program hmatches table _ _
                accepted.1.1,
              indexedExprMatches_raw program hmatches table _ _ accepted.1.2,
              indexedExprMatches_raw program hmatches table _ _ accepted.2⟩
        | _ => simp [nextPortMatches] at accepted
      · cases cert <;>
          simp [nextPortMatches, Loom.Hw.Compile.memPort, samePort, sameWidths]
            at accepted ⊢
        subst out
        exact currentMatches
    · cases cert <;>
        simp [nextPortMatches, Loom.Hw.Compile.memPort, samePort] at accepted ⊢
      subst out
      exact currentMatches

/-- Soundness of the ordered scheduler fold used to construct one compiled
memory write port. -/
theorem nextPortRulesMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (memory : String)
    (addressWidth dataWidth port : Nat) :
    ∀ (rules : List Loom.Hw.Rule) (current out : PortRefs)
      (cert : NextPortRulesCert),
      nextPortRulesMatches indexeds table memory addressWidth dataWidth port
        rules current out cert = true →
      ∀ currentPort : Loom.Hw.Compile.Port addressWidth dataWidth,
        RawPortMatches program table currentPort current →
        RawPortMatches program table
          (rules.foldl (fun acc rule => Loom.Hw.Compile.memPort memory
            addressWidth dataWidth port rule.body acc) currentPort) out := by
  intro rules
  induction rules with
  | nil =>
      intro current out cert accepted currentPort currentMatches
      cases cert <;> simp [nextPortRulesMatches] at accepted
      subst out
      exact currentMatches
  | cons rule rules rulesIH =>
      intro current out cert accepted currentPort currentMatches
      cases cert with
      | nil => simp [nextPortRulesMatches] at accepted
      | cons mid head tail =>
          simp only [nextPortRulesMatches, Bool.and_eq_true] at accepted
          have headMatches := nextPortMatches_raw program hmatches table memory
            addressWidth dataWidth port rule.body current mid head accepted.1
            currentPort currentMatches
          simpa only [List.foldl_cons] using
            rulesIH mid out tail accepted.2
              (Loom.Hw.Compile.memPort memory addressWidth dataWidth port
                rule.body currentPort) headMatches

/-- Certificate-free behavioral meaning of three SSA roots as one compiled
memory port. Metadata and rendered-field binding are kept separate so this
statement captures exactly the semantic result of the verified rule fold. -/
def MemoryPortBehavior (design : Loom.Hw.Design) (program : Program)
    (table : WireTable) (memory : String) (addressWidth dataWidth port : Nat)
    (refs : PortRefs) : Prop :=
  RawPortMatches program table
    (Loom.Hw.Compile.compilePort design memory addressWidth dataWidth port) refs

/-- An ordered action certificate plus three checked zero-port roots yields
the certificate-free behavior of a complete compiled memory port. -/
theorem memoryPortBehavior_of_checks
    (design : Loom.Hw.Design) (program : Program)
    {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (memory : String) (addressWidth dataWidth port : Nat)
    (initial out : PortRefs) (cert : NextPortRulesCert)
    (rules : nextPortRulesMatches indexeds table memory addressWidth dataWidth
      port design.rules initial out cert = true)
    (hen : indexedExprMatches indexeds table
      (.lit (BitVec.ofNat 1 0)) initial.en = true)
    (haddr : indexedExprMatches indexeds table
      (.lit (BitVec.ofNat addressWidth 0)) initial.addr = true)
    (hdata : indexedExprMatches indexeds table
      (.lit (BitVec.ofNat dataWidth 0)) initial.data = true) :
    MemoryPortBehavior design program table memory addressWidth dataWidth port
      out := by
  apply nextPortRulesMatches_raw program hmatches table memory addressWidth
    dataWidth port design.rules initial out cert rules
  exact ⟨indexedExprMatches_raw program hmatches table _ _ hen,
    indexedExprMatches_raw program hmatches table _ _ haddr,
    indexedExprMatches_raw program hmatches table _ _ hdata⟩

/-- Declarative register-level meaning of a concrete SSA root.  This
proposition deliberately contains no symbolic certificate data: generated
leaf theorems discharge the Boolean check once, then the rest of the release
proof graph depends only on this semantic statement. -/
def RegisterBehaviorAt (design : Loom.Hw.Design) (program : Program)
    (table : WireTable) (index : Nat) (root : Ref) : Prop :=
  match design.regs[index]?, program.regs[index]? with
  | some source, some concrete =>
      source.name = concrete.name ∧ source.width = concrete.width ∧
      source.init.toNat = concrete.init ∧ concrete.next = root.render ∧
      RawExprMatches program table
        (design.rules.foldl
          (fun current rule => Loom.Hw.Compile.nextReg source.name
            source.width rule.body current)
          (.reg source.width source.name)) root
  | _, _ => False

/-- A bounded metadata check and an independently checked ordered-rule
certificate yield the certificate-free semantic proposition for one source
register.  The raw/indexed rope correspondence is the only bridge from the
numeric witness to the exact names present in the rendered program. -/
theorem registerBehaviorAt_of_checks
    (design : Loom.Hw.Design) (program : Program)
    {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (index : Nat) (source : Loom.Hw.RegDecl) (root : Ref)
    (cert : NextRulesCert)
    (sourceFound : design.regs[index]? = some source)
    (metadata : indexedRegisterMetadataMatchesAt design program index root = true)
    (rules : nextRulesMatches indexeds table source.name source.width
      design.rules (some (.reg source.name)) root cert = true) :
    RegisterBehaviorAt design program table index root := by
  cases concreteFound : program.regs[index]? with
  | none =>
      simp [indexedRegisterMetadataMatchesAt, sourceFound, concreteFound]
        at metadata
  | some concrete =>
      simp only [indexedRegisterMetadataMatchesAt, sourceFound, concreteFound,
        Bool.and_eq_true, beq_iff_eq] at metadata
      simp only [RegisterBehaviorAt, sourceFound, concreteFound]
      exact ⟨metadata.1.1.1, metadata.1.1.2, metadata.1.2, metadata.2,
        nextRulesMatches_raw program hmatches table source.name source.width
          design.rules (some (.reg source.name)) root cert rules
          (.reg source.width source.name) (.reg source.width source.name)⟩

/-- Shared-footprint variant of `registerBehaviorAt_of_checks`.  The coverage
proof is intended to be one named declaration reused by every generated
register leaf. -/
theorem registerBehaviorAt_of_covered_checks
    (design : Loom.Hw.Design) (program : Program)
    {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (footprints : RuleRegFootprints)
    (coverage : ruleRegFootprintsCoverB design.rules footprints = true)
    (index : Nat) (source : Loom.Hw.RegDecl) (root : Ref)
    (cert : NextRulesCert)
    (sourceFound : design.regs[index]? = some source)
    (metadata : indexedRegisterMetadataMatchesAt design program index root = true)
    (rules : nextRulesMatchesCovered indexeds table source.name source.width
      design.rules footprints (some (.reg source.name)) root cert = true) :
    RegisterBehaviorAt design program table index root := by
  cases concreteFound : program.regs[index]? with
  | none =>
      simp [indexedRegisterMetadataMatchesAt, sourceFound, concreteFound]
        at metadata
  | some concrete =>
      simp only [indexedRegisterMetadataMatchesAt, sourceFound, concreteFound,
        Bool.and_eq_true, beq_iff_eq] at metadata
      simp only [RegisterBehaviorAt, sourceFound, concreteFound]
      exact ⟨metadata.1.1.1, metadata.1.1.2, metadata.1.2, metadata.2,
        nextRulesMatchesCovered_raw program hmatches table source.name
          source.width design.rules footprints (some (.reg source.name)) root
          cert coverage rules (.reg source.width source.name)
          (.reg source.width source.name)⟩

/-- Ordered certificate-free register behavior for one bounded list.  The
explicit starting index makes completeness and source-order alignment part of
the proposition rather than a generator convention. -/
inductive RegisterBehaviorsFrom (design : Loom.Hw.Design) (program : Program)
    (table : WireTable) : Nat → List RegisterRoot → Prop
  | nil (start : Nat) : RegisterBehaviorsFrom design program table start []
  | cons {start : Nat} {entry : RegisterRoot} {entries : List RegisterRoot} :
      entry.index = start →
      RegisterBehaviorAt design program table entry.index entry.root →
      RegisterBehaviorsFrom design program table (start + 1) entries →
      RegisterBehaviorsFrom design program table start (entry :: entries)

/-- Balanced composition of bounded register-behavior leaves.  Generated
artifacts use this rope-shaped proposition so the top-level proof has
logarithmic depth and only references already-checked leaf declarations. -/
inductive RegisterBehaviorRopeFrom (design : Loom.Hw.Design)
    (program : Program) (table : WireTable) : Nat →
      Rope (List RegisterRoot) → Prop
  | leaf {start : Nat} {entries : List RegisterRoot} :
      RegisterBehaviorsFrom design program table start entries →
      RegisterBehaviorRopeFrom design program table start (.leaf entries)
  | node {start : Nat} {left right : Rope (List RegisterRoot)} :
      RegisterBehaviorRopeFrom design program table start left →
      RegisterBehaviorRopeFrom design program table
        (start + left.listLength) right →
      RegisterBehaviorRopeFrom design program table start (.node left right)

/-- Certificate-free meaning of one bounded memory-initialization leaf. -/
def MemoryInitBlockBehavior (source : Loom.Hw.MemDecl) (start : Nat)
    (values : List Nat) : Prop :=
  ∀ index, index < values.length →
    values.getD index 0 = (source.init (start + index)).toNat

/-- A successful bounded initialization check yields its pointwise semantic
meaning.  Subsequent proofs depend on this proposition rather than reducing
the Boolean checker again. -/
theorem memoryInitBlockBehavior_of_check (source : Loom.Hw.MemDecl)
    (start : Nat) (values : List Nat)
    (accepted : memoryInitBlockMatches source start values = true) :
    MemoryInitBlockBehavior source start values := by
  intro index inBounds
  induction values generalizing start index with
  | nil => simp at inBounds
  | cons value values ih =>
      simp only [memoryInitBlockMatches, Bool.and_eq_true, beq_iff_eq]
        at accepted
      cases index with
      | zero => simpa [List.getD] using accepted.1
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at inBounds
          have tailExact := ih (start + 1) accepted.2 index inBounds
          simp only [List.getD_cons_succ]
          have indexEq : start + 1 + index = start + (index + 1) := by omega
          rw [indexEq] at tailExact
          exact tailExact

/-- Match-packaged form used by generated memory leaves.  Keeping this case
split generic avoids placing source-memory elimination tactics in generated
proof files. -/
theorem memoryInitBlockBehaviorAt_of_check (design : Loom.Hw.Design)
    (memoryIndex start : Nat) (values : List Nat)
    (accepted :
      (match design.mems[memoryIndex]? with
       | some source => memoryInitBlockMatches source start values
       | none => false) = true) :
    match design.mems[memoryIndex]? with
    | some source => MemoryInitBlockBehavior source start values
    | none => False := by
  cases found : design.mems[memoryIndex]? with
  | none => simp [found] at accepted
  | some source =>
      exact memoryInitBlockBehavior_of_check source start values
        (by simpa only [found] using accepted)

/-- Balanced pointwise meaning of a complete concrete initialization image. -/
inductive MemoryInitBehaviorRopeFrom (source : Loom.Hw.MemDecl) :
    Nat → Rope (List Nat) → Prop
  | leaf {start : Nat} {values : List Nat} :
      MemoryInitBlockBehavior source start values →
      MemoryInitBehaviorRopeFrom source start (.leaf values)
  | node {start : Nat} {left right : Rope (List Nat)} :
      MemoryInitBehaviorRopeFrom source start left →
      MemoryInitBehaviorRopeFrom source (start + left.listLength) right →
      MemoryInitBehaviorRopeFrom source start (.node left right)

/-- A balanced initialization proof gives exact direct-rope lookup at every
in-bounds address, without flattening the image. -/
theorem MemoryInitBehaviorRopeFrom.getD
    {source : Loom.Hw.MemDecl} {start : Nat} {image : Rope (List Nat)}
    (behavior : MemoryInitBehaviorRopeFrom source start image) :
    ∀ address, address < image.listLength →
      image.getD address 0 = (source.init (start + address)).toNat := by
  induction behavior with
  | leaf block =>
      intro address inBounds
      simpa [Rope.getD] using block address inBounds
  | @node nodeStart left right leftBehavior rightBehavior leftIH rightIH =>
      intro address inBounds
      by_cases inLeft : address < left.listLength
      · simpa [Rope.getD, inLeft] using leftIH address inLeft
      · have inRight : address - left.listLength < right.listLength := by
          simp only [Rope.listLength] at inBounds
          omega
        have rightExact := rightIH (address - left.listLength) inRight
        rw [Rope.getD, if_neg inLeft]
        have addressEq :
            nodeStart + left.listLength + (address - left.listLength) =
              nodeStart + address := by omega
        rw [addressEq] at rightExact
        exact rightExact

/-! ## Complete concrete memory behavior -/

/-- One ordered concrete write-port root in a generated memory witness. -/
structure MemoryPortRoot where
  index : Nat
  refs : PortRefs
  deriving Repr, DecidableEq

/-- Exact binding of one concrete SSA write entry to the corresponding
verified `Compile.compilePort` behavior. -/
def MemoryPortBehaviorAt (design : Loom.Hw.Design) (program : Program)
    (table : WireTable) (memoryIndex portIndex : Nat) (refs : PortRefs) : Prop :=
  match design.mems[memoryIndex]?, program.mems[memoryIndex]? with
  | some source, some concrete =>
      match concrete.writes[portIndex]? with
      | some write =>
          source.name = concrete.name ∧
          source.addrWidth = concrete.addrWidth ∧
          source.dataWidth = concrete.dataWidth ∧
          write.en = refs.en.render ∧ write.addr = refs.addr.render ∧
          write.data = refs.data.render ∧
          MemoryPortBehavior design program table source.name source.addrWidth
            source.dataWidth portIndex refs
      | none => False
  | _, _ => False

theorem memoryPortBehaviorAt_of_checks
    (design : Loom.Hw.Design) (program : Program) (table : WireTable)
    (memoryIndex portIndex : Nat) (source : Loom.Hw.MemDecl)
    (concrete : Loom.Release.SSA.Mem) (write : Loom.Release.SSA.Write)
    (refs : PortRefs)
    (sourceFound : design.mems[memoryIndex]? = some source)
    (concreteFound : program.mems[memoryIndex]? = some concrete)
    (writeFound : concrete.writes[portIndex]? = some write)
    (nameEq : source.name = concrete.name)
    (addressWidthEq : source.addrWidth = concrete.addrWidth)
    (dataWidthEq : source.dataWidth = concrete.dataWidth)
    (enEq : write.en = refs.en.render) (addrEq : write.addr = refs.addr.render)
    (dataEq : write.data = refs.data.render)
    (behavior : MemoryPortBehavior design program table source.name
      source.addrWidth source.dataWidth portIndex refs) :
    MemoryPortBehaviorAt design program table memoryIndex portIndex refs := by
  simp only [MemoryPortBehaviorAt, sourceFound, concreteFound, writeFound]
  exact ⟨nameEq, addressWidthEq, dataWidthEq, enEq, addrEq, dataEq, behavior⟩

/-- Ordered, gap-free behavioral coverage of a concrete memory's ports. -/
inductive MemoryPortBehaviorsFrom (design : Loom.Hw.Design) (program : Program)
    (table : WireTable) (memoryIndex : Nat) : Nat → List MemoryPortRoot → Prop
  | nil (start : Nat) :
      MemoryPortBehaviorsFrom design program table memoryIndex start []
  | cons {start : Nat} {entry : MemoryPortRoot} {entries : List MemoryPortRoot} :
      entry.index = start →
      MemoryPortBehaviorAt design program table memoryIndex entry.index
        entry.refs →
      MemoryPortBehaviorsFrom design program table memoryIndex (start + 1)
        entries →
      MemoryPortBehaviorsFrom design program table memoryIndex start
        (entry :: entries)

/-- Source-indexed initialization behavior whose source declaration remains
behind a small match. This lets generated leaves compose without embedding a
large or machine-specific `MemDecl.init` function in their theorem types. -/
inductive MemoryInitBehaviorAtRope (design : Loom.Hw.Design)
    (memoryIndex : Nat) : Nat → Rope (List Nat) → Prop
  | leaf {start : Nat} {values : List Nat} :
      (match design.mems[memoryIndex]? with
       | some source => MemoryInitBlockBehavior source start values
       | none => False) →
      MemoryInitBehaviorAtRope design memoryIndex start (.leaf values)
  | node {start : Nat} {left right : Rope (List Nat)} :
      MemoryInitBehaviorAtRope design memoryIndex start left →
      MemoryInitBehaviorAtRope design memoryIndex
        (start + left.listLength) right →
      MemoryInitBehaviorAtRope design memoryIndex start (.node left right)

/-- Complete certificate-free meaning of one concrete SSA memory: exact
metadata, exact initialization tree, and ordered coverage of every write
entry by the verified compiler fold. -/
def MemoryBehaviorAt (design : Loom.Hw.Design) (program : Program)
    (table : WireTable) (memoryIndex : Nat) (init : Rope (List Nat))
    (ports : List MemoryPortRoot) : Prop :=
  match design.mems[memoryIndex]?, program.mems[memoryIndex]? with
  | some source, some concrete =>
      source.name = concrete.name ∧
      source.addrWidth = concrete.addrWidth ∧
      source.dataWidth = concrete.dataWidth ∧
      concrete.init = init ∧ concrete.writes.length = ports.length ∧
      MemoryInitBehaviorAtRope design memoryIndex 0 init ∧
      MemoryPortBehaviorsFrom design program table memoryIndex 0 ports
  | _, _ => False

theorem memoryBehaviorAt_of_checks
    (design : Loom.Hw.Design) (program : Program) (table : WireTable)
    (memoryIndex : Nat) (source : Loom.Hw.MemDecl)
    (concrete : Loom.Release.SSA.Mem) (init : Rope (List Nat))
    (ports : List MemoryPortRoot)
    (sourceFound : design.mems[memoryIndex]? = some source)
    (concreteFound : program.mems[memoryIndex]? = some concrete)
    (nameEq : source.name = concrete.name)
    (addressWidthEq : source.addrWidth = concrete.addrWidth)
    (dataWidthEq : source.dataWidth = concrete.dataWidth)
    (initEq : concrete.init = init) (portCount : concrete.writes.length = ports.length)
    (initBehavior : MemoryInitBehaviorAtRope design memoryIndex 0 init)
    (portBehavior : MemoryPortBehaviorsFrom design program table memoryIndex 0
      ports) :
    MemoryBehaviorAt design program table memoryIndex init ports := by
  simp only [MemoryBehaviorAt, sourceFound, concreteFound]
  exact ⟨nameEq, addressWidthEq, dataWidthEq, initEq, portCount,
    initBehavior, portBehavior⟩

/-- One complete concrete memory witness in source order. -/
structure MemoryRoot where
  index : Nat
  init : Rope (List Nat)
  ports : List MemoryPortRoot

/-- Ordered, gap-free behavioral coverage of all concrete memories. -/
inductive MemoryBehaviorsFrom (design : Loom.Hw.Design) (program : Program)
    (table : WireTable) : Nat → List MemoryRoot → Prop
  | nil (start : Nat) : MemoryBehaviorsFrom design program table start []
  | cons {start : Nat} {entry : MemoryRoot} {entries : List MemoryRoot} :
      entry.index = start →
      MemoryBehaviorAt design program table entry.index entry.init entry.ports →
      MemoryBehaviorsFrom design program table (start + 1) entries →
      MemoryBehaviorsFrom design program table start (entry :: entries)

/-- Exact concrete observability-output binding for one **exported** source
register (D39 `Design.outputs`: `exportedRegs` is every register unless the
design declares a selection, so this is the pre-D39 statement for every
design that does not use the feature). -/
def OutputBehaviorAt (design : Loom.Hw.Design) (program : Program)
    (index : Nat) : Prop :=
  match design.exportedRegs[index]?, program.outs[index]? with
  | some source, some concrete =>
      concrete.name = s!"o_{source.name}" ∧ concrete.width = source.width ∧
      concrete.value = source.name
  | _, _ => False

/-- Ordered output behavior over one bounded leaf. -/
inductive OutputBehaviorsFrom (design : Loom.Hw.Design) (program : Program) :
    Nat → List Nat → Prop
  | nil (start : Nat) : OutputBehaviorsFrom design program start []
  | cons {start index : Nat} {indices : List Nat} :
      index = start → OutputBehaviorAt design program index →
      OutputBehaviorsFrom design program (start + 1) indices →
      OutputBehaviorsFrom design program start (index :: indices)

/-- Balanced output coverage used by processor-scale generated artifacts. -/
inductive OutputBehaviorRopeFrom (design : Loom.Hw.Design) (program : Program) :
    Nat → Rope (List Nat) → Prop
  | leaf {start : Nat} {indices : List Nat} :
      OutputBehaviorsFrom design program start indices →
      OutputBehaviorRopeFrom design program start (.leaf indices)
  | node {start : Nat} {left right : Rope (List Nat)} :
      OutputBehaviorRopeFrom design program start left →
      OutputBehaviorRopeFrom design program (start + left.listLength) right →
      OutputBehaviorRopeFrom design program start (.node left right)

/-- Single certificate-free statement connecting a source design to every
state-bearing and observable component of an exact concrete SSA program. -/
def ModuleBehavior (design : Loom.Hw.Design) (program : Program)
    (indexeds : Rope (List IndexedWire)) (table : WireTable)
    (registers : Rope (List RegisterRoot)) (memories : List MemoryRoot)
    (outputs : Rope (List Nat)) : Prop :=
  design.name = program.name ∧
  IndexedRopeMatches 0 program.wires indexeds ∧
  IndexedRopeWellFormed program indexeds table 0 indexeds ∧
  DesignReadsValid design program ∧
  design.regs.length = registers.listLength ∧
  program.regs.length = registers.listLength ∧
  design.mems.length = memories.length ∧
  program.mems.length = memories.length ∧
  program.outs.length = outputs.listLength ∧
  RegisterBehaviorRopeFrom design program table 0 registers ∧
  MemoryBehaviorsFrom design program table 0 memories ∧
  OutputBehaviorRopeFrom design program 0 outputs

theorem moduleBehavior_of_checks
    (design : Loom.Hw.Design) (program : Program)
    (indexeds : Rope (List IndexedWire)) (table : WireTable)
    (registers : Rope (List RegisterRoot)) (memories : List MemoryRoot)
    (outputs : Rope (List Nat))
    (name : design.name = program.name)
    (wires : IndexedRopeMatches 0 program.wires indexeds)
    (wiresWellFormed : IndexedRopeWellFormed program indexeds table 0 indexeds)
    (readsValid : DesignReadsValid design program)
    (sourceRegisterCount : design.regs.length = registers.listLength)
    (concreteRegisterCount : program.regs.length = registers.listLength)
    (sourceMemoryCount : design.mems.length = memories.length)
    (concreteMemoryCount : program.mems.length = memories.length)
    (outputCount : program.outs.length = outputs.listLength)
    (registerBehavior : RegisterBehaviorRopeFrom design program table 0 registers)
    (memoryBehavior : MemoryBehaviorsFrom design program table 0 memories)
    (outputBehavior : OutputBehaviorRopeFrom design program 0 outputs) :
    ModuleBehavior design program indexeds table registers memories outputs :=
  ⟨name, wires, wiresWellFormed, readsValid, sourceRegisterCount,
    concreteRegisterCount, sourceMemoryCount,
    concreteMemoryCount, outputCount, registerBehavior, memoryBehavior,
    outputBehavior⟩

end Loom.Release.Symbolic
