-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ActionWideRegister
import Loom.Release.SymbolicSound

/-!
# Hash-consed register states for release certificates

Large action proofs must not place an expanded persistent register trie in the
type of every intermediate theorem.  This module gives trie nodes stable
numeric identities in a balanced table.  Action evidence therefore threads a
small root number; every write and lookup remains independently kernel
checkable against the table.
-/

namespace Loom.Release.Symbolic.ActionWide

open Loom.Hw
open Loom.Release.SSA

/-- One hash-consed node of a persistent register-reference trie. -/
inductive RefStateNode where
  | empty
  | leaf (value : Ref)
  | branch (zeroChild oneChild : Nat)
  deriving Repr, DecidableEq

/-- Balanced layout metadata for hash-consed state nodes. `emptyRoot` names a
checked empty node used when a write first descends through an empty subtree. -/
structure RefStateTable where
  leafSize : Nat
  leafCount : Nat
  emptyRoot : Nat
  depth : Nat
  deriving Repr, DecidableEq

/-- Resolve a state-node number without flattening the global table. -/
def lookupStateNode? (nodes : Rope (List RefStateNode))
    (table : RefStateTable) (number : Nat) : Option RefStateNode := do
  guard (table.leafSize > 0)
  let path ← balancedPath? table.leafCount (number / table.leafSize)
  nodes.resolve? ⟨path, number % table.leafSize⟩

theorem lookupStateNode_of_resolve
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {number : Nat} {path : List Bool} {node : RefStateNode}
    (positive : table.leafSize > 0)
    (pathFound : balancedPath? table.leafCount
      (number / table.leafSize) = some path)
    (resolved : nodes.resolve? ⟨path, number % table.leafSize⟩ = some node) :
    lookupStateNode? nodes table number = some node := by
  simp [lookupStateNode?, positive, pathFound, resolved, guard]

/-- Interpret one register lookup from a hash-consed trie root. Empty subtrees
fall back to the corresponding source register, exactly as `SparseRefs` does. -/
def lookupStateRef? (nodes : Rope (List RefStateNode))
    (table : RefStateTable) (registers : Array RegDecl) :
    Nat → Nat → Nat → Option Ref
  | 0, root, index =>
      match lookupStateNode? nodes table root with
      | some (.leaf value) => some value
      | some .empty => registers[index]?.map (Ref.reg ·.name)
      | _ => none
  | depth + 1, root, index =>
      match lookupStateNode? nodes table root with
      | some .empty => registers[index]?.map (Ref.reg ·.name)
      | some (.branch zeroChild oneChild) =>
          lookupStateRef? nodes table registers depth
            (if index.testBit depth then oneChild else zeroChild) index
      | _ => none

/-- Check one persistent-trie update. The output path is fresh witness data;
the checker verifies every new branch and every shared unchanged child. -/
def checkedStateWrite (nodes : Rope (List RefStateNode))
    (table : RefStateTable) : Nat → Nat → Nat → Ref → Nat → Bool
  | 0, _, _, value, output =>
      lookupStateNode? nodes table output == some (.leaf value)
  | depth + 1, input, index, value, output =>
      let oldChildren :=
        match lookupStateNode? nodes table input with
        | some .empty => some (table.emptyRoot, table.emptyRoot)
        | some (.branch zeroChild oneChild) => some (zeroChild, oneChild)
        | _ => none
      match oldChildren, lookupStateNode? nodes table output with
      | some (oldZero, oldOne), some (.branch newZero newOne) =>
          if index.testBit depth then
            newZero == oldZero &&
              checkedStateWrite nodes table depth oldOne index value newOne
          else
            newOne == oldOne &&
              checkedStateWrite nodes table depth oldZero index value newZero
      | _, _ => false

/-- Structural persistent-trie update evidence. Every constructor checks at
most two bounded node lookups; no proof normalizes the global table. -/
inductive StateWriteEvidence (nodes : Rope (List RefStateNode))
    (table : RefStateTable) : Nat → Nat → Nat → Ref → Nat → Prop where
  | leaf {input index value output}
      (outputAccepted : lookupStateNode? nodes table output =
        some (.leaf value)) :
      StateWriteEvidence nodes table 0 input index value output
  | emptyZero {depth input index value output newZero}
      (bitAccepted : index.testBit depth = false)
      (inputAccepted : lookupStateNode? nodes table input = some .empty)
      (outputAccepted : lookupStateNode? nodes table output =
        some (.branch newZero table.emptyRoot))
      (childAccepted : StateWriteEvidence nodes table depth table.emptyRoot
        index value newZero) :
      StateWriteEvidence nodes table (depth + 1) input index value output

  | emptyOne {depth input index value output newOne}
      (bitAccepted : index.testBit depth = true)
      (inputAccepted : lookupStateNode? nodes table input = some .empty)
      (outputAccepted : lookupStateNode? nodes table output =
        some (.branch table.emptyRoot newOne))
      (childAccepted : StateWriteEvidence nodes table depth table.emptyRoot
        index value newOne) :
      StateWriteEvidence nodes table (depth + 1) input index value output
  | branchZero {depth input index value output oldZero oldOne newZero}
      (bitAccepted : index.testBit depth = false)
      (inputAccepted : lookupStateNode? nodes table input =
        some (.branch oldZero oldOne))
      (outputAccepted : lookupStateNode? nodes table output =
        some (.branch newZero oldOne))
      (childAccepted : StateWriteEvidence nodes table depth oldZero index value
        newZero) :
      StateWriteEvidence nodes table (depth + 1) input index value output
  | branchOne {depth input index value output oldZero oldOne newOne}
      (bitAccepted : index.testBit depth = true)
      (inputAccepted : lookupStateNode? nodes table input =
        some (.branch oldZero oldOne))
      (outputAccepted : lookupStateNode? nodes table output =
        some (.branch oldZero newOne))
      (childAccepted : StateWriteEvidence nodes table depth oldOne index value
        newOne) :
      StateWriteEvidence nodes table (depth + 1) input index value output

/-- The executable persistent-write checker produces kernel evidence. This is
the first translation-validation bridge: generated artifacts need only prove
the small Boolean check, while this theorem supplies the reusable structural
proof. -/
theorem checkedStateWrite_sound {nodes : Rope (List RefStateNode)}
    {table : RefStateTable} {depth input index output : Nat} {value : Ref}
    (accepted : checkedStateWrite nodes table depth input index value output =
      true) :
    StateWriteEvidence nodes table depth input index value output := by
  induction depth generalizing input output with
  | zero =>
      exact .leaf (by simpa [checkedStateWrite] using accepted)
  | succ depth ih =>
      cases hInput : lookupStateNode? nodes table input with
      | none => simp [checkedStateWrite, hInput] at accepted
      | some inputNode =>
        cases inputNode with
        | leaf inputValue => simp [checkedStateWrite, hInput] at accepted
        | empty =>
          cases hOutput : lookupStateNode? nodes table output with
          | none => simp [checkedStateWrite, hInput, hOutput] at accepted
          | some outputNode =>
            cases outputNode with
            | empty =>
                simp [checkedStateWrite, hInput, hOutput] at accepted
            | leaf outputValue =>
                simp [checkedStateWrite, hInput, hOutput] at accepted
            | branch newZero newOne =>
                by_cases bit : index.testBit depth = true
                · have parts : newZero = table.emptyRoot ∧
                      checkedStateWrite nodes table depth table.emptyRoot index
                        value newOne = true := by
                    simpa [checkedStateWrite, hInput, hOutput, bit] using
                      accepted
                  exact .emptyOne bit hInput
                    (by simpa [parts.1] using hOutput) (ih parts.2)
                · have bit' : index.testBit depth = false := by
                    cases value : index.testBit depth <;> simp_all
                  have parts : newOne = table.emptyRoot ∧
                      checkedStateWrite nodes table depth table.emptyRoot index
                        value newZero = true := by
                    simpa [checkedStateWrite, hInput, hOutput, bit'] using
                      accepted
                  exact .emptyZero bit' hInput
                    (by simpa [parts.1] using hOutput) (ih parts.2)
        | branch oldZero oldOne =>
          cases hOutput : lookupStateNode? nodes table output with
          | none => simp [checkedStateWrite, hInput, hOutput] at accepted
          | some outputNode =>
            cases outputNode with
            | empty =>
                simp [checkedStateWrite, hInput, hOutput] at accepted
            | leaf outputValue =>
                simp [checkedStateWrite, hInput, hOutput] at accepted
            | branch newZero newOne =>
                by_cases bit : index.testBit depth = true
                · have parts : newZero = oldZero ∧
                      checkedStateWrite nodes table depth oldOne index value
                        newOne = true := by
                    simpa [checkedStateWrite, hInput, hOutput, bit] using
                      accepted
                  exact .branchOne bit hInput
                    (by simpa [parts.1] using hOutput) (ih parts.2)
                · have bit' : index.testBit depth = false := by
                    cases value : index.testBit depth <;> simp_all
                  have parts : newOne = oldOne ∧
                      checkedStateWrite nodes table depth oldZero index value
                        newZero = true := by
                    simpa [checkedStateWrite, hInput, hOutput, bit'] using
                      accepted
                  exact .branchZero bit' hInput
                    (by simpa [parts.1] using hOutput) (ih parts.2)
/-- Structural lookup evidence for one register reference. -/
inductive StateLookupEvidence (nodes : Rope (List RefStateNode))
    (table : RefStateTable) (registers : Array RegDecl) :
    Nat → Nat → Nat → Ref → Prop where
  | empty {depth root index register}
      (nodeAccepted : lookupStateNode? nodes table root = some .empty)
      (registerAccepted : registers[index]? = some register) :
      StateLookupEvidence nodes table registers depth root index
        (.reg register.name)
  | leaf {root index value}
      (nodeAccepted : lookupStateNode? nodes table root = some (.leaf value)) :
      StateLookupEvidence nodes table registers 0 root index value
  | branchZero {depth root index value zeroChild oneChild}
      (bitAccepted : index.testBit depth = false)
      (nodeAccepted : lookupStateNode? nodes table root =
        some (.branch zeroChild oneChild))
      (childAccepted : StateLookupEvidence nodes table registers depth zeroChild
        index value) :
      StateLookupEvidence nodes table registers (depth + 1) root index value
  | branchOne {depth root index value zeroChild oneChild}
      (bitAccepted : index.testBit depth = true)
      (nodeAccepted : lookupStateNode? nodes table root =
        some (.branch zeroChild oneChild))
      (childAccepted : StateLookupEvidence nodes table registers depth oneChild
        index value) :
      StateLookupEvidence nodes table registers (depth + 1) root index value

/-- Structural lookup evidence computes the corresponding executable lookup.
This direction lets later semantic projection theorems consume named evidence
without reducing the balanced state-node table again. -/
theorem StateLookupEvidence.accepted
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {registers : Array RegDecl} {depth root index : Nat} {value : Ref}
    (evidence : StateLookupEvidence nodes table registers depth root index value) :
    lookupStateRef? nodes table registers depth root index = some value := by
  induction evidence with
  | @empty depth root index register nodeAccepted registerAccepted =>
      cases depth <;> unfold lookupStateRef? <;>
        rw [nodeAccepted, registerAccepted] <;> rfl
  | leaf nodeAccepted =>
      simp [lookupStateRef?, nodeAccepted]
  | branchZero bitAccepted nodeAccepted _ childIH =>
      simp [lookupStateRef?, nodeAccepted, bitAccepted, childIH]
  | branchOne bitAccepted nodeAccepted _ childIH =>
      simp [lookupStateRef?, nodeAccepted, bitAccepted, childIH]

/-- A certified trie write makes the written value observable at its output
root. This is the local state-to-register bridge used by shared action
projections. -/
theorem StateWriteEvidence.outputLookup
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {registers : Array RegDecl} {depth input index output : Nat} {value : Ref}
    (evidence : StateWriteEvidence nodes table depth input index value output) :
    StateLookupEvidence nodes table registers depth output index value := by
  induction evidence with
  | leaf outputAccepted => exact .leaf outputAccepted
  | emptyZero bitAccepted _ outputAccepted _ childIH =>
      exact .branchZero bitAccepted outputAccepted childIH
  | emptyOne bitAccepted _ outputAccepted _ childIH =>
      exact .branchOne bitAccepted outputAccepted childIH
  | branchZero bitAccepted _ outputAccepted _ childIH =>
      exact .branchZero bitAccepted outputAccepted childIH
  | branchOne bitAccepted _ outputAccepted _ childIH =>
      exact .branchOne bitAccepted outputAccepted childIH

/-- The distinguished empty root denotes the register fallback at every trie
depth. This invariant is deliberately supplied by the release witness rather
than trusted as part of `RefStateTable` metadata. -/
theorem lookupStateRef?_emptyRoot
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {registers : Array RegDecl}
    (emptyValid : lookupStateNode? nodes table table.emptyRoot = some .empty)
    (depth index : Nat) :
    lookupStateRef? nodes table registers depth table.emptyRoot index =
      registers[index]?.map (Ref.reg ·.name) := by
  cases depth <;> simp [lookupStateRef?, emptyValid]

/-- Distinct indices below the capacity of a trie differ in a represented
bit. -/
theorem exists_testBit_ne_of_ne_of_lt_pow
    {left right depth : Nat} (distinct : left ≠ right)
    (leftBound : left < 2 ^ depth) (rightBound : right < 2 ^ depth) :
    ∃ bit, bit < depth ∧ left.testBit bit ≠ right.testBit bit := by
  apply Classical.byContradiction
  intro noDifference
  apply distinct
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases represented : bit < depth
  · by_cases bitEq : left.testBit bit = right.testBit bit
    · exact bitEq
    · exact False.elim (noDifference ⟨bit, represented, bitEq⟩)
  · have depthLe : depth ≤ bit := Nat.le_of_not_gt represented
    have powerLe : 2 ^ depth ≤ 2 ^ bit :=
      Nat.pow_le_pow_right Nat.zero_lt_two depthLe
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le leftBound powerLe),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le rightBound powerLe)]

/-- A persistent trie write preserves every path which differs from the
written path in one of the represented low bits. At release depth ten,
distinct in-range register indices satisfy this premise. -/
theorem StateWriteEvidence.lookup_other
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {registers : Array RegDecl} {depth input index output : Nat} {value : Ref}
    (evidence : StateWriteEvidence nodes table depth input index value output)
    (emptyValid : lookupStateNode? nodes table table.emptyRoot = some .empty)
    (other : Nat)
    (differs : ∃ bit, bit < depth ∧
      index.testBit bit ≠ other.testBit bit) :
    lookupStateRef? nodes table registers depth output other =
      lookupStateRef? nodes table registers depth input other := by
  induction evidence with
  | leaf outputAccepted =>
      obtain ⟨bit, bitLt, _⟩ := differs
      omega
  | @emptyZero childDepth input index value output newZero bitAccepted
      inputAccepted outputAccepted childAccepted childIH =>
      obtain ⟨bit, bitLt, bitDiff⟩ := differs
      cases otherBit : other.testBit childDepth with
      | false =>
          have bitNe : bit ≠ childDepth := by
            intro bitEq
            subst bit
            simp [bitAccepted, otherBit] at bitDiff
          have lowerDiff : ∃ bit, bit < childDepth ∧
              index.testBit bit ≠ other.testBit bit := by
            exact ⟨bit, by omega, bitDiff⟩
          simp [lookupStateRef?, inputAccepted, outputAccepted, otherBit]
          rw [childIH lowerDiff, lookupStateRef?_emptyRoot emptyValid]
      | true =>
          simp [lookupStateRef?, inputAccepted, outputAccepted, otherBit,
            lookupStateRef?_emptyRoot emptyValid]
  | @emptyOne childDepth input index value output newOne bitAccepted
      inputAccepted outputAccepted childAccepted childIH =>
      obtain ⟨bit, bitLt, bitDiff⟩ := differs
      cases otherBit : other.testBit childDepth with
      | false =>
          simp [lookupStateRef?, inputAccepted, outputAccepted, otherBit,
            lookupStateRef?_emptyRoot emptyValid]
      | true =>
          have bitNe : bit ≠ childDepth := by
            intro bitEq
            subst bit
            simp [bitAccepted, otherBit] at bitDiff
          have lowerDiff : ∃ bit, bit < childDepth ∧
              index.testBit bit ≠ other.testBit bit := by
            exact ⟨bit, by omega, bitDiff⟩
          simp [lookupStateRef?, inputAccepted, outputAccepted, otherBit]
          rw [childIH lowerDiff, lookupStateRef?_emptyRoot emptyValid]
  | @branchZero childDepth input index value output oldZero oldOne newZero
      bitAccepted inputAccepted outputAccepted childAccepted childIH =>
      obtain ⟨bit, bitLt, bitDiff⟩ := differs
      cases otherBit : other.testBit childDepth with
      | false =>
          have bitNe : bit ≠ childDepth := by
            intro bitEq
            subst bit
            simp [bitAccepted, otherBit] at bitDiff
          have lowerDiff : ∃ bit, bit < childDepth ∧
              index.testBit bit ≠ other.testBit bit := by
            exact ⟨bit, by omega, bitDiff⟩
          simp [lookupStateRef?, inputAccepted, outputAccepted, otherBit,
            childIH lowerDiff]
      | true =>
          simp [lookupStateRef?, inputAccepted, outputAccepted, otherBit]
  | @branchOne childDepth input index value output oldZero oldOne newOne
      bitAccepted inputAccepted outputAccepted childAccepted childIH =>
      obtain ⟨bit, bitLt, bitDiff⟩ := differs
      cases otherBit : other.testBit childDepth with
      | false =>
          simp [lookupStateRef?, inputAccepted, outputAccepted, otherBit]
      | true =>
          have bitNe : bit ≠ childDepth := by
            intro bitEq
            subst bit
            simp [bitAccepted, otherBit] at bitDiff
          have lowerDiff : ∃ bit, bit < childDepth ∧
              index.testBit bit ≠ other.testBit bit := by
            exact ⟨bit, by omega, bitDiff⟩
          simp [lookupStateRef?, inputAccepted, outputAccepted, otherBit,
            childIH lowerDiff]

/-- Structural lookup evidence is functional. -/
theorem StateLookupEvidence.unique
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {registers : Array RegDecl} {depth root index : Nat} {left right : Ref}
    (leftEvidence : StateLookupEvidence nodes table registers depth root index left)
    (rightEvidence : StateLookupEvidence nodes table registers depth root index right) :
    left = right := by
  have leftAccepted := leftEvidence.accepted
  rw [rightEvidence.accepted] at leftAccepted
  exact (Option.some.inj leftAccepted).symm

/-- Lookup evidence before and after a write agrees at every distinct,
in-range register index. -/
theorem StateWriteEvidence.lookup_other_eq
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {registers : Array RegDecl} {depth input index output other : Nat}
    {value before after : Ref}
    (writeEvidence : StateWriteEvidence nodes table depth input index value output)
    (emptyValid : lookupStateNode? nodes table table.emptyRoot = some .empty)
    (distinct : index ≠ other)
    (indexBound : index < 2 ^ depth) (otherBound : other < 2 ^ depth)
    (beforeEvidence : StateLookupEvidence nodes table registers depth input other before)
    (afterEvidence : StateLookupEvidence nodes table registers depth output other after) :
    after = before := by
  have preserved := writeEvidence.lookup_other (registers := registers)
    emptyValid other
    (exists_testBit_ne_of_ne_of_lt_pow distinct indexBound otherBound)
  have beforeAccepted := beforeEvidence.accepted
  have afterAccepted := afterEvidence.accepted
  rw [afterAccepted, beforeAccepted] at preserved
  exact Option.some.inj preserved

/-- Successful executable lookup yields structural lookup evidence. -/
theorem lookupStateRef?_sound {nodes : Rope (List RefStateNode)}
    {table : RefStateTable} {registers : Array RegDecl}
    {depth root index : Nat} {value : Ref}
    (accepted : lookupStateRef? nodes table registers depth root index =
      some value) :
    StateLookupEvidence nodes table registers depth root index value := by
  induction depth generalizing root with
  | zero =>
      cases nodeFound : lookupStateNode? nodes table root with
      | none => simp [lookupStateRef?, nodeFound] at accepted
      | some node =>
        cases node with
        | empty =>
            cases registerFound : registers[index]? with
            | none => simp [lookupStateRef?, nodeFound, registerFound] at accepted
            | some register =>
                simp [lookupStateRef?, nodeFound, registerFound] at accepted
                subst value
                exact .empty nodeFound registerFound
        | leaf found =>
            simp [lookupStateRef?, nodeFound] at accepted
            subst value
            exact .leaf nodeFound
        | branch zeroChild oneChild =>
            simp [lookupStateRef?, nodeFound] at accepted
  | succ depth ih =>
      cases nodeFound : lookupStateNode? nodes table root with
      | none => simp [lookupStateRef?, nodeFound] at accepted
      | some node =>
        cases node with
        | empty =>
            cases registerFound : registers[index]? with
            | none => simp [lookupStateRef?, nodeFound, registerFound] at accepted
            | some register =>
                simp [lookupStateRef?, nodeFound, registerFound] at accepted
                subst value
                exact .empty nodeFound registerFound
        | leaf found => simp [lookupStateRef?, nodeFound] at accepted
        | branch zeroChild oneChild =>
            by_cases bit : index.testBit depth = true
            · exact .branchOne bit nodeFound
                (ih (by simpa [lookupStateRef?, nodeFound, bit] using accepted))
            · have bit' : index.testBit depth = false := by
                cases value : index.testBit depth <;> simp_all
              exact .branchZero bit' nodeFound
                (ih (by simpa [lookupStateRef?, nodeFound, bit'] using accepted))

/-- Check that one join output is the claimed mux in the indexed SSA graph. -/
def checkedJoinOutput (wires : Rope (List IndexedWire)) (table : WireTable)
    (join : Join) : Bool :=
  match join.output with
  | .wire number =>
      lookupIndexed? wires table number == some
        { number := number, width := join.width,
          rhs := .mux join.guard join.thenInput join.elseInput }
  | .reg _ => false
  | .namedWire _ _ => false

/-- Structural form of `checkedJoinOutput`, retaining the exact indexed-wire
lookup needed by semantic soundness. -/
inductive JoinOutputEvidence (wires : Rope (List IndexedWire))
    (table : WireTable) (join : Join) : Prop where
  | wire {number : Nat}
      (outputAccepted : join.output = .wire number)
      (lookupAccepted : lookupIndexed? wires table number = some
        { number := number, width := join.width,
          rhs := .mux join.guard join.thenInput join.elseInput }) :
      JoinOutputEvidence wires table join

theorem checkedJoinOutput_sound {wires : Rope (List IndexedWire)}
    {table : WireTable} {join : Join}
    (accepted : checkedJoinOutput wires table join = true) :
    JoinOutputEvidence wires table join := by
  cases outputEq : join.output with
  | reg name => simp [checkedJoinOutput, outputEq] at accepted
  | namedWire number name => simp [checkedJoinOutput, outputEq] at accepted
  | wire number =>
      simp [checkedJoinOutput, outputEq] at accepted
      exact .wire outputEq accepted

/-- Check the sequence of state updates introduced by an `ite` join block.
The list contains the root after each write, so the checker never constructs
or compares an expanded persistent state. -/
def checkedStateJoins (wires : Rope (List IndexedWire)) (wireTable : WireTable)
    (nodes : Rope (List RefStateNode)) (table : RefStateTable)
    (registers : Array RegDecl) (condition : Ref)
    (thenRoot elseRoot : Nat) :
    Nat → Nat → List Join → List Nat → Nat → Bool
  | input, changed, [], [], output =>
      changed == 0 && input == output
  | input, changed, join :: joins, nextRoot :: roots, output =>
      changed.testBit join.index &&
        registers[join.index]?.map (·.width) == some join.width &&
        lookupStateRef? nodes table registers table.depth thenRoot join.index ==
          some join.thenInput &&
        lookupStateRef? nodes table registers table.depth elseRoot join.index ==
          some join.elseInput &&
        join.guard == condition &&
        checkedJoinOutput wires wireTable join &&
        checkedStateWrite nodes table table.depth input join.index join.output nextRoot &&
        checkedStateJoins wires wireTable nodes table registers condition
          thenRoot elseRoot
          nextRoot (changed ^^^ (1 <<< join.index)) joins roots output
  | _, _, _, _, _ => false

/-- Kernel-checked conditional joins over hash-consed state roots. -/
inductive StateJoinsEvidence (wires : Rope (List IndexedWire))
    (wireTable : WireTable) (nodes : Rope (List RefStateNode))
    (table : RefStateTable) (registers : Array RegDecl) (condition : Ref) :
    Nat → Nat → Nat → Nat → List Join → Nat → Prop where
  | nil {input thenRoot elseRoot} :
      StateJoinsEvidence wires wireTable nodes table registers condition input
        thenRoot elseRoot 0 [] input
  | cons {input thenRoot elseRoot changed join joins nextRoot outputRoot}
      (bitAccepted : changed.testBit join.index = true)
      (widthAccepted : registers[join.index]?.map (·.width) = some join.width)
      (thenAccepted : StateLookupEvidence nodes table registers table.depth thenRoot
        join.index join.thenInput)
      (elseAccepted : StateLookupEvidence nodes table registers table.depth elseRoot
        join.index join.elseInput)
      (guardAccepted : join.guard = condition)
      (outputAccepted : JoinOutputEvidence wires wireTable join)
      (writeAccepted : StateWriteEvidence nodes table table.depth input join.index
        join.output nextRoot)
      (tailAccepted : StateJoinsEvidence wires wireTable nodes table registers
        condition nextRoot thenRoot elseRoot
        (changed ^^^ (1 <<< join.index)) joins outputRoot) :
      StateJoinsEvidence wires wireTable nodes table registers condition input
        thenRoot elseRoot changed (join :: joins) outputRoot

/-- The compact join checker implies the structural join evidence used by the
action soundness proof. -/
theorem checkedStateJoins_sound {wires : Rope (List IndexedWire)}
    {wireTable : WireTable} {nodes : Rope (List RefStateNode)}
    {table : RefStateTable} {registers : Array RegDecl} {condition : Ref}
    {thenRoot elseRoot input changed output : Nat} {joins : List Join}
    {roots : List Nat}
    (accepted : checkedStateJoins wires wireTable nodes table registers condition
      thenRoot elseRoot input changed joins roots output = true) :
    StateJoinsEvidence wires wireTable nodes table registers condition input
      thenRoot elseRoot changed joins output := by
  induction joins generalizing input changed roots with
  | nil =>
      cases roots with
      | nil =>
          simp [checkedStateJoins] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          exact .nil
      | cons root roots => simp [checkedStateJoins] at accepted
  | cons join joins ih =>
      cases roots with
      | nil => simp [checkedStateJoins] at accepted
      | cons nextRoot roots =>
          simp only [checkedStateJoins, Bool.and_eq_true] at accepted
          rcases accepted with
            ⟨⟨⟨⟨⟨⟨⟨bitAccepted, widthAccepted⟩, thenAccepted⟩,
              elseAccepted⟩, guardAccepted⟩, wireAccepted⟩,
              writeAccepted⟩, tailAccepted⟩
          refine .cons bitAccepted (beq_iff_eq.mp widthAccepted)
            (lookupStateRef?_sound (beq_iff_eq.mp thenAccepted))
            (lookupStateRef?_sound (beq_iff_eq.mp elseAccepted)) ?_ ?_
            (checkedStateWrite_sound writeAccepted) (ih tailAccepted)
          · exact of_decide_eq_true guardAccepted
          · exact checkedJoinOutput_sound wireAccepted

private theorem registerIndex_lt_pow_of_width
    {registers : Array RegDecl} {index width depth : Nat}
    (sizeBound : registers.size ≤ 2 ^ depth)
    (widthFound : registers[index]?.map (·.width) = some width) :
    index < 2 ^ depth := by
  cases found : registers[index]? with
  | none => simp [found] at widthFound
  | some register =>
      exact Nat.lt_of_lt_of_le (getElem?_eq_some_iff.mp found).1 sizeBound

/-- If a conditional join bitmap does not contain an index, the complete join
spine preserves that index's state lookup. -/
theorem StateJoinsEvidence.lookup_unchanged
    {wires : Rope (List IndexedWire)} {wireTable : WireTable}
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {registers : Array RegDecl} {condition : Ref}
    {input thenRoot elseRoot changed outputRoot query : Nat}
    {joins : List Join} {value : Ref}
    (evidence : StateJoinsEvidence wires wireTable nodes table registers
      condition input thenRoot elseRoot changed joins outputRoot)
    (emptyValid : lookupStateNode? nodes table table.emptyRoot = some .empty)
    (sizeBound : registers.size ≤ 2 ^ table.depth)
    (queryBound : query < 2 ^ table.depth)
    (unchanged : changed.testBit query = false)
    (inputLookup : StateLookupEvidence nodes table registers table.depth input query value) :
    StateLookupEvidence nodes table registers table.depth outputRoot query value := by
  induction evidence with
  | nil => exact inputLookup
  | @cons input thenRoot elseRoot changed join joins nextRoot outputRoot
      bitAccepted widthAccepted thenAccepted elseAccepted guardAccepted
      outputAccepted writeAccepted tailAccepted tailIH =>
      have indexBound : join.index < 2 ^ table.depth :=
        registerIndex_lt_pow_of_width sizeBound widthAccepted
      have distinct : join.index ≠ query := by
        intro equal
        subst query
        rw [bitAccepted] at unchanged
        contradiction
      have nextAccepted : lookupStateRef? nodes table registers table.depth nextRoot query =
          some value := by
        rw [writeAccepted.lookup_other (registers := registers) emptyValid query
          (exists_testBit_ne_of_ne_of_lt_pow distinct indexBound queryBound)]
        exact inputLookup.accepted
      have nextLookup := lookupStateRef?_sound nextAccepted
      apply tailIH
      · have shiftedBit : (1 <<< join.index).testBit query = false := by
          have beqFalse : (join.index == query) = false :=
            beq_eq_false_iff_ne.mpr distinct
          simpa [singletonIndex, beqFalse] using
            singletonIndex_testBit join.index query
        rw [Nat.testBit_xor, unchanged, shiftedBit]
        rfl
      · exact nextLookup

/-- A set bit in the conditional join bitmap has one corresponding mux join,
and the final state root observes that mux output. -/
theorem StateJoinsEvidence.lookup_changed
    {wires : Rope (List IndexedWire)} {wireTable : WireTable}
    {nodes : Rope (List RefStateNode)} {table : RefStateTable}
    {registers : Array RegDecl} {condition : Ref}
    {input thenRoot elseRoot changed outputRoot query : Nat}
    {joins : List Join}
    (evidence : StateJoinsEvidence wires wireTable nodes table registers
      condition input thenRoot elseRoot changed joins outputRoot)
    (emptyValid : lookupStateNode? nodes table table.emptyRoot = some .empty)
    (sizeBound : registers.size ≤ 2 ^ table.depth)
    (queryBound : query < 2 ^ table.depth)
    (changedAt : changed.testBit query = true) :
    ∃ join : Join,
      join.index = query ∧ join.guard = condition ∧
      JoinOutputEvidence wires wireTable join ∧
      StateLookupEvidence nodes table registers table.depth thenRoot query join.thenInput ∧
      StateLookupEvidence nodes table registers table.depth elseRoot query join.elseInput ∧
      StateLookupEvidence nodes table registers table.depth outputRoot query join.output := by
  induction evidence with
  | nil => simp at changedAt
  | @cons input thenRoot elseRoot changed join joins nextRoot outputRoot
      bitAccepted widthAccepted thenAccepted elseAccepted guardAccepted
      outputAccepted writeAccepted tailAccepted tailIH =>
      have indexBound : join.index < 2 ^ table.depth :=
        registerIndex_lt_pow_of_width sizeBound widthAccepted
      by_cases equal : join.index = query
      · subst query
        have nextLookup := writeAccepted.outputLookup (registers := registers)
        have shiftedBit : (1 <<< join.index).testBit join.index = true := by
          simp
        have tailUnchanged :
            (changed ^^^ (1 <<< join.index)).testBit join.index = false := by
          rw [Nat.testBit_xor, bitAccepted, shiftedBit]
          rfl
        exact ⟨join, rfl, guardAccepted, outputAccepted, thenAccepted,
          elseAccepted,
          tailAccepted.lookup_unchanged emptyValid sizeBound indexBound
            tailUnchanged nextLookup⟩
      · have tailChanged :
            (changed ^^^ (1 <<< join.index)).testBit query = true := by
          have shiftedBit : (1 <<< join.index).testBit query = false := by
            have beqFalse : (join.index == query) = false :=
              beq_eq_false_iff_ne.mpr equal
            simpa [singletonIndex, beqFalse] using
              singletonIndex_testBit join.index query
          rw [Nat.testBit_xor, changedAt, shiftedBit]
          rfl
        exact tailIH tailChanged

/-- Compact, untrusted control-flow witness. Only state-write roots are stored;
all logical evidence is reconstructed by `checkDagAction`. -/
inductive DagActionTrace where
  | atom (writeRoot : Option Nat)
  | seq (left right : DagActionTrace)
  | ite (thenTrace elseTrace : DagActionTrace) (joinRoots : List Nat)
  deriving Repr, DecidableEq

/-- The final root of a conditional join trace. -/
def joinedRoot (input : Nat) (roots : List Nat) : Nat :=
  roots.getLast?.getD input

/-- Execute the compact action witness. This checker follows at most one
bounded generated leaf at a time; it returns only a numeric state root and
does not construct a proof tree. -/
def checkDagAction (wires : Rope (List IndexedWire))
    (wireTable : WireTable) (nodes : Rope (List RefStateNode))
    (stateTable : RefStateTable) (registers : Array RegDecl) :
    Act → Nat → Nat → ActionCert → DagActionTrace → Option Nat
  | .skip, root, _, .skip, .atom none => some root
  | .memWrite .., root, _, .memWrite, .atom none => some root
  | .write width name value, root, needed, .write index valueRef,
      .atom writeRoot =>
      if checkedWriteHeader registers index width name then
        if needed.testBit index then
          if indexedExprMatches wires wireTable
              (Loom.Hw.Compile.compileExpr value) valueRef then
            match writeRoot with
            | some output =>
                if checkedStateWrite nodes stateTable stateTable.depth root index valueRef
                    output then some output else none
            | none => none
          else none
        else if writeRoot.isNone then some root else none
      else none
  | .seq left right, root, needed, .seq summary leftCert rightCert,
      .seq leftTrace rightTrace =>
      if summary == seqSummary leftCert.summary rightCert.summary then do
        let middle ← checkDagAction wires wireTable nodes stateTable registers
          left root (neededBitsBefore rightCert.summary needed) leftCert leftTrace
        checkDagAction wires wireTable nodes stateTable registers right middle
          needed rightCert rightTrace
      else none
  | .ite condition thenAction elseAction, root, needed,
      .ite summary conditionRef joins thenCert elseCert,
      .ite thenTrace elseTrace joinRoots =>
      if summary == iteSummary thenCert.summary elseCert.summary then
        if indexedExprMatches wires wireTable
            (Loom.Hw.Compile.compileExpr condition) conditionRef then do
          let changed := changedBitsAt summary needed
          let thenRoot ← checkDagAction wires wireTable nodes stateTable registers
            thenAction root changed thenCert thenTrace
          let elseRoot ← checkDagAction wires wireTable nodes stateTable registers
            elseAction root changed elseCert elseTrace
          let output := joinedRoot root joinRoots
          if checkedStateJoins wires wireTable nodes stateTable registers
              conditionRef thenRoot elseRoot root changed joins joinRoots output
              then some output
          else none
        else none
      else none
  | _, _, _, _, _ => none

/-- Action evidence whose state indices are constant-size numeric roots. -/
inductive DagBitSparseEvidence (wires : Rope (List IndexedWire))
    (wireTable : WireTable) (nodes : Rope (List RefStateNode))
    (stateTable : RefStateTable) (registers : Array RegDecl) :
    Act → Nat → Nat → ActionCert → Nat → Prop where
  | skip {root needed} :
      DagBitSparseEvidence wires wireTable nodes stateTable registers .skip root
        needed .skip root
  | memWrite {aw dw mem port address data root needed} :
      DagBitSparseEvidence wires wireTable nodes stateTable registers
        (.memWrite aw dw mem port address data) root needed .memWrite root
  | writeUnused {width name value root needed index valueRef}
      (headerAccepted : checkedWriteHeader registers index width name = true)
      (unused : needed.testBit index = false) :
      DagBitSparseEvidence wires wireTable nodes stateTable registers
        (.write width name value) root needed (.write index valueRef) root
  | writeNeeded {width name value root needed index valueRef outputRoot}
      (headerAccepted : checkedWriteHeader registers index width name = true)
      (used : needed.testBit index = true)
      (valueAccepted : indexedExprMatches wires wireTable
        (Loom.Hw.Compile.compileExpr value) valueRef = true)
      (writeAccepted : StateWriteEvidence nodes stateTable stateTable.depth root index valueRef
        outputRoot) :
      DagBitSparseEvidence wires wireTable nodes stateTable registers
        (.write width name value) root needed (.write index valueRef) outputRoot
  | seq {left right root needed summary leftCert rightCert middleRoot outputRoot}
      (summaryAccepted : summary = seqSummary leftCert.summary rightCert.summary)
      (leftAccepted : DagBitSparseEvidence wires wireTable nodes stateTable
        registers left root (neededBitsBefore rightCert.summary needed) leftCert
        middleRoot)
      (rightAccepted : DagBitSparseEvidence wires wireTable nodes stateTable
        registers right middleRoot needed rightCert outputRoot) :
      DagBitSparseEvidence wires wireTable nodes stateTable registers
        (.seq left right) root needed (.seq summary leftCert rightCert) outputRoot
  | ite {condition thenAction elseAction root needed summary conditionRef joins
      thenCert elseCert thenRoot elseRoot outputRoot}
      (summaryAccepted : summary = iteSummary thenCert.summary elseCert.summary)
      (conditionAccepted : indexedExprMatches wires wireTable
        (Loom.Hw.Compile.compileExpr condition) conditionRef = true)
      (thenAccepted : DagBitSparseEvidence wires wireTable nodes stateTable
        registers thenAction root (changedBitsAt summary needed) thenCert
        thenRoot)
      (elseAccepted : DagBitSparseEvidence wires wireTable nodes stateTable
        registers elseAction root (changedBitsAt summary needed) elseCert
        elseRoot)
      (joinsAccepted : StateJoinsEvidence wires wireTable nodes stateTable
        registers conditionRef root thenRoot elseRoot
        (changedBitsAt summary needed) joins outputRoot) :
      DagBitSparseEvidence wires wireTable nodes stateTable registers
        (.ite condition thenAction elseAction) root needed
        (.ite summary conditionRef joins thenCert elseCert) outputRoot

/-- The cached possible/definite bitmaps in a DAG certificate agree with a
structural traversal of its write leaves. This theorem is checked once over
the shared action evidence and then reused opaquely by every register
projection. -/
theorem DagBitSparseEvidence.summary_valid
    {wires : Rope (List IndexedWire)} {wireTable : WireTable}
    {nodes : Rope (List RefStateNode)} {stateTable : RefStateTable}
    {registers : Array RegDecl} {action : Act} {root needed output : Nat}
    {cert : ActionCert}
    (evidence : DagBitSparseEvidence wires wireTable nodes stateTable registers
      action root needed cert output) (query : Nat) :
    cert.summary.possible.testBit query = cert.possiblyWritesIndex query ∧
      cert.summary.definite.testBit query = cert.definitelyWritesIndex query := by
  induction evidence with
  | skip | memWrite => simp [ActionCert.summary,
      ActionCert.possiblyWritesIndex, ActionCert.definitelyWritesIndex]
  | writeUnused | writeNeeded =>
      simp [ActionCert.summary, singletonIndex,
        ActionCert.possiblyWritesIndex, ActionCert.definitelyWritesIndex]
  | @seq left right root needed summary leftCert rightCert middleRoot outputRoot
      summaryAccepted leftAccepted rightAccepted leftIH rightIH =>
      subst summaryAccepted
      constructor
      · change (seqSummary leftCert.summary rightCert.summary).possible.testBit
            query =
          (leftCert.possiblyWritesIndex query ||
            rightCert.possiblyWritesIndex query)
        simp only [seqSummary, Nat.testBit_or]
        rw [leftIH.1, rightIH.1]
      · change (seqSummary leftCert.summary rightCert.summary).definite.testBit
            query =
          (leftCert.definitelyWritesIndex query ||
            rightCert.definitelyWritesIndex query)
        simp only [seqSummary, Nat.testBit_or]
        rw [leftIH.2, rightIH.2]
  | @ite condition thenAction elseAction root needed summary conditionRef joins
      thenCert elseCert thenRoot elseRoot outputRoot summaryAccepted
      conditionAccepted thenAccepted elseAccepted joinsAccepted thenIH elseIH =>
      subst summaryAccepted
      constructor
      · change (iteSummary thenCert.summary elseCert.summary).possible.testBit
            query =
          (thenCert.possiblyWritesIndex query ||
            elseCert.possiblyWritesIndex query)
        simp only [iteSummary, Nat.testBit_or]
        rw [thenIH.1, elseIH.1]
      · change (iteSummary thenCert.summary elseCert.summary).definite.testBit
            query =
          (thenCert.definitelyWritesIndex query &&
            elseCert.definitelyWritesIndex query)
        simp only [iteSummary, Nat.testBit_and]
        rw [thenIH.2, elseIH.2]

theorem DagBitSparseEvidence.summary_definite_false_of_possible_false
    {wires : Rope (List IndexedWire)} {wireTable : WireTable}
    {nodes : Rope (List RefStateNode)} {stateTable : RefStateTable}
    {registers : Array RegDecl} {action : Act} {root needed output query : Nat}
    {cert : ActionCert}
    (evidence : DagBitSparseEvidence wires wireTable nodes stateTable registers
      action root needed cert output)
    (possibleFalse : cert.summary.possible.testBit query = false) :
    cert.summary.definite.testBit query = false := by
  have valid := evidence.summary_valid query
  cases definiteEq : cert.summary.definite.testBit query with
  | false => rfl
  | true =>
      have structuralDefinite : cert.definitelyWritesIndex query = true :=
        valid.2.symm.trans definiteEq
      have structuralPossible :=
        cert.possiblyWritesIndex_of_definitelyWritesIndex query structuralDefinite
      rw [← valid.1, possibleFalse] at structuralPossible
      contradiction

/-- Register-name uniqueness stated directly over the array representation
used by action certificates. -/
def RegisterNamesUnique (registers : Array RegDecl) : Prop :=
  ∀ {left right : Nat} {leftReg rightReg : RegDecl},
    registers[left]? = some leftReg → registers[right]? = some rightReg →
      leftReg.name = rightReg.name → left = right

/-- The structural `possible` write bit of a checked action certificate is
exactly the source compiler's `writesRegB` query for the declaration at that
index. -/
theorem DagBitSparseEvidence.possiblyWritesIndex_eq_writesRegB
    {wires : Rope (List IndexedWire)} {wireTable : WireTable}
    {nodes : Rope (List RefStateNode)} {stateTable : RefStateTable}
    {registers : Array RegDecl} {action : Act} {root needed output : Nat}
    {cert : ActionCert}
    (evidence : DagBitSparseEvidence wires wireTable nodes stateTable registers
      action root needed cert output)
    (unique : RegisterNamesUnique registers) (query : Nat) (source : RegDecl)
    (sourceFound : registers[query]? = some source) :
    cert.possiblyWritesIndex query =
      Loom.Hw.Compile.writesRegB source.name source.width action := by
  induction evidence with
  | skip | memWrite => simp [ActionCert.possiblyWritesIndex,
      Loom.Hw.Compile.writesRegB]
  | @writeUnused width name value root needed index valueRef headerAccepted
      unused =>
      cases actualFound : registers[index]? with
      | none => simp [checkedWriteHeader, actualFound] at headerAccepted
      | some actual =>
          simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
            beq_iff_eq] at headerAccepted
          by_cases indexEq : index = query
          · subst query
            have regEq : actual = source :=
              Option.some.inj (actualFound.symm.trans sourceFound)
            subst source
            simp [ActionCert.possiblyWritesIndex, singletonIndex_testBit,
              Loom.Hw.Compile.writesRegB, headerAccepted]
          · have nameNe : name ≠ source.name := by
              intro nameEq
              apply indexEq
              exact unique actualFound sourceFound
                (headerAccepted.1.trans nameEq)
            have indexFalse : (index == query) = false :=
              beq_eq_false_iff_ne.mpr indexEq
            have nameFalse : (name == source.name) = false :=
              beq_eq_false_iff_ne.mpr nameNe
            simp [ActionCert.possiblyWritesIndex, singletonIndex_testBit,
              Loom.Hw.Compile.writesRegB, indexFalse, nameFalse]
  | @writeNeeded width name value root needed index valueRef outputRoot
      headerAccepted used valueAccepted writeAccepted =>
      cases actualFound : registers[index]? with
      | none => simp [checkedWriteHeader, actualFound] at headerAccepted
      | some actual =>
          simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
            beq_iff_eq] at headerAccepted
          by_cases indexEq : index = query
          · subst query
            have regEq : actual = source :=
              Option.some.inj (actualFound.symm.trans sourceFound)
            subst source
            simp [ActionCert.possiblyWritesIndex, singletonIndex_testBit,
              Loom.Hw.Compile.writesRegB, headerAccepted]
          · have nameNe : name ≠ source.name := by
              intro nameEq
              apply indexEq
              exact unique actualFound sourceFound
                (headerAccepted.1.trans nameEq)
            have indexFalse : (index == query) = false :=
              beq_eq_false_iff_ne.mpr indexEq
            have nameFalse : (name == source.name) = false :=
              beq_eq_false_iff_ne.mpr nameNe
            simp [ActionCert.possiblyWritesIndex, singletonIndex_testBit,
              Loom.Hw.Compile.writesRegB, indexFalse, nameFalse]
  | seq summaryAccepted leftAccepted rightAccepted leftIH rightIH =>
      simp [ActionCert.possiblyWritesIndex, Loom.Hw.Compile.writesRegB,
        leftIH, rightIH]
  | ite summaryAccepted conditionAccepted thenAccepted elseAccepted
      joinsAccepted thenIH elseIH =>
      simp [ActionCert.possiblyWritesIndex, Loom.Hw.Compile.writesRegB,
        thenIH, elseIH]

/-- Cached-summary form of `possiblyWritesIndex_eq_writesRegB`. -/
theorem DagBitSparseEvidence.summary_possible_eq_writesRegB
    {wires : Rope (List IndexedWire)} {wireTable : WireTable}
    {nodes : Rope (List RefStateNode)} {stateTable : RefStateTable}
    {registers : Array RegDecl} {action : Act} {root needed output : Nat}
    {cert : ActionCert}
    (evidence : DagBitSparseEvidence wires wireTable nodes stateTable registers
      action root needed cert output)
    (unique : RegisterNamesUnique registers) (query : Nat) (source : RegDecl)
    (sourceFound : registers[query]? = some source) :
    cert.summary.possible.testBit query =
      Loom.Hw.Compile.writesRegB source.name source.width action :=
  (evidence.summary_valid query).1.trans
    (evidence.possiblyWritesIndex_eq_writesRegB unique query source sourceFound)

/-- An action certificate never changes a register whose needed bit is clear.
This is the central pruning invariant behind the action-wide speedup. -/
theorem DagBitSparseEvidence.lookup_unused
    {wires : Rope (List IndexedWire)} {wireTable : WireTable}
    {nodes : Rope (List RefStateNode)} {stateTable : RefStateTable}
    {registers : Array RegDecl} {action : Act} {root needed output query : Nat}
    {cert : ActionCert} {value : Ref}
    (evidence : DagBitSparseEvidence wires wireTable nodes stateTable registers
      action root needed cert output)
    (emptyValid : lookupStateNode? nodes stateTable stateTable.emptyRoot =
      some .empty)
    (sizeBound : registers.size ≤ 2 ^ stateTable.depth)
    (queryBound : query < 2 ^ stateTable.depth)
    (unused : needed.testBit query = false)
    (inputLookup : StateLookupEvidence nodes stateTable registers stateTable.depth root query
      value) :
    StateLookupEvidence nodes stateTable registers stateTable.depth output query value := by
  induction evidence with
  | skip | memWrite | writeUnused => exact inputLookup
  | @writeNeeded width name expression root needed index valueRef outputRoot
      headerAccepted used valueAccepted writeAccepted =>
      have distinct : index ≠ query := by
        intro equal
        subst query
        rw [used] at unused
        contradiction
      have indexBound : index < 2 ^ stateTable.depth := by
        cases found : registers[index]? with
        | none => simp [checkedWriteHeader, found] at headerAccepted
        | some register =>
            exact Nat.lt_of_lt_of_le (getElem?_eq_some_iff.mp found).1 sizeBound
      have outputAccepted :
          lookupStateRef? nodes stateTable registers stateTable.depth outputRoot query =
            some value := by
        rw [writeAccepted.lookup_other (registers := registers) emptyValid query
          (exists_testBit_ne_of_ne_of_lt_pow distinct indexBound queryBound)]
        exact inputLookup.accepted
      exact lookupStateRef?_sound outputAccepted
  | @seq left right root needed summary leftCert rightCert middleRoot outputRoot
      summaryAccepted leftAccepted rightAccepted leftIH rightIH =>
      have leftUnused :
          (neededBitsBefore rightCert.summary needed).testBit query = false := by
        simp [neededBitsBefore, Nat.testBit_xor, Nat.testBit_and, unused]
      exact rightIH unused (leftIH leftUnused inputLookup)
  | @ite condition thenAction elseAction root needed summary conditionRef joins
      thenCert elseCert thenRoot elseRoot outputRoot summaryAccepted
      conditionAccepted thenAccepted elseAccepted joinsAccepted thenIH elseIH =>
      have changedUnused : (changedBitsAt summary needed).testBit query = false := by
        simp [changedBitsAt, Nat.testBit_and, unused]
      exact joinsAccepted.lookup_unchanged emptyValid sizeBound queryBound
        changedUnused inputLookup

/-- Optional current-reference premise for one register projection. A
definitely-written action is independent of its incoming value. -/
def ActionCert.semanticCurrentRef (cert : ActionCert) (query : Nat)
    (input : Ref) : Option Ref :=
  if cert.summary.definite.testBit query then none else some input

theorem ActionCert.semanticCurrentRef_eq_none {cert : ActionCert}
    {query : Nat} {input : Ref}
    (definite : cert.summary.definite.testBit query = true) :
    cert.semanticCurrentRef query input = none := by
  simp [ActionCert.semanticCurrentRef, definite]

theorem ActionCert.semanticCurrentRef_eq_some {cert : ActionCert}
    {query : Nat} {input : Ref}
    (notDefinite : cert.summary.definite.testBit query = false) :
    cert.semanticCurrentRef query input = some input := by
  simp [ActionCert.semanticCurrentRef, notDefinite]

/-- One shared action-DAG certificate semantically validates every requested
register projection. Applying this theorem to a named certificate does not
re-traverse the source action: the kernel consumes the certificate as an
opaque constant and specializes only this generic proof. -/
theorem DagBitSparseEvidence.nextReg_raw
    (program : Program) {wires : Rope (List IndexedWire)}
    (wiresMatch : IndexedRopeMatches 0 program.wires wires)
    (wireTable : WireTable) {nodes : Rope (List RefStateNode)}
    {stateTable : RefStateTable} {registers : Array RegDecl}
    {action : Act} {root needed output query : Nat} {cert : ActionCert}
    (evidence : DagBitSparseEvidence wires wireTable nodes stateTable registers
      action root needed cert output)
    (emptyValid : lookupStateNode? nodes stateTable stateTable.emptyRoot =
      some .empty)
    (sizeBound : registers.size ≤ 2 ^ stateTable.depth)
    (unique : RegisterNamesUnique registers)
    (source : RegDecl) (sourceFound : registers[query]? = some source)
    (queryBound : query < 2 ^ stateTable.depth) (used : needed.testBit query = true)
    (inputRef : Ref)
    (inputLookup : StateLookupEvidence nodes stateTable registers stateTable.depth root query
      inputRef) :
    ∀ current : Loom.Emit.MicroVerilog.Expr source.width,
      RawCurrentMatches program wireTable current
        (cert.semanticCurrentRef query inputRef) →
      ∃ outputRef,
        StateLookupEvidence nodes stateTable registers stateTable.depth output query outputRef ∧
        RawExprMatches program wireTable
          (Loom.Hw.Compile.nextReg source.name source.width action current)
          outputRef := by
  induction evidence generalizing inputRef with
  | skip | memWrite =>
      intro current currentMatches
      exact ⟨inputRef, inputLookup, by
        simpa [ActionCert.semanticCurrentRef, ActionCert.summary,
          Loom.Hw.Compile.nextReg] using currentMatches⟩
  | @writeUnused width name expression root needed index valueRef
      headerAccepted unusedWrite =>
      intro current currentMatches
      have distinct : index ≠ query := by
        intro equal
        subst query
        rw [used] at unusedWrite
        contradiction
      cases actualFound : registers[index]? with
      | none => simp [checkedWriteHeader, actualFound] at headerAccepted
      | some actual =>
          simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
            beq_iff_eq] at headerAccepted
          have nameNe : name ≠ source.name := by
            intro nameEq
            apply distinct
            exact unique actualFound sourceFound
              (headerAccepted.1.trans nameEq)
          have definiteFalse :
              (ActionCert.write index valueRef).summary.definite.testBit query =
                false := by
            rw [ActionCert.summary]
            exact (singletonIndex_testBit index query).trans
              (beq_eq_false_iff_ne.mpr distinct)
          refine ⟨inputRef, inputLookup, ?_⟩
          simpa [ActionCert.semanticCurrentRef, definiteFalse,
            Loom.Hw.Compile.nextReg, nameNe] using currentMatches
  | @writeNeeded width name expression root needed index valueRef outputRoot
      headerAccepted writeUsed valueAccepted writeAccepted =>
      intro current currentMatches
      cases actualFound : registers[index]? with
      | none => simp [checkedWriteHeader, actualFound] at headerAccepted
      | some actual =>
          simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
            beq_iff_eq] at headerAccepted
          by_cases equal : index = query
          · subst query
            have regEq : actual = source :=
              Option.some.inj (actualFound.symm.trans sourceFound)
            subst source
            rcases headerAccepted with ⟨rfl, rfl⟩
            refine ⟨valueRef,
              writeAccepted.outputLookup (registers := registers), ?_⟩
            simpa [Loom.Hw.Compile.nextReg] using
              indexedExprMatches_raw program wiresMatch wireTable _ _
                valueAccepted
          · have nameNe : name ≠ source.name := by
              intro nameEq
              apply equal
              exact unique actualFound sourceFound
                (headerAccepted.1.trans nameEq)
            have indexBound : index < 2 ^ stateTable.depth :=
              Nat.lt_of_lt_of_le (getElem?_eq_some_iff.mp actualFound).1 sizeBound
            have outputAccepted :
                lookupStateRef? nodes stateTable registers stateTable.depth outputRoot query =
                  some inputRef := by
              rw [writeAccepted.lookup_other (registers := registers) emptyValid
                query (exists_testBit_ne_of_ne_of_lt_pow equal indexBound
                  queryBound)]
              exact inputLookup.accepted
            have outputLookup := lookupStateRef?_sound outputAccepted
            have definiteFalse :
                (ActionCert.write index valueRef).summary.definite.testBit query =
                  false := by
              rw [ActionCert.summary]
              exact (singletonIndex_testBit index query).trans
                (beq_eq_false_iff_ne.mpr equal)
            refine ⟨inputRef, outputLookup, ?_⟩
            simpa [ActionCert.semanticCurrentRef, definiteFalse,
              Loom.Hw.Compile.nextReg, nameNe] using currentMatches
  | @seq left right root needed summary leftCert rightCert middleRoot outputRoot
      summaryAccepted leftAccepted rightAccepted leftIH rightIH =>
      subst summary
      intro current currentMatches
      cases rightDef : rightCert.summary.definite.testBit query with
      | false =>
          have leftUsed :
              (neededBitsBefore rightCert.summary needed).testBit query = true := by
            simp [neededBitsBefore, Nat.testBit_xor, Nat.testBit_and, used,
              rightDef]
          have leftCurrent : RawCurrentMatches program wireTable current
              (leftCert.semanticCurrentRef query inputRef) := by
            cases leftDef : leftCert.summary.definite.testBit query with
            | false =>
                have wholeDefFalse :
                    (ActionCert.seq (seqSummary leftCert.summary
                      rightCert.summary) leftCert rightCert).summary.definite.testBit
                        query = false := by
                  change (seqSummary leftCert.summary rightCert.summary).definite.testBit
                    query = false
                  simp [seqSummary, leftDef, rightDef]
                rw [ActionCert.semanticCurrentRef_eq_some wholeDefFalse] at currentMatches
                rw [ActionCert.semanticCurrentRef_eq_some leftDef]
                exact currentMatches
            | true =>
                rw [ActionCert.semanticCurrentRef_eq_none leftDef]
                trivial
          obtain ⟨middleRef, middleLookup, middleMatches⟩ :=
            leftIH leftUsed inputRef inputLookup current leftCurrent
          have rightCurrent : RawCurrentMatches program wireTable
              (Loom.Hw.Compile.nextReg source.name source.width left current)
              (rightCert.semanticCurrentRef query middleRef) := by
            simpa [ActionCert.semanticCurrentRef, rightDef] using middleMatches
          obtain ⟨outputRef, outputLookup, outputMatches⟩ :=
            rightIH used middleRef middleLookup _ rightCurrent
          exact ⟨outputRef, outputLookup, outputMatches⟩
      | true =>
          have leftUnused :
              (neededBitsBefore rightCert.summary needed).testBit query = false := by
            simp [neededBitsBefore, Nat.testBit_xor, Nat.testBit_and, used,
              rightDef]
          have middleLookup := leftAccepted.lookup_unused emptyValid sizeBound
            queryBound leftUnused inputLookup
          have rightCurrent : RawCurrentMatches program wireTable
              (Loom.Hw.Compile.nextReg source.name source.width left current)
              (rightCert.semanticCurrentRef query inputRef) := by
            rw [ActionCert.semanticCurrentRef_eq_none rightDef]
            trivial
          obtain ⟨outputRef, outputLookup, outputMatches⟩ :=
            rightIH used inputRef middleLookup _ rightCurrent
          exact ⟨outputRef, outputLookup, outputMatches⟩
  | @ite condition thenAction elseAction root needed summary conditionRef joins
      thenCert elseCert thenRoot elseRoot outputRoot summaryAccepted
      conditionAccepted thenAccepted elseAccepted joinsAccepted thenIH elseIH =>
      subst summary
      intro current currentMatches
      let wholeCert : ActionCert := .ite
        (iteSummary thenCert.summary elseCert.summary) conditionRef joins
        thenCert elseCert
      cases possible : wholeCert.summary.possible.testBit query with
      | false =>
          have changedFalse :
              (changedBitsAt wholeCert.summary needed).testBit query = false := by
            simp [changedBitsAt, Nat.testBit_and, possible]
          have outputLookup := joinsAccepted.lookup_unchanged emptyValid sizeBound
            queryBound changedFalse inputLookup
          have wholeEvidence : DagBitSparseEvidence wires wireTable nodes
              stateTable registers (.ite condition thenAction elseAction) root
              needed wholeCert outputRoot :=
            .ite rfl conditionAccepted thenAccepted elseAccepted joinsAccepted
          have definiteFalse :=
            wholeEvidence.summary_definite_false_of_possible_false possible
          have noWrite :=
            (wholeEvidence.summary_possible_eq_writesRegB unique query source
              sourceFound).symm.trans possible
          have branchNoWrite :
              (Loom.Hw.Compile.writesRegB source.name source.width thenAction ||
                Loom.Hw.Compile.writesRegB source.name source.width elseAction) =
                false := by
            simpa [Loom.Hw.Compile.writesRegB] using noWrite
          have currentRaw : RawExprMatches program wireTable current inputRef := by
            rw [ActionCert.semanticCurrentRef_eq_some definiteFalse] at currentMatches
            exact currentMatches
          refine ⟨inputRef, outputLookup, ?_⟩
          simpa [Loom.Hw.Compile.nextReg, branchNoWrite] using currentRaw
      | true =>
          have changedTrue :
              (changedBitsAt wholeCert.summary needed).testBit query = true := by
            simp [changedBitsAt, Nat.testBit_and, possible, used]
          obtain ⟨join, joinIndex, joinGuard, joinOutput, thenLookup,
              elseLookup, outputLookup⟩ :=
            joinsAccepted.lookup_changed emptyValid sizeBound queryBound
              changedTrue
          subst query
          have thenCurrent : RawCurrentMatches program wireTable current
              (thenCert.semanticCurrentRef join.index inputRef) := by
            cases thenDef : thenCert.summary.definite.testBit join.index with
            | true =>
                rw [ActionCert.semanticCurrentRef_eq_none thenDef]
                trivial
            | false =>
                have wholeDefFalse : wholeCert.summary.definite.testBit
                    join.index = false := by
                  change (iteSummary thenCert.summary elseCert.summary).definite.testBit
                    join.index = false
                  simp [iteSummary, thenDef]
                have currentRaw : RawExprMatches program wireTable current
                    inputRef := by
                  rw [ActionCert.semanticCurrentRef_eq_some wholeDefFalse] at currentMatches
                  exact currentMatches
                rw [ActionCert.semanticCurrentRef_eq_some thenDef]
                exact currentRaw
          have elseCurrent : RawCurrentMatches program wireTable current
              (elseCert.semanticCurrentRef join.index inputRef) := by
            cases elseDef : elseCert.summary.definite.testBit join.index with
            | true =>
                rw [ActionCert.semanticCurrentRef_eq_none elseDef]
                trivial
            | false =>
                have wholeDefFalse : wholeCert.summary.definite.testBit
                    join.index = false := by
                  change (iteSummary thenCert.summary elseCert.summary).definite.testBit
                    join.index = false
                  simp [iteSummary, elseDef]
                have currentRaw : RawExprMatches program wireTable current
                    inputRef := by
                  rw [ActionCert.semanticCurrentRef_eq_some wholeDefFalse] at currentMatches
                  exact currentMatches
                rw [ActionCert.semanticCurrentRef_eq_some elseDef]
                exact currentRaw
          obtain ⟨thenRef, thenOutputLookup, thenMatches⟩ :=
            thenIH changedTrue inputRef inputLookup current thenCurrent
          obtain ⟨elseRef, elseOutputLookup, elseMatches⟩ :=
            elseIH changedTrue inputRef inputLookup current elseCurrent
          have thenEq := thenOutputLookup.unique thenLookup
          have elseEq := elseOutputLookup.unique elseLookup
          subst thenRef
          subst elseRef
          have guardMatches := indexedExprMatches_raw program wiresMatch
            wireTable _ _ conditionAccepted
          have guardMatches' : RawExprMatches program wireTable
              (Loom.Hw.Compile.compileExpr condition) join.guard := by
            simpa [joinGuard] using guardMatches
          cases joinOutput with
          | @wire number outputEq lookupAccepted =>
              rw [outputEq] at outputLookup
              obtain ⟨raw, rawAt, rawMatch⟩ :=
                lookupIndexed_rawWireAt program wiresMatch wireTable number _
                  lookupAccepted
              obtain ⟨widthEq, rhsEq⟩ :=
                IndexedWire.matchesRaw_width_rhs rawMatch
              have muxMatches : RawExprMatches program wireTable
                  (.mux (Loom.Hw.Compile.compileExpr condition)
                    (Loom.Hw.Compile.nextReg source.name source.width
                      thenAction current)
                    (Loom.Hw.Compile.nextReg source.name source.width
                      elseAction current)) (.wire number) :=
                .mux rawAt widthEq rhsEq guardMatches' thenMatches elseMatches
              have wholeEvidence : DagBitSparseEvidence wires wireTable nodes
                  stateTable registers (.ite condition thenAction elseAction)
                  root needed wholeCert outputRoot :=
                .ite rfl conditionAccepted thenAccepted elseAccepted joinsAccepted
              have writeTrue :=
                (wholeEvidence.summary_possible_eq_writesRegB unique join.index
                  source sourceFound).symm.trans possible
              have branchWriteTrue :
                  (Loom.Hw.Compile.writesRegB source.name source.width
                      thenAction ||
                    Loom.Hw.Compile.writesRegB source.name source.width
                      elseAction) = true := by
                simpa [Loom.Hw.Compile.writesRegB] using writeTrue
              exact ⟨.wire number, outputLookup,
                by simpa [Loom.Hw.Compile.nextReg, branchWriteTrue] using
                  muxMatches⟩

/-- Specialize a shared action-DAG certificate to one exact input/output state
observation. The large certificate remains an opaque premise; only the generic
semantic induction above is reused for each register. -/
theorem DagBitSparseEvidence.nextReg_raw_of_lookups
    (program : Program) {wires : Rope (List IndexedWire)}
    (wiresMatch : IndexedRopeMatches 0 program.wires wires)
    (wireTable : WireTable) {nodes : Rope (List RefStateNode)}
    {stateTable : RefStateTable} {registers : Array RegDecl}
    {action : Act} {root needed output query : Nat} {cert : ActionCert}
    (evidence : DagBitSparseEvidence wires wireTable nodes stateTable registers
      action root needed cert output)
    (emptyValid : lookupStateNode? nodes stateTable stateTable.emptyRoot =
      some .empty)
    (sizeBound : registers.size ≤ 2 ^ stateTable.depth)
    (unique : RegisterNamesUnique registers)
    (source : RegDecl) (sourceFound : registers[query]? = some source)
    (queryBound : query < 2 ^ stateTable.depth) (used : needed.testBit query = true)
    (inputRef outputRef : Ref)
    (inputLookup : StateLookupEvidence nodes stateTable registers stateTable.depth root query
      inputRef)
    (outputLookup : StateLookupEvidence nodes stateTable registers stateTable.depth output
      query outputRef)
    (current : Loom.Emit.MicroVerilog.Expr source.width)
    (currentMatches : RawCurrentMatches program wireTable current
      (cert.semanticCurrentRef query inputRef)) :
    RawExprMatches program wireTable
      (Loom.Hw.Compile.nextReg source.name source.width action current)
      outputRef := by
  obtain ⟨actualRef, actualLookup, actualMatches⟩ :=
    evidence.nextReg_raw program wiresMatch wireTable emptyValid sizeBound unique
      source sourceFound queryBound used inputRef inputLookup current
      currentMatches
  have equal := actualLookup.unique outputLookup
  subst actualRef
  exact actualMatches

/-- Acceptance by the compact checker reconstructs the full structural action
evidence. The generated trace is therefore untrusted data, not proof code. -/
theorem checkDagAction_sound {wires : Rope (List IndexedWire)}
    {wireTable : WireTable} {nodes : Rope (List RefStateNode)}
    {stateTable : RefStateTable} {registers : Array RegDecl}
    {action : Act} {root needed : Nat} {cert : ActionCert}
    {trace : DagActionTrace} {output : Nat}
    (accepted : checkDagAction wires wireTable nodes stateTable registers
      action root needed cert trace = some output) :
    DagBitSparseEvidence wires wireTable nodes stateTable registers action root
      needed cert output := by
  induction trace generalizing action root needed cert output with
  | atom writeRoot =>
      cases action <;> cases cert <;> cases writeRoot <;>
        simp [checkDagAction] at accepted
      case skip.skip.none =>
        subst output
        exact .skip
      case memWrite.memWrite.none =>
        subst output
        exact .memWrite
      case write.write.none width name value index valueRef =>
        cases headerAccepted : checkedWriteHeader registers index width name <;>
          simp [headerAccepted] at accepted
        cases unused : needed.testBit index <;> simp [unused] at accepted
        subst output
        exact .writeUnused headerAccepted unused
      case write.write.some width name value index valueRef outputRoot =>
        cases headerAccepted : checkedWriteHeader registers index width name <;>
          simp [headerAccepted] at accepted
        cases used : needed.testBit index <;> simp [used] at accepted
        cases valueAccepted : indexedExprMatches wires wireTable
            (Loom.Hw.Compile.compileExpr value) valueRef <;>
          simp [valueAccepted] at accepted
        cases writeAccepted : checkedStateWrite nodes stateTable stateTable.depth root index
            valueRef outputRoot <;> simp [writeAccepted] at accepted
        subst output
        exact .writeNeeded headerAccepted used valueAccepted
          (checkedStateWrite_sound writeAccepted)
  | seq leftTrace rightTrace leftIH rightIH =>
      cases action <;> cases cert <;>
        simp [checkDagAction] at accepted
      case seq.seq left right summary leftCert rightCert =>
        by_cases summaryAccepted :
            summary = seqSummary leftCert.summary rightCert.summary
        · simp [summaryAccepted] at accepted
          cases leftAccepted : checkDagAction wires wireTable nodes stateTable
              registers left root (neededBitsBefore rightCert.summary needed)
              leftCert leftTrace with
          | none => simp [leftAccepted] at accepted
          | some middle =>
              simp [leftAccepted] at accepted
              exact .seq summaryAccepted (leftIH leftAccepted)
                (rightIH accepted)
        · simp [summaryAccepted] at accepted
  | ite thenTrace elseTrace joinRoots thenIH elseIH =>
      cases action <;> cases cert <;>
        simp [checkDagAction] at accepted
      case ite.ite condition thenAction elseAction summary conditionRef joins
          thenCert elseCert =>
        by_cases summaryAccepted :
            summary = iteSummary thenCert.summary elseCert.summary
        · subst summary
          simp at accepted
          cases conditionAccepted : indexedExprMatches wires wireTable
              (Loom.Hw.Compile.compileExpr condition) conditionRef <;>
            simp [conditionAccepted] at accepted
          cases thenAccepted : checkDagAction wires wireTable nodes stateTable
              registers thenAction root
              (changedBitsAt (iteSummary thenCert.summary elseCert.summary)
                needed) thenCert thenTrace with
          | none => simp [thenAccepted] at accepted
          | some thenRoot =>
              simp [thenAccepted] at accepted
              cases elseAccepted : checkDagAction wires wireTable nodes
                  stateTable registers elseAction root
                  (changedBitsAt (iteSummary thenCert.summary elseCert.summary)
                    needed) elseCert elseTrace with
              | none => simp [elseAccepted] at accepted
              | some elseRoot =>
                  simp [elseAccepted] at accepted
                  cases joinsAccepted : checkedStateJoins wires wireTable nodes
                      stateTable registers conditionRef thenRoot elseRoot root
                      (changedBitsAt
                        (iteSummary thenCert.summary elseCert.summary) needed)
                      joins joinRoots
                      (joinedRoot root joinRoots) <;>
                    simp [joinsAccepted] at accepted
                  subst output
                  exact .ite rfl conditionAccepted
                    (thenIH thenAccepted) (elseIH elseAccepted)
                    (checkedStateJoins_sound joinsAccepted)
        · simp [summaryAccepted] at accepted

end Loom.Release.Symbolic.ActionWide
