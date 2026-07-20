-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ActionWideRegister

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

/-- Check the sequence of state updates introduced by an `ite` join block.
The list contains the root after each write, so the checker never constructs
or compares an expanded persistent state. -/
def checkedStateJoins (nodes : Rope (List RefStateNode))
    (table : RefStateTable) (registers : Array RegDecl) (condition : Ref)
    (thenRoot elseRoot : Nat) :
    Nat → Nat → List Join → List Nat → Nat → Bool
  | input, changed, [], [], output =>
      changed == 0 && input == output
  | input, changed, join :: joins, nextRoot :: roots, output =>
      changed.testBit join.index &&
        registers[join.index]?.map (·.width) == some join.width &&
        lookupStateRef? nodes table registers 10 thenRoot join.index ==
          some join.thenInput &&
        lookupStateRef? nodes table registers 10 elseRoot join.index ==
          some join.elseInput &&
        join.guard == condition &&
        (match join.output with | .wire _ => true | _ => false) &&
        checkedStateWrite nodes table 10 input join.index join.output nextRoot &&
        checkedStateJoins nodes table registers condition thenRoot elseRoot
          nextRoot (changed ^^^ (1 <<< join.index)) joins roots output
  | _, _, _, _, _ => false

/-- Kernel-checked conditional joins over hash-consed state roots. -/
inductive StateJoinsEvidence (nodes : Rope (List RefStateNode))
    (table : RefStateTable) (registers : Array RegDecl) (condition : Ref) :
    Nat → Nat → Nat → Nat → List Join → Nat → Prop where
  | nil {input thenRoot elseRoot} :
      StateJoinsEvidence nodes table registers condition input thenRoot elseRoot
        0 [] input
  | cons {input thenRoot elseRoot changed join joins nextRoot outputRoot}
      (bitAccepted : changed.testBit join.index = true)
      (widthAccepted : registers[join.index]?.map (·.width) = some join.width)
      (thenAccepted : StateLookupEvidence nodes table registers 10 thenRoot
        join.index join.thenInput)
      (elseAccepted : StateLookupEvidence nodes table registers 10 elseRoot
        join.index join.elseInput)
      (guardAccepted : join.guard = condition)
      (wireAccepted : ∃ number, join.output = .wire number)
      (writeAccepted : StateWriteEvidence nodes table 10 input join.index
        join.output nextRoot)
      (tailAccepted : StateJoinsEvidence nodes table registers condition
        nextRoot thenRoot elseRoot (changed ^^^ (1 <<< join.index)) joins
        outputRoot) :
      StateJoinsEvidence nodes table registers condition input thenRoot elseRoot
        changed (join :: joins) outputRoot

/-- The compact join checker implies the structural join evidence used by the
action soundness proof. -/
theorem checkedStateJoins_sound {nodes : Rope (List RefStateNode)}
    {table : RefStateTable} {registers : Array RegDecl} {condition : Ref}
    {thenRoot elseRoot input changed output : Nat} {joins : List Join}
    {roots : List Nat}
    (accepted : checkedStateJoins nodes table registers condition thenRoot
      elseRoot input changed joins roots output = true) :
    StateJoinsEvidence nodes table registers condition input thenRoot elseRoot
      changed joins output := by
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
          · cases outputKind : join.output with
            | reg name => simp [outputKind] at wireAccepted
            | wire number => exact ⟨number, rfl⟩

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
                if checkedStateWrite nodes stateTable 10 root index valueRef
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
          if checkedStateJoins nodes stateTable registers conditionRef thenRoot
              elseRoot root changed joins joinRoots output then some output
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
      (writeAccepted : StateWriteEvidence nodes stateTable 10 root index valueRef
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
      (joinsAccepted : StateJoinsEvidence nodes stateTable registers conditionRef
        root thenRoot elseRoot (changedBitsAt summary needed) joins outputRoot) :
      DagBitSparseEvidence wires wireTable nodes stateTable registers
        (.ite condition thenAction elseAction) root needed
        (.ite summary conditionRef joins thenCert elseCert) outputRoot

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
        cases writeAccepted : checkedStateWrite nodes stateTable 10 root index
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
                  cases joinsAccepted : checkedStateJoins nodes stateTable
                      registers conditionRef thenRoot elseRoot root
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
