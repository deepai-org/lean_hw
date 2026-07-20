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

end Loom.Release.Symbolic.ActionWide
