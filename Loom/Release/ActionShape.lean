-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ActionStateDag

/-!
# State-free action certificate shape

The hash-consed state DAG is useful for observing a concrete register state,
but it is unnecessarily expensive for validating control-flow shape.  This
module separates the two concerns. `ActionShapeEvidence` checks the source
action, cached summaries, register headers, condition expressions, and mux
outputs exactly once without threading a persistent register trie.

Register-specific semantic certificates can reuse this opaque shape theorem
and inspect only branches whose cached summary mentions the queried register.
-/

namespace Loom.Release.Symbolic.ActionWide

open Loom.Hw
open Loom.Release.SSA

/-- Every mux output in a cached conditional is present with exactly the
claimed guard and branch references in the indexed SSA program. -/
inductive JoinOutputsEvidence (wires : Rope (List IndexedWire))
    (table : WireTable) : List Join → Prop where
  | nil : JoinOutputsEvidence wires table []
  | cons {join joins}
      (head : JoinOutputEvidence wires table join)
      (tail : JoinOutputsEvidence wires table joins) :
      JoinOutputsEvidence wires table (join :: joins)

/-- Structural correspondence between one source action and its cached,
indexed compilation certificate, independent of any concrete register state. -/
inductive ActionShapeEvidence (wires : Rope (List IndexedWire))
    (table : WireTable) (registers : Array RegDecl) :
    Act → Nat → ActionCert → Prop where
  | skip {needed} : ActionShapeEvidence wires table registers .skip needed .skip
  | memWrite {aw dw memory port address data needed} :
      ActionShapeEvidence wires table registers
        (.memWrite aw dw memory port address data) needed .memWrite
  | writeDead {width name value index valueRef needed}
      (header : checkedWriteHeader registers index width name = true)
      (dead : needed.testBit index = false) :
      ActionShapeEvidence wires table registers (.write width name value) needed
        (.write index valueRef)
  | writeLive {width name value index valueRef needed}
      (header : checkedWriteHeader registers index width name = true)
      (live : needed.testBit index = true) :
      ActionShapeEvidence wires table registers (.write width name value) needed
        (.write index valueRef)
  | sliceDead {width name lo fieldWidth inBounds value index valueRef needed}
      (header : checkedWriteHeader registers index width name = true)
      (dead : needed.testBit index = false) :
      ActionShapeEvidence wires table registers
        (.writeSlice width name lo fieldWidth inBounds value) needed
        (.writeSlice index valueRef)
  | sliceLive {width name lo fieldWidth inBounds value index valueRef needed}
      (header : checkedWriteHeader registers index width name = true)
      (live : needed.testBit index = true) :
      ActionShapeEvidence wires table registers
        (.writeSlice width name lo fieldWidth inBounds value) needed
        (.writeSlice index valueRef)
  | seq {left right needed summary leftCert rightCert}
      (summaryAccepted :
        summary = seqSummary leftCert.summary rightCert.summary)
      (leftAccepted : ActionShapeEvidence wires table registers left
        (neededBitsBefore rightCert.summary needed) leftCert)
      (rightAccepted : ActionShapeEvidence wires table registers right needed rightCert) :
      ActionShapeEvidence wires table registers (.seq left right) needed
        (.seq summary leftCert rightCert)
  | ite {condition thenAction elseAction needed summary conditionRef joins
      thenCert elseCert}
      (summaryAccepted :
        summary = iteSummary thenCert.summary elseCert.summary)
      (thenAccepted :
        ActionShapeEvidence wires table registers thenAction
          (changedBitsAt summary needed) thenCert)
      (elseAccepted :
        ActionShapeEvidence wires table registers elseAction
          (changedBitsAt summary needed) elseCert) :
      ActionShapeEvidence wires table registers
        (.ite condition thenAction elseAction) needed
        (.ite summary conditionRef joins thenCert elseCert)

/-- Locate the unique mux join used by one queried register. The evidence also
retains the exact SSA lookup, so the semantic theorem never trusts list search
or the generator's selected output. -/
inductive JoinAtEvidence (wires : Rope (List IndexedWire)) (table : WireTable)
    (condition : Ref) (query width : Nat) (thenRef elseRef : Ref) :
    List Join → Ref → Prop where
  | here {join joins}
      (indexAccepted : join.index = query)
      (widthAccepted : join.width = width)
      (guardAccepted : join.guard = condition)
      (thenAccepted : join.thenInput = thenRef)
      (elseAccepted : join.elseInput = elseRef)
      (outputAccepted : JoinOutputEvidence wires table join) :
      JoinAtEvidence wires table condition query width thenRef elseRef
        (join :: joins) join.output
  | there {join joins output}
      (tail : JoinAtEvidence wires table condition query width thenRef elseRef
        joins output) :
      JoinAtEvidence wires table condition query width thenRef elseRef
        (join :: joins) output

/-- Query-local execution of a cached action certificate. Unlike
`DagBitSparseEvidence`, this proof carries no persistent map: sequence nodes
thread one reference, and a conditional observes only the queried join. -/
inductive RegQueryEvidence (wires : Rope (List IndexedWire))
    (table : WireTable) (registers : Array RegDecl) (query width : Nat) :
    Act → Ref → Nat → ActionCert → Ref → Prop where
  | skip {input needed} :
      RegQueryEvidence wires table registers query width .skip input needed .skip input
  | memWrite {aw dw memory port address data input needed} :
      RegQueryEvidence wires table registers query width
        (.memWrite aw dw memory port address data) input needed .memWrite input
  | writeOther {writeWidth name value input needed index valueRef}
      (different : index ≠ query) :
      RegQueryEvidence wires table registers query width (.write writeWidth name value)
        input needed (.write index valueRef) input
  | writeDead {writeWidth name value input needed valueRef}
      (dead : needed.testBit query = false) :
      RegQueryEvidence wires table registers query width (.write writeWidth name value)
        input needed (.write query valueRef) input
  | writeLive {writeWidth name value input needed valueRef}
      (live : needed.testBit query = true)
      (valueAccepted : indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr value) valueRef = true) :
      RegQueryEvidence wires table registers query width (.write writeWidth name value)
        input needed (.write query valueRef) valueRef
  | sliceOther {writeWidth name lo fieldWidth inBounds value input needed index valueRef}
      (different : index ≠ query) :
      RegQueryEvidence wires table registers query width
        (.writeSlice writeWidth name lo fieldWidth inBounds value)
        input needed (.writeSlice index valueRef) input
  | sliceDead {writeWidth name lo fieldWidth inBounds value input needed valueRef}
      (dead : needed.testBit query = false) :
      RegQueryEvidence wires table registers query width
        (.writeSlice writeWidth name lo fieldWidth inBounds value)
        input needed (.writeSlice query valueRef) input
  | sliceLive {writeWidth name lo fieldWidth inBounds value input needed valueRef}
      (live : needed.testBit query = true)
      (valueAccepted : indexedInsertMatches wires table writeWidth lo fieldWidth
        value input valueRef = true) :
      RegQueryEvidence wires table registers query width
        (.writeSlice writeWidth name lo fieldWidth inBounds value)
        input needed (.writeSlice query valueRef) valueRef
  | seq {left right input needed summary leftCert rightCert middle output}
      (leftAccepted : RegQueryEvidence wires table registers query width left input
        (neededBitsBefore rightCert.summary needed) leftCert middle)
      (rightAccepted : RegQueryEvidence wires table registers query width right middle
        needed rightCert output) :
      RegQueryEvidence wires table registers query width (.seq left right) input needed
        (.seq summary leftCert rightCert) output
  | iteUnchanged {condition thenAction elseAction input needed summary conditionRef
      joins thenCert elseCert}
      (unchanged : (changedBitsAt summary needed).testBit query = false) :
      RegQueryEvidence wires table registers query width
        (.ite condition thenAction elseAction) input needed
        (.ite summary conditionRef joins thenCert elseCert) input
  | iteChanged {condition thenAction elseAction input needed summary conditionRef
      joins thenCert elseCert thenRef elseRef output}
      (changed : (changedBitsAt summary needed).testBit query = true)
      (conditionAccepted : indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr condition) conditionRef = true)
      (thenAccepted : RegQueryEvidence wires table registers query width thenAction input
        (changedBitsAt summary needed) thenCert thenRef)
      (elseAccepted : RegQueryEvidence wires table registers query width elseAction input
        (changedBitsAt summary needed) elseCert elseRef)
      (joinAccepted : JoinAtEvidence wires table conditionRef query width thenRef elseRef
        joins output) :
      RegQueryEvidence wires table registers query width
        (.ite condition thenAction elseAction) input needed
        (.ite summary conditionRef joins thenCert elseCert) output

/-- Exact concrete join predicate used by the compact register checker. -/
def queryJoinMatches (condition : Ref) (query width : Nat) (thenRef elseRef : Ref)
    (join : Join) : Bool :=
  join.index == query && join.width == width && join.guard == condition &&
    join.thenInput == thenRef && join.elseInput == elseRef

/-- State-free reference interpreter for one register. This is deliberately a
small structurally recursive checker: artifact certificates state only that it
returns the claimed reference. `ActionShapeEvidence` supplies all expensive
expression and wire-lookup facts once, outside this computation. -/
def queryRef (query width : Nat) :
    Act → Ref → Nat → ActionCert → Option Ref
  | .skip, input, _, .skip => some input
  | .memWrite _ _ _ _ _ _, input, _, .memWrite => some input
  | .write _ _ _, input, needed, .write index valueRef =>
      if index == query && needed.testBit query then some valueRef else some input
  | .writeSlice _ _ _ _ _ _, input, needed, .writeSlice index valueRef =>
      if index == query && needed.testBit query then some valueRef else some input
  | .seq left right, input, needed, .seq _ leftCert rightCert => do
      let middle ← queryRef query width left input
        (neededBitsBefore rightCert.summary needed) leftCert
      queryRef query width right middle needed rightCert
  | .ite _ thenAction elseAction, input, needed,
      .ite summary conditionRef joins thenCert elseCert =>
      if (changedBitsAt summary needed).testBit query then do
        let thenRef ← queryRef query width thenAction input
          (changedBitsAt summary needed) thenCert
        let elseRef ← queryRef query width elseAction input
          (changedBitsAt summary needed) elseCert
        let join ← joins.find? (queryJoinMatches conditionRef query width thenRef elseRef)
        some join.output
      else some input
  | _, _, _, _ => none

/-- Reassociate an ordered rule list into one action.  This is a proof-facing
view only: `nextReg` on the result is exactly the source compiler's ordered
rule fold, while a single action certificate can share cached subactions. -/
def rulesAction : List Rule → Act
  | [] => .skip
  | rule :: rules => .seq rule.body (rulesAction rules)

/-- Reassociate one certificate per ordered rule in the same shape as
`rulesAction`.  The summary at every new sequence node is derived from its
children, so the original backwards liveness sets remain definitionally
visible to the compact checker. -/
def rulesActionCert : RulesCert → ActionCert
  | [] => .skip
  | cert :: certs =>
      let tail := rulesActionCert certs
      .seq (seqSummary cert.summary tail.summary) cert tail

/-- The proof-facing reassociation does not change register compilation. -/
theorem nextReg_rulesAction (name : String) (width : Nat) (rules : List Rule)
    (current : Loom.Emit.MicroVerilog.Expr width) :
    Loom.Hw.Compile.nextReg name width (rulesAction rules) current =
      rules.foldl
        (fun value rule => Loom.Hw.Compile.nextReg name width rule.body value)
        current := by
  induction rules generalizing current with
  | nil => rfl
  | cons rule rules ih =>
      simp only [rulesAction, Loom.Hw.Compile.nextReg, List.foldl_cons]
      exact ih _

/-- Apply the mux joins of one conditional to a concrete reference array,
checking that each join consumes exactly the references computed by its two
branches. -/
def applyQueryJoins (registers : Array RegDecl) (condition : Ref) :
    Nat → List Join → Array Ref → Array Ref → Array Ref → Option (Array Ref)
  | changed, [], _, _, output => if changed == 0 then some output else none
  | changed, join :: joins, thenRefs, elseRefs, output =>
      if changed.testBit join.index &&
          (registers[join.index]?.map (·.width) == some join.width) &&
          join.guard == condition && thenRefs[join.index]? == some join.thenInput &&
          elseRefs[join.index]? == some join.elseInput then
        applyQueryJoins registers condition (changed ^^^ (1 <<< join.index)) joins
          thenRefs elseRefs (output.setIfInBounds join.index join.output)
      else none

/-- Bounded join evaluator used by generated chunk certificates. Unlike
`applyQueryJoins`, reaching the end returns the remaining bitmap and state so
independently checked chunks can be composed without re-evaluating suffixes. -/
def applyQueryJoinChunk (registers : Array RegDecl) (condition : Ref) :
    Nat → List Join → Array Ref → Array Ref → Array Ref →
      Option (Nat × Array Ref)
  | changed, [], _, _, output => some (changed, output)
  | changed, join :: joins, thenRefs, elseRefs, output =>
      if changed.testBit join.index &&
          (registers[join.index]?.map (·.width) == some join.width) &&
          join.guard == condition && thenRefs[join.index]? == some join.thenInput &&
          elseRefs[join.index]? == some join.elseInput then
        applyQueryJoinChunk registers condition (changed ^^^ (1 <<< join.index))
          joins thenRefs elseRefs (output.setIfInBounds join.index join.output)
      else none

/-- Evaluate all demanded register references in one pass over an action.
Unlike per-register `queryRef`, this shares control-flow traversal across the
entire state vector and is the preferred full-artifact checker. -/
def queryState (registers : Array RegDecl) :
    Act → Array Ref → Nat → ActionCert → Option (Array Ref)
  | .skip, input, _, .skip => some input
  | .memWrite _ _ _ _ _ _, input, _, .memWrite => some input
  | .write _ _ _, input, needed, .write index valueRef =>
      some (if needed.testBit index then input.setIfInBounds index valueRef else input)
  | .writeSlice _ _ _ _ _ _, input, needed, .writeSlice index valueRef =>
      some (if needed.testBit index then input.setIfInBounds index valueRef else input)
  | .seq left right, input, needed, .seq _ leftCert rightCert => do
      let middle ← queryState registers left input
        (neededBitsBefore rightCert.summary needed) leftCert
      queryState registers right middle needed rightCert
  | .ite _ thenAction elseAction, input, needed,
      .ite summary conditionRef joins thenCert elseCert =>
      let changed := changedBitsAt summary needed
      if changed == 0 then some input else do
        let thenRefs ← queryState registers thenAction input changed thenCert
        let elseRefs ← queryState registers elseAction input changed elseCert
        applyQueryJoins registers conditionRef changed joins thenRefs elseRefs input
  | _, _, _, _ => none

/-- Kernel-checked composition of independently reduced join chunks. -/
inductive QueryJoinChunksEvidence (registers : Array RegDecl) (condition : Ref)
    (thenRefs elseRefs : Array Ref) :
    Nat → Array Ref → List (List Join) → Nat → Array Ref → Prop where
  | nil {changed output} :
      QueryJoinChunksEvidence registers condition thenRefs elseRefs changed output
        [] changed output
  | cons {changed input chunk chunks middleChanged middle finalChanged output}
      (head : applyQueryJoinChunk registers condition changed chunk thenRefs
        elseRefs input = some (middleChanged, middle))
      (tail : QueryJoinChunksEvidence registers condition thenRefs elseRefs
        middleChanged middle chunks finalChanged output) :
      QueryJoinChunksEvidence registers condition thenRefs elseRefs changed input
        (chunk :: chunks) finalChanged output

/-- Compositional full-state certificate. Leaves use bounded kernel reduction;
sequence and conditional nodes refer only to already checked child statements. -/
inductive StateQueryEvidence (registers : Array RegDecl) :
    Act → Array Ref → Nat → ActionCert → Array Ref → Prop where
  | checked {action input needed cert output}
      (accepted : queryState registers action input needed cert = some output) :
      StateQueryEvidence registers action input needed cert output
  | seq {left right input needed summary leftCert rightCert middle output}
      (summaryAccepted : summary = seqSummary leftCert.summary rightCert.summary)
      (leftAccepted : StateQueryEvidence registers left input
        (neededBitsBefore rightCert.summary needed) leftCert middle)
      (rightAccepted : StateQueryEvidence registers right middle needed rightCert output) :
      StateQueryEvidence registers (.seq left right) input needed
        (.seq summary leftCert rightCert) output
  | iteUnchanged {condition thenAction elseAction input needed summary conditionRef
      joins thenCert elseCert}
      (summaryAccepted : summary = iteSummary thenCert.summary elseCert.summary)
      (unchanged : changedBitsAt summary needed = 0) :
      StateQueryEvidence registers (.ite condition thenAction elseAction) input
        needed (.ite summary conditionRef joins thenCert elseCert) input
  | iteChanged {condition thenAction elseAction input needed summary conditionRef
      joins thenCert elseCert thenRefs elseRefs chunks output}
      (summaryAccepted : summary = iteSummary thenCert.summary elseCert.summary)
      (changed : changedBitsAt summary needed ≠ 0)
      (thenAccepted : StateQueryEvidence registers thenAction input
        (changedBitsAt summary needed) thenCert thenRefs)
      (elseAccepted : StateQueryEvidence registers elseAction input
        (changedBitsAt summary needed) elseCert elseRefs)
      (chunksAccepted : chunks.flatten = joins)
      (joinsAccepted : QueryJoinChunksEvidence registers conditionRef thenRefs
        elseRefs (changedBitsAt summary needed) input chunks 0 output) :
      StateQueryEvidence registers (.ite condition thenAction elseAction) input
        needed (.ite summary conditionRef joins thenCert elseCert) output

/-- A bounded join-chunk result composes with the unchecked suffix without
re-evaluating the chunk. -/
theorem applyQueryJoinChunk_append
    {registers : Array RegDecl} {condition : Ref} {changed : Nat}
    {chunk rest : List Join} {thenRefs elseRefs input : Array Ref}
    {middleChanged : Nat} {middle output : Array Ref}
    (head : applyQueryJoinChunk registers condition changed chunk thenRefs
      elseRefs input = some (middleChanged, middle))
    (tail : applyQueryJoins registers condition middleChanged rest thenRefs
      elseRefs middle = some output) :
    applyQueryJoins registers condition changed (chunk ++ rest) thenRefs
      elseRefs input = some output := by
  induction chunk generalizing changed input middleChanged middle with
  | nil =>
      simp [applyQueryJoinChunk] at head
      rcases head with ⟨rfl, rfl⟩
      exact tail
  | cons join joins ih =>
      simp only [applyQueryJoinChunk] at head
      split at head
      · rename_i accepted
        simp only [List.cons_append, applyQueryJoins]
        rw [if_pos accepted]
        exact ih head tail
      · contradiction

/-- Independently checked join chunks imply the result of the reference join
evaluator over their flattened list. -/
theorem QueryJoinChunksEvidence.applyQueryJoins
    {registers : Array RegDecl} {condition : Ref} {thenRefs elseRefs : Array Ref}
    {changed : Nat} {input : Array Ref} {chunks : List (List Join)}
    {finalChanged : Nat} {output : Array Ref}
    (evidence : QueryJoinChunksEvidence registers condition thenRefs elseRefs
      changed input chunks finalChanged output)
    (finished : finalChanged = 0) :
    applyQueryJoins registers condition changed chunks.flatten thenRefs elseRefs
      input = some output := by
  induction evidence with
  | nil =>
      rw [finished]
      rfl
  | cons head tail ih =>
      simp only [List.flatten_cons]
      exact applyQueryJoinChunk_append head (ih finished)

/-- The compositional certificate denotes exactly the result of the full-state
reference evaluator. Generated leaves and join chunks are reduced once; this
generic proof only composes their statements. -/
theorem StateQueryEvidence.to_queryState
    {registers : Array RegDecl} {action : Act} {input : Array Ref}
    {needed : Nat} {cert : ActionCert} {output : Array Ref}
    (evidence : StateQueryEvidence registers action input needed cert output) :
    queryState registers action input needed cert = some output := by
  induction evidence with
  | checked accepted => exact accepted
  | seq summaryAccepted leftAccepted rightAccepted leftIH rightIH =>
      simp [queryState, leftIH, rightIH]
  | iteUnchanged summaryAccepted unchanged =>
      simp [queryState, unchanged]
  | @iteChanged condition thenAction elseAction input needed summary conditionRef
      joins thenCert elseCert thenRefs elseRefs chunks output summaryAccepted
      changed thenAccepted elseAccepted chunksAccepted joinsAccepted thenIH elseIH =>
      have joinResult : applyQueryJoins registers conditionRef
          (changedBitsAt summary needed) joins thenRefs elseRefs input =
          some output := by
        rw [← chunksAccepted]
        exact joinsAccepted.applyQueryJoins rfl
      simp [queryState, changed, thenIH, elseIH, joinResult]

theorem JoinOutputsEvidence.find_query
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {condition : Ref} {query width : Nat} {thenRef elseRef : Ref}
    {joins : List Join} {join : Join}
    (evidence : JoinOutputsEvidence wires table joins)
    (found : joins.find? (queryJoinMatches condition query width thenRef elseRef) =
      some join) :
    JoinAtEvidence wires table condition query width thenRef elseRef joins
      join.output := by
  induction evidence with
  | nil => simp at found
  | @cons head joins headAccepted tailAccepted ih =>
      simp only [List.find?] at found
      split at found <;> rename_i matchEq
      ·
        have joinEq : head = join := Option.some.inj found
        subst join
        simp only [queryJoinMatches, Bool.and_eq_true, beq_iff_eq] at matchEq
        rcases matchEq with ⟨⟨⟨⟨indexEq, widthEq⟩, guardEq⟩, thenEq⟩, elseEq⟩
        exact .here indexEq widthEq guardEq thenEq elseEq headAccepted
      ·
        exact .there (ih found)

theorem JoinAtEvidence.raw_mux
    (program : Program) {wires : Rope (List IndexedWire)}
    (wiresMatch : IndexedRopeMatches 0 program.wires wires)
    (wireTable : WireTable) {condition : Ref} {query width : Nat}
    {thenRef elseRef output : Ref} {joins : List Join}
    (evidence : JoinAtEvidence wires wireTable condition query width thenRef
      elseRef joins output)
    {guardExpr : Loom.Emit.MicroVerilog.Expr 1}
    {thenExpr elseExpr : Loom.Emit.MicroVerilog.Expr width}
    (guardMatches : RawExprMatches program wireTable guardExpr condition)
    (thenMatches : RawExprMatches program wireTable thenExpr thenRef)
    (elseMatches : RawExprMatches program wireTable elseExpr elseRef) :
    RawExprMatches program wireTable (.mux guardExpr thenExpr elseExpr) output := by
  induction evidence with
  | @here join joins indexAccepted widthAccepted guardAccepted thenAccepted
      elseAccepted outputAccepted =>
      subst query
      subst width
      subst condition
      subst thenRef
      subst elseRef
      cases outputAccepted with
      | @wire number outputEq lookupAccepted =>
          rw [outputEq]
          obtain ⟨raw, rawAt, rawMatch⟩ :=
            lookupIndexed_rawWireAt program wiresMatch wireTable number _
              lookupAccepted
          obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs rawMatch
          exact .mux rawAt widthEq rhsEq guardMatches thenMatches elseMatches
  | there tail ih => exact ih

/-- A checked write header identifies the source register represented by its
certificate index. -/
private theorem checkedWriteHeader_summary_valid
    {registers : Array RegDecl} {width index query : Nat} {name : String}
    {value : Expr width} {valueRef : Ref}
    (header : checkedWriteHeader registers index width name = true)
    (unique : RegisterNamesUnique registers) (source : RegDecl)
    (sourceFound : registers[query]? = some source) :
    (ActionCert.write index valueRef).summary.possible.testBit query =
        Loom.Hw.Compile.writesRegB source.name source.width
          (.write width name value) ∧
      (ActionCert.write index valueRef).summary.definite.testBit query =
        (ActionCert.write index valueRef).definitelyWritesIndex query := by
  cases actualFound : registers[index]? with
  | none => simp [checkedWriteHeader, actualFound] at header
  | some actual =>
      simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
        beq_iff_eq] at header
      by_cases indexEq : index = query
      · subst query
        have regEq : actual = source :=
          Option.some.inj (actualFound.symm.trans sourceFound)
        subst source
        simp [ActionCert.summary, ActionCert.definitelyWritesIndex,
          singletonIndex_testBit, Loom.Hw.Compile.writesRegB, header]
      · have nameNe : name ≠ source.name := by
          intro nameEq
          apply indexEq
          exact unique actualFound sourceFound (header.1.trans nameEq)
        have indexFalse : (index == query) = false :=
          beq_eq_false_iff_ne.mpr indexEq
        have nameFalse : (name == source.name) = false :=
          beq_eq_false_iff_ne.mpr nameNe
        simp [ActionCert.summary, ActionCert.definitelyWritesIndex,
          singletonIndex_testBit, Loom.Hw.Compile.writesRegB, indexFalse,
          nameFalse]

private theorem checkedWriteHeader_slice_summary_valid
    {registers : Array RegDecl} {width index query lo fieldWidth : Nat}
    {name : String} {inBounds : lo + fieldWidth ≤ width}
    {value : Expr fieldWidth} {valueRef : Ref}
    (header : checkedWriteHeader registers index width name = true)
    (unique : RegisterNamesUnique registers) (source : RegDecl)
    (sourceFound : registers[query]? = some source) :
    (ActionCert.writeSlice index valueRef).summary.possible.testBit query =
        Loom.Hw.Compile.writesRegB source.name source.width
          (.writeSlice width name lo fieldWidth inBounds value) ∧
      (ActionCert.writeSlice index valueRef).summary.definite.testBit query =
        (ActionCert.writeSlice index valueRef).definitelyWritesIndex query := by
  cases actualFound : registers[index]? with
  | none => simp [checkedWriteHeader, actualFound] at header
  | some actual =>
      simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
        beq_iff_eq] at header
      by_cases indexEq : index = query
      · subst query
        have regEq : actual = source :=
          Option.some.inj (actualFound.symm.trans sourceFound)
        subst source
        simp [ActionCert.summary, ActionCert.definitelyWritesIndex,
          singletonIndex_testBit, Loom.Hw.Compile.writesRegB, header]
      · have nameNe : name ≠ source.name := by
          intro nameEq
          apply indexEq
          exact unique actualFound sourceFound (header.1.trans nameEq)
        have indexFalse : (index == query) = false :=
          beq_eq_false_iff_ne.mpr indexEq
        have nameFalse : (name == source.name) = false :=
          beq_eq_false_iff_ne.mpr nameNe
        simp [ActionCert.summary, ActionCert.definitelyWritesIndex,
          singletonIndex_testBit, Loom.Hw.Compile.writesRegB, indexFalse,
          nameFalse]

/-- A shape certificate determines the same structural possible/definite
write bits as its source action. -/
theorem ActionShapeEvidence.summary_valid
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {registers : Array RegDecl} {action : Act} {needed : Nat} {cert : ActionCert}
    (evidence : ActionShapeEvidence wires table registers action needed cert)
    (unique : RegisterNamesUnique registers) (query : Nat) (source : RegDecl)
    (sourceFound : registers[query]? = some source) :
    cert.summary.possible.testBit query =
        Loom.Hw.Compile.writesRegB source.name source.width action ∧
      cert.summary.definite.testBit query =
        cert.definitelyWritesIndex query := by
  induction evidence with
  | skip | memWrite =>
      simp [ActionCert.summary, ActionCert.definitelyWritesIndex,
        Loom.Hw.Compile.writesRegB]
  | writeDead header dead =>
      exact checkedWriteHeader_summary_valid header unique source sourceFound
  | writeLive header live =>
      exact checkedWriteHeader_summary_valid header unique source sourceFound
  | sliceDead header dead =>
      exact checkedWriteHeader_slice_summary_valid header unique source sourceFound
  | sliceLive header live =>
      exact checkedWriteHeader_slice_summary_valid header unique source sourceFound
  | @seq left right needed summary leftCert rightCert summaryAccepted leftAccepted
      rightAccepted leftIH rightIH =>
      subst summaryAccepted
      constructor
      · change (seqSummary _ _).possible.testBit query = _
        simp only [seqSummary, Nat.testBit_or,
          Loom.Hw.Compile.writesRegB]
        rw [leftIH.1, rightIH.1]
      · change (seqSummary _ _).definite.testBit query = _
        simp only [seqSummary, Nat.testBit_or,
          ActionCert.definitelyWritesIndex]
        rw [leftIH.2, rightIH.2]
  | @ite condition thenAction elseAction needed summary conditionRef joins thenCert
      elseCert summaryAccepted thenAccepted elseAccepted
      thenIH elseIH =>
      subst summaryAccepted
      constructor
      · change (iteSummary _ _).possible.testBit query = _
        simp only [iteSummary, Nat.testBit_or,
          Loom.Hw.Compile.writesRegB]
        rw [thenIH.1, elseIH.1]
      · change (iteSummary _ _).definite.testBit query = _
        simp only [iteSummary, Nat.testBit_and,
          ActionCert.definitelyWritesIndex]
        rw [thenIH.2, elseIH.2]

theorem ActionShapeEvidence.summary_definite_false_of_possible_false
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {registers : Array RegDecl} {action : Act} {needed : Nat} {cert : ActionCert}
    (evidence : ActionShapeEvidence wires table registers action needed cert)
    {query : Nat} (possibleFalse : cert.summary.possible.testBit query = false) :
    cert.summary.definite.testBit query = false := by
  induction evidence with
  | skip | memWrite => simp [ActionCert.summary]
  | writeDead | writeLive =>
      simpa [ActionCert.summary] using possibleFalse
  | sliceDead | sliceLive => simp [ActionCert.summary]
  | @seq left right needed summary leftCert rightCert summaryAccepted leftAccepted
      rightAccepted leftIH rightIH =>
      subst summary
      change (seqSummary leftCert.summary rightCert.summary).possible.testBit query =
        false at possibleFalse
      change (seqSummary leftCert.summary rightCert.summary).definite.testBit query =
        false
      simp only [seqSummary, Nat.testBit_or, Bool.or_eq_false_iff] at possibleFalse ⊢
      exact ⟨leftIH possibleFalse.1, rightIH possibleFalse.2⟩
  | @ite condition thenAction elseAction needed summary conditionRef joins thenCert
      elseCert summaryAccepted thenAccepted elseAccepted
      thenIH elseIH =>
      subst summary
      change (iteSummary thenCert.summary elseCert.summary).possible.testBit query =
        false at possibleFalse
      change (iteSummary thenCert.summary elseCert.summary).definite.testBit query =
        false
      simp only [iteSummary, Nat.testBit_or, Bool.or_eq_false_iff] at possibleFalse
      simp only [iteSummary, Nat.testBit_and, Bool.and_eq_false_iff]
      exact Or.inl (thenIH possibleFalse.1)

/-- Query-local evidence implies the semantic next-register expression. The
large action-shape theorem is passed as an opaque constant at artifact sites;
this generic induction is checked only once. -/
theorem RegQueryEvidence.nextReg_raw
    (program : Program) {wires : Rope (List IndexedWire)}
    (wiresMatch : IndexedRopeMatches 0 program.wires wires)
    (wireTable : WireTable) {registers : Array RegDecl}
    {query width : Nat} {action : Act} {input : Ref} {needed : Nat}
    {cert : ActionCert} {output : Ref}
    (evidence : RegQueryEvidence wires wireTable registers query width action
      input needed cert output)
    (shape : ActionShapeEvidence wires wireTable registers action needed cert)
    (unique : RegisterNamesUnique registers)
    (source : RegDecl) (sourceFound : registers[query]? = some source)
    (sourceWidth : source.width = width)
    (used : needed.testBit query = true) :
    ∀ current : Loom.Emit.MicroVerilog.Expr source.width,
      RawCurrentMatches program wireTable current
        (cert.semanticCurrentRef query input) →
      RawExprMatches program wireTable
        (Loom.Hw.Compile.nextReg source.name source.width action current)
        output := by
  subst width
  intro current currentMatches
  induction evidence generalizing current with
  | skip =>
      cases shape
      simpa [ActionCert.semanticCurrentRef, ActionCert.summary,
        Loom.Hw.Compile.nextReg] using currentMatches
  | memWrite =>
      cases shape
      simpa [ActionCert.semanticCurrentRef, ActionCert.summary,
        Loom.Hw.Compile.nextReg] using currentMatches
  | @writeOther writeWidth name value input needed index valueRef different =>
      have finish (header : checkedWriteHeader registers index writeWidth name = true) :
          RawExprMatches program wireTable
            (Loom.Hw.Compile.nextReg source.name source.width
              (.write writeWidth name value) current) input := by
        cases actualFound : registers[index]? with
        | none => simp [checkedWriteHeader, actualFound] at header
        | some actual =>
          simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
            beq_iff_eq] at header
          have nameNe : name ≠ source.name := by
            intro nameEq
            apply different
            exact unique actualFound sourceFound (header.1.trans nameEq)
          have definiteFalse :
              (ActionCert.write index valueRef).summary.definite.testBit query =
                false := by
            rw [ActionCert.summary]
            exact (singletonIndex_testBit index query).trans
              (beq_eq_false_iff_ne.mpr different)
          simpa [ActionCert.semanticCurrentRef, definiteFalse,
            Loom.Hw.Compile.nextReg, nameNe] using currentMatches
      cases shape with
      | writeDead header dead => exact finish header
      | writeLive header live => exact finish header
  | writeDead dead =>
      rw [used] at dead
      contradiction
  | @writeLive writeWidth name value input needed valueRef live valueAccepted =>
      cases shape with
      | writeDead header dead =>
        rw [live] at dead
        contradiction
      | writeLive header shapeLive =>
        cases actualFound : registers[query]? with
        | none => simp [checkedWriteHeader, actualFound] at header
        | some actual =>
          have actualEq : actual = source :=
            Option.some.inj (actualFound.symm.trans sourceFound)
          subst actual
          simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
            beq_iff_eq] at header
          rcases header with ⟨rfl, rfl⟩
          simpa [Loom.Hw.Compile.nextReg] using
            indexedExprMatches_raw program wiresMatch wireTable _ _ valueAccepted
  | @sliceOther writeWidth name lo fieldWidth inBounds value input needed index
      valueRef different =>
      have finish (header : checkedWriteHeader registers index writeWidth name = true) :
          RawExprMatches program wireTable
            (Loom.Hw.Compile.nextReg source.name source.width
              (.writeSlice writeWidth name lo fieldWidth inBounds value) current)
            input := by
        cases actualFound : registers[index]? with
        | none => simp [checkedWriteHeader, actualFound] at header
        | some actual =>
          simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
            beq_iff_eq] at header
          have nameNe : name ≠ source.name := by
            intro nameEq
            apply different
            exact unique actualFound sourceFound (header.1.trans nameEq)
          simpa [ActionCert.semanticCurrentRef, ActionCert.summary,
            Loom.Hw.Compile.nextReg, nameNe] using currentMatches
      cases shape with
      | sliceDead header dead => exact finish header
      | sliceLive header live => exact finish header
  | sliceDead dead =>
      rw [used] at dead
      contradiction
  | @sliceLive writeWidth name lo fieldWidth inBounds value input needed valueRef
      live valueAccepted =>
      cases shape with
      | sliceDead header dead =>
        rw [live] at dead
        contradiction
      | sliceLive header shapeLive =>
        cases actualFound : registers[query]? with
        | none => simp [checkedWriteHeader, actualFound] at header
        | some actual =>
          have actualEq : actual = source :=
            Option.some.inj (actualFound.symm.trans sourceFound)
          subst actual
          simp only [checkedWriteHeader, actualFound, Bool.and_eq_true,
            beq_iff_eq] at header
          rcases header with ⟨rfl, rfl⟩
          have currentRaw : RawExprMatches program wireTable current input := by
            simpa [ActionCert.semanticCurrentRef, ActionCert.summary] using
              currentMatches
          simpa [Loom.Hw.Compile.nextReg] using
            indexedInsertMatches_raw program wiresMatch wireTable lo value current
              input valueRef currentRaw valueAccepted
  | @seq left right input needed summary leftCert rightCert middle output
      leftAccepted rightAccepted leftIH rightIH =>
      cases shape with
      | seq summaryAccepted leftShape rightShape =>
        subst summary
        cases rightDef : rightCert.summary.definite.testBit query with
        | false =>
          have leftUsed :
              (neededBitsBefore rightCert.summary needed).testBit query = true := by
            simp [neededBitsBefore, Nat.testBit_xor, Nat.testBit_and, used,
              rightDef]
          have leftCurrent : RawCurrentMatches program wireTable current
              (leftCert.semanticCurrentRef query input) := by
            cases leftDef : leftCert.summary.definite.testBit query with
            | false =>
              have wholeDefFalse :
                  (ActionCert.seq (seqSummary leftCert.summary rightCert.summary)
                    leftCert rightCert).summary.definite.testBit query = false := by
                change (seqSummary leftCert.summary rightCert.summary).definite.testBit
                  query = false
                simp [seqSummary, leftDef, rightDef]
              rw [ActionCert.semanticCurrentRef_eq_some wholeDefFalse] at currentMatches
              rw [ActionCert.semanticCurrentRef_eq_some leftDef]
              exact currentMatches
            | true =>
              rw [ActionCert.semanticCurrentRef_eq_none leftDef]
              trivial
          have middleMatches := leftIH leftShape leftUsed current leftCurrent
          have rightCurrent : RawCurrentMatches program wireTable
              (Loom.Hw.Compile.nextReg source.name source.width left current)
              (rightCert.semanticCurrentRef query middle) := by
            simpa [ActionCert.semanticCurrentRef, rightDef] using middleMatches
          exact rightIH rightShape used _ rightCurrent
        | true =>
          have rightCurrent : RawCurrentMatches program wireTable
              (Loom.Hw.Compile.nextReg source.name source.width left current)
              (rightCert.semanticCurrentRef query middle) := by
            rw [ActionCert.semanticCurrentRef_eq_none rightDef]
            trivial
          exact rightIH rightShape used _ rightCurrent
  | @iteUnchanged condition thenAction elseAction input needed summary conditionRef
      joins thenCert elseCert unchanged =>
      cases shape with
      | ite summaryAccepted thenShape elseShape =>
        subst summary
        let wholeShape : ActionShapeEvidence wires wireTable registers
            (.ite condition thenAction elseAction) needed
            (.ite (iteSummary thenCert.summary elseCert.summary) conditionRef joins
              thenCert elseCert) :=
          .ite rfl thenShape elseShape
        have possibleFalse :
            (iteSummary thenCert.summary elseCert.summary).possible.testBit query =
              false := by
          simpa [changedBitsAt, Nat.testBit_and, used] using unchanged
        have noWrite := (wholeShape.summary_valid unique query source sourceFound).1.symm.trans
          possibleFalse
        have branchNoWrite :
            (Loom.Hw.Compile.writesRegB source.name source.width thenAction ||
              Loom.Hw.Compile.writesRegB source.name source.width elseAction) =
              false := by
          simpa [Loom.Hw.Compile.writesRegB] using noWrite
        have definiteFalse :
            (iteSummary thenCert.summary elseCert.summary).definite.testBit query =
              false :=
          wholeShape.summary_definite_false_of_possible_false possibleFalse
        have currentRaw : RawExprMatches program wireTable current input := by
          rw [ActionCert.semanticCurrentRef_eq_some
            (cert := .ite (iteSummary thenCert.summary elseCert.summary)
              conditionRef joins thenCert elseCert)
            (query := query) (input := input) definiteFalse] at currentMatches
          exact currentMatches
        simpa [Loom.Hw.Compile.nextReg, branchNoWrite] using currentRaw
  | @iteChanged condition thenAction elseAction input needed summary conditionRef
      joins thenCert elseCert thenRef elseRef output changed conditionAccepted thenAccepted
      elseAccepted joinAccepted thenIH elseIH =>
      cases shape with
      | ite summaryAccepted thenShape elseShape =>
        subst summary
        let wholeCert : ActionCert := .ite
          (iteSummary thenCert.summary elseCert.summary) conditionRef joins
          thenCert elseCert
        have possibleTrue : wholeCert.summary.possible.testBit query = true := by
          simpa [wholeCert, changedBitsAt, Nat.testBit_and, used] using changed
        have thenCurrent : RawCurrentMatches program wireTable current
            (thenCert.semanticCurrentRef query input) := by
          cases thenDef : thenCert.summary.definite.testBit query with
          | true => rw [ActionCert.semanticCurrentRef_eq_none thenDef]; trivial
          | false =>
            have wholeDefFalse : wholeCert.summary.definite.testBit query = false := by
              change (iteSummary thenCert.summary elseCert.summary).definite.testBit
                query = false
              simp [iteSummary, thenDef]
            rw [ActionCert.semanticCurrentRef_eq_some wholeDefFalse] at currentMatches
            rw [ActionCert.semanticCurrentRef_eq_some thenDef]
            exact currentMatches
        have elseCurrent : RawCurrentMatches program wireTable current
            (elseCert.semanticCurrentRef query input) := by
          cases elseDef : elseCert.summary.definite.testBit query with
          | true => rw [ActionCert.semanticCurrentRef_eq_none elseDef]; trivial
          | false =>
            have wholeDefFalse : wholeCert.summary.definite.testBit query = false := by
              change (iteSummary thenCert.summary elseCert.summary).definite.testBit
                query = false
              simp [iteSummary, elseDef]
            rw [ActionCert.semanticCurrentRef_eq_some wholeDefFalse] at currentMatches
            rw [ActionCert.semanticCurrentRef_eq_some elseDef]
            exact currentMatches
        have thenMatches := thenIH thenShape changed current thenCurrent
        have elseMatches := elseIH elseShape changed current elseCurrent
        have guardMatches := indexedExprMatches_raw program wiresMatch wireTable _ _
          conditionAccepted
        have muxMatches := joinAccepted.raw_mux program wiresMatch wireTable
          guardMatches thenMatches elseMatches
        let wholeShape : ActionShapeEvidence wires wireTable registers
            (.ite condition thenAction elseAction) needed wholeCert :=
          .ite rfl thenShape elseShape
        have writeTrue :=
          (wholeShape.summary_valid unique query source sourceFound).1.symm.trans
            possibleTrue
        have branchWriteTrue :
            (Loom.Hw.Compile.writesRegB source.name source.width thenAction ||
              Loom.Hw.Compile.writesRegB source.name source.width elseAction) =
              true := by
          simpa [Loom.Hw.Compile.writesRegB] using writeTrue
        simpa [Loom.Hw.Compile.nextReg, branchWriteTrue] using muxMatches

/-- Chaining form of `nextReg_raw`.  A caller that knows the incoming raw
expression matches the incoming reference need not inspect the certificate's
definite-write bit: a definite write discards that premise, while every other
action consumes it directly. -/
theorem RegQueryEvidence.nextReg_raw_of_input
    (program : Program) {wires : Rope (List IndexedWire)}
    (wiresMatch : IndexedRopeMatches 0 program.wires wires)
    (wireTable : WireTable) {registers : Array RegDecl}
    {query width : Nat} {action : Act} {input : Ref} {needed : Nat}
    {cert : ActionCert} {output : Ref}
    (evidence : RegQueryEvidence wires wireTable registers query width action
      input needed cert output)
    (shape : ActionShapeEvidence wires wireTable registers action needed cert)
    (unique : RegisterNamesUnique registers)
    (source : RegDecl) (sourceFound : registers[query]? = some source)
    (sourceWidth : source.width = width)
    (used : needed.testBit query = true)
    (current : Loom.Emit.MicroVerilog.Expr source.width)
    (currentMatches : RawExprMatches program wireTable current input) :
    RawExprMatches program wireTable
      (Loom.Hw.Compile.nextReg source.name source.width action current) output := by
  apply evidence.nextReg_raw program wiresMatch wireTable shape unique source
    sourceFound sourceWidth used current
  cases definite : cert.summary.definite.testBit query <;>
    simp [ActionCert.semanticCurrentRef, definite, RawCurrentMatches,
      currentMatches]

/-- Publication-facing compact-checker rule: a shared lightweight action-shape
theorem and a query-local certificate together establish one semantic register
projection. -/
theorem ActionShapeEvidence.queryEvidence_nextReg_raw
    (program : Program) {wires : Rope (List IndexedWire)}
    (wiresMatch : IndexedRopeMatches 0 program.wires wires)
    (wireTable : WireTable) {registers : Array RegDecl}
    {query width : Nat} {action : Act} {input : Ref} {needed : Nat}
    {cert : ActionCert} {output : Ref}
    (shape : ActionShapeEvidence wires wireTable registers action needed cert)
    (evidence : RegQueryEvidence wires wireTable registers query width action
      input needed cert output)
    (unique : RegisterNamesUnique registers)
    (source : RegDecl) (sourceFound : registers[query]? = some source)
    (sourceWidth : source.width = width)
    (used : needed.testBit query = true)
    (current : Loom.Emit.MicroVerilog.Expr source.width)
    (currentMatches : RawCurrentMatches program wireTable current
      (cert.semanticCurrentRef query input)) :
    RawExprMatches program wireTable
      (Loom.Hw.Compile.nextReg source.name source.width action current) output :=
  evidence.nextReg_raw program wiresMatch wireTable shape
    unique source sourceFound sourceWidth used current currentMatches

/-- End-to-end register rule for the hybrid release checker.  The generated
artifact supplies only a structural shape constant, one query-local evidence
constant, and bounded metadata equalities; this generic theorem removes all
certificate data from the resulting `RegisterBehaviorAt` proposition. -/
theorem RegQueryEvidence.registerBehaviorAt
    (design : Loom.Hw.Design) (program : Program)
    {wires : Rope (List IndexedWire)}
    (wiresMatch : IndexedRopeMatches 0 program.wires wires)
    (wireTable : WireTable) {registers : Array RegDecl}
    (index : Nat) (source : RegDecl) (root : Ref)
    (needed : Nat) (cert : ActionCert)
    (shape : ActionShapeEvidence wires wireTable registers
      (rulesAction design.rules) needed cert)
    (evidence : RegQueryEvidence wires wireTable registers index
      source.width (rulesAction design.rules) (.reg source.name) needed cert root)
    (unique : RegisterNamesUnique registers)
    (registersEq : registers = design.regs.toArray)
    (sourceArrayFound : registers[index]? = some source)
    (sourceFound : design.regs[index]? = some source)
    (used : needed.testBit index = true)
    (metadata : indexedRegisterMetadataMatchesAt design program index root = true) :
    RegisterBehaviorAt design program wireTable index root := by
  subst registers
  have raw := evidence.nextReg_raw_of_input program wiresMatch wireTable shape
    unique source sourceArrayFound rfl used (.reg source.width source.name)
    (.reg source.width source.name)
  rw [nextReg_rulesAction] at raw
  cases concreteFound : program.regs[index]? with
  | none =>
      simp [indexedRegisterMetadataMatchesAt, sourceFound, concreteFound] at metadata
  | some concrete =>
      simp only [indexedRegisterMetadataMatchesAt, sourceFound, concreteFound,
        Bool.and_eq_true, beq_iff_eq] at metadata
      simp only [RegisterBehaviorAt, sourceFound, concreteFound]
      exact ⟨metadata.1.1.1, metadata.1.1.2, metadata.1.2, metadata.2, raw⟩

end Loom.Release.Symbolic.ActionWide
