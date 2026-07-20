-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CompileWhole
import Loom.Release.ActionWideJoin

/-!
# Action-wide release checking for register roots

The reference compiler is pointwise, but checking it once per register repeats
the complete source action hundreds of times.  This checker instead follows an
action once while carrying an indexed array of current SSA references.  Writes
update one slot, sequences thread the array, and conditionals join only the
sparse union of slots changed by their branches.

The certificate is merely an untrusted execution hint.  The checker verifies
every source register index, compiled write expression, guard, and SSA mux.
-/

namespace Loom.Release.Symbolic.ActionWide

open Loom.Hw
open Loom.Release.SSA

structure Summary where
  /-- Bitmap of register indices which may be written. -/
  possible : Nat
  /-- Bitmap of register indices written on every path. -/
  definite : Nat
  deriving Repr, DecidableEq

/-- Sparse execution hints following the source action syntax. -/
inductive ActionCert where
  | skip
  | write (index : Nat) (value : Ref)
  | seq (summary : Summary) (left right : ActionCert)
  | ite (summary : Summary) (guard : Ref) (joins : List Join)
      (thenCert elseCert : ActionCert)
  | memWrite
  deriving Repr, DecidableEq

/-- One action certificate per ordered source rule. -/
abbrev RulesCert := List ActionCert

/-- Source-action projections used to give large generated subactions stable
names without copying their syntax. -/
def iteThenAction : Loom.Hw.Act → Loom.Hw.Act
  | .ite _ thenAction _ => thenAction
  | _ => .skip

def iteElseAction : Loom.Hw.Act → Loom.Hw.Act
  | .ite _ _ elseAction => elseAction
  | _ => .skip

def iteConditionAction : Loom.Hw.Act → Loom.Hw.Expr 1
  | .ite condition _ _ => condition
  | _ => .lit 0

def isIteAction : Loom.Hw.Act → Bool
  | .ite .. => true
  | _ => false

def isSeqAction : Loom.Hw.Act → Bool
  | .seq .. => true
  | _ => false

def seqLeftAction : Loom.Hw.Act → Loom.Hw.Act
  | .seq left _ => left
  | _ => .skip

def seqRightAction : Loom.Hw.Act → Loom.Hw.Act
  | .seq _ right => right
  | _ => .skip

theorem action_eq_ite_projections {action : Loom.Hw.Act}
    (accepted : isIteAction action = true) :
    action = .ite (iteConditionAction action) (iteThenAction action)
      (iteElseAction action) := by
  cases action <;> simp [isIteAction, iteConditionAction, iteThenAction,
    iteElseAction] at accepted ⊢

theorem action_eq_seq_projections {action : Loom.Hw.Act}
    (accepted : isSeqAction action = true) :
    action = .seq (seqLeftAction action) (seqRightAction action) := by
  cases action <;> simp [isSeqAction, seqLeftAction, seqRightAction]
    at accepted ⊢

def ActionCert.iteThen : ActionCert → ActionCert
  | .ite _ _ _ thenCert _ => thenCert
  | _ => .skip

def ActionCert.iteElse : ActionCert → ActionCert
  | .ite _ _ _ _ elseCert => elseCert
  | _ => .skip

def ActionCert.seqLeft : ActionCert → ActionCert
  | .seq _ left _ => left
  | _ => .skip

def ActionCert.seqRight : ActionCert → ActionCert
  | .seq _ _ right => right
  | _ => .skip

def ActionCert.claimedSummary : ActionCert → Summary
  | .seq summary .. | .ite summary .. => summary
  | .skip | .memWrite | .write .. => { possible := 0, definite := 0 }

def ActionCert.iteGuardRef : ActionCert → Ref
  | .ite _ guard _ _ _ => guard
  | _ => .reg ""

def ActionCert.iteJoins : ActionCert → List Join
  | .ite _ _ joins _ _ => joins
  | _ => []

def ActionCert.isIte : ActionCert → Bool
  | .ite .. => true
  | _ => false

def ActionCert.isSeq : ActionCert → Bool
  | .seq .. => true
  | _ => false

theorem ActionCert.eq_ite_projections {cert : ActionCert}
    (accepted : cert.isIte = true) :
    cert = .ite cert.claimedSummary cert.iteGuardRef cert.iteJoins
      cert.iteThen cert.iteElse := by
  cases cert <;> simp [ActionCert.isIte, ActionCert.claimedSummary,
    ActionCert.iteGuardRef, ActionCert.iteJoins, ActionCert.iteThen,
    ActionCert.iteElse] at accepted ⊢

theorem ActionCert.eq_seq_projections {cert : ActionCert}
    (accepted : cert.isSeq = true) :
    cert = .seq cert.claimedSummary cert.seqLeft cert.seqRight := by
  cases cert <;> simp [ActionCert.isSeq, ActionCert.claimedSummary,
    ActionCert.seqLeft, ActionCert.seqRight] at accepted ⊢

/-! ### Compact untrusted transport

Release certificates contain tens of thousands of action nodes.  Spelling the
derived summaries and structure field names in generated Lean source makes
elaboration dominate verification.  The transport below stores every word as
four printable base-64 bytes inside one included string.  A total kernel
function reconstructs the typed certificate and recomputes every summary;
malformed input is rejected.

Reference words use the low bit as a tag: `2 * n` is wire `n`, while
`2 * i + 1` is source-register index `i`.
-/

private structure Decoder where
  bytes : ByteArray
  cursor : Nat := 0

private abbrev DecodeM := StateT Decoder Option

private def decodeDigit (byte : UInt8) : Option Nat :=
  let value := byte.toNat
  if 33 ≤ value && value < 97 then some (value - 33) else none

private def takeWord : DecodeM Nat := do
  let state ← get
  let some byte0 := state.bytes[state.cursor]? | failure
  let some byte1 := state.bytes[state.cursor + 1]? | failure
  let some byte2 := state.bytes[state.cursor + 2]? | failure
  let some byte3 := state.bytes[state.cursor + 3]? | failure
  let digit0 ← decodeDigit byte0
  let digit1 ← decodeDigit byte1
  let digit2 ← decodeDigit byte2
  let digit3 ← decodeDigit byte3
  set { state with cursor := state.cursor + 4 }
  pure (((digit0 * 64 + digit1) * 64 + digit2) * 64 + digit3)

private def decodeRef (registers : Array Loom.Hw.RegDecl)
    (word : Nat) : Option Ref :=
  if word % 2 == 0 then some (.wire (word / 2))
  else do
    let register ← registers[word / 2]?
    pure (.reg register.name)

/-- Checked roots plus the sparse set of slots changed by this action. -/
structure Result where
  refs : Array Ref
  changed : List Nat
  deriving Repr, DecidableEq

/-! ### Kernel-friendly sparse register state

The release checker must update hundreds of register roots across tens of
thousands of action nodes. Persistent `Array.set!` makes that quadratic in the
register count under kernel reduction. A fixed-depth binary trie rebuilds only
sixteen constructors per update and has a canonical shape independent of
insertion order. Missing entries denote the corresponding source register.
-/

inductive SparseRefs where
  | empty
  | leaf (value : Ref)
  | branch (zero one : SparseRefs)
  deriving Repr, DecidableEq

private def sparseDepth : Nat := 16

def SparseRefs.get? : Nat → SparseRefs → Nat → Option Ref
  | 0, .leaf value, _ => some value
  | 0, _, _ => none
  | depth + 1, .branch zero one, index =>
      if index.testBit depth then
        SparseRefs.get? depth one index
      else SparseRefs.get? depth zero index
  | _ + 1, _, _ => none

def SparseRefs.set : Nat → SparseRefs → Nat → Ref → SparseRefs
  | 0, _, _, value => .leaf value
  | depth + 1, .branch zero one, index, value =>
      if index.testBit depth then
        .branch zero (SparseRefs.set depth one index value)
      else .branch (SparseRefs.set depth zero index value) one
  | depth + 1, _, index, value =>
      if index.testBit depth then
        .branch .empty (SparseRefs.set depth .empty index value)
      else .branch (SparseRefs.set depth .empty index value) .empty

def SparseRefs.lookup (registers : Array Loom.Hw.RegDecl)
    (refs : SparseRefs) (index : Nat) : Option Ref :=
  match refs.get? sparseDepth index with
  | some value => some value
  | none => do
      let register ← registers[index]?
      some (.reg register.name)

def SparseRefs.write (refs : SparseRefs) (index : Nat) (value : Ref) :
    SparseRefs :=
  refs.set sparseDepth index value

def SparseRefs.materialize (registers : Array Loom.Hw.RegDecl)
    (refs : SparseRefs) : Array Ref :=
  registers.mapIdx fun index register =>
    (refs.get? sparseDepth index).getD (.reg register.name)

structure SparseResult where
  refs : SparseRefs
  changed : List Nat
  deriving Repr, DecidableEq

private def singletonIndex (index : Nat) : Nat := 1 <<< index

def ActionCert.summary : ActionCert → Summary
  | .skip | .memWrite => { possible := 0, definite := 0 }
  | .write index _ =>
      { possible := singletonIndex index, definite := singletonIndex index }
  | .seq summary _ _ | .ite summary _ _ _ _ => summary

def seqSummary (left right : Summary) : Summary :=
  { possible := left.possible ||| right.possible
    definite := left.definite ||| right.definite }

def iteSummary (thenSummary elseSummary : Summary) : Summary :=
  { possible := thenSummary.possible ||| elseSummary.possible
    definite := thenSummary.definite &&& elseSummary.definite }

private def initialRefs (registers : Array Loom.Hw.RegDecl) : Array Ref :=
  registers.map fun register => .reg register.name

private def unchanged (refs : Array Ref) : Result :=
  { refs, changed := [] }

def neededInputs (summary : Summary) (needed : List Nat) : List Nat :=
  needed.filter (!summary.definite.testBit ·)

def changedOutputs (summary : Summary) (needed : List Nat) : List Nat :=
  needed.filter (summary.possible.testBit ·)

def neededRuleInputs : RulesCert → List Nat → List Nat
  | [], needed => needed
  | cert :: certs, needed =>
      neededInputs cert.summary (neededRuleInputs certs needed)

mutual
def refsEquivalent (wires : Rope (List IndexedWire))
    (table : WireTable) : Nat → Ref → Ref → Bool
  | 0, left, right => left == right
  | fuel + 1, left, right =>
      if left == right then true else
      match left, right with
      | .reg _, .reg _ => false
      | .wire number, .reg _ =>
          match lookupIndexed? wires table number with
          | some ⟨_, _, .ident value⟩ =>
              refsEquivalent wires table fuel value right
          | _ => false
      | .reg _, .wire number =>
          match lookupIndexed? wires table number with
          | some ⟨_, _, .ident value⟩ =>
              refsEquivalent wires table fuel left value
          | _ => false
      | .wire leftNumber, .wire rightNumber =>
          match lookupIndexed? wires table leftNumber,
              lookupIndexed? wires table rightNumber with
          | some leftWire, some rightWire =>
              leftWire.width == rightWire.width &&
                rhsEquivalent wires table fuel leftWire.rhs rightWire.rhs
          | _, _ => false

def rhsEquivalent (wires : Rope (List IndexedWire))
    (table : WireTable) : Nat → IndexedRhs → IndexedRhs → Bool
  | 0, left, right => left == right
  | _ + 1, .lit width value, .lit width' value' =>
      width == width' && value == value'
  | fuel + 1, .ident left, .ident right =>
      refsEquivalent wires table fuel left right
  | fuel + 1, .memRead memory address, .memRead memory' address' =>
      memory == memory' && refsEquivalent wires table fuel address address'
  | fuel + 1, .slice value hi lo, .slice value' hi' lo' =>
      hi == hi' && lo == lo' &&
        refsEquivalent wires table fuel value value'
  | fuel + 1, .not value, .not value' =>
      refsEquivalent wires table fuel value value'
  | fuel + 1, .bin op left right, .bin op' left' right' =>
      op == op' && refsEquivalent wires table fuel left left' &&
        refsEquivalent wires table fuel right right'
  | fuel + 1, .slt left right, .slt left' right' =>
      refsEquivalent wires table fuel left left' &&
        refsEquivalent wires table fuel right right'
  | fuel + 1, .mux guard yes no, .mux guard' yes' no' =>
      refsEquivalent wires table fuel guard guard' &&
        refsEquivalent wires table fuel yes yes' &&
        refsEquivalent wires table fuel no no'
  | fuel + 1, .sext amount value signBit,
      .sext amount' value' signBit' =>
      amount == amount' && signBit == signBit' &&
        refsEquivalent wires table fuel value value'
  | _ + 1, _, _ => false
end

private def joinMatchesWithFuel (wires : Rope (List IndexedWire))
    (table : WireTable) (registers : Array Loom.Hw.RegDecl) (_fuel : Nat)
    (join : Join) : Bool :=
  match registers[join.index]?, join.output with
  | some source, .wire number =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .mux actualGuard actualThen actualElse⟩ =>
          join.width == source.width && actualWidth == join.width &&
            join.guard == actualGuard &&
            join.thenInput == actualThen &&
            join.elseInput == actualElse
      | _ => false
  | _, _ => false

/-- Independently check one concrete SSA mux join. -/
def joinMatches (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) (join : Join) : Bool :=
  joinMatchesWithFuel wires table registers (wires.listLength + 1) join

def joinBlockMatchesFuel (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) (fuel : Nat)
    (joins : List Join) : Bool :=
  joins.all (joinMatchesWithFuel wires table registers fuel)

/-- Check a bounded list of independent mux joins. -/
def joinBlockMatches (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) (joins : List Join) : Bool :=
  joinBlockMatchesFuel wires table registers (wires.listLength + 1) joins

private def mergeJoins (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) (guard : Ref)
    (thenResult elseResult : Result) :
    List Nat → List Join → Array Ref → Option (Array Ref)
  | [], [], output => some output
  | index :: indices, join :: joins, output => do
      let source ← registers[index]?
      let thenRef ← thenResult.refs[index]?
      let elseRef ← elseResult.refs[index]?
      if join.index != index || join.width != source.width then none else
      match join.output with
      | .reg _ => none
      | .wire number =>
          match lookupIndexed? wires table number with
          | some ⟨_, actualWidth, .mux actualGuard actualThen actualElse⟩ =>
              if actualWidth == source.width &&
                  guard == actualGuard && thenRef == actualThen &&
                  elseRef == actualElse then
                mergeJoins wires table registers guard thenResult elseResult
                  indices joins (output.set! index join.output)
              else none
          | _ => none
  | _, _, _ => none

/-- Validate one source action in a single traversal. -/
def runAction (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    Loom.Hw.Act → Array Ref → List Nat → ActionCert → Option Result
  | .skip, refs, _, .skip => some (unchanged refs)
  | .memWrite .., refs, _, .memWrite => some (unchanged refs)
  | .write width name value, refs, needed,
      .write index valueRef => do
      let source ← registers[index]?
      if source.name != name || source.width != width then none
      else if index ∉ needed then some (unchanged refs)
      else if !indexedExprMatches wires table
          (Loom.Hw.Compile.compileExpr value) valueRef then none
      else if index < refs.size then
        some { refs := refs.set! index valueRef, changed := [index] }
      else none
  | .seq left right, refs, needed, .seq summary leftCert rightCert => do
      if summary != seqSummary leftCert.summary rightCert.summary then none
      let leftNeeded := neededInputs rightCert.summary needed
      let leftResult ← runAction wires table registers left refs leftNeeded
        leftCert
      let rightResult ← runAction wires table registers right leftResult.refs
        needed rightCert
      some { refs := rightResult.refs
             changed := changedOutputs summary needed }
  | .ite guard thenAction elseAction, refs, needed,
      .ite summary guardRef joins thenCert elseCert => do
      if summary != iteSummary thenCert.summary elseCert.summary then none
      if !indexedExprMatches wires table
          (Loom.Hw.Compile.compileExpr guard) guardRef then none
      let changed := changedOutputs summary needed
      let thenResult ← runAction wires table registers thenAction refs changed
        thenCert
      let elseResult ← runAction wires table registers elseAction refs changed
        elseCert
      let merged ← mergeJoins wires table registers guardRef thenResult
        elseResult changed joins refs
      some { refs := merged, changed }
  | _, _, _, _ => none

/-- Validate the ordered source-rule traversal. -/
def runRules (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    List Loom.Hw.Rule → Array Ref → List Nat → RulesCert → Option (Array Ref)
  | [], refs, _, [] => some refs
  | rule :: rules, refs, needed, cert :: certs => do
      let headNeeded := neededRuleInputs certs needed
      let result ← runAction wires table registers rule.body refs headNeeded cert
      runRules wires table registers rules result.refs needed certs
  | _, _, _, _ => none

private def finalMetadataMatches (program : Program) :
    List Loom.Hw.RegDecl → Array Ref → Nat → Bool
  | [], refs, index => index == refs.size && index == program.regs.length
  | source :: sources, refs, index =>
      match program.regs[index]?, refs[index]? with
      | some concrete, some root =>
          source.name == concrete.name && source.width == concrete.width &&
          source.init.toNat == concrete.init && concrete.next == root.render &&
          finalMetadataMatches program sources refs (index + 1)
      | _, _ => false

/-- End-to-end Boolean gate for all concrete register roots. -/
def registersMatch (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (cert : RulesCert) : Bool :=
  let registers := design.regs.toArray
  let needed := List.range registers.size
  match runRules wires table registers design.rules (initialRefs registers)
      needed cert with
  | some refs => finalMetadataMatches program design.regs refs 0
  | none => false

private def checkedJoinUpdates (registers : Array Loom.Hw.RegDecl)
    (condition : Ref) (thenResult elseResult : Result) :
    List Nat → List Join → Option (List (Nat × Ref))
  | [], [] => some []
  | index :: indices, join :: joins => do
      let source ← registers[index]?
      let thenRef ← thenResult.refs[index]?
      let elseRef ← elseResult.refs[index]?
      guard (join.index == index && join.width == source.width)
      guard (join.guard == condition && join.thenInput == thenRef &&
        join.elseInput == elseRef)
      match join.output with
      | .wire _ =>
          let updates ← checkedJoinUpdates registers condition thenResult
            elseResult indices joins
          some ((index, join.output) :: updates)
      | .reg _ => none
  | _, _ => none

private def applySortedJoinUpdates :
    Nat → List Ref → List (Nat × Ref) → List Ref
  | _, [], _ => []
  | index, ref :: refs, [] =>
      ref :: applySortedJoinUpdates (index + 1) refs []
  | index, ref :: refs, remaining@((updateIndex, updated) :: updates) =>
      if index == updateIndex then
        updated :: applySortedJoinUpdates (index + 1) refs updates
      else
        ref :: applySortedJoinUpdates (index + 1) refs remaining

/-- Validate conditional joins, then apply their sorted updates in one linear
pass over the register array. -/
def checkedJoinMerge (registers : Array Loom.Hw.RegDecl)
    (condition : Ref) (thenResult elseResult : Result)
    (indices : List Nat) (joins : List Join) (output : Array Ref) :
    Option (Array Ref) := do
  let updates ← checkedJoinUpdates registers condition thenResult elseResult
    indices joins
  some (applySortedJoinUpdates 0 output.toList updates).toArray

/-- Source-action traversal after concrete mux leaves have been checked
independently.  It validates control flow, writes, guards, summaries, and the
association of every checked mux with the source-register state, but performs
no repeated global mux lookup. -/
def runCheckedAction (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    Loom.Hw.Act → Array Ref → List Nat → ActionCert → Option Result
  | .skip, refs, _, .skip => some (unchanged refs)
  | .memWrite .., refs, _, .memWrite => some (unchanged refs)
  | .write width name value, refs, needed, .write index valueRef => do
      let source ← registers[index]?
      guard (source.name == name && source.width == width)
      if index ∉ needed then some (unchanged refs)
      else do
        guard (indexedExprMatches wires table
          (Loom.Hw.Compile.compileExpr value) valueRef)
        guard (index < refs.size)
        some { refs := refs.set! index valueRef, changed := [index] }
  | .seq left right, refs, needed, .seq summary leftCert rightCert => do
      if summary != seqSummary leftCert.summary rightCert.summary then none
      else do
        let leftNeeded := neededInputs rightCert.summary needed
        let leftResult ← runCheckedAction wires table registers left refs
          leftNeeded leftCert
        let rightResult ← runCheckedAction wires table registers right
          leftResult.refs needed rightCert
        some { refs := rightResult.refs, changed := changedOutputs summary needed }
  | .ite condition thenAction elseAction, refs, needed,
      .ite summary conditionRef joins thenCert elseCert => do
      if summary != iteSummary thenCert.summary elseCert.summary then none
      else if !indexedExprMatches wires table
          (Loom.Hw.Compile.compileExpr condition) conditionRef then none
      else do
        let changed := changedOutputs summary needed
        let thenResult ← runCheckedAction wires table registers thenAction refs
          changed thenCert
        let elseResult ← runCheckedAction wires table registers elseAction refs
          changed elseCert
        let merged ← checkedJoinMerge registers conditionRef thenResult
          elseResult changed joins refs
        some { refs := merged, changed }
  | _, _, _, _ => none

/-- Constant-only composition for a checked sequence. -/
theorem runCheckedAction_seq_of_checks
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) (left right : Loom.Hw.Act)
    (refs : Array Ref) (needed : List Nat) (summary : Summary)
    (leftCert rightCert : ActionCert) (leftResult rightResult : Result)
    (summaryAccepted : summary = seqSummary leftCert.summary rightCert.summary)
    (leftAccepted : runCheckedAction wires table registers left refs
      (neededInputs rightCert.summary needed) leftCert = some leftResult)
    (rightAccepted : runCheckedAction wires table registers right
      leftResult.refs needed rightCert = some rightResult) :
    runCheckedAction wires table registers (.seq left right) refs needed
      (.seq summary leftCert rightCert) = some
        { refs := rightResult.refs, changed := changedOutputs summary needed } := by
  subst summary
  simp [runCheckedAction, leftAccepted, rightAccepted]

/-- Constant-only composition for a checked conditional. -/
theorem runCheckedAction_ite_of_checks
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) (condition : Loom.Hw.Expr 1)
    (thenAction elseAction : Loom.Hw.Act) (refs : Array Ref)
    (needed : List Nat) (summary : Summary) (conditionRef : Ref)
    (joins : List Join) (thenCert elseCert : ActionCert)
    (thenResult elseResult : Result) (merged : Array Ref)
    (summaryAccepted : summary = iteSummary thenCert.summary elseCert.summary)
    (conditionAccepted : indexedExprMatches wires table
      (Loom.Hw.Compile.compileExpr condition) conditionRef = true)
    (thenAccepted : runCheckedAction wires table registers thenAction refs
      (changedOutputs summary needed) thenCert = some thenResult)
    (elseAccepted : runCheckedAction wires table registers elseAction refs
      (changedOutputs summary needed) elseCert = some elseResult)
    (mergeAccepted : checkedJoinMerge registers conditionRef thenResult
      elseResult (changedOutputs summary needed) joins refs = some merged) :
    runCheckedAction wires table registers
      (.ite condition thenAction elseAction) refs needed
      (.ite summary conditionRef joins thenCert elseCert) = some
        { refs := merged, changed := changedOutputs summary needed } := by
  subst summary
  simp [runCheckedAction, conditionAccepted, thenAccepted, elseAccepted,
    mergeAccepted]

/-- Compositional evidence for the action-wide checker.  Generated artifacts
use `direct` only for bounded segments and use `seq`/`ite` to connect already
named child evidence, so checking a parent never normalizes a child again. -/
inductive CheckedEvidence (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    Loom.Hw.Act → Array Ref → List Nat → ActionCert → Result → Prop where
  | direct {action refs needed cert result}
      (accepted : runCheckedAction wires table registers action refs needed cert =
        some result) :
      CheckedEvidence wires table registers action refs needed cert result
  | seq {left right refs needed summary leftCert rightCert leftResult rightResult}
      (summaryAccepted : summary =
        seqSummary leftCert.summary rightCert.summary)
      (leftAccepted : CheckedEvidence wires table registers left refs
        (neededInputs rightCert.summary needed) leftCert leftResult)
      (rightAccepted : CheckedEvidence wires table registers right
        leftResult.refs needed rightCert rightResult) :
      CheckedEvidence wires table registers (.seq left right) refs needed
        (.seq summary leftCert rightCert)
        { refs := rightResult.refs, changed := changedOutputs summary needed }
  | ite {condition thenAction elseAction refs needed summary conditionRef joins
      thenCert elseCert thenResult elseResult merged}
      (summaryAccepted : summary =
        iteSummary thenCert.summary elseCert.summary)
      (conditionAccepted : indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr condition) conditionRef = true)
      (thenAccepted : CheckedEvidence wires table registers thenAction refs
        (changedOutputs summary needed) thenCert thenResult)
      (elseAccepted : CheckedEvidence wires table registers elseAction refs
        (changedOutputs summary needed) elseCert elseResult)
      (mergeAccepted : checkedJoinMerge registers conditionRef thenResult
        elseResult (changedOutputs summary needed) joins refs = some merged) :
      CheckedEvidence wires table registers
        (.ite condition thenAction elseAction) refs needed
        (.ite summary conditionRef joins thenCert elseCert)
        { refs := merged, changed := changedOutputs summary needed }

/-- Compositional evidence is sound for the original action-wide checker. -/
theorem CheckedEvidence.accepted
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {registers : Array Loom.Hw.RegDecl} {action refs needed cert result}
    (evidence : CheckedEvidence wires table registers action refs needed cert
      result) :
    runCheckedAction wires table registers action refs needed cert =
      some result := by
  induction evidence with
  | direct accepted => exact accepted
  | seq summaryAccepted _ _ leftIH rightIH =>
      exact runCheckedAction_seq_of_checks wires table registers _ _ _ _ _ _ _
        _ _ summaryAccepted leftIH rightIH
  | ite summaryAccepted conditionAccepted _ _ mergeAccepted thenIH elseIH =>
      exact runCheckedAction_ite_of_checks wires table registers _ _ _ _ _ _ _
        _ _ _ _ _ _ summaryAccepted conditionAccepted thenIH elseIH
        mergeAccepted

def runCheckedRules (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    List Loom.Hw.Rule → Array Ref → List Nat → RulesCert → Option (Array Ref)
  | [], refs, _, [] => some refs
  | rule :: rules, refs, needed, cert :: certs => do
      let headNeeded := neededRuleInputs certs needed
      let result ← runCheckedAction wires table registers rule.body refs
        headNeeded cert
      runCheckedRules wires table registers rules result.refs needed certs
  | _, _, _, _ => none

/-- Fast artifact gate whose mux premises are discharged by bounded local
join certificates. -/
def checkedRegistersMatch (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (cert : RulesCert) : Bool :=
  let registers := design.regs.toArray
  let needed := List.range registers.size
  match runCheckedRules wires table registers design.rules
      (initialRefs registers) needed cert with
  | some refs => finalMetadataMatches program design.regs refs 0
  | none => false

/-! ### Sparse compositional checker

This is the release path used by generated action evidence. Every constructor
determines its output state, so artifact proofs check only local headers,
expressions, summaries, and join associations—not equality of whole states.
-/

def checkedWriteHeader (registers : Array Loom.Hw.RegDecl) (index width : Nat)
    (name : String) : Bool :=
  match registers[index]? with
  | some source => source.name == name && source.width == width
  | none => false

def checkedSparseJoins (registers : Array Loom.Hw.RegDecl) (condition : Ref)
    (thenResult elseResult : SparseResult) : List Nat → List Join → Bool
  | [], [] => true
  | index :: indices, join :: joins =>
      match registers[index]?, thenResult.refs.lookup registers index,
          elseResult.refs.lookup registers index with
      | some source, some thenRef, some elseRef =>
          join.index == index && join.width == source.width &&
            join.guard == condition && join.thenInput == thenRef &&
            join.elseInput == elseRef &&
            (match join.output with | .wire _ => true | .reg _ => false) &&
            checkedSparseJoins registers condition thenResult elseResult
              indices joins
      | _, _, _ => false
  | _, _ => false

/-- Validate one bitmap-indexed join. Keeping this check separate from the
recursive spine lets release certificates prove each bounded lookup once. -/
def checkedBitJoin (registers : Array Loom.Hw.RegDecl) (condition : Ref)
    (thenRefs elseRefs : SparseRefs) (changed : Nat) (join : Join) : Bool :=
  let index := join.index
  changed.testBit index &&
    match registers[index]?, thenRefs.lookup registers index,
        elseRefs.lookup registers index with
    | some source, some thenRef, some elseRef =>
        join.width == source.width && join.guard == condition &&
          join.thenInput == thenRef && join.elseInput == elseRef &&
          (match join.output with | .wire _ => true | .reg _ => false)
    | _, _, _ => false

/-- Validate exactly the joins named by a register bitmap. Each accepted join
clears its bit, so duplicates reject and the final zero check rejects missing
joins. Join order is irrelevant because distinct register writes commute. -/
def checkedBitJoins (registers : Array Loom.Hw.RegDecl) (condition : Ref)
    (thenRefs elseRefs : SparseRefs) : Nat → List Join → Bool
  | changed, [] => changed == 0
  | changed, join :: joins =>
      checkedBitJoin registers condition thenRefs elseRefs changed join &&
        checkedBitJoins registers condition thenRefs elseRefs
          (changed ^^^ (1 <<< join.index)) joins

/-- Structural evidence for the recursive bitmap join checker. Each `cons`
premise is bounded to one register lookup, so checking a parent never unfolds
the already-validated tail. -/
inductive BitJoinsEvidence (registers : Array Loom.Hw.RegDecl) (condition : Ref)
    (thenRefs elseRefs : SparseRefs) : Nat → List Join → Prop where
  | nil : BitJoinsEvidence registers condition thenRefs elseRefs 0 []
  | cons {changed join joins}
      (headAccepted : checkedBitJoin registers condition thenRefs elseRefs
        changed join = true)
      (tailAccepted : BitJoinsEvidence registers condition thenRefs elseRefs
        (changed ^^^ (1 <<< join.index)) joins) :
      BitJoinsEvidence registers condition thenRefs elseRefs changed
        (join :: joins)

theorem BitJoinsEvidence.accepted
    {registers : Array Loom.Hw.RegDecl} {condition : Ref}
    {thenRefs elseRefs : SparseRefs} {changed : Nat} {joins : List Join}
    (evidence : BitJoinsEvidence registers condition thenRefs elseRefs changed
      joins) :
    checkedBitJoins registers condition thenRefs elseRefs changed joins = true := by
  induction evidence with
  | nil => rfl
  | cons headAccepted _ tailIH =>
      simp only [checkedBitJoins, headAccepted, tailIH, Bool.and_self]

def applySparseJoins (refs : SparseRefs) (joins : List Join) : SparseRefs :=
  joins.foldl (fun result join => result.write join.index join.output) refs

def runSparseAction (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    Loom.Hw.Act → SparseRefs → List Nat → ActionCert → Option SparseResult
  | .skip, refs, _, .skip => some { refs, changed := [] }
  | .memWrite .., refs, _, .memWrite => some { refs, changed := [] }
  | .write width name value, refs, needed, .write index valueRef =>
      if !checkedWriteHeader registers index width name then none
      else if index ∉ needed then some { refs, changed := [] }
      else if indexedExprMatches wires table
          (Loom.Hw.Compile.compileExpr value) valueRef then
        some { refs := refs.write index valueRef, changed := [index] }
      else none
  | .seq left right, refs, needed, .seq summary leftCert rightCert => do
      guard (summary == seqSummary leftCert.summary rightCert.summary)
      let leftNeeded := neededInputs rightCert.summary needed
      let leftResult ← runSparseAction wires table registers left refs leftNeeded
        leftCert
      let rightResult ← runSparseAction wires table registers right
        leftResult.refs needed rightCert
      some { refs := rightResult.refs, changed := changedOutputs summary needed }
  | .ite condition thenAction elseAction, refs, needed,
      .ite summary conditionRef joins thenCert elseCert => do
      guard (summary == iteSummary thenCert.summary elseCert.summary)
      guard (indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr condition) conditionRef)
      let changed := changedOutputs summary needed
      let thenResult ← runSparseAction wires table registers thenAction refs
        changed thenCert
      let elseResult ← runSparseAction wires table registers elseAction refs
        changed elseCert
      guard (checkedSparseJoins registers conditionRef thenResult elseResult
        changed joins)
      some { refs := applySparseJoins refs joins, changed }
  | _, _, _, _ => none

inductive SparseEvidence (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    Loom.Hw.Act → SparseRefs → List Nat → ActionCert → SparseResult → Prop where
  | skip {refs needed} :
      SparseEvidence wires table registers .skip refs needed .skip
        { refs, changed := [] }
  | memWrite {aw dw mem port address data refs needed} :
      SparseEvidence wires table registers
        (.memWrite aw dw mem port address data) refs needed .memWrite
        { refs, changed := [] }
  | writeUnused {width name value refs needed index valueRef}
      (headerAccepted : checkedWriteHeader registers index width name = true)
      (unused : index ∉ needed) :
      SparseEvidence wires table registers (.write width name value) refs needed
        (.write index valueRef) { refs, changed := [] }
  | writeNeeded {width name value refs needed index valueRef}
      (headerAccepted : checkedWriteHeader registers index width name = true)
      (used : index ∈ needed)
      (valueAccepted : indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr value) valueRef = true) :
      SparseEvidence wires table registers (.write width name value) refs needed
        (.write index valueRef)
        { refs := refs.write index valueRef, changed := [index] }
  | seq {left right refs needed summary leftCert rightCert leftResult rightResult}
      (summaryAccepted : summary =
        seqSummary leftCert.summary rightCert.summary)
      (leftAccepted : SparseEvidence wires table registers left refs
        (neededInputs rightCert.summary needed) leftCert leftResult)
      (rightAccepted : SparseEvidence wires table registers right
        leftResult.refs needed rightCert rightResult) :
      SparseEvidence wires table registers (.seq left right) refs needed
        (.seq summary leftCert rightCert)
        { refs := rightResult.refs, changed := changedOutputs summary needed }
  | ite {condition thenAction elseAction refs needed summary conditionRef joins
      thenCert elseCert thenResult elseResult}
      (summaryAccepted : summary =
        iteSummary thenCert.summary elseCert.summary)
      (conditionAccepted : indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr condition) conditionRef = true)
      (thenAccepted : SparseEvidence wires table registers thenAction refs
        (changedOutputs summary needed) thenCert thenResult)
      (elseAccepted : SparseEvidence wires table registers elseAction refs
        (changedOutputs summary needed) elseCert elseResult)
      (joinsAccepted : checkedSparseJoins registers conditionRef thenResult
        elseResult (changedOutputs summary needed) joins = true) :
      SparseEvidence wires table registers (.ite condition thenAction elseAction)
        refs needed (.ite summary conditionRef joins thenCert elseCert)
        { refs := applySparseJoins refs joins
          changed := changedOutputs summary needed }

theorem SparseEvidence.seqProjected
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {registers : Array Loom.Hw.RegDecl} {action : Loom.Hw.Act}
    {refs : SparseRefs} {needed : List Nat} {cert : ActionCert}
    {leftResult rightResult : SparseResult}
    (actionAccepted : isSeqAction action = true)
    (certAccepted : cert.isSeq = true)
    (summaryAccepted : cert.claimedSummary =
      seqSummary cert.seqLeft.summary cert.seqRight.summary)
    (leftAccepted : SparseEvidence wires table registers
      (seqLeftAction action) refs (neededInputs cert.seqRight.summary needed)
      cert.seqLeft leftResult)
    (rightAccepted : SparseEvidence wires table registers
      (seqRightAction action) leftResult.refs needed cert.seqRight rightResult) :
    SparseEvidence wires table registers action refs needed cert
      { refs := rightResult.refs
        changed := changedOutputs cert.claimedSummary needed } := by
  rw [action_eq_seq_projections actionAccepted]
  rw [ActionCert.eq_seq_projections certAccepted]
  exact .seq summaryAccepted leftAccepted rightAccepted

theorem SparseEvidence.iteProjected
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {registers : Array Loom.Hw.RegDecl} {action : Loom.Hw.Act}
    {refs : SparseRefs} {needed : List Nat} {cert : ActionCert}
    {thenResult elseResult : SparseResult}
    (actionAccepted : isIteAction action = true)
    (certAccepted : cert.isIte = true)
    (summaryAccepted : cert.claimedSummary =
      iteSummary cert.iteThen.summary cert.iteElse.summary)
    (conditionAccepted : indexedExprMatches wires table
      (Loom.Hw.Compile.compileExpr (iteConditionAction action))
      cert.iteGuardRef = true)
    (thenAccepted : SparseEvidence wires table registers
      (iteThenAction action) refs (changedOutputs cert.claimedSummary needed)
      cert.iteThen thenResult)
    (elseAccepted : SparseEvidence wires table registers
      (iteElseAction action) refs (changedOutputs cert.claimedSummary needed)
      cert.iteElse elseResult)
    (joinsAccepted : checkedSparseJoins registers cert.iteGuardRef thenResult
      elseResult (changedOutputs cert.claimedSummary needed) cert.iteJoins = true) :
    SparseEvidence wires table registers action refs needed cert
      { refs := applySparseJoins refs cert.iteJoins
        changed := changedOutputs cert.claimedSummary needed } := by
  rw [action_eq_ite_projections actionAccepted]
  rw [ActionCert.eq_ite_projections certAccepted]
  exact .ite summaryAccepted conditionAccepted thenAccepted elseAccepted
    joinsAccepted

theorem SparseEvidence.transport
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {registers : Array Loom.Hw.RegDecl}
    {action action' : Loom.Hw.Act} {refs refs' : SparseRefs}
    {needed needed' : List Nat} {cert cert' : ActionCert}
    {result result' : SparseResult}
    (actionEq : action = action') (refsEq : refs = refs')
    (neededEq : needed = needed') (certEq : cert = cert')
    (resultEq : result = result')
    (evidence : SparseEvidence wires table registers action refs needed cert
      result) :
    SparseEvidence wires table registers action' refs' needed' cert' result' := by
  subst action'
  subst refs'
  subst needed'
  subst cert'
  subst result'
  exact evidence

theorem SparseEvidence.accepted
    {wires : Rope (List IndexedWire)} {table : WireTable}
    {registers : Array Loom.Hw.RegDecl} {action refs needed cert result}
    (evidence : SparseEvidence wires table registers action refs needed cert
      result) :
    runSparseAction wires table registers action refs needed cert =
      some result := by
  induction evidence with
  | skip => rfl
  | memWrite => rfl
  | writeUnused headerAccepted unused =>
      simp [runSparseAction, headerAccepted, unused]
  | writeNeeded headerAccepted used valueAccepted =>
      simp [runSparseAction, headerAccepted, used, valueAccepted]
  | seq summaryAccepted _ _ leftIH rightIH =>
      subst summaryAccepted
      simp [runSparseAction, leftIH, rightIH, guard]
  | ite summaryAccepted conditionAccepted _ _ joinsAccepted thenIH elseIH =>
      subst summaryAccepted
      simp [runSparseAction, conditionAccepted, thenIH, elseIH, joinsAccepted,
        guard]

/-! ### Bitmap-indexed sparse evidence

The large release checker carries needed-register sets as bitmaps.  The older
list-indexed evidence above repeatedly scans lists of hundreds of register
indices at every source write.  This equivalent certificate shape keeps the
same `Summary` representation throughout the action traversal; conversion to
ordered index lists is isolated at the compatibility boundary. -/

/-- Remove registers definitely overwritten by an action. -/
def neededBitsBefore (summary : Summary) (needed : Nat) : Nat :=
  needed ^^^ (needed &&& summary.definite)

/-- Registers both needed by the continuation and possibly changed here. -/
def changedBitsAt (summary : Summary) (needed : Nat) : Nat :=
  needed &&& summary.possible

/-- Deterministic ascending list view used only by the existing join checker. -/
def bitIndices (count bits : Nat) : List Nat :=
  (List.range count).filter (bits.testBit ·)

structure BitSparseResult where
  refs : SparseRefs
  changed : Nat

/-- Sparse action evidence indexed by a register bitmap rather than a list. -/
inductive BitSparseEvidence (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    Loom.Hw.Act → SparseRefs → Nat → ActionCert → BitSparseResult → Prop where
  | skip {refs needed} :
      BitSparseEvidence wires table registers .skip refs needed .skip
        { refs, changed := 0 }
  | memWrite {aw dw mem port address data refs needed} :
      BitSparseEvidence wires table registers
        (.memWrite aw dw mem port address data) refs needed .memWrite
        { refs, changed := 0 }
  | writeUnused {width name value refs needed index valueRef}
      (headerAccepted : checkedWriteHeader registers index width name = true)
      (unused : needed.testBit index = false) :
      BitSparseEvidence wires table registers (.write width name value) refs needed
        (.write index valueRef) { refs, changed := 0 }
  | writeNeeded {width name value refs needed index valueRef}
      (headerAccepted : checkedWriteHeader registers index width name = true)
      (used : needed.testBit index = true)
      (valueAccepted : indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr value) valueRef = true) :
      BitSparseEvidence wires table registers (.write width name value) refs needed
        (.write index valueRef)
        { refs := refs.write index valueRef, changed := 1 <<< index }
  | seq {left right refs needed summary leftCert rightCert leftResult rightResult}
      (summaryAccepted : summary = seqSummary leftCert.summary rightCert.summary)
      (leftAccepted : BitSparseEvidence wires table registers left refs
        (neededBitsBefore rightCert.summary needed) leftCert leftResult)
      (rightAccepted : BitSparseEvidence wires table registers right
        leftResult.refs needed rightCert rightResult) :
      BitSparseEvidence wires table registers (.seq left right) refs needed
        (.seq summary leftCert rightCert)
        { refs := rightResult.refs, changed := changedBitsAt summary needed }
  | ite {condition thenAction elseAction refs needed summary conditionRef joins
      thenCert elseCert thenResult elseResult}
      (summaryAccepted : summary = iteSummary thenCert.summary elseCert.summary)
      (conditionAccepted : indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr condition) conditionRef = true)
      (thenAccepted : BitSparseEvidence wires table registers thenAction refs
        (changedBitsAt summary needed) thenCert thenResult)
      (elseAccepted : BitSparseEvidence wires table registers elseAction refs
        (changedBitsAt summary needed) elseCert elseResult)
      (joinsAccepted : checkedBitJoins registers conditionRef
        thenResult.refs elseResult.refs (changedBitsAt summary needed)
        joins = true) :
      BitSparseEvidence wires table registers (.ite condition thenAction elseAction)
        refs needed (.ite summary conditionRef joins thenCert elseCert)
        { refs := applySparseJoins refs joins
          changed := changedBitsAt summary needed }

def runSparseRules (wires : Rope (List IndexedWire)) (table : WireTable)
    (registers : Array Loom.Hw.RegDecl) :
    List Loom.Hw.Rule → SparseRefs → List Nat → RulesCert → Option SparseRefs
  | [], refs, _, [] => some refs
  | rule :: rules, refs, needed, cert :: certs => do
      let headNeeded := neededRuleInputs certs needed
      let result ← runSparseAction wires table registers rule.body refs
        headNeeded cert
      runSparseRules wires table registers rules result.refs needed certs
  | _, _, _, _ => none

def sparseRegistersMatch (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (cert : RulesCert) : Bool :=
  let registers := design.regs.toArray
  let needed := List.range registers.size
  match runSparseRules wires table registers design.rules .empty needed cert with
  | some refs => finalMetadataMatches program design.regs
      (refs.materialize registers) 0
  | none => false

private def takeMaskIndices (limit : Nat) : Nat → Nat → DecodeM Nat
  | 0, mask => pure mask
  | count + 1, mask => do
      let index ← takeWord
      guard (index < limit)
      guard (!mask.testBit index)
      takeMaskIndices limit count (mask ||| (1 <<< index))

private def takeMask (limit : Nat) : DecodeM Nat := do
  let count ← takeWord
  guard (count ≤ limit)
  takeMaskIndices limit count 0

private def takeSummary (limit : Nat) : DecodeM Summary := do
  let possible ← takeMask limit
  let definite ← takeMask limit
  pure { possible, definite }

private def takeSummaries (limit : Nat) : Nat → DecodeM (List Summary)
  | 0 => pure []
  | count + 1 => do
      let summary ← takeSummary limit
      pure (summary :: (← takeSummaries limit count))

private def mergePackedJoins (wires : Rope (List IndexedWire))
    (table : WireTable) (registers : Array Loom.Hw.RegDecl) (condition : Ref)
    (thenResult elseResult : Result) :
    List Nat → Array Ref → DecodeM (Array Ref)
  | [], output => pure output
  | index :: indices, output => do
      let actualIndex ← takeWord
      let outputNumber ← takeWord
      guard (actualIndex == index)
      let source ← registers[index]?
      let thenRef ← thenResult.refs[index]?
      let elseRef ← elseResult.refs[index]?
      match lookupIndexed? wires table outputNumber with
      | some ⟨_, actualWidth, .mux actualGuard actualThen actualElse⟩ =>
          guard (actualWidth == source.width)
          guard (condition == actualGuard)
          guard (thenRef == actualThen)
          guard (elseRef == actualElse)
          mergePackedJoins wires table registers condition thenResult elseResult
            indices (output.set! index (.wire outputNumber))
      | _ => failure

private def runPackedAction (wires : Rope (List IndexedWire))
    (table : WireTable) (registers : Array Loom.Hw.RegDecl) :
    Loom.Hw.Act → Array Ref → List Nat → DecodeM (Result × Summary)
  | .skip, refs, _ => do
      guard ((← takeWord) == 0)
      pure (unchanged refs, { possible := 0, definite := 0 })
  | .memWrite .., refs, _ => do
      guard ((← takeWord) == 1)
      pure (unchanged refs, { possible := 0, definite := 0 })
  | .write width name value, refs, needed => do
      guard ((← takeWord) == 2)
      let index ← takeWord
      let valueRef ← decodeRef registers (← takeWord)
      let source ← registers[index]?
      guard (source.name == name && source.width == width)
      let mask : Nat := 1 <<< index
      let summary := { possible := mask, definite := mask }
      if index ∉ needed then pure (unchanged refs, summary)
      else do
        guard (indexedExprMatches wires table
          (Loom.Hw.Compile.compileExpr value) valueRef)
        guard (index < refs.size)
        pure ({ refs := refs.set! index valueRef, changed := [index] }, summary)
  | .seq left right, refs, needed => do
      guard ((← takeWord) == 3)
      let claimed ← takeSummary registers.size
      let claimedRight ← takeSummary registers.size
      let leftNeeded := neededInputs claimedRight needed
      let (leftResult, leftSummary) ←
        runPackedAction wires table registers left refs leftNeeded
      let (rightResult, rightSummary) ←
        runPackedAction wires table registers right leftResult.refs needed
      guard (claimedRight == rightSummary)
      let actual := seqSummary leftSummary rightSummary
      guard (claimed == actual)
      pure ({ refs := rightResult.refs
              changed := changedOutputs actual needed }, actual)
  | .ite condition thenAction elseAction, refs, needed => do
      guard ((← takeWord) == 4)
      let claimed ← takeSummary registers.size
      let guardRef ← decodeRef registers (← takeWord)
      guard (indexedExprMatches wires table
        (Loom.Hw.Compile.compileExpr condition) guardRef)
      let changed := changedOutputs claimed needed
      let joinCount ← takeWord
      guard (joinCount == changed.length)
      let (thenResult, thenSummary) ←
        runPackedAction wires table registers thenAction refs changed
      let (elseResult, elseSummary) ←
        runPackedAction wires table registers elseAction refs changed
      let actual := iteSummary thenSummary elseSummary
      guard (claimed == actual)
      let merged ← mergePackedJoins wires table registers guardRef thenResult
        elseResult changed refs
      pure ({ refs := merged, changed }, actual)

private def neededSummaryInputs (summaries : List Summary)
    (needed : List Nat) : List Nat :=
  summaries.foldr (fun summary result => neededInputs summary result) needed

private def runPackedRules (wires : Rope (List IndexedWire))
    (table : WireTable) (registers : Array Loom.Hw.RegDecl) :
    List Loom.Hw.Rule → List Summary → Array Ref → List Nat →
      DecodeM (Array Ref)
  | [], [], refs, _ => pure refs
  | rule :: rules, claimed :: claimedTail, refs, needed => do
      let headNeeded := neededSummaryInputs claimedTail needed
      let (result, actual) ← runPackedAction wires table registers rule.body refs
        headNeeded
      guard (claimed == actual)
      runPackedRules wires table registers rules claimedTail result.refs needed
  | _, _, _, _ => failure

/-- Stream-decode and validate compact untrusted release data without ever
materializing the full certificate tree. -/
def packedRegistersMatch (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable)
    (encoded : String) : Bool :=
  let registers := design.regs.toArray
  let needed := List.range registers.size
  let bytes := encoded.toUTF8
  match (do
      let count ← takeWord
      guard (count == design.rules.length)
      let summaries ← takeSummaries registers.size count
      runPackedRules wires table registers design.rules summaries
        (initialRefs registers) needed).run { bytes } with
  | some (refs, state) =>
      state.cursor == bytes.size &&
        finalMetadataMatches program design.regs refs 0
  | none => false

end Loom.Release.Symbolic.ActionWide
