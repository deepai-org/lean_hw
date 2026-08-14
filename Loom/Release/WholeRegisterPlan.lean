-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.WholeRegisterPlan
import Loom.Release.SymbolicSound

/-!
# Bounded SSA checks for shared register plans

These checks consume the compact plans produced by `Compile.Plans.ofAction`.
Unlike `Symbolic.nextRegMatches`, they never inspect the original source
action.  Once the shared plan family has been accepted, each concrete register
root therefore costs only its relevant writes and control-flow nodes.
-/

namespace Loom.Release.Symbolic.WholePlan

open Loom.Release.SSA
open Loom.Hw.Compile

/-- Validate one compact register plan against a concrete SSA root. -/
def planMatches (wires : Rope (List IndexedWire)) (table : WireTable) :
    {width : Nat} → RegPlan width → Option Ref → Ref → NextRegCert → Bool
  | _, .same, some current, out, .same => current == out
  | _, .write value, _, out, .write =>
      indexedExprMatches wires table (compileExpr value) out
  | width, .writeSlice lo fieldWidth _ value, some current, out, .writeSlice =>
      indexedInsertMatches wires table width lo fieldWidth value current out
  | _, .seq left right, current, out, .seq mid leftCert rightCert =>
      match mid with
      | some mid =>
          planMatches wires table left current mid leftCert &&
            planMatches wires table right (some mid) out rightCert
      | none => planMatches wires table right none out rightCert
  | width, .ite guard thenPlan elsePlan, current, .wire number,
      .ite thenCert elseCert =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .mux guardRef thenRef elseRef⟩ =>
          actualWidth == width &&
            indexedExprMatches wires table (compileExpr guard) guardRef &&
            planMatches wires table thenPlan current thenRef thenCert &&
            planMatches wires table elsePlan current elseRef elseCert
      | _ => false
  | width, .ite guard thenPlan elsePlan, current, .namedWire number _,
      .ite thenCert elseCert =>
      match lookupIndexed? wires table number with
      | some ⟨_, actualWidth, .mux guardRef thenRef elseRef⟩ =>
          actualWidth == width &&
            indexedExprMatches wires table (compileExpr guard) guardRef &&
            planMatches wires table thenPlan current thenRef thenCert &&
            planMatches wires table elsePlan current elseRef elseCert
      | _ => false
  | _, _, _, _, _ => false

/-- Validate an ordered list of compact rule plans. -/
def rulesMatch (wires : Rope (List IndexedWire)) (table : WireTable) :
    {width : Nat} → List (RegPlan width) → Option Ref → Ref →
      NextRulesCert → Bool
  | _, [], some current, out, .nil => current == out
  | _, plan :: plans, current, out, .cons mid head tail =>
      match mid with
      | some mid =>
          planMatches wires table plan current mid head &&
            rulesMatch wires table plans (some mid) out tail
      | none => rulesMatch wires table plans none out tail
  | _, _, _, _, _ => false

/-! ## Compositional acceptance

The symbolic elaborator uses these small constructor lemmas to build a proof
whose shape follows the compact plan.  Named child proofs remain opaque to the
kernel, avoiding normalization of the complete plan/certificate equality.
-/

theorem planMatches_same
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (current : Ref) :
    planMatches wires table (RegPlan.same : RegPlan width) (some current)
      current .same = true := by
  simp [planMatches]

theorem planMatches_write
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (value : Loom.Hw.Expr width) (out : Ref)
    (accepted : indexedExprMatches wires table (compileExpr value) out = true) :
    planMatches wires table (.write value) none out .write = true := by
  simpa [planMatches] using accepted

theorem planMatches_write_current
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (value : Loom.Hw.Expr width) (current out : Ref)
    (accepted : indexedExprMatches wires table (compileExpr value) out = true) :
    planMatches wires table (.write value) (some current) out .write = true := by
  simpa [planMatches] using accepted

theorem planMatches_writeSlice
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (lo fieldWidth : Nat) (inBounds : lo + fieldWidth ≤ width)
    (value : Loom.Hw.Expr fieldWidth) (current out : Ref)
    (accepted : indexedInsertMatches wires table width lo fieldWidth value
      current out = true) :
    planMatches wires table (.writeSlice lo fieldWidth inBounds value)
      (some current) out .writeSlice = true := by
  simpa [planMatches] using accepted

theorem planMatches_seq_named
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (left right : RegPlan width) (current : Option Ref) (mid out : Ref)
    (leftCert rightCert : NextRegCert)
    (leftAccepted : planMatches wires table left current mid leftCert = true)
    (rightAccepted : planMatches wires table right (some mid) out rightCert = true) :
    planMatches wires table (.seq left right) current out
      (.seq (some mid) leftCert rightCert) = true := by
  simp [planMatches, leftAccepted, rightAccepted]

theorem planMatches_seq_discard
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (left right : RegPlan width) (current : Option Ref) (out : Ref)
    (leftCert rightCert : NextRegCert)
    (rightAccepted : planMatches wires table right none out rightCert = true) :
    planMatches wires table (.seq left right) current out
      (.seq none leftCert rightCert) = true := by
  simpa [planMatches] using rightAccepted

theorem planMatches_ite
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (guard : Loom.Hw.Expr 1) (thenPlan elsePlan : RegPlan width)
    (current : Option Ref) (number : Nat) (guardRef thenRef elseRef : Ref)
    (thenCert elseCert : NextRegCert)
    (lookupAccepted : lookupIndexed? wires table number = some
      { number := number, width := width,
        rhs := .mux guardRef thenRef elseRef })
    (guardAccepted : indexedExprMatches wires table (compileExpr guard)
      guardRef = true)
    (thenAccepted : planMatches wires table thenPlan current thenRef
      thenCert = true)
    (elseAccepted : planMatches wires table elsePlan current elseRef
      elseCert = true) :
    planMatches wires table (.ite guard thenPlan elsePlan) current
      (.wire number) (.ite thenCert elseCert) = true := by
  simp [planMatches, lookupAccepted, guardAccepted, thenAccepted, elseAccepted]

theorem planMatches_ite_named
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (guard : Loom.Hw.Expr 1) (thenPlan elsePlan : RegPlan width)
    (current : Option Ref) (number : Nat) (name : String)
    (guardRef thenRef elseRef : Ref) (thenCert elseCert : NextRegCert)
    (lookupAccepted : lookupIndexed? wires table number = some
      { number := number, width := width,
        rhs := .mux guardRef thenRef elseRef })
    (guardAccepted : indexedExprMatches wires table (compileExpr guard)
      guardRef = true)
    (thenAccepted : planMatches wires table thenPlan current thenRef
      thenCert = true)
    (elseAccepted : planMatches wires table elsePlan current elseRef
      elseCert = true) :
    planMatches wires table (.ite guard thenPlan elsePlan) current
      (.namedWire number name) (.ite thenCert elseCert) = true := by
  simp [planMatches, lookupAccepted, guardAccepted, thenAccepted, elseAccepted]

theorem rulesMatch_nil
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (current : Ref) :
    rulesMatch wires table ([] : List (RegPlan width)) (some current) current
      .nil = true := by
  simp [rulesMatch]

theorem rulesMatch_cons_named
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (plan : RegPlan width) (plans : List (RegPlan width))
    (current : Option Ref) (mid out : Ref) (head : NextRegCert)
    (tail : NextRulesCert)
    (headAccepted : planMatches wires table plan current mid head = true)
    (tailAccepted : rulesMatch wires table plans (some mid) out tail = true) :
    rulesMatch wires table (plan :: plans) current out
      (.cons (some mid) head tail) = true := by
  simp [rulesMatch, headAccepted, tailAccepted]

theorem rulesMatch_cons_discard
    (wires : Rope (List IndexedWire)) (table : WireTable) (width : Nat)
    (plan : RegPlan width) (plans : List (RegPlan width))
    (current : Option Ref) (out : Ref) (head : NextRegCert)
    (tail : NextRulesCert)
    (tailAccepted : rulesMatch wires table plans none out tail = true) :
    rulesMatch wires table (plan :: plans) current out
      (.cons none head tail) = true := by
  simpa [rulesMatch] using tailAccepted

/-- A successful compact-plan check denotes `RegPlan.apply` in the raw
structural SSA semantics. -/
theorem planMatches_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) {width : Nat} :
    ∀ (plan : RegPlan width) (current : Option Ref) (out : Ref)
      (cert : NextRegCert),
      planMatches indexeds table plan current out cert = true →
      ∀ cur : Loom.Emit.MicroVerilog.Expr width,
        RawCurrentMatches program table cur current →
        RawExprMatches program table (plan.apply cur) out := by
  intro plan
  induction plan <;> intro current out cert accepted cur currentMatches
  · cases current <;> cases cert <;> simp [planMatches] at accepted
    subst out
    exact currentMatches
  · rename_i value
    cases cert <;> simp [planMatches] at accepted
    exact indexedExprMatches_raw program hmatches table _ _ accepted
  · rename_i lo fieldWidth inBounds value
    cases current <;> cases cert <;> simp [planMatches] at accepted
    exact indexedInsertMatches_raw program hmatches table lo value cur _ out
      currentMatches accepted
  · rename_i left right leftIH rightIH
    cases cert with
    | seq mid leftCert rightCert =>
        cases mid with
        | none =>
            simp only [planMatches] at accepted
            simpa only [RegPlan.apply] using
              rightIH none out rightCert accepted (left.apply cur) trivial
        | some mid =>
            simp only [planMatches, Bool.and_eq_true] at accepted
            have leftMatches := leftIH current mid leftCert accepted.1 cur
              currentMatches
            simpa only [RegPlan.apply] using
              rightIH (some mid) out rightCert accepted.2 (left.apply cur)
                leftMatches
    | same => simp [planMatches] at accepted
    | write => simp [planMatches] at accepted
    | writeSlice => simp [planMatches] at accepted
    | ite thenCert elseCert => simp [planMatches] at accepted
  · rename_i guard thenPlan elsePlan thenIH elseIH
    cases cert with
    | ite thenCert elseCert =>
        cases out with
        | reg name => simp [planMatches] at accepted
        | namedWire number name =>
            apply RawExprMatches.named
            simp only [planMatches] at accepted
            cases found : lookupIndexed? indexeds table number with
            | none => simp [found] at accepted
            | some indexed =>
                obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
                cases rhs <;> simp [found] at accepted
                case mux guardRef thenRef elseRef =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth,
                        .mux guardRef thenRef elseRef⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .mux guardRef thenRef elseRef⟩) rawMatch
                  exact .mux rawAt (widthEq.trans accepted.1.1.1) rhsEq
                    (indexedExprMatches_raw program hmatches table _ _
                      accepted.1.1.2)
                    (thenIH current thenRef thenCert accepted.1.2 cur
                      currentMatches)
                    (elseIH current elseRef elseCert accepted.2 cur
                      currentMatches)
        | wire number =>
            simp only [planMatches] at accepted
            cases found : lookupIndexed? indexeds table number with
            | none => simp [found] at accepted
            | some indexed =>
                obtain ⟨indexedNumber, actualWidth, rhs⟩ := indexed
                cases rhs <;> simp [found] at accepted
                case mux guardRef thenRef elseRef =>
                  obtain ⟨raw, rawAt, rawMatch⟩ :=
                    lookupIndexed_rawWireAt program hmatches table number
                      ⟨indexedNumber, actualWidth,
                        .mux guardRef thenRef elseRef⟩ found
                  obtain ⟨widthEq, rhsEq⟩ := IndexedWire.matchesRaw_width_rhs
                    (indexed := ⟨indexedNumber, actualWidth,
                      .mux guardRef thenRef elseRef⟩) rawMatch
                  exact .mux rawAt (widthEq.trans accepted.1.1.1) rhsEq
                    (indexedExprMatches_raw program hmatches table _ _
                      accepted.1.1.2)
                    (thenIH current thenRef thenCert accepted.1.2 cur
                      currentMatches)
                    (elseIH current elseRef elseCert accepted.2 cur
                      currentMatches)
    | same => simp [planMatches] at accepted
    | write => simp [planMatches] at accepted
    | writeSlice => simp [planMatches] at accepted
    | seq mid leftCert rightCert => simp [planMatches] at accepted

/-- Soundness of the compact ordered-rule fold. -/
theorem rulesMatch_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) {width : Nat} :
    ∀ (plans : List (RegPlan width)) (current : Option Ref) (out : Ref)
      (cert : NextRulesCert),
      rulesMatch indexeds table plans current out cert = true →
      ∀ cur : Loom.Emit.MicroVerilog.Expr width,
        RawCurrentMatches program table cur current →
        RawExprMatches program table
          (plans.foldl (fun value plan => plan.apply value) cur) out := by
  intro plans
  induction plans with
  | nil =>
      intro current out cert accepted cur currentMatches
      cases current <;> cases cert <;> simp [rulesMatch] at accepted
      rw [← accepted]
      exact currentMatches
  | cons plan plans plansIH =>
      intro current out cert accepted cur currentMatches
      cases cert with
      | nil => simp [rulesMatch] at accepted
      | cons mid head tail =>
          cases mid with
          | none =>
              simp only [rulesMatch] at accepted
              simpa only [List.foldl_cons] using
                plansIH none out tail accepted (plan.apply cur) trivial
          | some mid =>
              simp only [rulesMatch, Bool.and_eq_true] at accepted
              have headMatches := planMatches_raw program hmatches table plan
                current mid head accepted.1 cur currentMatches
              simpa only [List.foldl_cons] using
                plansIH (some mid) out tail accepted.2 (plan.apply cur)
                  headMatches

/-- The compact checker can be used directly in place of an action traversal;
the established projection theorem supplies the bridge to `nextReg`. -/
theorem planMatches_action_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (action : Loom.Hw.Act) (name : String) (width : Nat)
    (current : Option Ref) (out : Ref) (cert : NextRegCert)
    (accepted : planMatches indexeds table (RegPlan.ofAction name width action)
      current out cert = true) :
    ∀ cur : Loom.Emit.MicroVerilog.Expr width,
      RawCurrentMatches program table cur current →
      RawExprMatches program table
        (nextReg name width action cur) out := by
  intro cur currentMatches
  rw [← RegPlan.apply_ofAction action name width cur]
  exact planMatches_raw program hmatches table _ _ _ _ accepted cur currentMatches

/-- Ordered-rule form of `planMatches_action_raw`. -/
theorem rulesMatch_actions_raw
    (program : Program) {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (rules : List Loom.Hw.Rule)
    (name : String) (width : Nat) (current : Option Ref) (out : Ref)
    (cert : NextRulesCert)
    (accepted : rulesMatch indexeds table
      (rules.map fun rule => RegPlan.ofAction name width rule.body)
      current out cert = true) :
    ∀ cur : Loom.Emit.MicroVerilog.Expr width,
      RawCurrentMatches program table cur current →
      RawExprMatches program table
        (rules.foldl (fun value rule => nextReg name width rule.body value) cur)
        out := by
  intro cur currentMatches
  rw [← RegPlan.fold_rulePlans rules name width cur]
  exact rulesMatch_raw program hmatches table _ _ _ _ accepted cur currentMatches

/-- Metadata plus one compact rule-plan certificate yields the existing
certificate-free register behavior proposition. -/
theorem registerBehaviorAt_of_plan_checks
    (design : Loom.Hw.Design) (program : Program)
    {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) (index : Nat) (source : Loom.Hw.RegDecl) (root : Ref)
    (cert : NextRulesCert)
    (sourceFound : design.regs[index]? = some source)
    (metadata : indexedRegisterMetadataMatchesAt design program index root = true)
    (rules : rulesMatch indexeds table
      (design.rules.map fun rule =>
        RegPlan.ofAction source.name source.width rule.body)
      (some (.reg source.name)) root cert = true) :
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
        rulesMatch_actions_raw program hmatches table design.rules source.name
          source.width (some (.reg source.name)) root cert rules
          (.reg source.width source.name) (.reg source.width source.name)⟩

/-- One concrete root and compact ordered-rule certificate in a bounded
register block. -/
structure RegisterPlanRoot where
  root : Ref
  cert : NextRulesCert

/-- Proof that a bounded declaration list is a consecutive slice of the full
source design. -/
inductive RegistersFrom (design : Loom.Hw.Design) :
    Nat → List Loom.Hw.RegDecl → Prop
  | nil (start : Nat) : RegistersFrom design start []
  | cons {start : Nat} {source : Loom.Hw.RegDecl}
      {sources : List Loom.Hw.RegDecl} :
      design.regs[start]? = some source →
      RegistersFrom design (start + 1) sources →
      RegistersFrom design start (source :: sources)

/-- Public register-root entries denoted by a consecutive plan block. -/
def registerRootEntries : Nat → List RegisterPlanRoot → List RegisterRoot
  | _, [] => []
  | start, entry :: entries =>
      { index := start, root := entry.root } ::
        registerRootEntries (start + 1) entries

/-- Check a bounded register block.  The shared `RulePlans` value is computed
once for the entire block; recursion over individual entries only inspects the
already-projected compact plans. -/
def blockMatches (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable) :
    Nat → {registers : List Loom.Hw.RegDecl} → RulePlans registers →
      List RegisterPlanRoot → Bool
  | _, [], .nil, entries => entries.isEmpty
  | start, source :: _, .cons plans rest, entries =>
      match entries with
      | [] => false
      | entry :: entries =>
          indexedRegisterMetadataMatchesAt design program start entry.root &&
          rulesMatch wires table plans (some (.reg source.name)) entry.root
            entry.cert &&
          blockMatches design program wires table (start + 1) rest entries

theorem blockMatches_nil
    (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable) (start : Nat) :
    blockMatches design program wires table start RulePlans.nil [] = true := by
  rfl

theorem blockMatches_cons
    (design : Loom.Hw.Design) (program : Program)
    (wires : Rope (List IndexedWire)) (table : WireTable) (start : Nat)
    (source : Loom.Hw.RegDecl) (sources : List Loom.Hw.RegDecl)
    (plans : List (RegPlan source.width)) (rest : RulePlans sources)
    (entry : RegisterPlanRoot) (entries : List RegisterPlanRoot)
    (metadataAccepted : indexedRegisterMetadataMatchesAt design program start
      entry.root = true)
    (rulesAccepted : rulesMatch wires table plans (some (.reg source.name))
      entry.root entry.cert = true)
    (restAccepted : blockMatches design program wires table (start + 1) rest
      entries = true) :
    blockMatches design program wires table start (.cons plans rest)
      (entry :: entries) = true := by
  simp [blockMatches, metadataAccepted, rulesAccepted, restAccepted]

/-- Soundness of one bounded shared-plan block. -/
theorem blockMatches_sound
    (design : Loom.Hw.Design) (program : Program)
    {indexeds : Rope (List IndexedWire)}
    (hmatches : IndexedRopeMatches 0 program.wires indexeds)
    (table : WireTable) :
    ∀ (start : Nat) (registers : List Loom.Hw.RegDecl)
      (plans : RulePlans registers) (entries : List RegisterPlanRoot),
      RegistersFrom design start registers →
      RulePlans.Projects design.rules plans →
      blockMatches design program indexeds table start plans entries = true →
      RegisterBehaviorsFrom design program table start
        (registerRootEntries start entries) := by
  intro start registers
  induction registers generalizing start with
  | nil =>
      intro plans entries aligned projects accepted
      cases plans
      cases entries with
      | nil => exact .nil start
      | cons entry entries => simp [blockMatches] at accepted
  | cons source sources ih =>
      intro plans entries aligned projects accepted
      cases plans with
      | cons planList planRest =>
        cases entries with
        | nil => simp [blockMatches] at accepted
        | cons entry entries =>
          cases aligned with
          | cons sourceFound restAligned =>
            simp only [blockMatches, Bool.and_eq_true] at accepted
            have headAccepted := accepted.1.2
            rw [projects.1] at headAccepted
            have behavior := registerBehaviorAt_of_plan_checks design program
              hmatches table start source entry.root entry.cert sourceFound
              accepted.1.1 headAccepted
            exact .cons rfl behavior
              (ih (start := start + 1) planRest entries restAligned projects.2
                accepted.2)

theorem RegisterBehaviorsFrom.head
    {design : Loom.Hw.Design} {program : Program} {table : WireTable}
    {start : Nat} {entry : RegisterRoot} {entries : List RegisterRoot}
    (behaviors : RegisterBehaviorsFrom design program table start
      (entry :: entries)) :
    RegisterBehaviorAt design program table entry.index entry.root := by
  cases behaviors with
  | cons _ behavior _ => exact behavior

theorem RegisterBehaviorsFrom.tail
    {design : Loom.Hw.Design} {program : Program} {table : WireTable}
    {start : Nat} {entry : RegisterRoot} {entries : List RegisterRoot}
    (behaviors : RegisterBehaviorsFrom design program table start
      (entry :: entries)) :
    RegisterBehaviorsFrom design program table (start + 1) entries := by
  cases behaviors with
  | cons _ _ tail => exact tail

end Loom.Release.Symbolic.WholePlan
