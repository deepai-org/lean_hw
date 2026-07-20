-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate
import Loom.Release.SymbolicElaborate
import Loom.Release.WholeRegisterPlan
import Loom.Release.ActionWideRegister
import Loom.Release.ActionStateDag
import Loom.Hw.CompileCorrect
import Lean.Elab.Term
import Lean.Elab.Command
import Lean.Meta.Tactic.AuxLemma
import Lean.Meta.Tactic.Simp
import Lean.Meta.Reduce
import Lean.Meta.Eval
import Batteries.Lean.TagAttribute

/-!
# Compositional symbolic release proofs

Large source actions are checked a subtree at a time. Each recursive proof is
installed as an auxiliary theorem before its parent is constructed, so kernel
checking a parent uses the child's statement without normalizing its proof.
-/

open Lean Elab Term Meta
open Loom.Release

namespace Loom.Release.Symbolic

/-- Generated bounded register-lookup leaves. The term elaborator seeds its
memo table from these already kernel-checked theorem constants. -/
initialize releaseReadLeafAttr : TagAttribute ←
  registerTagAttribute `release_read_leaf
    "register-read leaf available to compositional release certificates"

/-- Generated bounded source-declaration leaves used by `action_decls_ok`. -/
initialize releaseDeclLeafAttr : TagAttribute ←
  registerTagAttribute `release_decl_leaf
    "source declaration leaf available to compositional release certificates"

private def cacheClosedProof (type proof : Expr) : MetaM Expr := do
  let lemma ← withOptions (Elab.async.set · false) do
    mkAuxLemma [] type proof (kind? := `_symbolicNoWrite)
  pure (.const lemma [])

private def cachePropProof (type : Expr) (proof : MetaM Expr) : MetaM Expr := do
  cacheClosedProof type (← proof)

private abbrev ProofCache := IO.Ref (Std.HashMap Expr Expr)

private unsafe def normalizeRegisterExpression (expression : Expr) : MetaM Expr := do
  let args := expression.getAppArgs
  let simpContext ← Simp.Context.mkDefault
  let (widthResult, _) ← simp args[args.size - 2]! simpContext
  let (nameResult, _) ← simp args[args.size - 1]! simpContext
  let reducedWidth ← Lean.Meta.reduce widthResult.expr
  let reducedName ← Lean.Meta.reduce nameResult.expr
  let some width ← getNatValue? reducedWidth
    | throwError "design_reads_valid: register width did not reduce: {reducedWidth}"
  let name ← evalExpr String (mkConst ``String) reducedName
  pure <| mkApp2 (mkConst ``Loom.Hw.Expr.reg) (toExpr width) (toExpr name)

private def cachePropProofMemo (cache : ProofCache) (type : Expr)
    (proof : MetaM Expr) : MetaM Expr := do
  if let some cached := (← cache.get).get? type then
    return cached
  let cached ← cachePropProof type proof
  cache.modify (fun entries => entries.insert type cached)
  pure cached

private unsafe def seedReleaseReadProofs (cache : ProofCache) : MetaM Unit := do
  let env ← getEnv
  for declaration in releaseReadLeafAttr.getDecls env do
    let info ← getConstInfo declaration
    unless info.levelParams.isEmpty || info.type.hasFVar || info.type.hasMVar do
      throwError "release_read_leaf theorem must be closed: {declaration}"
    let args := info.type.getAppArgs
    let type ← if info.type.getAppFn.constName? == some ``HwExprRegistersValid &&
        !args.isEmpty then
      let expression := args[args.size - 1]!
      if expression.getAppFn.constName? == some ``Loom.Hw.Expr.reg then
        mkAppM ``HwExprRegistersValid
          #[args[0]!, ← normalizeRegisterExpression expression]
      else pure info.type
    else pure info.type
    cache.modify (fun entries => entries.insert type (.const declaration []))

private unsafe def normalizeDeclAcceptedType (type : Expr) : MetaM Expr := do
  let equalityArgs := type.getAppArgs
  unless type.getAppFn.constName? == some ``Eq && equalityArgs.size == 3 do
    return type
  let lhs := equalityArgs[1]!
  let args := lhs.getAppArgs
  if lhs.getAppFn.constName? == some ``Loom.Hw.Compile.registerDeclOk &&
      args.size == 3 then
    let widthExpr ← Lean.Meta.reduce args[1]!
    let nameExpr ← Lean.Meta.reduce args[2]!
    let some width ← getNatValue? widthExpr
      | throwError "action_decls_ok: register width did not reduce: {widthExpr}"
    let name ← evalExpr String (mkConst ``String) nameExpr
    return ← mkEq (← mkAppM ``Loom.Hw.Compile.registerDeclOk
      #[args[0]!, toExpr width, toExpr name]) (mkConst ``Bool.true)
  if lhs.getAppFn.constName? == some ``Loom.Hw.Compile.memoryDeclOk &&
      args.size == 4 then
    let awExpr ← Lean.Meta.reduce args[1]!
    let dwExpr ← Lean.Meta.reduce args[2]!
    let nameExpr ← Lean.Meta.reduce args[3]!
    let some aw ← getNatValue? awExpr
      | throwError "action_decls_ok: address width did not reduce: {awExpr}"
    let some dw ← getNatValue? dwExpr
      | throwError "action_decls_ok: data width did not reduce: {dwExpr}"
    let name ← evalExpr String (mkConst ``String) nameExpr
    return ← mkEq (← mkAppM ``Loom.Hw.Compile.memoryDeclOk
      #[args[0]!, toExpr aw, toExpr dw, toExpr name]) (mkConst ``Bool.true)
  pure type

private unsafe def seedReleaseDeclProofs (cache : ProofCache) : MetaM Unit := do
  let env ← getEnv
  for declaration in releaseDeclLeafAttr.getDecls env do
    let info ← getConstInfo declaration
    unless info.levelParams.isEmpty || info.type.hasFVar || info.type.hasMVar do
      throwError "release_decl_leaf theorem must be closed: {declaration}"
    let type ← normalizeDeclAcceptedType info.type
    cache.modify (fun entries => entries.insert type (.const declaration []))

private def mkAndProof (left right : Expr) : MetaM Expr :=
  mkAppM ``And.intro #[left, right]

private partial def exposeHwExpr (expression : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf expression
  if let some name := reduced.getAppFn.constName? then
    if name == ``Loom.Hw.Expr.lit || name == ``Loom.Hw.Expr.reg ||
        name == ``Loom.Hw.Expr.memRead || name == ``Loom.Hw.Expr.and ||
        name == ``Loom.Hw.Expr.or || name == ``Loom.Hw.Expr.xor ||
        name == ``Loom.Hw.Expr.not || name == ``Loom.Hw.Expr.add ||
        name == ``Loom.Hw.Expr.sub || name == ``Loom.Hw.Expr.shl ||
        name == ``Loom.Hw.Expr.shr || name == ``Loom.Hw.Expr.eq ||
        name == ``Loom.Hw.Expr.ult || name == ``Loom.Hw.Expr.slt ||
        name == ``Loom.Hw.Expr.mux || name == ``Loom.Hw.Expr.slice ||
        name == ``Loom.Hw.Expr.zext || name == ``Loom.Hw.Expr.sext then
      return reduced
  match ← unfoldDefinition? reduced (ignoreTransparency := true) with
  | some unfolded => exposeHwExpr unfolded
  | none =>
      try
        let unfoldedFn ← unfoldDefinition reduced.getAppFn
        exposeHwExpr (mkAppN unfoldedFn reduced.getAppArgs)
      catch _ => return reduced

private unsafe def proveHwExprRegistersValid (cache : ProofCache)
    (program expression : Expr) : MetaM Expr := do
  let reduced ← exposeHwExpr expression
  let args := reduced.getAppArgs
  let type ← mkAppM ``HwExprRegistersValid #[program, reduced]
  if let some cached := (← cache.get).get? type then
    return cached
  if reduced.getAppFn.constName? == some ``Loom.Hw.Expr.reg then
    let normalized ← normalizeRegisterExpression reduced
    let normalizedType ← mkAppM ``HwExprRegistersValid #[program, normalized]
    if let some cached := (← cache.get).get? normalizedType then
      return cached
    let env ← getEnv
    unless releaseReadLeafAttr.getDecls env |>.isEmpty do
      throwError "design_reads_valid: no generated register leaf for {normalized}"
  match reduced.getAppFn.constName? with
  | some ``Loom.Hw.Expr.lit => pure (mkConst ``True.intro)
  | some ``Loom.Hw.Expr.reg =>
      let check ← mkAppM ``hwExprRegistersValidB #[program, reduced]
      let acceptedType ← mkEq check (mkConst ``Bool.true)
      let accepted ← cachePropProofMemo cache acceptedType (mkDecideProof acceptedType)
      mkAppM ``hwExprRegistersValidB_sound #[reduced, accepted]
  | some ``Loom.Hw.Expr.memRead | some ``Loom.Hw.Expr.not =>
      let child := args[args.size - 1]!
      let childType ← mkAppM ``HwExprRegistersValid #[program, child]
      cachePropProofMemo cache childType (proveHwExprRegistersValid cache program child)
  | some ``Loom.Hw.Expr.slice =>
      let child := args[args.size - 3]!
      let childType ← mkAppM ``HwExprRegistersValid #[program, child]
      cachePropProofMemo cache childType (proveHwExprRegistersValid cache program child)
  | some ``Loom.Hw.Expr.zext | some ``Loom.Hw.Expr.sext =>
      let child := args[args.size - 2]!
      let childType ← mkAppM ``HwExprRegistersValid #[program, child]
      cachePropProofMemo cache childType (proveHwExprRegistersValid cache program child)
  | some ``Loom.Hw.Expr.and | some ``Loom.Hw.Expr.or |
    some ``Loom.Hw.Expr.xor | some ``Loom.Hw.Expr.add |
    some ``Loom.Hw.Expr.sub | some ``Loom.Hw.Expr.shl |
    some ``Loom.Hw.Expr.shr | some ``Loom.Hw.Expr.eq |
    some ``Loom.Hw.Expr.ult | some ``Loom.Hw.Expr.slt =>
      let left := args[args.size - 2]!
      let right := args[args.size - 1]!
      let leftType ← mkAppM ``HwExprRegistersValid #[program, left]
      let rightType ← mkAppM ``HwExprRegistersValid #[program, right]
      mkAndProof
        (← cachePropProofMemo cache leftType
          (proveHwExprRegistersValid cache program left))
        (← cachePropProofMemo cache rightType
          (proveHwExprRegistersValid cache program right))
  | some ``Loom.Hw.Expr.mux =>
      let condition := args[args.size - 3]!
      let yes := args[args.size - 2]!
      let no := args[args.size - 1]!
      let conditionType ← mkAppM ``HwExprRegistersValid #[program, condition]
      let yesType ← mkAppM ``HwExprRegistersValid #[program, yes]
      let noType ← mkAppM ``HwExprRegistersValid #[program, no]
      let conditionProof ← cachePropProofMemo cache conditionType
        (proveHwExprRegistersValid cache program condition)
      let yesProof ← cachePropProofMemo cache yesType
        (proveHwExprRegistersValid cache program yes)
      let noProof ← cachePropProofMemo cache noType
        (proveHwExprRegistersValid cache program no)
      mkAndProof conditionProof (← mkAndProof yesProof noProof)
  | _ => throwError "design_reads_valid: expression did not reduce to a constructor: {reduced}"

private partial def exposeAction (action : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf action
  if let some name := reduced.getAppFn.constName? then
    if name == ``Loom.Hw.Act.skip || name == ``Loom.Hw.Act.seq ||
        name == ``Loom.Hw.Act.ite || name == ``Loom.Hw.Act.write ||
        name == ``Loom.Hw.Act.memWrite then
      return reduced
  match ← unfoldDefinition? reduced (ignoreTransparency := true) with
  | some unfolded => exposeAction unfolded
  | none =>
      try
        let unfoldedFn ← unfoldDefinition reduced.getAppFn
        exposeAction (mkAppN unfoldedFn reduced.getAppArgs)
      catch _ => return reduced

private partial def expandListFoldr (function initial values : Expr) : MetaM Expr := do
  let values ← withTransparency .all <| whnf values
  let args := values.getAppArgs
  match values.getAppFn.constName? with
  | some ``List.nil => pure initial
  | some ``List.cons =>
      let head := args[args.size - 2]!
      let tail := args[args.size - 1]!
      pure (mkApp2 function head (← expandListFoldr function initial tail))
  | _ => throwError "design_reads_valid: List.foldr input did not reduce to a list: {values}"

private def transportActRegistersValid (program actionEq proof : Expr) : MetaM Expr := do
  let equalityType ← inferType actionEq
  let actionType := equalityType.getAppArgs[0]!
  let motive ← withLocalDeclD `action actionType fun act => do
    let body ← mkAppM ``ActRegistersValid #[program, act]
    mkLambdaFVars #[act] body
  let propositionEq ← mkCongrArg motive actionEq
  mkAppM ``Eq.mpr #[propositionEq, proof]

private def transportActionDeclsOk (design actionEq proof : Expr) : MetaM Expr := do
  let equalityType ← inferType actionEq
  let actionType := equalityType.getAppArgs[0]!
  let motive ← withLocalDeclD `action actionType fun act => do
    let check ← mkAppM ``Loom.Hw.Compile.actionDeclsOk #[design, act]
    let body ← mkEq check (mkConst ``Bool.true)
    mkLambdaFVars #[act] body
  let propositionEq ← mkCongrArg motive actionEq
  mkAppM ``Eq.mpr #[propositionEq, proof]

private unsafe def proveActionDeclsOk (cache : ProofCache)
    (design action : Expr) : MetaM Expr := do
  let reduced ← exposeAction action
  let args := reduced.getAppArgs
  match reduced.getAppFn.constName? with
  | some ``Loom.Hw.Act.skip =>
      let check ← mkAppM ``Loom.Hw.Compile.actionDeclsOk #[design, reduced]
      mkEqRefl check
  | some ``Loom.Hw.Act.seq | some ``Loom.Hw.Act.ite =>
      let left := args[args.size - 2]!
      let right := args[args.size - 1]!
      let leftCheck ← mkAppM ``Loom.Hw.Compile.actionDeclsOk #[design, left]
      let rightCheck ← mkAppM ``Loom.Hw.Compile.actionDeclsOk #[design, right]
      let leftType ← mkEq leftCheck (mkConst ``Bool.true)
      let rightType ← mkEq rightCheck (mkConst ``Bool.true)
      let leftProof ← cachePropProofMemo cache leftType
        (proveActionDeclsOk cache design left)
      let rightProof ← cachePropProofMemo cache rightType
        (proveActionDeclsOk cache design right)
      let conjunction ← mkAndProof leftProof rightProof
      let decomposition ← mkAppM ``Bool.and_eq_true #[leftCheck, rightCheck]
      mkAppM ``Eq.mpr #[decomposition, conjunction]
  | some ``Loom.Hw.Act.write =>
      let width := args[args.size - 3]!
      let name := args[args.size - 2]!
      let leaf ← mkAppM ``Loom.Hw.Compile.registerDeclOk #[design, width, name]
      let leafType ← normalizeDeclAcceptedType
        (← mkEq leaf (mkConst ``Bool.true))
      if let some proof := (← cache.get).get? leafType then
        pure proof
      else
        throwError "action_decls_ok: no generated register declaration leaf for {leafType}"
  | some ``Loom.Hw.Act.memWrite =>
      let aw := args[args.size - 6]!
      let dw := args[args.size - 5]!
      let name := args[args.size - 4]!
      let leaf ← mkAppM ``Loom.Hw.Compile.memoryDeclOk #[design, aw, dw, name]
      let leafType ← normalizeDeclAcceptedType
        (← mkEq leaf (mkConst ``Bool.true))
      if let some proof := (← cache.get).get? leafType then
        pure proof
      else
        throwError "action_decls_ok: no generated memory declaration leaf for {leafType}"
  | some ``List.foldr =>
      let function := args[args.size - 3]!
      let initial := args[args.size - 2]!
      let values := args[args.size - 1]!
      let simpContext ← Simp.Context.mkDefault
      let (result, _) ← simp values simpContext
      let expanded ← expandListFoldr function initial result.expr
      let proof ← proveActionDeclsOk cache design expanded
      match result.proof? with
      | none => pure proof
      | some valuesEq =>
          let valuesType ← inferType values
          let foldMotive ← withLocalDeclD `values valuesType fun xs =>
            mkLambdaFVars #[xs] <| mkAppN reduced.getAppFn (args.pop.push xs)
          transportActionDeclsOk design (← mkCongrArg foldMotive valuesEq) proof
  | _ => throwError "action_decls_ok: action did not reduce to a constructor: {reduced}"

/-- Compose generated declaration leaves over an arbitrary closed action tree. -/
syntax (name := actionDeclsOkTerm) "action_decls_ok" : term

@[term_elab actionDeclsOkTerm]
unsafe def elabActionDeclsOk : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "action_decls_ok requires an expected Boolean acceptance equality"
  let expected ← instantiateMVars expected
  if expected.hasFVar || expected.hasMVar then
    throwError "action_decls_ok requires a closed proposition"
  let equalityArgs := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``Eq && equalityArgs.size == 3 do
    throwError "action_decls_ok expected actionDeclsOk design action = true"
  let check := equalityArgs[1]!
  let args := check.getAppArgs
  unless check.getAppFn.constName? == some ``Loom.Hw.Compile.actionDeclsOk &&
      args.size == 2 do
    throwError "action_decls_ok expected actionDeclsOk design action = true"
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  seedReleaseDeclProofs cache
  proveActionDeclsOk cache args[0]! args[1]!

private unsafe def proveActRegistersValid (cache : ProofCache)
    (program action : Expr) : MetaM Expr := do
  let reduced ← exposeAction action
  let args := reduced.getAppArgs
  match reduced.getAppFn.constName? with
  | some ``Loom.Hw.Act.skip => pure (mkConst ``True.intro)
  | some ``Loom.Hw.Act.seq =>
      let left := args[args.size - 2]!
      let right := args[args.size - 1]!
      let leftType ← mkAppM ``ActRegistersValid #[program, left]
      let rightType ← mkAppM ``ActRegistersValid #[program, right]
      mkAndProof
        (← cachePropProofMemo cache leftType (proveActRegistersValid cache program left))
        (← cachePropProofMemo cache rightType (proveActRegistersValid cache program right))
  | some ``Loom.Hw.Act.ite =>
      let condition := args[args.size - 3]!
      let yes := args[args.size - 2]!
      let no := args[args.size - 1]!
      let conditionType ← mkAppM ``HwExprRegistersValid #[program, condition]
      let yesType ← mkAppM ``ActRegistersValid #[program, yes]
      let noType ← mkAppM ``ActRegistersValid #[program, no]
      let conditionProof ← cachePropProofMemo cache conditionType
        (proveHwExprRegistersValid cache program condition)
      let yesProof ← cachePropProofMemo cache yesType
        (proveActRegistersValid cache program yes)
      let noProof ← cachePropProofMemo cache noType
        (proveActRegistersValid cache program no)
      mkAndProof conditionProof (← mkAndProof yesProof noProof)
  | some ``Loom.Hw.Act.write =>
      let value := args[args.size - 1]!
      let valueType ← mkAppM ``HwExprRegistersValid #[program, value]
      cachePropProofMemo cache valueType (proveHwExprRegistersValid cache program value)
  | some ``Loom.Hw.Act.memWrite =>
      let address := args[args.size - 2]!
      let value := args[args.size - 1]!
      let addressType ← mkAppM ``HwExprRegistersValid #[program, address]
      let valueType ← mkAppM ``HwExprRegistersValid #[program, value]
      mkAndProof
        (← cachePropProofMemo cache addressType
          (proveHwExprRegistersValid cache program address))
        (← cachePropProofMemo cache valueType
          (proveHwExprRegistersValid cache program value))
  | some ``List.foldr =>
      let function := args[args.size - 3]!
      let initial := args[args.size - 2]!
      let values := args[args.size - 1]!
      let simpContext ← Simp.Context.mkDefault
      let (result, _) ← simp values simpContext
      let expanded ← expandListFoldr function initial result.expr
      let proof ← proveActRegistersValid cache program expanded
      match result.proof? with
      | none => pure proof
      | some valuesEq =>
          let valuesType ← inferType values
          let foldMotive ← withLocalDeclD `values valuesType fun xs =>
            mkLambdaFVars #[xs] <| mkAppN reduced.getAppFn (args.pop.push xs)
          transportActRegistersValid program (← mkCongrArg foldMotive valuesEq) proof
  | _ => throwError "design_reads_valid: action did not reduce to a constructor: {reduced}"

private partial def exposeList (values : Expr) : MetaM (Name × Array Expr) := do
  let reduced ← withTransparency .all <| whnf values
  match reduced.getAppFn.constName? with
  | some ``List.nil => pure (``List.nil, reduced.getAppArgs)
  | some ``List.cons => pure (``List.cons, reduced.getAppArgs)
  | _ =>
      match ← unfoldDefinition? reduced (ignoreTransparency := true) with
      | some unfolded => exposeList unfolded
      | none => throwError "design_reads_valid: expected a concrete list, got {reduced}"

private unsafe def proveRulesDeclsOk (cache : ProofCache)
    (design rules : Expr) : MetaM Expr := do
  let (name, args) ← exposeList rules
  if name == ``List.nil then
    return mkConst ``True.intro
  let rule := args[args.size - 2]!
  let rest := args[args.size - 1]!
  let body ← mkAppM ``Loom.Hw.Rule.body #[rule]
  let headCheck ← mkAppM ``Loom.Hw.Compile.actionDeclsOk #[design, body]
  let headType ← mkEq headCheck (mkConst ``Bool.true)
  let headProof ← cachePropProofMemo cache headType
    (proveActionDeclsOk cache design body)
  let tailType ← mkAppM ``Loom.Hw.Compile.RulesDeclsOk #[design, rest]
  let tailProof ← cachePropProof tailType (proveRulesDeclsOk cache design rest)
  mkAndProof headProof tailProof

/-- Compose generated declaration leaves over every concrete source rule. -/
syntax (name := rulesDeclsOkTerm) "rules_decls_ok" : term

@[term_elab rulesDeclsOkTerm]
unsafe def elabRulesDeclsOk : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "rules_decls_ok requires an expected RulesDeclsOk proposition"
  let expected ← instantiateMVars expected
  if expected.hasFVar || expected.hasMVar then
    throwError "rules_decls_ok requires a closed proposition"
  let args := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``Loom.Hw.Compile.RulesDeclsOk &&
      args.size == 2 do
    throwError "rules_decls_ok expected RulesDeclsOk design rules"
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  seedReleaseDeclProofs cache
  proveRulesDeclsOk cache args[0]! args[1]!

private unsafe def proveSourceRegistersValid (cache : ProofCache)
    (program sources : Expr) : MetaM Expr := do
  let (name, args) ← exposeList sources
  if name == ``List.nil then
    return mkConst ``True.intro
  let source := args[args.size - 2]!
  let rest := args[args.size - 1]!
  let oneType ← mkAppM ``SourceRegisterValid #[program, source]
  let width ← mkAppM ``Loom.Hw.RegDecl.width #[source]
  let name ← mkAppM ``Loom.Hw.RegDecl.name #[source]
  let expression := mkApp2 (mkConst ``Loom.Hw.Expr.reg) width name
  let expressionProof ← proveHwExprRegistersValid cache program expression
  let oneProof ← mkAppM ``SourceRegisterValid.ofHwReg #[source, expressionProof]
  let oneProof ← cacheClosedProof oneType oneProof
  -- Keep the list composition in one linear proof term. Caching every tail
  -- would repeat all remaining declarations in auxiliary theorem statements.
  mkAndProof oneProof (← proveSourceRegistersValid cache program rest)

private unsafe def proveRulesRegistersValid (cache : ProofCache)
    (program rules : Expr) : MetaM Expr := do
  let (name, args) ← exposeList rules
  if name == ``List.nil then
    return mkConst ``True.intro
  let rule := args[args.size - 2]!
  let rest := args[args.size - 1]!
  let body ← mkAppM ``Loom.Hw.Rule.body #[rule]
  let bodyType ← mkAppM ``ActRegistersValid #[program, body]
  let restType ← mkAppM ``RulesRegistersValid #[program, rest]
  mkAndProof
    (← cachePropProofMemo cache bodyType (proveActRegistersValid cache program body))
    (← cachePropProof restType (proveRulesRegistersValid cache program rest))

/-- Build only the compositional rule-body portion of a read certificate. -/
syntax (name := rulesReadsValidTerm) "rules_reads_valid" : term

@[term_elab rulesReadsValidTerm]
unsafe def elabRulesReadsValid : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "rules_reads_valid requires an expected RulesRegistersValid proposition"
  let expected ← instantiateMVars expected
  if expected.hasFVar || expected.hasMVar then
    throwError "rules_reads_valid requires a closed proposition"
  let args := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``RulesRegistersValid && args.size == 2 do
    throwError "rules_reads_valid expected RulesRegistersValid program rules"
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  seedReleaseReadProofs cache
  proveRulesRegistersValid cache args[0]! args[1]!

/-- Build the complete source-read certificate from separately named
constructor and list proofs. The generator is not trusted: every auxiliary
declaration and the composed result are checked by the kernel. -/
syntax (name := designReadsValidTerm) "design_reads_valid" : term

@[term_elab designReadsValidTerm]
unsafe def elabDesignReadsValid : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "design_reads_valid requires an expected DesignReadsValid proposition"
  let expected ← instantiateMVars expected
  if expected.hasFVar || expected.hasMVar then
    throwError "design_reads_valid requires a closed proposition"
  let args := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``DesignReadsValid && args.size == 2 do
    throwError "design_reads_valid expected DesignReadsValid design program"
  let design := args[0]!
  let program := args[1]!
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  seedReleaseReadProofs cache
  let sources ← mkAppM ``Loom.Hw.Design.regs #[design]
  let rules ← mkAppM ``Loom.Hw.Design.rules #[design]
  let sourceType ← mkAppM ``SourceRegistersValid #[program, sources]
  let rulesType ← mkAppM ``RulesRegistersValid #[program, rules]
  let sourceProof ← cachePropProof sourceType
    (proveSourceRegistersValid cache program sources)
  let rulesProof ← cachePropProof rulesType
    (proveRulesRegistersValid cache program rules)
  mkAppM ``DesignReadsValid.ofLists #[sourceProof, rulesProof]

private def transportNoRegWrite (register width actionEq proof : Expr) : MetaM Expr := do
  let equalityType ← inferType actionEq
  let actionType := equalityType.getAppArgs[0]!
  let motive ← withLocalDeclD `action actionType fun act => do
    let body ← mkAppM ``NoRegWrite #[register, width, act]
    mkLambdaFVars #[act] body
  let propositionEq ← mkCongrArg motive actionEq
  mkAppM ``Eq.mpr #[propositionEq, proof]

private partial def proveNoRegWrite (register width action : Expr) : MetaM Expr := do
  let reduced ← exposeAction action
  let args := reduced.getAppArgs
  match reduced.getAppFn.constName? with
  | some ``Loom.Hw.Act.skip =>
      pure <| mkAppN (mkConst ``NoRegWrite.skip) #[register, width]
  | some ``Loom.Hw.Act.seq =>
      let left := args[args.size - 2]!
      let right := args[args.size - 1]!
      let leftType ← mkAppM ``NoRegWrite #[register, width, left]
      let rightType ← mkAppM ``NoRegWrite #[register, width, right]
      let leftProof ← cacheClosedProof leftType
        (← proveNoRegWrite register width left)
      let rightProof ← cacheClosedProof rightType
        (← proveNoRegWrite register width right)
      pure <| mkAppN (mkConst ``NoRegWrite.seq)
        #[register, width, left, right, leftProof, rightProof]
  | some ``Loom.Hw.Act.ite =>
      let thenAction := args[args.size - 2]!
      let elseAction := args[args.size - 1]!
      let thenType ← mkAppM ``NoRegWrite #[register, width, thenAction]
      let elseType ← mkAppM ``NoRegWrite #[register, width, elseAction]
      let thenProof ← cacheClosedProof thenType
        (← proveNoRegWrite register width thenAction)
      let elseProof ← cacheClosedProof elseType
        (← proveNoRegWrite register width elseAction)
      let guard := args[args.size - 3]!
      pure <| mkAppN (mkConst ``NoRegWrite.ite)
        #[register, width, guard, thenAction, elseAction, thenProof, elseProof]
  | some ``Loom.Hw.Act.write =>
      let actualWidth := args[args.size - 3]!
      let name := args[args.size - 2]!
      let value := args[args.size - 1]!
      if ← isDefEq name register then
        let differentType ← mkAppM ``Ne #[actualWidth, width]
        let different ← cacheClosedProof differentType
          (← mkDecideProof differentType)
        pure <| mkAppN (mkConst ``NoRegWrite.writeWidth)
          #[register, width, actualWidth, value, different]
      else
        let differentType ← mkAppM ``Ne #[name, register]
        let different ← cacheClosedProof differentType
          (← mkDecideProof differentType)
        pure <| mkAppN (mkConst ``NoRegWrite.writeName)
          #[register, width, actualWidth, name, value, different]
  | some ``Loom.Hw.Act.memWrite =>
      let address := args[args.size - 2]!
      let value := args[args.size - 1]!
      let addressWidth := args[args.size - 6]!
      let dataWidth := args[args.size - 5]!
      let name := args[args.size - 4]!
      let port := args[args.size - 3]!
      pure <| mkAppN (mkConst ``NoRegWrite.memWrite)
        #[register, width, addressWidth, dataWidth, name, port, address, value]
  | some ``List.foldr =>
      let function := args[args.size - 3]!
      let initial := args[args.size - 2]!
      let values := args[args.size - 1]!
      let simpContext ← Simp.Context.mkDefault
      let (result, _) ← simp values simpContext
      let expanded ← expandListFoldr function initial result.expr
      let proof ← proveNoRegWrite register width expanded
      match result.proof? with
      | none => pure proof
      | some valuesEq =>
          let valuesType ← inferType values
          -- `List.foldr` takes the function and initial value before the list;
          -- build the congruence function directly to preserve that order.
          let foldMotive ← withLocalDeclD `values valuesType fun xs =>
            mkLambdaFVars #[xs] <|
              mkAppN reduced.getAppFn (args.pop.push xs)
          transportNoRegWrite register width (← mkCongrArg foldMotive valuesEq) proof
  | _ => throwError "no_reg_write: action did not reduce to an Act constructor: {reduced}"

private partial def proveNoPortWrite (memory port action : Expr) : MetaM Expr := do
  let reduced ← exposeAction action
  let args := reduced.getAppArgs
  match reduced.getAppFn.constName? with
  | some ``Loom.Hw.Act.skip =>
      pure <| mkAppN (mkConst ``NoPortWrite.skip) #[memory, port]
  | some ``Loom.Hw.Act.seq =>
      let left := args[args.size - 2]!
      let right := args[args.size - 1]!
      let leftType ← mkAppM ``NoPortWrite #[memory, port, left]
      let rightType ← mkAppM ``NoPortWrite #[memory, port, right]
      let leftProof ← cacheClosedProof leftType
        (← proveNoPortWrite memory port left)
      let rightProof ← cacheClosedProof rightType
        (← proveNoPortWrite memory port right)
      pure <| mkAppN (mkConst ``NoPortWrite.seq)
        #[memory, port, left, right, leftProof, rightProof]
  | some ``Loom.Hw.Act.ite =>
      let guard := args[args.size - 3]!
      let thenAction := args[args.size - 2]!
      let elseAction := args[args.size - 1]!
      let thenType ← mkAppM ``NoPortWrite #[memory, port, thenAction]
      let elseType ← mkAppM ``NoPortWrite #[memory, port, elseAction]
      let thenProof ← cacheClosedProof thenType
        (← proveNoPortWrite memory port thenAction)
      let elseProof ← cacheClosedProof elseType
        (← proveNoPortWrite memory port elseAction)
      pure <| mkAppN (mkConst ``NoPortWrite.ite)
        #[memory, port, guard, thenAction, elseAction, thenProof, elseProof]
  | some ``Loom.Hw.Act.write =>
      let width := args[args.size - 3]!
      let name := args[args.size - 2]!
      let value := args[args.size - 1]!
      pure <| mkAppN (mkConst ``NoPortWrite.write)
        #[memory, port, width, name, value]
  | some ``Loom.Hw.Act.memWrite =>
      let addressWidth := args[args.size - 6]!
      let dataWidth := args[args.size - 5]!
      let name := args[args.size - 4]!
      let actualPort := args[args.size - 3]!
      let address := args[args.size - 2]!
      let value := args[args.size - 1]!
      if ← isDefEq name memory then
        let differentType ← mkAppM ``Ne #[actualPort, port]
        let different ← cacheClosedProof differentType
          (← mkDecideProof differentType)
        pure <| mkAppN (mkConst ``NoPortWrite.memWritePort)
          #[memory, port, addressWidth, dataWidth, actualPort, address, value,
            different]
      else
        let differentType ← mkAppM ``Ne #[name, memory]
        let different ← cacheClosedProof differentType
          (← mkDecideProof differentType)
        pure <| mkAppN (mkConst ``NoPortWrite.memWriteName)
          #[memory, port, addressWidth, dataWidth, name, actualPort, address,
            value, different]
  | some ``List.foldr =>
      let function := args[args.size - 3]!
      let initial := args[args.size - 2]!
      let values := args[args.size - 1]!
      let simpContext ← Simp.Context.mkDefault
      let (result, _) ← simp values simpContext
      let expanded ← expandListFoldr function initial result.expr
      let proof ← proveNoPortWrite memory port expanded
      match result.proof? with
      | none => pure proof
      | some valuesEq =>
          let valuesType ← inferType values
          let foldMotive ← withLocalDeclD `values valuesType fun xs =>
            mkLambdaFVars #[xs] <| mkAppN reduced.getAppFn (args.pop.push xs)
          let actionEq ← mkCongrArg foldMotive valuesEq
          let equalityType ← inferType actionEq
          let actionType := equalityType.getAppArgs[0]!
          let motive ← withLocalDeclD `action actionType fun act => do
            let body ← mkAppM ``NoPortWrite #[memory, port, act]
            mkLambdaFVars #[act] body
          let propositionEq ← mkCongrArg motive actionEq
          mkAppM ``Eq.mpr #[propositionEq, proof]
  | _ => throwError "symbolic_kernel_decide: action did not reduce for NoPortWrite: {reduced}"

private def transportHasPortWrite (memory port actionEq proof : Expr) : MetaM Expr := do
  let equalityType ← inferType actionEq
  let actionType := equalityType.getAppArgs[0]!
  let motive ← withLocalDeclD `action actionType fun act => do
    let body ← mkAppM ``HasPortWrite #[memory, port, act]
    mkLambdaFVars #[act] body
  let propositionEq ← mkCongrArg motive actionEq
  mkAppM ``Eq.mpr #[propositionEq, proof]

private partial def proveHasPortWrite (memory port action : Expr) : MetaM Expr := do
  let reduced ← exposeAction action
  let args := reduced.getAppArgs
  match reduced.getAppFn.constName? with
  | some ``Loom.Hw.Act.seq =>
      let left := args[args.size - 2]!
      let right := args[args.size - 1]!
      try
        let childType ← mkAppM ``HasPortWrite #[memory, port, left]
        let child ← cacheClosedProof childType
          (← proveHasPortWrite memory port left)
        pure <| mkAppN (mkConst ``HasPortWrite.seqLeft)
          #[memory, port, left, right, child]
      catch _ =>
        let childType ← mkAppM ``HasPortWrite #[memory, port, right]
        let child ← cacheClosedProof childType
          (← proveHasPortWrite memory port right)
        pure <| mkAppN (mkConst ``HasPortWrite.seqRight)
          #[memory, port, left, right, child]
  | some ``Loom.Hw.Act.ite =>
      let guard := args[args.size - 3]!
      let thenAction := args[args.size - 2]!
      let elseAction := args[args.size - 1]!
      try
        let childType ← mkAppM ``HasPortWrite #[memory, port, thenAction]
        let child ← cacheClosedProof childType
          (← proveHasPortWrite memory port thenAction)
        pure <| mkAppN (mkConst ``HasPortWrite.iteThen)
          #[memory, port, guard, thenAction, elseAction, child]
      catch _ =>
        let childType ← mkAppM ``HasPortWrite #[memory, port, elseAction]
        let child ← cacheClosedProof childType
          (← proveHasPortWrite memory port elseAction)
        pure <| mkAppN (mkConst ``HasPortWrite.iteElse)
          #[memory, port, guard, thenAction, elseAction, child]
  | some ``Loom.Hw.Act.memWrite =>
      let addressWidth := args[args.size - 6]!
      let dataWidth := args[args.size - 5]!
      let name := args[args.size - 4]!
      let actualPort := args[args.size - 3]!
      let address := args[args.size - 2]!
      let value := args[args.size - 1]!
      unless ← isDefEq name memory do
        throwError "symbolic_kernel_decide: memory write has a different name"
      unless ← isDefEq actualPort port do
        throwError "symbolic_kernel_decide: memory write has a different port"
      pure <| mkAppN (mkConst ``HasPortWrite.memWrite)
        #[memory, port, addressWidth, dataWidth, address, value]
  | some ``List.foldr =>
      let function := args[args.size - 3]!
      let initial := args[args.size - 2]!
      let values := args[args.size - 1]!
      let simpContext ← Simp.Context.mkDefault
      let (result, _) ← simp values simpContext
      let expanded ← expandListFoldr function initial result.expr
      let proof ← proveHasPortWrite memory port expanded
      match result.proof? with
      | none => pure proof
      | some valuesEq =>
          let valuesType ← inferType values
          let foldMotive ← withLocalDeclD `values valuesType fun xs =>
            mkLambdaFVars #[xs] <| mkAppN reduced.getAppFn (args.pop.push xs)
          transportHasPortWrite memory port
            (← mkCongrArg foldMotive valuesEq) proof
  | _ => throwError "symbolic_kernel_decide: no write to requested memory port in {reduced}"

private def provePortWritesOr (memory port left right : Expr) : MetaM Expr := do
  let leftCheck ← mkAppM ``Loom.Hw.Compile.writesPortB #[memory, port, left]
  let rightCheck ← mkAppM ``Loom.Hw.Compile.writesPortB #[memory, port, right]
  let leftAccepted ← mkEq leftCheck (mkConst ``Bool.true)
  let rightAccepted ← mkEq rightCheck (mkConst ``Bool.true)
  let disjunction ← try
    let witnessType ← mkAppM ``HasPortWrite #[memory, port, left]
    let witness ← cacheClosedProof witnessType
      (← proveHasPortWrite memory port left)
    let accepted ← mkAppM ``HasPortWrite.writesPortB_eq_true #[witness]
    pure <| mkAppN (mkConst ``Or.inl) #[leftAccepted, rightAccepted, accepted]
  catch leftError =>
    let witnessType ← mkAppM ``HasPortWrite #[memory, port, right]
    let witness ← try
      cacheClosedProof witnessType (← proveHasPortWrite memory port right)
    catch rightError =>
      throwError "symbolic_kernel_decide: neither conditional branch writes the port; left: {leftError.toMessageData}; right: {rightError.toMessageData}"
    let accepted ← mkAppM ``HasPortWrite.writesPortB_eq_true #[witness]
    pure <| mkAppN (mkConst ``Or.inr) #[leftAccepted, rightAccepted, accepted]
  let decomposition ← mkAppM ``Bool.or_eq_true #[leftCheck, rightCheck]
  mkAppM ``Eq.mpr #[decomposition, disjunction]

/-- Construct closed, compositional evidence that an action cannot write the
expected register. Every recursive child is checked as a named auxiliary
theorem. -/
syntax (name := noRegWriteTerm) "no_reg_write" : term

@[term_elab noRegWriteTerm]
def elabNoRegWrite : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "no_reg_write requires an expected NoRegWrite proposition"
  let expected ← instantiateMVars expected
  if expected.hasFVar || expected.hasMVar then
    throwError "no_reg_write requires a closed proposition"
  let args := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``NoRegWrite && args.size == 3 do
    throwError "no_reg_write expected NoRegWrite register width action"
  let register := args[0]!
  let width := args[1]!
  let action := args[2]!
  let simpContext ← Simp.Context.mkDefault
  let (result, _) ← simp action simpContext
  let proof ← proveNoRegWrite register width result.expr
  match result.proof? with
  | none => pure proof
  | some actionEq =>
      transportNoRegWrite register width actionEq proof

private def trueExpr : Expr := mkConst ``Bool.true

private def mkBoolAccepted (value : Expr) : MetaM Expr :=
  mkEq value trueExpr

private def cacheAccepted (type proof : Expr) : MetaM Expr :=
  cacheClosedProof type proof

private def decideAccepted (type : Expr) : MetaM Expr := do
  cacheClosedProof type (← mkDecideProof type)

private def inlineDecideAccepted (type : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) type)
  let decision := mkApp2 (mkConst ``decide) type inst
  let proof ← mkEqRefl decision
  pure <| mkAppN (mkConst ``of_decide_eq_true) #[type, inst, proof]

private def trueDecisionProof (decision : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf decision
  if reduced.getAppFn.constName? == some ``Decidable.isTrue then
    return reduced.getAppArgs.back!
  throwError "indexed expression arithmetic side condition is false"

private def proveNatLt (left right : Expr) : MetaM Expr :=
  trueDecisionProof (mkApp2 (mkConst ``Nat.decLt) left right)

private def proveNatLe (left right : Expr) : MetaM Expr :=
  trueDecisionProof (mkApp2 (mkConst ``Nat.decLe) left right)

private abbrev IndexedExprCache := IO.Ref (Std.HashMap Nat Expr)

private initialize indexedExprModuleCache : IndexedExprCache ← IO.mkRef {}
private initialize indexedExprCheckpoints : IO.Ref (Std.HashSet Nat) ← IO.mkRef {}
private initialize indexedExprPendingNodes : IO.Ref Nat ← IO.mkRef 0
private initialize indexedLookupMs : IO.Ref Nat ← IO.mkRef 0
private initialize indexedExposeMs : IO.Ref Nat ← IO.mkRef 0

private structure LocalProofBinding where
  placeholder : Expr
  type : Expr
  value : Expr

private initialize localProofBindings : IO.Ref (Array LocalProofBinding) ←
  IO.mkRef #[]
private initialize useLocalProofBindings : IO.Ref Bool ← IO.mkRef false

private def checkpointLocalProof (type value : Expr) : MetaM Expr := do
  unless ← useLocalProofBindings.get do
    return ← cacheClosedProof type value
  let placeholder ← mkFreshExprMVar type
  localProofBindings.modify (·.push { placeholder, type, value })
  pure placeholder

private def wrapLocalProofBindings (body : Expr) : MetaM Expr := do
  let bindings ← localProofBindings.get
  let mut allIndices : Std.HashMap MVarId Nat := {}
  for index in [:bindings.size] do
    if let some binding := bindings[index]? then
      allIndices := allIndices.insert binding.placeholder.mvarId! index
  -- Select only checkpoints reachable from this proof. This lets an opaque
  -- action chunk consume its own telescope without invalidating live sibling
  -- proofs, while the final theorem omits checkpoints already hidden behind
  -- chunk constants.
  let body ← instantiateMVars body
  let mut selected : Std.HashSet Nat := {}
  let mut pending : Array Nat := #[]
  for id in ← getMVars body do
    if let some index := allIndices[id]? then
      unless selected.contains index do
        selected := selected.insert index
        pending := pending.push index
  let mut cursor := 0
  while cursor < pending.size do
    let index := pending[cursor]!
    cursor := cursor + 1
    let some binding := bindings[index]?
      | throwError "release proof binding index is out of bounds"
    for expression in #[binding.type, binding.value] do
      for id in ← getMVars (← instantiateMVars expression) do
        if let some dependency := allIndices[id]? then
          unless selected.contains dependency do
            selected := selected.insert dependency
            pending := pending.push dependency
  let selectedIndices := (List.range bindings.size).filter selected.contains
  let mut positions : Std.HashMap MVarId Nat := {}
  for compact in [:selectedIndices.length] do
    let original := selectedIndices[compact]!
    let some binding := bindings[original]?
      | throwError "release proof binding index is out of bounds"
    positions := positions.insert binding.placeholder.mvarId! compact
  let replaceAt (depth : Nat) (expression : Expr) : Expr :=
    expression.replace fun subterm => match subterm with
      | .mvar id => do
          let index ← positions[id]?
          if index < depth then some (.bvar (depth - 1 - index)) else none
      | _ => none
  let mut result := replaceAt selectedIndices.length body
  for compact in (List.range selectedIndices.length).reverse do
    let original := selectedIndices[compact]!
    let some binding := bindings[original]?
      | throwError "release proof binding index is out of bounds"
    let type := replaceAt compact (← instantiateMVars binding.type)
    let value := replaceAt compact (← instantiateMVars binding.value)
    result := .letE (Name.mkSimple s!"releaseProof{original}") type value result false
  if result.hasMVar then
    let mvars ← getMVars result
    for id in mvars do
      let declaration ← id.getDecl
      logInfo m!"unresolved release proof metavariable {id.name}; checkpoint index: {allIndices[id]?}; type: {declaration.type}"
    throwError "release proof telescope contains unresolved metavariables: {mvars.map (·.name)}"
  pure result

/-- Select SSA hubs whose evidence should be installed as named auxiliary
theorems. This is elaboration-only performance guidance; every selected proof
is independently checked by the kernel. -/
syntax (name := indexedExprCheckpointCmd)
  "indexed_expr_checkpoints" num* : command

@[command_elab indexedExprCheckpointCmd]
unsafe def elabIndexedExprCheckpoints : Lean.Elab.Command.CommandElab := fun stx => do
  let mut checkpoints : Std.HashSet Nat := {}
  for argument in stx[1].getArgs do
    let some value := argument.isNatLit?
      | throwErrorAt argument "indexed_expr_checkpoints expects natural literals"
    checkpoints := checkpoints.insert value
  indexedExprCheckpoints.set checkpoints

private partial def exposeMvExpr (expression : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf expression
  if let some name := reduced.getAppFn.constName? then
    if name == ``Loom.Emit.MicroVerilog.Expr.lit ||
        name == ``Loom.Emit.MicroVerilog.Expr.reg ||
        name == ``Loom.Emit.MicroVerilog.Expr.memRead ||
        name == ``Loom.Emit.MicroVerilog.Expr.and ||
        name == ``Loom.Emit.MicroVerilog.Expr.or ||
        name == ``Loom.Emit.MicroVerilog.Expr.xor ||
        name == ``Loom.Emit.MicroVerilog.Expr.not ||
        name == ``Loom.Emit.MicroVerilog.Expr.add ||
        name == ``Loom.Emit.MicroVerilog.Expr.sub ||
        name == ``Loom.Emit.MicroVerilog.Expr.shl ||
        name == ``Loom.Emit.MicroVerilog.Expr.shr ||
        name == ``Loom.Emit.MicroVerilog.Expr.eq ||
        name == ``Loom.Emit.MicroVerilog.Expr.ult ||
        name == ``Loom.Emit.MicroVerilog.Expr.slt ||
        name == ``Loom.Emit.MicroVerilog.Expr.mux ||
        name == ``Loom.Emit.MicroVerilog.Expr.slice ||
        name == ``Loom.Emit.MicroVerilog.Expr.zext ||
        name == ``Loom.Emit.MicroVerilog.Expr.sext then
      return reduced
  match ← unfoldDefinition? reduced (ignoreTransparency := true) with
  | some unfolded => exposeMvExpr unfolded
  | none => throwError "indexed_expr_decide: expression did not expose: {reduced}"

private partial def exposeSymbolicRef (reference : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf reference
  if reduced.getAppFn.constName? == some ``Ref.reg ||
      reduced.getAppFn.constName? == some ``Ref.wire then
    return reduced
  match ← unfoldDefinition? reduced (ignoreTransparency := true) with
  | some unfolded => exposeSymbolicRef unfolded
  | none => throwError "indexed_expr_decide: reference did not expose: {reduced}"

private def cacheIndexedExprEvidence (cache : IndexedExprCache)
    (number : Option Nat) (type proof : Expr) : MetaM Expr := do
  let pending ← indexedExprPendingNodes.modifyGet fun count =>
    (count + 1, count + 1)
  let checkpoints ← indexedExprCheckpoints.get
  let hub := match number with
    | some value => checkpoints.contains value
    | none => false
  let shouldCheckpoint := hub || pending >= 128
  let cached ← match number with
    | some _ =>
        if shouldCheckpoint then checkpointLocalProof type proof else pure proof
    | none => pure proof
  if shouldCheckpoint then indexedExprPendingNodes.set 0
  if let some number := number then
    cache.modify fun entries => entries.insert number cached
  let size := (← cache.get).size
  if size % 1000 == 0 then
    logInfo m!"indexed expression evidence nodes: {size}"
  pure cached

private def pad4 (number : Nat) : String :=
  let value := toString number
  if number < 10 then "000" ++ value
  else if number < 100 then "00" ++ value
  else if number < 1000 then "0" ++ value
  else value

/-- Build a global lookup fact from a named leaf-resolution theorem.  The
resolver is checked once per 128-wire leaf; this function only normalizes the
bounded lookup within that leaf. -/
private def proveIndexedLookup (wires table number : Expr) : MetaM (Expr × Expr) := do
  let started ← IO.monoMsNow
  let reducedNumber ← withTransparency .all <| whnf number
  let some numberValue ← getNatValue? reducedNumber
    | throwError "indexed_expr_decide: wire number is not concrete: {number}"
  let some wiresName := wires.getAppFn.constName?
    | throwError "indexed_expr_decide: indexed wire tree is not a named constant"
  let fastLookup :=
    wiresName == wiresName.getPrefix.str "fastIndexedWireTree"
  let resolverName := wiresName.getPrefix.str
    ((if fastLookup then "fastIndexedWireResolveBlock"
      else "indexedWireResolveBlock") ++ pad4 (numberValue / 128))
  unless (← getEnv).contains resolverName do
    throwError "indexed_expr_decide: missing leaf resolver {resolverName}"
  let offset := mkNatLit (numberValue % 128)
  let resolver ← mkAppM resolverName #[offset]
  let resolverType ← inferType resolver
  let resolverArgs := resolverType.getAppArgs
  unless resolverType.getAppFn.constName? == some ``Eq && resolverArgs.size == 3 do
    throwError "indexed_expr_decide: malformed leaf resolver {resolverName}"
  let (reducedLookup, resolved) ← if fastLookup then do
    let blockSuffix := pad4 (numberValue / 128)
    let lookupBlockName := wiresName.getPrefix.str
      ("fastIndexedWireLookupBlock" ++ blockSuffix)
    let lookupWellFormedName := wiresName.getPrefix.str
      ("fastIndexedWireLookupBlock" ++ blockSuffix ++ "WellFormed")
    unless (← getEnv).contains lookupBlockName &&
        (← getEnv).contains lookupWellFormedName do
      throwError "indexed_expr_decide: missing balanced lookup block {lookupBlockName}"
    let lookupBlock := Lean.mkConst lookupBlockName
    let blockLookup ← mkAppM ``LookupTree.get? #[lookupBlock, offset]
    let reducedLookup ← withTransparency .all <| whnf blockLookup
    let lookupBridge ← mkAppM ``LookupTree.get?_eq_getElem?_toList
      #[Lean.mkConst lookupWellFormedName, offset]
    let resolved ← mkAppM ``Eq.trans
      #[resolver, ← mkAppM ``Eq.symm #[lookupBridge]]
    pure (reducedLookup, resolved)
  else
    pure (← withTransparency .all <| whnf resolverArgs[2]!, resolver)
  unless reducedLookup.getAppFn.constName? == some ``Option.some do
    throwError "indexed_expr_decide: leaf lookup failed for {numberValue}"
  let indexed := reducedLookup.getAppArgs.back!
  let resolveLhs := resolverArgs[1]!
  let resolveArgs := resolveLhs.getAppArgs
  unless resolveLhs.getAppFn.constName? == some ``Rope.resolve? &&
      resolveArgs.size >= 2 do
    throwError "indexed_expr_decide: malformed resolver lookup {resolverName}"
  let reference ← withTransparency .all <| whnf resolveArgs.back!
  let referenceArgs := reference.getAppArgs
  unless reference.getAppFn.constName? == some ``Rope.Ref.mk &&
      referenceArgs.size >= 2 do
    throwError "indexed_expr_decide: malformed resolver reference {resolverName}"
  let path := referenceArgs[referenceArgs.size - 2]!
  let tableReduced ← withTransparency .all <| whnf table
  let tableArgs := tableReduced.getAppArgs
  unless tableReduced.getAppFn.constName? == some ``WireTable.mk &&
      tableArgs.size >= 2 do
    throwError "indexed_expr_decide: wire table did not expose"
  let leafSize := tableArgs[tableArgs.size - 2]!
  let leafCount := tableArgs.back!
  let some leafSizeValue ← getNatValue? leafSize
    | throwError "indexed_expr_decide: leaf size is not concrete"
  if leafSizeValue == 0 then
    throwError "indexed_expr_decide: leaf size is zero"
  let positiveProof ← mkAppM ``Nat.zero_lt_succ
    #[mkNatLit (leafSizeValue - 1)]
  let pathLookup ← mkAppM ``balancedPath?
    #[leafCount, mkApp2 (mkConst ``Nat.div) reducedNumber leafSize]
  let somePath ← mkAppM ``Option.some #[path]
  let pathType ← mkEq pathLookup somePath
  let indexedReduced ← withTransparency .all <| whnf indexed
  let indexedArgs := indexedReduced.getAppArgs
  let numberEqType ← mkEq indexedArgs[indexedArgs.size - 3]! reducedNumber
  let found := mkAppN (mkConst ``lookupIndexed_of_resolve)
    #[wires, table, reducedNumber, path, indexed, positiveProof,
      ← inlineDecideAccepted pathType, resolved,
      ← inlineDecideAccepted numberEqType]
  let finished ← IO.monoMsNow
  indexedLookupMs.modify (· + (finished - started))
  pure (indexed, found)

private partial def proveIndexedExprEvidence (cache : IndexedExprCache)
    (wires table expression reference : Expr) : MetaM Expr := do
  let reference ← exposeSymbolicRef reference
  let referenceName := reference.getAppFn.constName?.getD Name.anonymous
  let referenceArgs := reference.getAppArgs
  let wireNumber ← if referenceName == ``Ref.wire then do
      let reduced ← withTransparency .all <| whnf referenceArgs.back!
      let some value ← getNatValue? reduced
        | throwError "indexed_expr_decide: non-concrete wire reference"
      pure (some value)
    else pure none
  if let some number := wireNumber then
    if let some cached := (← cache.get).get? number then
      return cached
  let type ← mkAppM ``IndexedExprEvidence #[wires, table, expression, reference]
  let exposeStarted ← IO.monoMsNow
  let expression ← exposeMvExpr expression
  let exposeFinished ← IO.monoMsNow
  indexedExposeMs.modify (· + (exposeFinished - exposeStarted))
  let expressionName := expression.getAppFn.constName?.getD Name.anonymous
  let expressionArgs := expression.getAppArgs
  if expressionName == ``Loom.Emit.MicroVerilog.Expr.reg &&
      referenceName == ``Ref.reg then
    let proof := mkAppN (mkConst ``IndexedExprEvidence.reg)
      #[wires, table, expressionArgs[expressionArgs.size - 2]!,
        expressionArgs.back!]
    return proof
  unless referenceName == ``Ref.wire do
    throwError "indexed_expr_decide: non-register expression has register reference"
  let number := referenceArgs[referenceArgs.size - 1]!
  let (indexed, found) ← proveIndexedLookup wires table number
  let indexedReduced ← withTransparency .all <| whnf indexed
  unless indexedReduced.getAppFn.constName? == some ``IndexedWire.mk do
    throwError "indexed_expr_decide: lookup did not return an indexed wire"
  let indexedArgs := indexedReduced.getAppArgs
  let rhs ← withTransparency .all <| whnf indexedArgs.back!
  let rhsArgs := rhs.getAppArgs
  let child (source actual : Expr) :=
    proveIndexedExprEvidence cache wires table source actual
  let proof ←
    if expressionName == ``Loom.Emit.MicroVerilog.Expr.lit then
      pure <| mkAppN (mkConst ``IndexedExprEvidence.lit)
        #[wires, table, expressionArgs[expressionArgs.size - 2]!,
          expressionArgs.back!, number, found]
    else if expressionName == ``Loom.Emit.MicroVerilog.Expr.memRead then
      pure <| mkAppN (mkConst ``IndexedExprEvidence.memRead)
        #[wires, table, expressionArgs[expressionArgs.size - 2]!,
          expressionArgs[expressionArgs.size - 4]!,
          expressionArgs[expressionArgs.size - 3]!, expressionArgs.back!,
          rhsArgs.back!, number, found,
          ← child expressionArgs.back! rhsArgs.back!]
    else if expressionName == ``Loom.Emit.MicroVerilog.Expr.not then
      pure <| mkAppN (mkConst ``IndexedExprEvidence.not)
        #[wires, table, expressionArgs[expressionArgs.size - 2]!,
          expressionArgs.back!, rhsArgs.back!, number, found,
          ← child expressionArgs.back! rhsArgs.back!]
    else if expressionName == ``Loom.Emit.MicroVerilog.Expr.slice then
      pure <| mkAppN (mkConst ``IndexedExprEvidence.slice)
        #[wires, table, expressionArgs[expressionArgs.size - 4]!,
          expressionArgs.back!, expressionArgs[expressionArgs.size - 2]!,
          expressionArgs[expressionArgs.size - 3]!,
          rhsArgs[rhsArgs.size - 3]!, number, found,
          ← child expressionArgs[expressionArgs.size - 3]!
            rhsArgs[rhsArgs.size - 3]!]
    else if expressionName == ``Loom.Emit.MicroVerilog.Expr.zext then
      let source := expressionArgs[expressionArgs.size - 2]!
      let width := expressionArgs[expressionArgs.size - 3]!
      let outputWidth := expressionArgs.back!
      pure <| mkAppN (mkConst ``IndexedExprEvidence.zext)
        #[wires, table, width, outputWidth, source, rhsArgs.back!, number,
          found, ← proveNatLe width outputWidth,
          ← child source rhsArgs.back!]
    else if expressionName == ``Loom.Emit.MicroVerilog.Expr.sext then
      let source := expressionArgs[expressionArgs.size - 2]!
      let inputWidth := expressionArgs[expressionArgs.size - 3]!
      let outputWidth := expressionArgs.back!
      pure <| mkAppN (mkConst ``IndexedExprEvidence.sext)
        #[wires, table, inputWidth, outputWidth, source,
          rhsArgs[rhsArgs.size - 2]!, number, found,
          ← proveNatLt (mkNatLit 0) inputWidth,
          ← proveNatLt inputWidth outputWidth,
          ← child source rhsArgs[rhsArgs.size - 2]!]
    else if expressionName == ``Loom.Emit.MicroVerilog.Expr.mux then
      pure <| mkAppN (mkConst ``IndexedExprEvidence.mux)
        #[wires, table, expressionArgs[expressionArgs.size - 4]!,
          expressionArgs[expressionArgs.size - 3]!,
          expressionArgs[expressionArgs.size - 2]!, expressionArgs.back!,
          rhsArgs[rhsArgs.size - 3]!, rhsArgs[rhsArgs.size - 2]!,
          rhsArgs.back!, number, found,
          ← child expressionArgs[expressionArgs.size - 3]!
            rhsArgs[rhsArgs.size - 3]!,
          ← child expressionArgs[expressionArgs.size - 2]!
            rhsArgs[rhsArgs.size - 2]!,
          ← child expressionArgs.back! rhsArgs.back!]
    else
      let constructor ←
        if expressionName == ``Loom.Emit.MicroVerilog.Expr.and then
          pure ``IndexedExprEvidence.and
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.or then
          pure ``IndexedExprEvidence.or
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.xor then
          pure ``IndexedExprEvidence.xor
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.add then
          pure ``IndexedExprEvidence.add
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.sub then
          pure ``IndexedExprEvidence.sub
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.shl then
          pure ``IndexedExprEvidence.shl
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.shr then
          pure ``IndexedExprEvidence.shr
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.eq then
          pure ``IndexedExprEvidence.eq
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.ult then
          pure ``IndexedExprEvidence.ult
        else if expressionName == ``Loom.Emit.MicroVerilog.Expr.slt then
          pure ``IndexedExprEvidence.slt
        else throwError "indexed_expr_decide: unsupported expression {expression}"
      pure <| mkAppN (mkConst constructor)
        #[wires, table, expressionArgs[expressionArgs.size - 3]!,
          expressionArgs[expressionArgs.size - 2]!, expressionArgs.back!,
          rhsArgs[rhsArgs.size - 2]!, rhsArgs.back!, number, found,
          ← child expressionArgs[expressionArgs.size - 2]!
            rhsArgs[rhsArgs.size - 2]!,
          ← child expressionArgs.back! rhsArgs.back!]
  cacheIndexedExprEvidence cache wireNumber type proof

/-- Prove an indexed expression check by a memoized DAG of named kernel
theorems instead of reducing the shared expression as a tree. -/
syntax (name := indexedExprDecide) "indexed_expr_decide" : term

private partial def zetaIndexedExprLets (expression : Expr) : TermElabM Expr := do
  let some fvar := expression.find? (·.isFVar) | return expression
  let some declaration := (← getLCtx).find? fvar.fvarId!
    | return expression
  let some value := declaration.value? (allowNondep := true)
    | return expression
  zetaIndexedExprLets (expression.replaceFVar fvar value)

@[term_elab indexedExprDecide]
unsafe def elabIndexedExprDecide : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "indexed_expr_decide requires an expected proposition"
  let expected ← instantiateMVars expected >>= zetaIndexedExprLets
  if expected.hasFVar || expected.hasMVar then
    throwError "indexed_expr_decide requires a closed proposition"
  let equalityArgs := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``Eq && equalityArgs.size == 3 do
    throwError "indexed_expr_decide expected a Boolean equality"
  let lhs := equalityArgs[1]!
  let args := lhs.getAppArgs
  unless lhs.getAppFn.constName? == some ``indexedExprMatches && args.size == 5 do
    throwError "indexed_expr_decide expected indexedExprMatches = true"
  let evidence ← proveIndexedExprEvidence indexedExprModuleCache args[0]!
    args[1]! args[3]! args[4]!
  mkAppM ``IndexedExprEvidence.accepted #[evidence]

private def transportWritesRegAction (register width actionEq proof : Expr) :
    MetaM Expr := do
  let equalityType ← inferType actionEq
  let actionType := equalityType.getAppArgs[0]!
  let motive ← withLocalDeclD `action actionType fun act => do
    let check ← mkAppM ``Loom.Hw.Compile.writesRegB
      #[register, width, act]
    mkLambdaFVars #[act] (← mkEq check trueExpr)
  let propositionEq ← mkCongrArg motive actionEq
  mkAppM ``Eq.mpr #[propositionEq, proof]

/-- Prove that one concrete action writes the requested register without
normalizing the complete action's `regWrites` list. Only the matching write
leaf is discharged by `decide`; `seq`/`ite` parents use `Bool.or_eq_true`. -/
private partial def proveWritesRegTrue (register width action : Expr) : MetaM Expr := do
  let reduced ← exposeAction action
  let args := reduced.getAppArgs
  match reduced.getAppFn.constName? with
  | some ``Loom.Hw.Act.seq | some ``Loom.Hw.Act.ite =>
      let left := args[args.size - 2]!
      let right := args[args.size - 1]!
      let leftCheck ← mkAppM ``Loom.Hw.Compile.writesRegB
        #[register, width, left]
      let rightCheck ← mkAppM ``Loom.Hw.Compile.writesRegB
        #[register, width, right]
      let leftAccepted ← mkEq leftCheck trueExpr
      let rightAccepted ← mkEq rightCheck trueExpr
      let disjunction ← try
        let proof ← proveWritesRegTrue register width left
        pure <| mkAppN (mkConst ``Or.inl)
          #[leftAccepted, rightAccepted, proof]
      catch _ =>
        let proof ← proveWritesRegTrue register width right
        pure <| mkAppN (mkConst ``Or.inr)
          #[leftAccepted, rightAccepted, proof]
      let decomposition ← mkAppM ``Bool.or_eq_true #[leftCheck, rightCheck]
      mkAppM ``Eq.mpr #[decomposition, disjunction]
  | some ``Loom.Hw.Act.write =>
      let actualWidth := args[args.size - 3]!
      let name := args[args.size - 2]!
      unless ← isDefEq name register do
        throwError "symbolic_kernel_decide: register write has a different name"
      unless ← isDefEq actualWidth width do
        throwError "symbolic_kernel_decide: register write has a different width"
      let check ← mkAppM ``Loom.Hw.Compile.writesRegB
        #[register, width, reduced]
      mkDecideProof (← mkEq check trueExpr)
  | some ``List.foldr =>
      let function := args[args.size - 3]!
      let initial := args[args.size - 2]!
      let values := args[args.size - 1]!
      let simpContext ← Simp.Context.mkDefault
      let (result, _) ← simp values simpContext
      let expanded ← expandListFoldr function initial result.expr
      let proof ← proveWritesRegTrue register width expanded
      match result.proof? with
      | none => pure proof
      | some valuesEq =>
          let valuesType ← inferType values
          let foldMotive ← withLocalDeclD `values valuesType fun xs =>
            mkLambdaFVars #[xs] <| mkAppN reduced.getAppFn (args.pop.push xs)
          transportWritesRegAction register width
            (← mkCongrArg foldMotive valuesEq) proof
  | _ =>
      throwError "symbolic_kernel_decide: no write to requested register in {reduced}"

private def proveRegWritesOr (register width left right : Expr) : MetaM Expr := do
  let leftCheck ← mkAppM ``Loom.Hw.Compile.writesRegB
    #[register, width, left]
  let rightCheck ← mkAppM ``Loom.Hw.Compile.writesRegB
    #[register, width, right]
  let leftAccepted ← mkEq leftCheck trueExpr
  let rightAccepted ← mkEq rightCheck trueExpr
  let disjunction ← try
    let proof ← proveWritesRegTrue register width left
    pure <| mkAppN (mkConst ``Or.inl)
      #[leftAccepted, rightAccepted, proof]
  catch leftError =>
    let proof ← try
      proveWritesRegTrue register width right
    catch rightError =>
      throwError "symbolic_kernel_decide: neither conditional branch writes the register; left: {leftError.toMessageData}; right: {rightError.toMessageData}"
    pure <| mkAppN (mkConst ``Or.inr)
      #[leftAccepted, rightAccepted, proof]
  let decomposition ← mkAppM ``Bool.or_eq_true #[leftCheck, rightCheck]
  mkAppM ``Eq.mpr #[decomposition, disjunction]

private partial def expose (value : Expr) : MetaM (Name × Array Expr) := do
  let reduced ← withTransparency .all <| whnf value
  if let some name := reduced.getAppFn.constName? then
    if (← getEnv).isConstructor name then
      return (name, reduced.getAppArgs)
  match ← unfoldDefinition? reduced (ignoreTransparency := true) with
  | some unfolded => expose unfolded
  | none =>
      let fn := reduced.getAppFn
      let args := reduced.getAppArgs
      for index in [:args.size] do
        if let some unfolded ← unfoldDefinition? args[index]!
            (ignoreTransparency := true) then
          let candidate := mkAppN fn (args.set! index unfolded)
          let candidateReduced ← withTransparency .all <| whnf candidate
          unless candidateReduced == reduced do
            return ← expose candidateReduced
      try
        let unfoldedFn ← unfoldDefinition reduced.getAppFn
        expose (mkAppN unfoldedFn reduced.getAppArgs)
      catch _ =>
        throwError "symbolic_kernel_decide: expected constructor, got {reduced}"

private structure SparseProofBuild where
  result : Expr
  proof : Expr
  size : Nat

private initialize sparseNodeCount : IO.Ref Nat ← IO.mkRef 0
private initialize sparseActionExposeMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseCertExposeMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseBoundMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseExpressionMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseDecisionMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseMembershipMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseHeaderMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseBitMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseSummaryMs : IO.Ref Nat ← IO.mkRef 0
private initialize sparseJoinMs : IO.Ref Nat ← IO.mkRef 0

private def reportSparseStats : MetaM Unit := do
  IO.eprintln (s!"sparse evidence complete: nodes={← sparseNodeCount.get} " ++
    s!"action-expose={← sparseActionExposeMs.get}ms " ++
    s!"cert-expose={← sparseCertExposeMs.get}ms " ++
    s!"bound={← sparseBoundMs.get}ms expression={← sparseExpressionMs.get}ms " ++
    s!"decision={← sparseDecisionMs.get}ms membership={← sparseMembershipMs.get}ms " ++
    s!"header={← sparseHeaderMs.get}ms bit={← sparseBitMs.get}ms " ++
    s!"summary={← sparseSummaryMs.get}ms join={← sparseJoinMs.get}ms")

private def sparseResult (refs changed : Expr) : MetaM Expr :=
  mkAppM ``Loom.Release.Symbolic.ActionWide.BitSparseResult.mk #[refs, changed]

private def sparseRefs (result : Expr) : MetaM Expr :=
  mkAppM ``Loom.Release.Symbolic.ActionWide.BitSparseResult.refs #[result]

private def noChangedBits : Expr := mkNatLit 0

private def singletonChangedBit (value : Expr) : Expr :=
  mkApp2 (mkConst ``Nat.shiftLeft) (mkNatLit 1) value

/-- Collapse a computed bitmap at a recursive boundary. Without this, every
descendant re-evaluates the complete `neededBitsBefore`/`changedBitsAt` chain
when proving a single `testBit` fact. -/
private def normalizeNatLiteral (value : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf value
  let some number ← getNatValue? reduced
    | throwError "sparse_evidence_decide: bitmap did not reduce to a natural"
  pure (mkNatLit number)

private def decidePropositionIsTrue (type : Expr) : MetaM Bool := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) type)
  let decision := mkApp2 (mkConst ``decide) type inst
  let reduced ← withTransparency .all <| whnf decision
  pure (reduced.isConstOf ``Bool.true)

private partial def proveNatMembershipAux (index values : Expr) :
    MetaM (Bool × Expr) := do
  let reduced ← withTransparency .all <| whnf values
  let args := reduced.getAppArgs
  if reduced.getAppFn.constName? == some ``List.nil then
    return (false, mkAppN (mkConst ``List.not_mem_nil [Level.zero])
      #[mkConst ``Nat, index])
  unless reduced.getAppFn.constName? == some ``List.cons do
    throwError "sparse_evidence_decide: needed set did not expose as a list"
  let head := args[args.size - 2]!
  let tail := args.back!
  if ← isDefEq index head then
    return (true, mkAppN (mkConst ``List.mem_cons_self [Level.zero])
      #[mkConst ``Nat, index, tail])
  let (found, tailProof) ← proveNatMembershipAux index tail
  if found then
    return (true, mkAppN (mkConst ``List.mem_cons_of_mem [Level.zero])
      #[mkConst ``Nat, head, index, tail, tailProof])
  let inequalityDecision ← withTransparency .all <|
    whnf (mkApp2 (mkConst ``Nat.decEq) index head)
  unless inequalityDecision.getAppFn.constName? == some ``Decidable.isFalse do
    throwError "sparse_evidence_decide: unequal indices did not decide"
  let inequality := inequalityDecision.getAppArgs.back!
  return (false,
    mkAppN (mkConst ``List.not_mem_cons_of_ne_of_not_mem [Level.zero])
      #[mkConst ``Nat, index, head, tail, inequality, tailProof])

private def decideNatMembership (index needed : Expr) : MetaM (Bool × Expr) := do
  let started ← IO.monoMsNow
  let result ← proveNatMembershipAux index needed
  let finished ← IO.monoMsNow
  sparseMembershipMs.modify (· + (finished - started))
  pure result

private def boundSparseProof (build : SparseProofBuild) : MetaM SparseProofBuild := do
  if build.size < 1024 then return build
  let started ← IO.monoMsNow
  let type ← inferType build.proof
  let proof ← cacheClosedProof type (← wrapLocalProofBindings build.proof)
  let finished ← IO.monoMsNow
  sparseBoundMs.modify (· + (finished - started))
  pure { build with proof, size := 1 }

private def sparseDecide (type : Expr) : MetaM Expr := do
  let started ← IO.monoMsNow
  let proof ← inlineDecideAccepted type
  let finished ← IO.monoMsNow
  sparseDecisionMs.modify (· + (finished - started))
  pure proof

private def sparseTimedDecide (counter : IO.Ref Nat) (type : Expr) : MetaM Expr := do
  let started ← IO.monoMsNow
  let proof ← sparseDecide type
  let finished ← IO.monoMsNow
  counter.modify (· + (finished - started))
  pure proof

private def sparseExpressionEvidence (wires table expression reference : Expr) :
    MetaM Expr := do
  let started ← IO.monoMsNow
  let proof ← proveIndexedExprEvidence indexedExprModuleCache wires table
    expression reference
  let finished ← IO.monoMsNow
  sparseExpressionMs.modify (· + (finished - started))
  pure proof

/-- Build join-checker evidence one bounded lookup at a time. The tail is an
evidence term rather than a recursive Boolean reduction, so the kernel does
not repeatedly normalize the complete join list and sparse branch states. -/
private partial def proveBitJoinsEvidence (registers condition thenRefs elseRefs
    changed joins : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf joins
  let args := reduced.getAppArgs
  if reduced.getAppFn.constName? == some ``List.nil then
    let changedReduced ← normalizeNatLiteral changed
    unless (← getNatValue? changedReduced) == some 0 do
      throwError "sparse_evidence_decide: join bitmap is nonzero at list end"
    return mkAppN
      (mkConst ``Loom.Release.Symbolic.ActionWide.BitJoinsEvidence.nil)
      #[registers, condition, thenRefs, elseRefs]
  unless reduced.getAppFn.constName? == some ``List.cons do
    throwError "sparse_evidence_decide: joins did not expose as a list"
  let join := args[args.size - 2]!
  let tail := args.back!
  let headCheck ← mkAppM ``Loom.Release.Symbolic.ActionWide.checkedBitJoin
    #[registers, condition, thenRefs, elseRefs, changed, join]
  let headProof ← sparseTimedDecide sparseJoinMs (← mkEq headCheck trueExpr)
  let joinReduced ← withTransparency .all <| whnf join
  let joinArgs := joinReduced.getAppArgs
  unless joinReduced.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.Join.mk do
    throwError "sparse_evidence_decide: join did not expose as a constructor"
  let index := joinArgs[joinArgs.size - 6]!
  let nextChangedComputed := mkApp2 (mkConst ``Nat.xor) changed
    (singletonChangedBit index)
  let nextChanged ← normalizeNatLiteral nextChangedComputed
  let tailProof ← proveBitJoinsEvidence registers condition thenRefs elseRefs
    nextChanged tail
  return mkAppN
    (mkConst ``Loom.Release.Symbolic.ActionWide.BitJoinsEvidence.cons)
    #[registers, condition, thenRefs, elseRefs, changed, join, tail,
      headProof, tailProof]

/-- Construct sparse action evidence in one top-down traversal.  Unlike the
generated selector path, recursive calls receive the already exposed source
and certificate subterms, so no child walks back through the processor root. -/
private partial def proveSparseEvidence (wires table registers action refs needed cert :
    Expr) : MetaM SparseProofBuild := do
  let count ← sparseNodeCount.modifyGet fun count => (count + 1, count + 1)
  let actionStarted ← IO.monoMsNow
  let actionReduced ← exposeAction action
  let actionFinished ← IO.monoMsNow
  sparseActionExposeMs.modify (· + (actionFinished - actionStarted))
  let actionName := actionReduced.getAppFn.constName?.getD Name.anonymous
  let actionArgs := actionReduced.getAppArgs
  if actionName == ``List.foldr then
    let function := actionArgs[actionArgs.size - 3]!
    let initial := actionArgs[actionArgs.size - 2]!
    let values := actionArgs.back!
    let simpContext ← Simp.Context.mkDefault
    let (valuesResult, _) ← simp values simpContext
    let expanded ← expandListFoldr function initial valuesResult.expr
    let build ← proveSparseEvidence wires table registers expanded refs needed cert
    let some valuesEq := valuesResult.proof? | return build
    let valuesType ← inferType values
    let foldMotive ← withLocalDeclD `values valuesType fun xs =>
      mkLambdaFVars #[xs] (mkAppN actionReduced.getAppFn
        (actionArgs.pop.push xs))
    let actionEq ← mkCongrArg foldMotive valuesEq
    let equalityType ← inferType actionEq
    let actionType := equalityType.getAppArgs[0]!
    let evidenceMotive ← withLocalDeclD `action actionType fun concreteAction => do
      let proposition := mkAppN
        (mkConst ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence)
        #[wires, table, registers, concreteAction, refs, needed, cert, build.result]
      mkLambdaFVars #[concreteAction] proposition
    let propositionEq ← mkCongrArg evidenceMotive actionEq
    let proof ← mkAppM ``Eq.mpr #[propositionEq, build.proof]
    return { build with proof }
  let certStarted ← IO.monoMsNow
  let (certName, certArgs) ← expose cert
  let certFinished ← IO.monoMsNow
  sparseCertExposeMs.modify (· + (certFinished - certStarted))
  if count % 5000 == 0 then
    let actionMs ← sparseActionExposeMs.get
    let certMs ← sparseCertExposeMs.get
    let boundMs ← sparseBoundMs.get
    let expressionMs ← sparseExpressionMs.get
    let decisionMs ← sparseDecisionMs.get
    let membershipMs ← sparseMembershipMs.get
    let headerMs ← sparseHeaderMs.get
    let bitMs ← sparseBitMs.get
    let summaryMs ← sparseSummaryMs.get
    let joinMs ← sparseJoinMs.get
    let expressionNodes := (← indexedExprModuleCache.get).size
    let lookupMs ← indexedLookupMs.get
    let exprExposeMs ← indexedExposeMs.get
    IO.eprintln (s!"{count} nodes: action-expose={actionMs}ms " ++
      s!"cert-expose={certMs}ms bound={boundMs}ms " ++
      s!"expression={expressionMs}ms decision={decisionMs}ms " ++
      s!"membership={membershipMs}ms expression-nodes={expressionNodes} " ++
      s!"lookup={lookupMs}ms expr-expose={exprExposeMs}ms " ++
      s!"header={headerMs}ms bit={bitMs}ms summary={summaryMs}ms join={joinMs}ms")
  if actionName == ``Loom.Hw.Act.skip && certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.skip then
    let result ← sparseResult refs noChangedBits
    let proof := mkAppN (mkConst ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence.skip)
      #[wires, table, registers, refs, needed]
    return { result, proof, size := 1 }
  if actionName == ``Loom.Hw.Act.memWrite &&
      certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.memWrite then
    let proof := mkAppN (mkConst ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence.memWrite)
      #[wires, table, registers,
        actionArgs[actionArgs.size - 6]!, actionArgs[actionArgs.size - 5]!,
        actionArgs[actionArgs.size - 4]!, actionArgs[actionArgs.size - 3]!,
        actionArgs[actionArgs.size - 2]!, actionArgs.back!, refs, needed]
    return { result := ← sparseResult refs noChangedBits, proof, size := 1 }
  if actionName == ``Loom.Hw.Act.write &&
      certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.write then
    let width := actionArgs[actionArgs.size - 3]!
    let name := actionArgs[actionArgs.size - 2]!
    let value := actionArgs.back!
    let index := certArgs[certArgs.size - 2]!
    let valueRef := certArgs.back!
    let header ← mkAppM ``Loom.Release.Symbolic.ActionWide.checkedWriteHeader
      #[registers, index, width, name]
    let headerProof ← sparseTimedDecide sparseHeaderMs (← mkEq header trueExpr)
    let usedCheck ← mkAppM ``Nat.testBit #[needed, index]
    let usedReduced ← withTransparency .all <| whnf usedCheck
    let used := usedReduced.isConstOf ``Bool.true
    if used then
      let usedProof ← sparseTimedDecide sparseBitMs (← mkEq usedCheck trueExpr)
      let compiled ← mkAppM ``Loom.Hw.Compile.compileExpr #[value]
      let expressionEvidence ← sparseExpressionEvidence wires table compiled
        valueRef
      let expressionProof ← mkAppM ``IndexedExprEvidence.accepted
        #[expressionEvidence]
      let resultRefs ← mkAppM ``Loom.Release.Symbolic.ActionWide.SparseRefs.write
        #[refs, index, valueRef]
      let result ← sparseResult resultRefs (singletonChangedBit index)
      let proof := mkAppN (mkConst ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence.writeNeeded)
        #[wires, table, registers, width, name, value, refs, needed, index,
          valueRef, headerProof, usedProof, expressionProof]
      return { result, proof, size := 1 }
    else
      let unusedProof ← sparseTimedDecide sparseBitMs
        (← mkEq usedCheck (mkConst ``Bool.false))
      let result ← sparseResult refs noChangedBits
      let proof := mkAppN (mkConst ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence.writeUnused)
        #[wires, table, registers, width, name, value, refs, needed, index,
          valueRef, headerProof, unusedProof]
      return { result, proof, size := 1 }
  if actionName == ``Loom.Hw.Act.seq && certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.seq then
    let left := actionArgs[actionArgs.size - 2]!
    let right := actionArgs.back!
    let summary := certArgs[certArgs.size - 3]!
    let leftCert := certArgs[certArgs.size - 2]!
    let rightCert := certArgs.back!
    let rightSummary ← mkAppM ``Loom.Release.Symbolic.ActionWide.ActionCert.summary #[rightCert]
    let leftNeededComputed ← mkAppM
      ``Loom.Release.Symbolic.ActionWide.neededBitsBefore
      #[rightSummary, needed]
    let leftNeeded ← normalizeNatLiteral leftNeededComputed
    let leftBuild ← proveSparseEvidence wires table registers left refs
      leftNeeded leftCert >>= boundSparseProof
    let leftRefs ← sparseRefs leftBuild.result
    let rightBuild ← proveSparseEvidence wires table registers right leftRefs
      needed rightCert >>= boundSparseProof
    let expectedSummary ← mkAppM
      ``Loom.Release.Symbolic.ActionWide.ActionCert.summary #[cert]
    let summaryProof ← sparseTimedDecide sparseSummaryMs
      (← mkEq summary expectedSummary)
    let changedComputed ← mkAppM
      ``Loom.Release.Symbolic.ActionWide.changedBitsAt #[summary, needed]
    let changed ← normalizeNatLiteral changedComputed
    let result ← sparseResult (← sparseRefs rightBuild.result) changed
    let proof := mkAppN (mkConst ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence.seq)
      #[wires, table, registers, left, right, refs, needed, summary, leftCert,
        rightCert, leftBuild.result, rightBuild.result, summaryProof,
        leftBuild.proof, rightBuild.proof]
    return ← boundSparseProof
      { result, proof, size := leftBuild.size + rightBuild.size + 1 }
  if actionName == ``Loom.Hw.Act.ite && certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.ite then
    let condition := actionArgs[actionArgs.size - 3]!
    let thenAction := actionArgs[actionArgs.size - 2]!
    let elseAction := actionArgs.back!
    let summary := certArgs[certArgs.size - 5]!
    let conditionRef := certArgs[certArgs.size - 4]!
    let joins := certArgs[certArgs.size - 3]!
    let thenCert := certArgs[certArgs.size - 2]!
    let elseCert := certArgs.back!
    let changedComputed ← mkAppM
      ``Loom.Release.Symbolic.ActionWide.changedBitsAt #[summary, needed]
    let changed ← normalizeNatLiteral changedComputed
    let thenBuild ← proveSparseEvidence wires table registers thenAction refs
      changed thenCert >>= boundSparseProof
    let elseBuild ← proveSparseEvidence wires table registers elseAction refs
      changed elseCert >>= boundSparseProof
    let expectedSummary ← mkAppM
      ``Loom.Release.Symbolic.ActionWide.ActionCert.summary #[cert]
    let summaryProof ← sparseTimedDecide sparseSummaryMs
      (← mkEq summary expectedSummary)
    let compiled ← mkAppM ``Loom.Hw.Compile.compileExpr #[condition]
    let conditionEvidence ← sparseExpressionEvidence wires table compiled
      conditionRef
    let conditionProof ← mkAppM ``IndexedExprEvidence.accepted
      #[conditionEvidence]
    let thenRefs ← sparseRefs thenBuild.result
    let elseRefs ← sparseRefs elseBuild.result
    let joinsEvidence ← proveBitJoinsEvidence registers conditionRef thenRefs
      elseRefs changed joins
    let joinsProof ← mkAppM
      ``Loom.Release.Symbolic.ActionWide.BitJoinsEvidence.accepted
      #[joinsEvidence]
    let resultRefs ← mkAppM ``Loom.Release.Symbolic.ActionWide.applySparseJoins #[refs, joins]
    let result ← sparseResult resultRefs changed
    let proof := mkAppN (mkConst ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence.ite)
      #[wires, table, registers, condition, thenAction, elseAction, refs, needed,
        summary, conditionRef, joins, thenCert, elseCert, thenBuild.result,
        elseBuild.result, summaryProof, conditionProof, thenBuild.proof,
        elseBuild.proof, joinsProof]
    return ← boundSparseProof
      { result, proof, size := thenBuild.size + elseBuild.size + 1 }
  throwError "sparse_evidence_decide: source/certificate shape mismatch at node {count}: source={actionName}, certificate={certName}"

/-- Prove a complete sparse action certificate by a single source traversal. -/
syntax (name := sparseEvidenceDecide) "sparse_evidence_decide" : term

@[term_elab sparseEvidenceDecide]
unsafe def elabSparseEvidenceDecide : TermElab := fun _ expected? => do
  -- Auxiliary lemmas created while elaborating one declaration are committed
  -- with that declaration. Do not leak their temporary names into the next
  -- top-level sparse proof; sharing is needed across this traversal only.
  indexedExprModuleCache.set {}
  indexedExprPendingNodes.set 0
  indexedLookupMs.set 0
  indexedExposeMs.set 0
  sparseNodeCount.set 0
  sparseActionExposeMs.set 0
  sparseCertExposeMs.set 0
  sparseBoundMs.set 0
  sparseExpressionMs.set 0
  sparseDecisionMs.set 0
  sparseMembershipMs.set 0
  sparseHeaderMs.set 0
  sparseBitMs.set 0
  sparseSummaryMs.set 0
  sparseJoinMs.set 0
  localProofBindings.set #[]
  useLocalProofBindings.set true
  let some expected := expected?
    | throwError "sparse_evidence_decide requires an expected proposition"
  let expected ← instantiateMVars expected
  let args := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence &&
      args.size == 8 do
    throwError "sparse_evidence_decide expected BitSparseEvidence"
  let build ← proveSparseEvidence args[0]! args[1]! args[2]! args[3]!
    args[4]! args[5]! args[6]!
  unless ← isDefEq build.result args[7]! do
    throwError "sparse_evidence_decide result does not match the expected result"
  let proof ← wrapLocalProofBindings build.proof
  reportSparseStats
  useLocalProofBindings.set false
  pure proof

/-- Infer the sparse result while producing evidence. This keeps the theorem
statement compact; a later constant-time projection obtains checker
acceptance from the existential witness. -/
syntax (name := sparseEvidenceExists) "sparse_evidence_exists" : term

@[term_elab sparseEvidenceExists]
unsafe def elabSparseEvidenceExists : TermElab := fun _ expected? => do
  indexedExprModuleCache.set {}
  indexedExprPendingNodes.set 0
  indexedLookupMs.set 0
  indexedExposeMs.set 0
  sparseNodeCount.set 0
  sparseActionExposeMs.set 0
  sparseCertExposeMs.set 0
  sparseBoundMs.set 0
  sparseExpressionMs.set 0
  sparseDecisionMs.set 0
  sparseMembershipMs.set 0
  sparseHeaderMs.set 0
  sparseBitMs.set 0
  sparseSummaryMs.set 0
  sparseJoinMs.set 0
  localProofBindings.set #[]
  useLocalProofBindings.set true
  let some expected := expected?
    | throwError "sparse_evidence_exists requires an expected proposition"
  let expected ← instantiateMVars expected
  let existsArgs := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``Exists && existsArgs.size == 2 do
    throwError "sparse_evidence_exists expected an existential"
  let witness ← mkFreshExprMVar existsArgs[0]!
  let body ← whnf (mkApp existsArgs[1]! witness)
  let args := body.getAppArgs
  unless body.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.BitSparseEvidence &&
      args.size == 8 do
    throwError "sparse_evidence_exists expected existential BitSparseEvidence"
  let build ← proveSparseEvidence args[0]! args[1]! args[2]! args[3]!
    args[4]! args[5]! args[6]!
  let proof ← mkAppM ``Exists.intro #[build.result, build.proof]
  let proof ← wrapLocalProofBindings proof
  reportSparseStats
  useLocalProofBindings.set false
  pure proof

/-! ### Hash-consed state-DAG evidence

This path threads numeric trie roots rather than expanded `SparseRefs` terms.
The generator supplies traversal traces, but every referenced state update and
lookup is checked against the balanced node table by the kernel. -/

private initialize dagActionRoots : IO.Ref (Array Nat) ← IO.mkRef #[]
private initialize dagWriteRoots : IO.Ref (Array Nat) ← IO.mkRef #[]
private initialize dagActionCursor : IO.Ref Nat ← IO.mkRef 0
private initialize dagWriteCursor : IO.Ref Nat ← IO.mkRef 0
private initialize dagNodeCount : IO.Ref Nat ← IO.mkRef 0
private initialize dagBoundMs : IO.Ref Nat ← IO.mkRef 0
private initialize dagDecisionMs : IO.Ref Nat ← IO.mkRef 0

syntax (name := dagActionRootsCmd) "dag_action_roots" num* : command
syntax (name := dagWriteRootsCmd) "dag_write_roots" num* : command

private def readDagRoots (arguments : Array Syntax) : Command.CommandElabM
    (Array Nat) := do
  let mut roots := #[]
  for argument in arguments do
    let some value := argument.isNatLit?
      | throwErrorAt argument "DAG roots must be natural literals"
    roots := roots.push value
  pure roots

@[command_elab dagActionRootsCmd]
unsafe def elabDagActionRoots : Command.CommandElab := fun stx => do
  dagActionRoots.set (← readDagRoots stx[1].getArgs)

@[command_elab dagWriteRootsCmd]
unsafe def elabDagWriteRoots : Command.CommandElab := fun stx => do
  dagWriteRoots.set (← readDagRoots stx[1].getArgs)

private structure DagProofBuild where
  root : Expr
  proof : Expr
  size : Nat

private def takeDagRoot (values : IO.Ref (Array Nat))
    (cursor : IO.Ref Nat) (kind : String) : MetaM Expr := do
  let index ← cursor.get
  let roots ← values.get
  let some root := roots[index]?
    | throwError "dag_sparse_evidence_exists: exhausted {kind} roots at {index}"
  cursor.set (index + 1)
  pure (mkNatLit root)

private def checkDagActionRoot (actual : Expr) : MetaM Unit := do
  let expected ← takeDagRoot dagActionRoots dagActionCursor "action"
  unless ← isDefEq actual expected do
    throwError "dag_sparse_evidence_exists: action-root trace mismatch"

private def dagDecide (type : Expr) : MetaM Expr := do
  let started ← IO.monoMsNow
  let proof ← inlineDecideAccepted type
  let finished ← IO.monoMsNow
  dagDecisionMs.modify (· + (finished - started))
  pure proof

private def boundDagProof (build : DagProofBuild) : MetaM DagProofBuild := do
  if build.size < 8 then return build
  let started ← IO.monoMsNow
  let type ← inferType build.proof
  let proof ← cacheClosedProof type (← wrapLocalProofBindings build.proof)
  let finished ← IO.monoMsNow
  dagBoundMs.modify (· + (finished - started))
  pure { build with proof, size := 1 }

private def proveStateNodeLookup (nodes stateTable number : Expr) :
    MetaM (Expr × Expr) := do
  let reducedNumber ← withTransparency .all <| whnf number
  let some numberValue ← getNatValue? reducedNumber
    | throwError "dag_sparse_evidence_exists: state node is not concrete"
  let some nodesName := nodes.getAppFn.constName?
    | throwError "dag_sparse_evidence_exists: state nodes are not named"
  let tableReduced ← withTransparency .all <| whnf stateTable
  let tableArgs := tableReduced.getAppArgs
  unless tableReduced.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.RefStateTable.mk &&
      tableArgs.size >= 3 do
    throwError "dag_sparse_evidence_exists: state table did not expose"
  let leafSize := tableArgs[tableArgs.size - 3]!
  let leafCount := tableArgs[tableArgs.size - 2]!
  let some leafSizeValue ← getNatValue? leafSize
    | throwError "dag_sparse_evidence_exists: state leaf size is not concrete"
  if leafSizeValue == 0 then
    throwError "dag_sparse_evidence_exists: state leaf size is zero"
  let leafIndex := numberValue / leafSizeValue
  let resolverName := nodesName.getPrefix.str
    ("dagStateResolveLeaf" ++ pad4 leafIndex)
  unless (← getEnv).contains resolverName do
    throwError "dag_sparse_evidence_exists: missing state resolver {resolverName}"
  let offset := mkNatLit (numberValue % leafSizeValue)
  let resolver ← mkAppM resolverName #[offset]
  let resolverType ← inferType resolver
  let resolverArgs := resolverType.getAppArgs
  unless resolverType.getAppFn.constName? == some ``Eq &&
      resolverArgs.size == 3 do
    throwError "dag_sparse_evidence_exists: malformed state resolver"
  let reducedRight ← withTransparency .all <| whnf resolverArgs[2]!
  unless reducedRight.getAppFn.constName? == some ``Option.some do
    throwError "dag_sparse_evidence_exists: state node lookup failed"
  let node := reducedRight.getAppArgs.back!
  let resolveLeft := resolverArgs[1]!
  let resolveArgs := resolveLeft.getAppArgs
  let reference ← withTransparency .all <| whnf resolveArgs.back!
  let referenceArgs := reference.getAppArgs
  let path := referenceArgs[referenceArgs.size - 2]!
  let positiveProof ← mkAppM ``Nat.zero_lt_succ
    #[mkNatLit (leafSizeValue - 1)]
  let pathCheck ← mkAppM ``balancedPath?
    #[leafCount, mkNatLit leafIndex]
  let pathProof ← dagDecide
    (← mkEq pathCheck (← mkAppM ``Option.some #[path]))
  let proof := mkAppN (mkConst
    ``Loom.Release.Symbolic.ActionWide.lookupStateNode_of_resolve)
    #[nodes, stateTable, reducedNumber, path, node, positiveProof, pathProof,
      resolver]
  pure (node, proof)

private partial def proveDagWriteAt (nodes stateTable : Expr) (depth : Nat)
    (input index value output : Expr) : MetaM Expr := do
  let (outputNode, outputProof) ← proveStateNodeLookup nodes stateTable output
  if depth == 0 then
    let outputReduced ← withTransparency .all <| whnf outputNode
    unless outputReduced.getAppFn.constName? ==
        some ``Loom.Release.Symbolic.ActionWide.RefStateNode.leaf do
      throwError "dag_sparse_evidence_exists: write leaf is malformed"
    unless ← isDefEq outputReduced.getAppArgs.back! value do
      throwError "dag_sparse_evidence_exists: write leaf value mismatch"
    return mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.StateWriteEvidence.leaf)
      #[nodes, stateTable, input, index, value, output, outputProof]
  let childDepth := depth - 1
  let bitCheck ← mkAppM ``Nat.testBit #[index, mkNatLit childDepth]
  let bitReduced ← withTransparency .all <| whnf bitCheck
  let bit := bitReduced.isConstOf ``Bool.true
  let bitExpected := Lean.mkConst
    (if bit then ``Bool.true else ``Bool.false)
  let bitProof ← dagDecide (← mkEq bitCheck bitExpected)
  let (inputNode, inputProof) ← proveStateNodeLookup nodes stateTable input
  let inputReduced ← withTransparency .all <| whnf inputNode
  let outputReduced ← withTransparency .all <| whnf outputNode
  unless outputReduced.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.RefStateNode.branch do
    throwError "dag_sparse_evidence_exists: write output is not a branch"
  let outputArgs := outputReduced.getAppArgs
  let newZero := outputArgs[outputArgs.size - 2]!
  let newOne := outputArgs.back!
  let emptyRoot ← mkAppM
    ``Loom.Release.Symbolic.ActionWide.RefStateTable.emptyRoot #[stateTable]
  if inputReduced.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.RefStateNode.empty then
    if bit then
      unless ← isDefEq newZero emptyRoot do
        throwError "dag_sparse_evidence_exists: empty write changed zero child"
      let childProof ← proveDagWriteAt nodes stateTable childDepth emptyRoot
        index value newOne
      return mkAppN (mkConst
        ``Loom.Release.Symbolic.ActionWide.StateWriteEvidence.emptyOne)
        #[nodes, stateTable, mkNatLit childDepth, input, index, value, output,
          newOne, bitProof, inputProof, outputProof, childProof]
    else
      unless ← isDefEq newOne emptyRoot do
        throwError "dag_sparse_evidence_exists: empty write changed one child"
      let childProof ← proveDagWriteAt nodes stateTable childDepth emptyRoot
        index value newZero
      return mkAppN (mkConst
        ``Loom.Release.Symbolic.ActionWide.StateWriteEvidence.emptyZero)
        #[nodes, stateTable, mkNatLit childDepth, input, index, value, output,
          newZero, bitProof, inputProof, outputProof, childProof]
  unless inputReduced.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.RefStateNode.branch do
    throwError "dag_sparse_evidence_exists: write input is malformed"
  let inputArgs := inputReduced.getAppArgs
  let oldZero := inputArgs[inputArgs.size - 2]!
  let oldOne := inputArgs.back!
  if bit then
    unless ← isDefEq newZero oldZero do
      throwError "dag_sparse_evidence_exists: write changed zero child"
    let childProof ← proveDagWriteAt nodes stateTable childDepth oldOne index
      value newOne
    return mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.StateWriteEvidence.branchOne)
      #[nodes, stateTable, mkNatLit childDepth, input, index, value, output,
        oldZero, oldOne, newOne, bitProof, inputProof, outputProof, childProof]
  else
    unless ← isDefEq newOne oldOne do
      throwError "dag_sparse_evidence_exists: write changed one child"
    let childProof ← proveDagWriteAt nodes stateTable childDepth oldZero index
      value newZero
    return mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.StateWriteEvidence.branchZero)
      #[nodes, stateTable, mkNatLit childDepth, input, index, value, output,
        oldZero, oldOne, newZero, bitProof, inputProof, outputProof, childProof]

private def proveDagWrite (nodes stateTable input index value output : Expr) :
    MetaM Expr :=
  proveDagWriteAt nodes stateTable 10 input index value output

private partial def proveDagLookup (nodes stateTable registers : Expr)
    (depth : Nat) (root index value : Expr) : MetaM Expr := do
  let (node, nodeProof) ← proveStateNodeLookup nodes stateTable root
  let reduced ← withTransparency .all <| whnf node
  if reduced.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.RefStateNode.empty then
    let registerCheck ← mkAppM ``getElem? #[registers, index]
    let registerReduced ← withTransparency .all <| whnf registerCheck
    unless registerReduced.getAppFn.constName? == some ``Option.some do
      throwError "dag_sparse_evidence_exists: register lookup failed"
    let register := registerReduced.getAppArgs.back!
    let name ← mkAppM ``Loom.Hw.RegDecl.name #[register]
    let expected ← mkAppM ``Loom.Release.Symbolic.Ref.reg #[name]
    unless ← isDefEq expected value do
      throwError "dag_sparse_evidence_exists: fallback register mismatch"
    let registerProof ← mkEqRefl registerCheck
    return mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.StateLookupEvidence.empty)
      #[nodes, stateTable, registers, mkNatLit depth, root, index, register,
        nodeProof, registerProof]
  if depth == 0 then
    unless reduced.getAppFn.constName? ==
        some ``Loom.Release.Symbolic.ActionWide.RefStateNode.leaf do
      throwError "dag_sparse_evidence_exists: lookup leaf is malformed"
    unless ← isDefEq reduced.getAppArgs.back! value do
      throwError "dag_sparse_evidence_exists: lookup leaf value mismatch"
    return mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.StateLookupEvidence.leaf)
      #[nodes, stateTable, registers, root, index, value, nodeProof]
  unless reduced.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.RefStateNode.branch do
    throwError "dag_sparse_evidence_exists: lookup node is malformed"
  let nodeArgs := reduced.getAppArgs
  let zeroChild := nodeArgs[nodeArgs.size - 2]!
  let oneChild := nodeArgs.back!
  let childDepth := depth - 1
  let bitCheck ← mkAppM ``Nat.testBit #[index, mkNatLit childDepth]
  let bitReduced ← withTransparency .all <| whnf bitCheck
  let bit := bitReduced.isConstOf ``Bool.true
  let bitProof ← dagDecide (← mkEq bitCheck
    (mkConst (if bit then ``Bool.true else ``Bool.false)))
  let childProof ← proveDagLookup nodes stateTable registers childDepth
    (if bit then oneChild else zeroChild) index value
  pure <| mkAppN (mkConst (if bit then
      ``Loom.Release.Symbolic.ActionWide.StateLookupEvidence.branchOne
    else ``Loom.Release.Symbolic.ActionWide.StateLookupEvidence.branchZero))
    #[nodes, stateTable, registers, mkNatLit childDepth, root, index, value,
      zeroChild, oneChild, bitProof, nodeProof, childProof]

private partial def proveDagJoins (nodes stateTable registers condition input
    thenRoot elseRoot changed joins : Expr) : MetaM (Expr × Expr) := do
  let reduced ← withTransparency .all <| whnf joins
  let args := reduced.getAppArgs
  if reduced.getAppFn.constName? == some ``List.nil then
    let changed ← normalizeNatLiteral changed
    unless (← getNatValue? changed) == some 0 do
      throwError "dag_sparse_evidence_exists: nonzero join bitmap at list end"
    let proof := mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.StateJoinsEvidence.nil)
      #[nodes, stateTable, registers, condition, input, thenRoot, elseRoot]
    return (input, proof)
  unless reduced.getAppFn.constName? == some ``List.cons do
    throwError "dag_sparse_evidence_exists: joins did not expose as a list"
  let join := args[args.size - 2]!
  let tail := args.back!
  let index ← mkAppM ``Loom.Release.Symbolic.ActionWide.Join.index #[join]
  let width ← mkAppM ``Loom.Release.Symbolic.ActionWide.Join.width #[join]
  let guard ← mkAppM ``Loom.Release.Symbolic.ActionWide.Join.guard #[join]
  let thenInput ← mkAppM ``Loom.Release.Symbolic.ActionWide.Join.thenInput #[join]
  let elseInput ← mkAppM ``Loom.Release.Symbolic.ActionWide.Join.elseInput #[join]
  let output ← mkAppM ``Loom.Release.Symbolic.ActionWide.Join.output #[join]
  let bitCheck ← mkAppM ``Nat.testBit #[changed, index]
  let bitProof ← dagDecide (← mkEq bitCheck trueExpr)
  let register ← mkAppM ``getElem? #[registers, index]
  let widthProjection ← withLocalDeclD `register (mkConst ``Loom.Hw.RegDecl)
    fun source => mkLambdaFVars #[source]
      (mkApp (mkConst ``Loom.Hw.RegDecl.width) source)
  let widthCheck ← mkAppM ``Option.map #[widthProjection, register]
  let widthProof ← dagDecide
    (← mkEq widthCheck (← mkAppM ``Option.some #[width]))
  let thenProof ← proveDagLookup nodes stateTable registers 10 thenRoot index
    thenInput
  let elseProof ← proveDagLookup nodes stateTable registers 10 elseRoot index
    elseInput
  let guardProof ← dagDecide (← mkEq guard condition)
  let outputReduced ← withTransparency .all <| whnf output
  unless outputReduced.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.Ref.wire do
    throwError "dag_sparse_evidence_exists: join output is not a wire"
  let number := outputReduced.getAppArgs.back!
  let wireValue ← mkAppM ``Loom.Release.Symbolic.Ref.wire #[number]
  let wireEq ← dagDecide (← mkEq output wireValue)
  let wirePredicate ← withLocalDeclD `number (mkConst ``Nat) fun candidate => do
    let candidateWire ← mkAppM ``Loom.Release.Symbolic.Ref.wire #[candidate]
    mkLambdaFVars #[candidate] (← mkEq output candidateWire)
  let wireProof := mkAppN
    (mkConst ``Exists.intro [Level.succ Level.zero])
    #[mkConst ``Nat, wirePredicate, number, wireEq]
  let nextRoot ← takeDagRoot dagWriteRoots dagWriteCursor "write"
  let writeProof ← proveDagWrite nodes stateTable input index output nextRoot
  let nextChangedComputed := mkApp2 (mkConst ``Nat.xor) changed
    (singletonChangedBit index)
  let nextChanged ← normalizeNatLiteral nextChangedComputed
  let (outputRoot, tailProof) ← proveDagJoins nodes stateTable registers condition
    nextRoot thenRoot elseRoot nextChanged tail
  let proof := mkAppN (mkConst
    ``Loom.Release.Symbolic.ActionWide.StateJoinsEvidence.cons)
    #[nodes, stateTable, registers, condition, input, thenRoot, elseRoot,
      changed, join, tail, nextRoot, outputRoot, bitProof, widthProof,
      thenProof, elseProof, guardProof, wireProof, writeProof, tailProof]
  pure (outputRoot, proof)

private partial def proveDagEvidence (wires wireTable nodes stateTable registers
    action root needed cert : Expr) : MetaM DagProofBuild := do
  let count ← dagNodeCount.modifyGet fun count => (count + 1, count + 1)
  if count % 100 == 0 then
    IO.eprintln (s!"dag evidence {count} nodes: bound={← dagBoundMs.get}ms " ++
      s!"decision={← dagDecisionMs.get}ms")
  let actionReduced ← exposeAction action
  let actionName := actionReduced.getAppFn.constName?.getD Name.anonymous
  let actionArgs := actionReduced.getAppArgs
  if actionName == ``List.foldr then
    let function := actionArgs[actionArgs.size - 3]!
    let initial := actionArgs[actionArgs.size - 2]!
    let values := actionArgs.back!
    let simpContext ← Simp.Context.mkDefault
    let (valuesResult, _) ← simp values simpContext
    let expanded ← expandListFoldr function initial valuesResult.expr
    return ← proveDagEvidence wires wireTable nodes stateTable registers expanded
      root needed cert
  let (certName, certArgs) ← expose cert
  if actionName == ``Loom.Hw.Act.skip &&
      certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.skip then
    let proof := mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.DagBitSparseEvidence.skip)
      #[wires, wireTable, nodes, stateTable, registers, root, needed]
    checkDagActionRoot root
    return { root, proof, size := 1 }
  if actionName == ``Loom.Hw.Act.memWrite &&
      certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.memWrite then
    let proof := mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.DagBitSparseEvidence.memWrite)
      #[wires, wireTable, nodes, stateTable, registers,
        actionArgs[actionArgs.size - 6]!, actionArgs[actionArgs.size - 5]!,
        actionArgs[actionArgs.size - 4]!, actionArgs[actionArgs.size - 3]!,
        actionArgs[actionArgs.size - 2]!, actionArgs.back!, root, needed]
    checkDagActionRoot root
    return { root, proof, size := 1 }
  if actionName == ``Loom.Hw.Act.write &&
      certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.write then
    let width := actionArgs[actionArgs.size - 3]!
    let name := actionArgs[actionArgs.size - 2]!
    let value := actionArgs.back!
    let index := certArgs[certArgs.size - 2]!
    let valueRef := certArgs.back!
    let header ← mkAppM ``Loom.Release.Symbolic.ActionWide.checkedWriteHeader
      #[registers, index, width, name]
    let headerProof ← dagDecide (← mkEq header trueExpr)
    let usedCheck ← mkAppM ``Nat.testBit #[needed, index]
    let usedReduced ← withTransparency .all <| whnf usedCheck
    if usedReduced.isConstOf ``Bool.true then
      let usedProof ← dagDecide (← mkEq usedCheck trueExpr)
      let compiled ← mkAppM ``Loom.Hw.Compile.compileExpr #[value]
      let expressionEvidence ← sparseExpressionEvidence wires wireTable compiled
        valueRef
      let expressionProof ← mkAppM ``IndexedExprEvidence.accepted
        #[expressionEvidence]
      let outputRoot ← takeDagRoot dagWriteRoots dagWriteCursor "write"
      let writeProof ← proveDagWrite nodes stateTable root index valueRef outputRoot
      let proof := mkAppN (mkConst
        ``Loom.Release.Symbolic.ActionWide.DagBitSparseEvidence.writeNeeded)
        #[wires, wireTable, nodes, stateTable, registers, width, name, value,
          root, needed, index, valueRef, outputRoot, headerProof, usedProof,
          expressionProof, writeProof]
      checkDagActionRoot outputRoot
      return { root := outputRoot, proof, size := 1 }
    else
      let unusedProof ← dagDecide
        (← mkEq usedCheck (mkConst ``Bool.false))
      let proof := mkAppN (mkConst
        ``Loom.Release.Symbolic.ActionWide.DagBitSparseEvidence.writeUnused)
        #[wires, wireTable, nodes, stateTable, registers, width, name, value,
          root, needed, index, valueRef, headerProof, unusedProof]
      checkDagActionRoot root
      return { root, proof, size := 1 }
  if actionName == ``Loom.Hw.Act.seq &&
      certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.seq then
    let left := actionArgs[actionArgs.size - 2]!
    let right := actionArgs.back!
    let summary := certArgs[certArgs.size - 3]!
    let leftCert := certArgs[certArgs.size - 2]!
    let rightCert := certArgs.back!
    let rightSummary ← mkAppM
      ``Loom.Release.Symbolic.ActionWide.ActionCert.summary #[rightCert]
    let leftNeeded ← normalizeNatLiteral
      (← mkAppM ``Loom.Release.Symbolic.ActionWide.neededBitsBefore
        #[rightSummary, needed])
    let leftBuild ← proveDagEvidence wires wireTable nodes stateTable registers
      left root leftNeeded leftCert >>= boundDagProof
    let rightBuild ← proveDagEvidence wires wireTable nodes stateTable registers
      right leftBuild.root needed rightCert >>= boundDagProof
    let expectedSummary ← mkAppM ``Loom.Release.Symbolic.ActionWide.seqSummary
      #[← mkAppM ``Loom.Release.Symbolic.ActionWide.ActionCert.summary #[leftCert],
        rightSummary]
    let summaryProof ← dagDecide (← mkEq summary expectedSummary)
    let proof := mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.DagBitSparseEvidence.seq)
      #[wires, wireTable, nodes, stateTable, registers, left, right, root,
        needed, summary, leftCert, rightCert, leftBuild.root, rightBuild.root,
        summaryProof, leftBuild.proof, rightBuild.proof]
    checkDagActionRoot rightBuild.root
    return ← boundDagProof
      { root := rightBuild.root, proof,
        size := leftBuild.size + rightBuild.size + 1 }
  if actionName == ``Loom.Hw.Act.ite &&
      certName == ``Loom.Release.Symbolic.ActionWide.ActionCert.ite then
    let condition := actionArgs[actionArgs.size - 3]!
    let thenAction := actionArgs[actionArgs.size - 2]!
    let elseAction := actionArgs.back!
    let summary := certArgs[certArgs.size - 5]!
    let conditionRef := certArgs[certArgs.size - 4]!
    let joins := certArgs[certArgs.size - 3]!
    let thenCert := certArgs[certArgs.size - 2]!
    let elseCert := certArgs.back!
    let changed ← normalizeNatLiteral
      (← mkAppM ``Loom.Release.Symbolic.ActionWide.changedBitsAt
        #[summary, needed])
    let thenBuild ← proveDagEvidence wires wireTable nodes stateTable registers
      thenAction root changed thenCert >>= boundDagProof
    let elseBuild ← proveDagEvidence wires wireTable nodes stateTable registers
      elseAction root changed elseCert >>= boundDagProof
    let expectedSummary ← mkAppM ``Loom.Release.Symbolic.ActionWide.iteSummary
      #[← mkAppM ``Loom.Release.Symbolic.ActionWide.ActionCert.summary #[thenCert],
        ← mkAppM ``Loom.Release.Symbolic.ActionWide.ActionCert.summary #[elseCert]]
    let summaryProof ← dagDecide (← mkEq summary expectedSummary)
    let compiled ← mkAppM ``Loom.Hw.Compile.compileExpr #[condition]
    let conditionEvidence ← sparseExpressionEvidence wires wireTable compiled
      conditionRef
    let conditionProof ← mkAppM ``IndexedExprEvidence.accepted
      #[conditionEvidence]
    let (outputRoot, joinsProof) ← proveDagJoins nodes stateTable registers
      conditionRef root thenBuild.root elseBuild.root changed joins
    let proof := mkAppN (mkConst
      ``Loom.Release.Symbolic.ActionWide.DagBitSparseEvidence.ite)
      #[wires, wireTable, nodes, stateTable, registers, condition, thenAction,
        elseAction, root, needed, summary, conditionRef, joins, thenCert,
        elseCert, thenBuild.root, elseBuild.root, outputRoot, summaryProof,
        conditionProof, thenBuild.proof, elseBuild.proof, joinsProof]
    checkDagActionRoot outputRoot
    return ← boundDagProof
      { root := outputRoot, proof,
        size := thenBuild.size + elseBuild.size + 1 }
  throwError "dag_sparse_evidence_exists: source/certificate shape mismatch"

syntax (name := dagSparseEvidenceExists) "dag_sparse_evidence_exists" : term

@[term_elab dagSparseEvidenceExists]
unsafe def elabDagSparseEvidenceExists : TermElab := fun stx expected? => do
  IO.eprintln "dag evidence: elaborator start"
  let `(dag_sparse_evidence_exists) := stx
    | throwError "invalid dag_sparse_evidence_exists syntax"
  if (← dagActionRoots.get).isEmpty then
    throwError "dag_sparse_evidence_exists has no action-root trace"
  IO.eprintln "dag evidence: traces available"
  dagActionCursor.set 0
  dagWriteCursor.set 0
  dagNodeCount.set 0
  dagBoundMs.set 0
  dagDecisionMs.set 0
  indexedExprModuleCache.set {}
  localProofBindings.set #[]
  useLocalProofBindings.set true
  let some expected := expected?
    | throwError "dag_sparse_evidence_exists requires an expected proposition"
  let expected ← instantiateMVars expected
  let existsArgs := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``Exists && existsArgs.size == 2 do
    throwError "dag_sparse_evidence_exists expected an existential"
  let witness ← mkFreshExprMVar existsArgs[0]!
  let body ← whnf (mkApp existsArgs[1]! witness)
  let args := body.getAppArgs
  unless body.getAppFn.constName? ==
      some ``Loom.Release.Symbolic.ActionWide.DagBitSparseEvidence &&
      args.size == 10 do
    throwError "dag_sparse_evidence_exists expected DagBitSparseEvidence"
  let build ← proveDagEvidence args[0]! args[1]! args[2]! args[3]! args[4]!
    args[5]! args[6]! args[7]! args[8]!
  IO.eprintln "dag evidence: traversal finished"
  unless ← isDefEq build.root witness do
    throwError "dag_sparse_evidence_exists result mismatch"
  unless (← dagActionCursor.get) == (← dagActionRoots.get).size do
    throwError "dag_sparse_evidence_exists left unused action roots"
  unless (← dagWriteCursor.get) == (← dagWriteRoots.get).size do
    throwError "dag_sparse_evidence_exists left unused write roots"
  let proof ← mkAppM ``Exists.intro #[build.root, build.proof]
  let proof ← wrapLocalProofBindings proof
  IO.eprintln (s!"dag evidence complete: nodes={← dagNodeCount.get} " ++
    s!"bound={← dagBoundMs.get}ms decision={← dagDecisionMs.get}ms")
  useLocalProofBindings.set false
  pure proof

private def transportNextRegAction (wires table register width current out cert
    actionEq proof : Expr) : MetaM Expr := do
  let equalityType ← inferType actionEq
  let actionType := equalityType.getAppArgs[0]!
  let motive ← withLocalDeclD `action actionType fun act => do
    let value ← mkAppM ``nextRegMatches
      #[wires, table, register, width, act, current, out, cert]
    let body ← mkBoolAccepted value
    mkLambdaFVars #[act] body
  let propositionEq ← mkCongrArg motive actionEq
  mkAppM ``Eq.mpr #[propositionEq, proof]

private partial def proveNextReg (wires table register width action current out cert : Expr) :
    MetaM Expr := do
  let simpContext ← Simp.Context.mkDefault
  let (actionResult, _) ← simp action simpContext
  if let some actionEq := actionResult.proof? then
    let proof ← proveNextReg wires table register width actionResult.expr
      current out cert
    return ← transportNextRegAction wires table register width current out cert
      actionEq proof
  let (actionName, actionArgs) ← exposeAction action >>= fun reduced =>
    pure (reduced.getAppFn.constName?.getD Name.anonymous, reduced.getAppArgs)
  let (certName, certArgs) ← expose cert
  if certName == ``NextRegCert.same then
    let (currentName, currentArgs) ← expose current
    unless currentName == ``Option.some do
      throwError "symbolic_kernel_decide: `.same` requires a known current reference"
    let currentRef := currentArgs[currentArgs.size - 1]!
    let noWriteCheck ← mkAppM ``Loom.Hw.Compile.writesRegB
      #[register, width, action]
    let noWriteType ← mkEq noWriteCheck (mkConst ``Bool.false)
    let noWriteProof ← cacheClosedProof noWriteType
      (← mkDecideProof noWriteType)
    return ← mkAppM ``nextRegMatches_same_of_writesRegB_false
      #[wires, table, register, width, action, currentRef, noWriteProof]
  if actionName == ``Loom.Hw.Act.seq && certName == ``NextRegCert.seq then
    let left := actionArgs[actionArgs.size - 2]!
    let right := actionArgs[actionArgs.size - 1]!
    let mid := certArgs[certArgs.size - 3]!
    let leftCert := certArgs[certArgs.size - 2]!
    let rightCert := certArgs[certArgs.size - 1]!
    let (midName, midArgs) ← expose mid
    if midName == ``Option.some then
      let midRef := midArgs[midArgs.size - 1]!
      let leftValue ← mkAppM ``nextRegMatches
        #[wires, table, register, width, left, current, midRef, leftCert]
      let leftType ← mkBoolAccepted leftValue
      let leftProof ← cacheAccepted leftType
        (← proveNextReg wires table register width left current midRef leftCert)
      let someMid ← mkAppM ``Option.some #[midRef]
      let rightValue ← mkAppM ``nextRegMatches
        #[wires, table, register, width, right, someMid, out, rightCert]
      let rightType ← mkBoolAccepted rightValue
      let rightProof ← cacheAccepted rightType
        (← proveNextReg wires table register width right someMid out rightCert)
      return ← mkAppM ``nextRegMatches_seq_named
        #[wires, table, register, width, left, right, current, midRef, out,
          leftCert, rightCert, leftProof, rightProof]
    else if midName == ``Option.none then
      let noneRef := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Ref)
      let rightValue ← mkAppM ``nextRegMatches
        #[wires, table, register, width, right, noneRef, out, rightCert]
      let rightType ← mkBoolAccepted rightValue
      let rightProof ← cacheAccepted rightType
        (← proveNextReg wires table register width right noneRef out rightCert)
      return ← mkAppM ``nextRegMatches_seq_discard
        #[wires, table, register, width, left, right, current, out,
          leftCert, rightCert, rightProof]
  if actionName == ``Loom.Hw.Act.ite && certName == ``NextRegCert.ite then
    let guard := actionArgs[actionArgs.size - 3]!
    let thenAction := actionArgs[actionArgs.size - 2]!
    let elseAction := actionArgs[actionArgs.size - 1]!
    let thenCert := certArgs[certArgs.size - 2]!
    let elseCert := certArgs[certArgs.size - 1]!
    let (outName, outArgs) ← expose out
    unless outName == ``Ref.wire do
      throwError "symbolic_kernel_decide: written ite output is not a wire"
    let number := outArgs[outArgs.size - 1]!
    let lookup ← mkAppM ``lookupIndexed? #[wires, table, number]
    let lookupReduced ← withTransparency .all <| whnf lookup
    let (lookupName, lookupArgs) ← expose lookupReduced
    unless lookupName == ``Option.some do
      throwError "symbolic_kernel_decide: ite output lookup failed"
    let indexedWire := lookupArgs[lookupArgs.size - 1]!
    let (wireName, wireArgs) ← expose indexedWire
    unless wireName == ``IndexedWire.mk do
      throwError "symbolic_kernel_decide: malformed indexed wire"
    let actualWidth := wireArgs[wireArgs.size - 2]!
    unless ← isDefEq actualWidth width do
      throwError "symbolic_kernel_decide: ite output width mismatch"
    let rhs := wireArgs[wireArgs.size - 1]!
    let (rhsName, rhsArgs) ← expose rhs
    unless rhsName == ``IndexedRhs.mux do
      throwError "symbolic_kernel_decide: ite output is not a mux"
    let guardRef := rhsArgs[rhsArgs.size - 3]!
    let thenRef := rhsArgs[rhsArgs.size - 2]!
    let elseRef := rhsArgs[rhsArgs.size - 1]!
    let writesProof ← proveRegWritesOr register width thenAction elseAction
    let lookupExpected ← mkAppM ``Option.some #[indexedWire]
    let lookupType ← mkEq lookup lookupExpected
    let lookupProof ← cacheClosedProof lookupType (← mkEqRefl lookup)
    let compiledGuard ← mkAppM ``Loom.Hw.Compile.compileExpr #[guard]
    let guardValue ← mkAppM ``indexedExprMatches
      #[wires, table, compiledGuard, guardRef]
    let guardType ← mkBoolAccepted guardValue
    let guardProof ← decideAccepted guardType
    let thenValue ← mkAppM ``nextRegMatches
      #[wires, table, register, width, thenAction, current, thenRef, thenCert]
    let thenType ← mkBoolAccepted thenValue
    let thenProof ← cacheAccepted thenType
      (← proveNextReg wires table register width thenAction current thenRef thenCert)
    let elseValue ← mkAppM ``nextRegMatches
      #[wires, table, register, width, elseAction, current, elseRef, elseCert]
    let elseType ← mkBoolAccepted elseValue
    let elseProof ← cacheAccepted elseType
      (← proveNextReg wires table register width elseAction current elseRef elseCert)
    return ← mkAppM ``nextRegMatches_ite_written
      #[wires, table, register, width, guard, thenAction, elseAction, current,
        number, guardRef, thenRef, elseRef, thenCert, elseCert, writesProof,
        lookupProof, guardProof, thenProof, elseProof]
  let value ← mkAppM ``nextRegMatches
    #[wires, table, register, width, action, current, out, cert]
  decideAccepted (← mkBoolAccepted value)

private partial def proveNextRules (wires table register width rules current out cert : Expr) :
    MetaM Expr := do
  let (rulesName, rulesArgs) ← expose rules
  let (certName, certArgs) ← expose cert
  if rulesName == ``List.nil && certName == ``NextRulesCert.nil then
    let value ← mkAppM ``nextRulesMatches
      #[wires, table, register, width, rules, current, out, cert]
    return ← decideAccepted (← mkBoolAccepted value)
  if rulesName == ``List.cons && certName == ``NextRulesCert.cons then
    let rule := rulesArgs[rulesArgs.size - 2]!
    let tailRules := rulesArgs[rulesArgs.size - 1]!
    let mid := certArgs[certArgs.size - 3]!
    let headCert := certArgs[certArgs.size - 2]!
    let tailCert := certArgs[certArgs.size - 1]!
    let ruleBody ← mkAppM ``Loom.Hw.Rule.body #[rule]
    let (midName, midArgs) ← expose mid
    if midName == ``Option.some then
      let midRef := midArgs[midArgs.size - 1]!
      let headValue ← mkAppM ``nextRegMatches
        #[wires, table, register, width, ruleBody, current, midRef, headCert]
      let headType ← mkBoolAccepted headValue
      let headProof ← cacheAccepted headType
        (← proveNextReg wires table register width ruleBody current midRef headCert)
      let someMid ← mkAppM ``Option.some #[midRef]
      let tailValue ← mkAppM ``nextRulesMatches
        #[wires, table, register, width, tailRules, someMid, out, tailCert]
      let tailType ← mkBoolAccepted tailValue
      let tailProof ← cacheAccepted tailType
        (← proveNextRules wires table register width tailRules someMid out tailCert)
      return ← mkAppM ``nextRulesMatches_cons_named
        #[wires, table, register, width, rule, tailRules, current, midRef, out,
          headCert, tailCert, headProof, tailProof]
    else if midName == ``Option.none then
      let noneRef := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Ref)
      let tailValue ← mkAppM ``nextRulesMatches
        #[wires, table, register, width, tailRules, noneRef, out, tailCert]
      let tailType ← mkBoolAccepted tailValue
      let tailProof ← cacheAccepted tailType
        (← proveNextRules wires table register width tailRules noneRef out tailCert)
      return ← mkAppM ``nextRulesMatches_cons_discard
        #[wires, table, register, width, rule, tailRules, current, out,
          headCert, tailCert, tailProof]
  throwError "symbolic_kernel_decide: rule/certificate shape mismatch"

private partial def proveWholePlan (wires table width plan current out cert : Expr) :
    MetaM Expr := do
  let (planName, planArgs) ← expose plan
  let (certName, certArgs) ← expose cert
  if planName == ``Loom.Hw.Compile.RegPlan.same &&
      certName == ``NextRegCert.same then
    let (currentName, currentArgs) ← expose current
    unless currentName == ``Option.some do
      throwError "symbolic_kernel_decide: plan `.same` requires a current root"
    let currentRef := currentArgs[currentArgs.size - 1]!
    unless ← isDefEq currentRef out do
      throwError "symbolic_kernel_decide: plan `.same` roots differ"
    return ← mkAppM ``WholePlan.planMatches_same
      #[wires, table, width, currentRef]
  if planName == ``Loom.Hw.Compile.RegPlan.write &&
      certName == ``NextRegCert.write then
    let value := planArgs[planArgs.size - 1]!
    let compiled ← mkAppM ``Loom.Hw.Compile.compileExpr #[value]
    let expressionCheck ← mkAppM ``indexedExprMatches
      #[wires, table, compiled, out]
    let expressionProof ← decideAccepted (← mkBoolAccepted expressionCheck)
    let (currentName, currentArgs) ← expose current
    if currentName == ``Option.none then
      return ← mkAppM ``WholePlan.planMatches_write
        #[wires, table, width, value, out, expressionProof]
    else if currentName == ``Option.some then
      let currentRef := currentArgs[currentArgs.size - 1]!
      return ← mkAppM ``WholePlan.planMatches_write_current
        #[wires, table, width, value, currentRef, out, expressionProof]
  if planName == ``Loom.Hw.Compile.RegPlan.seq &&
      certName == ``NextRegCert.seq then
    let left := planArgs[planArgs.size - 2]!
    let right := planArgs[planArgs.size - 1]!
    let mid := certArgs[certArgs.size - 3]!
    let leftCert := certArgs[certArgs.size - 2]!
    let rightCert := certArgs[certArgs.size - 1]!
    let (midName, midArgs) ← expose mid
    if midName == ``Option.some then
      let midRef := midArgs[midArgs.size - 1]!
      let leftProof ← proveWholePlan wires table width left current midRef
        leftCert
      let someMid ← mkAppM ``Option.some #[midRef]
      let rightProof ← proveWholePlan wires table width right someMid out
        rightCert
      return ← mkAppM ``WholePlan.planMatches_seq_named
        #[wires, table, width, left, right, current, midRef, out, leftCert,
          rightCert, leftProof, rightProof]
    else if midName == ``Option.none then
      let noneRef := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Ref)
      let rightProof ← proveWholePlan wires table width right noneRef out
        rightCert
      return ← mkAppM ``WholePlan.planMatches_seq_discard
        #[wires, table, width, left, right, current, out, leftCert, rightCert,
          rightProof]
  if planName == ``Loom.Hw.Compile.RegPlan.ite &&
      certName == ``NextRegCert.ite then
    let guard := planArgs[planArgs.size - 3]!
    let thenPlan := planArgs[planArgs.size - 2]!
    let elsePlan := planArgs[planArgs.size - 1]!
    let thenCert := certArgs[certArgs.size - 2]!
    let elseCert := certArgs[certArgs.size - 1]!
    let (outName, outArgs) ← expose out
    unless outName == ``Ref.wire do
      throwError "symbolic_kernel_decide: plan ite output is not a wire"
    let number := outArgs[outArgs.size - 1]!
    let lookup ← mkAppM ``lookupIndexed? #[wires, table, number]
    let lookupReduced ← withTransparency .all <| whnf lookup
    let (lookupName, lookupArgs) ← expose lookupReduced
    unless lookupName == ``Option.some do
      throwError "symbolic_kernel_decide: plan ite output lookup failed"
    let indexedWire := lookupArgs[lookupArgs.size - 1]!
    let (wireName, wireArgs) ← expose indexedWire
    unless wireName == ``IndexedWire.mk do
      throwError "symbolic_kernel_decide: malformed indexed wire for plan ite"
    let actualWidth := wireArgs[wireArgs.size - 2]!
    unless ← isDefEq actualWidth width do
      throwError "symbolic_kernel_decide: plan ite output width mismatch"
    let rhs := wireArgs[wireArgs.size - 1]!
    let (rhsName, rhsArgs) ← expose rhs
    unless rhsName == ``IndexedRhs.mux do
      throwError "symbolic_kernel_decide: plan ite output is not a mux"
    let guardRef := rhsArgs[rhsArgs.size - 3]!
    let thenRef := rhsArgs[rhsArgs.size - 2]!
    let elseRef := rhsArgs[rhsArgs.size - 1]!
    let lookupExpected ← mkAppM ``Option.some #[indexedWire]
    let lookupProof ← cacheClosedProof (← mkEq lookup lookupExpected)
      (← mkEqRefl lookup)
    let compiledGuard ← mkAppM ``Loom.Hw.Compile.compileExpr #[guard]
    let guardValue ← mkAppM ``indexedExprMatches
      #[wires, table, compiledGuard, guardRef]
    let guardProof ← decideAccepted (← mkBoolAccepted guardValue)
    let thenProof ← proveWholePlan wires table width thenPlan current thenRef
      thenCert
    let elseProof ← proveWholePlan wires table width elsePlan current elseRef
      elseCert
    return ← mkAppM ``WholePlan.planMatches_ite
      #[wires, table, width, guard, thenPlan, elsePlan, current, number,
        guardRef, thenRef, elseRef, thenCert, elseCert, lookupProof, guardProof,
        thenProof, elseProof]
  throwError "symbolic_kernel_decide: plan/certificate shape mismatch"

private partial def proveWholeRules (wires table width plans current out cert : Expr) :
    MetaM Expr := do
  let (plansName, plansArgs) ← expose plans
  let (certName, certArgs) ← expose cert
  if plansName == ``List.nil && certName == ``NextRulesCert.nil then
    let (currentName, currentArgs) ← expose current
    unless currentName == ``Option.some do
      throwError "symbolic_kernel_decide: empty plan rules require a current root"
    let currentRef := currentArgs[currentArgs.size - 1]!
    unless ← isDefEq currentRef out do
      throwError "symbolic_kernel_decide: terminal plan rule roots differ"
    return ← mkAppM ``WholePlan.rulesMatch_nil
      #[wires, table, width, currentRef]
  if plansName == ``List.cons && certName == ``NextRulesCert.cons then
    let plan := plansArgs[plansArgs.size - 2]!
    let tailPlans := plansArgs[plansArgs.size - 1]!
    let mid := certArgs[certArgs.size - 3]!
    let headCert := certArgs[certArgs.size - 2]!
    let tailCert := certArgs[certArgs.size - 1]!
    let (midName, midArgs) ← expose mid
    if midName == ``Option.some then
      let midRef := midArgs[midArgs.size - 1]!
      let headProof ← proveWholePlan wires table width plan current midRef
        headCert
      let someMid ← mkAppM ``Option.some #[midRef]
      let tailProof ← proveWholeRules wires table width tailPlans someMid out
        tailCert
      return ← mkAppM ``WholePlan.rulesMatch_cons_named
        #[wires, table, width, plan, tailPlans, current, midRef, out, headCert,
          tailCert, headProof, tailProof]
    else if midName == ``Option.none then
      let noneRef := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Ref)
      let tailProof ← proveWholeRules wires table width tailPlans noneRef out
        tailCert
      return ← mkAppM ``WholePlan.rulesMatch_cons_discard
        #[wires, table, width, plan, tailPlans, current, out, headCert,
          tailCert, tailProof]
  throwError "symbolic_kernel_decide: plan rules/certificate shape mismatch"

private partial def proveWholeBlock (design program wires table start plans entries : Expr) :
    MetaM Expr := do
  let simpContext ← Simp.Context.mkDefault
  let (plansResult, _) ← simp plans simpContext
  let (entriesResult, _) ← simp entries simpContext
  let (plansName, plansArgs) ← expose plansResult.expr
  let (entriesName, entriesArgs) ← expose entriesResult.expr
  if plansName == ``Loom.Hw.Compile.RulePlans.nil &&
      entriesName == ``List.nil then
    return ← mkAppM ``WholePlan.blockMatches_nil
      #[design, program, wires, table, start]
  if plansName == ``Loom.Hw.Compile.RulePlans.cons &&
      entriesName == ``List.cons then
    let source := plansArgs[plansArgs.size - 4]!
    let sources := plansArgs[plansArgs.size - 3]!
    let headPlans := plansArgs[plansArgs.size - 2]!
    let restPlans := plansArgs[plansArgs.size - 1]!
    let entry := entriesArgs[entriesArgs.size - 2]!
    let restEntries := entriesArgs[entriesArgs.size - 1]!
    let root ← mkAppM ``WholePlan.RegisterPlanRoot.root #[entry]
    let cert ← mkAppM ``WholePlan.RegisterPlanRoot.cert #[entry]
    let sourceName ← mkAppM ``Loom.Hw.RegDecl.name #[source]
    let sourceWidth ← mkAppM ``Loom.Hw.RegDecl.width #[source]
    let metadataValue ← mkAppM ``indexedRegisterMetadataMatchesAt
      #[design, program, start, root]
    let metadataProof ← decideAccepted (← mkBoolAccepted metadataValue)
    let currentRef ← mkAppM ``Ref.reg #[sourceName]
    let someCurrent ← mkAppM ``Option.some #[currentRef]
    let rulesValue ← mkAppM ``WholePlan.rulesMatch
      #[wires, table, headPlans, someCurrent, root, cert]
    let rulesType ← mkBoolAccepted rulesValue
    let rulesProof ← cacheAccepted rulesType
      (← proveWholeRules wires table sourceWidth headPlans someCurrent root cert)
    let nextStart ← mkAppM ``HAdd.hAdd #[start, toExpr (1 : Nat)]
    let restValue ← mkAppM ``WholePlan.blockMatches
      #[design, program, wires, table, nextStart, restPlans, restEntries]
    let restType ← mkBoolAccepted restValue
    let restProof ← cacheAccepted restType
      (← proveWholeBlock design program wires table nextStart restPlans
        restEntries)
    return ← mkAppM ``WholePlan.blockMatches_cons
      #[design, program, wires, table, start, source, sources, headPlans,
        restPlans, entry, restEntries, metadataProof, rulesProof, restProof]
  throwError "symbolic_kernel_decide: plan block shape mismatch"

private def proveNextRegCovered (wires table covered register width action
    current out cert : Expr) : MetaM Expr := do
  let key ← mkAppM ``Prod.mk #[register, width]
  let presentValue ← instantiateMVars (← mkAppM ``List.elem #[key, covered])
  let reduced ← Lean.Meta.reduce presentValue
  let value ← mkAppM ``nextRegMatchesCovered
    #[wires, table, covered, register, width, action, current, out, cert]
  let expected ← mkBoolAccepted value
  if reduced.isConstOf ``Bool.true then
    let presentType ← mkEq presentValue (mkConst ``Bool.true)
    let presentProof ← cacheClosedProof presentType (← mkDecideProof presentType)
    let rawValue ← mkAppM ``nextRegMatches
      #[wires, table, register, width, action, current, out, cert]
    let rawType ← mkBoolAccepted rawValue
    let rawProof ← cacheAccepted rawType
      (← proveNextReg wires table register width action current out cert)
    return ← mkAppM ``nextRegMatchesCovered_of_present
      #[wires, table, covered, register, width, action, current, out, cert,
        presentProof, rawProof]
  if reduced.isConstOf ``Bool.false then
    return ← decideAccepted expected
  throwError "symbolic_kernel_decide: footprint membership did not reduce: {reduced}"

private partial def proveNextRulesCovered (wires table register width rules
    footprints current out cert : Expr) : MetaM Expr := do
  let (rulesName, rulesArgs) ← expose rules
  let (footprintsName, footprintsArgs) ← expose footprints
  let (certName, certArgs) ← expose cert
  if rulesName == ``List.nil && footprintsName == ``List.nil &&
      certName == ``NextRulesCert.nil then
    let value ← mkAppM ``nextRulesMatchesCovered
      #[wires, table, register, width, rules, footprints, current, out, cert]
    return ← decideAccepted (← mkBoolAccepted value)
  if rulesName == ``List.cons && footprintsName == ``List.cons &&
      certName == ``NextRulesCert.cons then
    let rule := rulesArgs[rulesArgs.size - 2]!
    let tailRules := rulesArgs[rulesArgs.size - 1]!
    let covered := footprintsArgs[footprintsArgs.size - 2]!
    let rest := footprintsArgs[footprintsArgs.size - 1]!
    let mid := certArgs[certArgs.size - 3]!
    let headCert := certArgs[certArgs.size - 2]!
    let tailCert := certArgs[certArgs.size - 1]!
    let ruleBody ← mkAppM ``Loom.Hw.Rule.body #[rule]
    let (midName, midArgs) ← expose mid
    if midName == ``Option.some then
      let midRef := midArgs[midArgs.size - 1]!
      let headValue ← mkAppM ``nextRegMatchesCovered
        #[wires, table, covered, register, width, ruleBody, current, midRef,
          headCert]
      let headType ← mkBoolAccepted headValue
      let headProof ← cacheAccepted headType
        (← proveNextRegCovered wires table covered register width ruleBody
          current midRef headCert)
      let someMid ← mkAppM ``Option.some #[midRef]
      let tailValue ← mkAppM ``nextRulesMatchesCovered
        #[wires, table, register, width, tailRules, rest, someMid, out, tailCert]
      let tailType ← mkBoolAccepted tailValue
      let tailProof ← cacheAccepted tailType
        (← proveNextRulesCovered wires table register width tailRules rest
          someMid out tailCert)
      return ← mkAppM ``nextRulesMatchesCovered_cons_named
        #[wires, table, register, width, rule, tailRules, covered, rest,
          current, midRef, out, headCert, tailCert, headProof, tailProof]
    else if midName == ``Option.none then
      let noneRef := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Ref)
      let tailValue ← mkAppM ``nextRulesMatchesCovered
        #[wires, table, register, width, tailRules, rest, noneRef, out, tailCert]
      let tailType ← mkBoolAccepted tailValue
      let tailProof ← cacheAccepted tailType
        (← proveNextRulesCovered wires table register width tailRules rest
          noneRef out tailCert)
      return ← mkAppM ``nextRulesMatchesCovered_cons_discard
        #[wires, table, register, width, rule, tailRules, covered, rest,
          current, out, headCert, tailCert, tailProof]
  throwError "symbolic_kernel_decide: covered rule/certificate shape mismatch"

private def transportNextPortAction (wires table memory addressWidth dataWidth
    port current out cert actionEq proof : Expr) : MetaM Expr := do
  let equalityType ← inferType actionEq
  let actionType := equalityType.getAppArgs[0]!
  let motive ← withLocalDeclD `action actionType fun act => do
    let value ← mkAppM ``nextPortMatches
      #[wires, table, memory, addressWidth, dataWidth, port, act, current, out,
        cert]
    mkLambdaFVars #[act] (← mkBoolAccepted value)
  let propositionEq ← mkCongrArg motive actionEq
  mkAppM ``Eq.mpr #[propositionEq, proof]

private partial def proveNextPort (wires table memory addressWidth dataWidth port
    action current out cert : Expr) : MetaM Expr := do
  let simpContext ← Simp.Context.mkDefault
  let (actionResult, _) ← simp action simpContext
  if let some actionEq := actionResult.proof? then
    let proof ← proveNextPort wires table memory addressWidth dataWidth port
      actionResult.expr current out cert
    return ← transportNextPortAction wires table memory addressWidth dataWidth
      port current out cert actionEq proof
  let reduced ← exposeAction action
  let actionName := reduced.getAppFn.constName?.getD Name.anonymous
  let actionArgs := reduced.getAppArgs
  let (certName, certArgs) ← expose cert
  if certName == ``NextPortCert.same then
    if ← isDefEq current out then
      try
        let noWriteType ← mkAppM ``NoPortWrite #[memory, port, action]
        let noWriteProof ← cacheClosedProof noWriteType
          (← proveNoPortWrite memory port action)
        return ← mkAppM ``nextPortMatches_same_of_noWrite
          #[wires, table, memory, addressWidth, dataWidth, port, action, current,
            noWriteProof]
      catch error =>
        throwError "symbolic_kernel_decide: `.same` structural no-write proof failed: {error.toMessageData}"
  if actionName == ``Loom.Hw.Act.seq && certName == ``NextPortCert.seq then
    let left := actionArgs[actionArgs.size - 2]!
    let right := actionArgs[actionArgs.size - 1]!
    let mid := certArgs[certArgs.size - 3]!
    let leftCert := certArgs[certArgs.size - 2]!
    let rightCert := certArgs[certArgs.size - 1]!
    let leftValue ← mkAppM ``nextPortMatches
      #[wires, table, memory, addressWidth, dataWidth, port, left, current, mid,
        leftCert]
    let leftType ← mkBoolAccepted leftValue
    let leftProof ← cacheAccepted leftType
      (← proveNextPort wires table memory addressWidth dataWidth port left
        current mid leftCert)
    let rightValue ← mkAppM ``nextPortMatches
      #[wires, table, memory, addressWidth, dataWidth, port, right, mid, out,
        rightCert]
    let rightType ← mkBoolAccepted rightValue
    let rightProof ← cacheAccepted rightType
      (← proveNextPort wires table memory addressWidth dataWidth port right
        mid out rightCert)
    return ← mkAppM ``nextPortMatches_seq_named
      #[wires, table, memory, addressWidth, dataWidth, port, left, right,
        current, mid, out, leftCert, rightCert, leftProof, rightProof]
  if actionName == ``Loom.Hw.Act.ite && certName == ``NextPortCert.ite then
    let guard := actionArgs[actionArgs.size - 3]!
    let thenAction := actionArgs[actionArgs.size - 2]!
    let elseAction := actionArgs[actionArgs.size - 1]!
    let guardRef := certArgs[certArgs.size - 5]!
    let thenPort := certArgs[certArgs.size - 4]!
    let elsePort := certArgs[certArgs.size - 3]!
    let thenCert := certArgs[certArgs.size - 2]!
    let elseCert := certArgs[certArgs.size - 1]!
    let writesProof ← provePortWritesOr memory port thenAction elseAction
    let compiledGuard ← mkAppM ``Loom.Hw.Compile.compileExpr #[guard]
    let guardValue ← mkAppM ``indexedExprMatches
      #[wires, table, compiledGuard, guardRef]
    let guardProof ← decideAccepted (← mkBoolAccepted guardValue)
    let thenValue ← mkAppM ``nextPortMatches
      #[wires, table, memory, addressWidth, dataWidth, port, thenAction,
        current, thenPort, thenCert]
    let thenType ← mkBoolAccepted thenValue
    let thenProof ← cacheAccepted thenType
      (← proveNextPort wires table memory addressWidth dataWidth port
        thenAction current thenPort thenCert)
    let elseValue ← mkAppM ``nextPortMatches
      #[wires, table, memory, addressWidth, dataWidth, port, elseAction,
        current, elsePort, elseCert]
    let elseType ← mkBoolAccepted elseValue
    let elseProof ← cacheAccepted elseType
      (← proveNextPort wires table memory addressWidth dataWidth port
        elseAction current elsePort elseCert)
    let muxValue ← mkAppM ``indexedPortMuxMatches
      #[wires, table, addressWidth, dataWidth, guardRef, thenPort, elsePort, out]
    let muxProof ← decideAccepted (← mkBoolAccepted muxValue)
    return ← mkAppM ``nextPortMatches_ite_written
      #[wires, table, memory, addressWidth, dataWidth, port, guard, thenAction,
        elseAction, current, out, guardRef, thenPort, elsePort, thenCert,
        elseCert, writesProof, guardProof, thenProof, elseProof, muxProof]
  let value ← mkAppM ``nextPortMatches
    #[wires, table, memory, addressWidth, dataWidth, port, action, current, out,
      cert]
  decideAccepted (← mkBoolAccepted value)

private partial def proveNextPortRules (wires table memory addressWidth dataWidth
    port rules current out cert : Expr) : MetaM Expr := do
  let (rulesName, rulesArgs) ← expose rules
  let (certName, certArgs) ← expose cert
  if rulesName == ``List.nil && certName == ``NextPortRulesCert.nil then
    unless ← isDefEq current out do
      throwError "symbolic_kernel_decide: terminal port references differ"
    return ← mkAppM ``nextPortRulesMatches_nil
      #[wires, table, memory, addressWidth, dataWidth, port, current]
  if rulesName == ``List.cons && certName == ``NextPortRulesCert.cons then
    let rule := rulesArgs[rulesArgs.size - 2]!
    let tailRules := rulesArgs[rulesArgs.size - 1]!
    let mid := certArgs[certArgs.size - 3]!
    let headCert := certArgs[certArgs.size - 2]!
    let tailCert := certArgs[certArgs.size - 1]!
    let ruleBody ← mkAppM ``Loom.Hw.Rule.body #[rule]
    let headValue ← mkAppM ``nextPortMatches
      #[wires, table, memory, addressWidth, dataWidth, port, ruleBody, current,
        mid, headCert]
    let headType ← mkBoolAccepted headValue
    let headProof ← cacheAccepted headType
      (← proveNextPort wires table memory addressWidth dataWidth port ruleBody
        current mid headCert)
    let tailValue ← mkAppM ``nextPortRulesMatches
      #[wires, table, memory, addressWidth, dataWidth, port, tailRules, mid, out,
        tailCert]
    let tailType ← mkBoolAccepted tailValue
    let tailProof ← cacheAccepted tailType
      (← proveNextPortRules wires table memory addressWidth dataWidth port
        tailRules mid out tailCert)
    return ← mkAppM ``nextPortRulesMatches_cons_named
      #[wires, table, memory, addressWidth, dataWidth, port, rule, tailRules,
        current, mid, out, headCert, tailCert, headProof, tailProof]
  throwError "symbolic_kernel_decide: port rule/certificate shape mismatch"

/-- Kernel-check a closed symbolic expression, register, or port certificate by
installing every recursive child as an auxiliary theorem. -/
syntax (name := symbolicKernelDecide) "symbolic_kernel_decide" : term

@[term_elab symbolicKernelDecide]
def elabSymbolicKernelDecide : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "symbolic_kernel_decide requires an expected proposition"
  let expected ← instantiateMVars expected
  if expected.hasFVar || expected.hasMVar then
    throwError "symbolic_kernel_decide requires a closed proposition"
  let equalityArgs := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``Eq && equalityArgs.size == 3 do
    throwError "symbolic_kernel_decide expected a Boolean equality"
  let lhs := equalityArgs[1]!
  let lhsArgs := lhs.getAppArgs
  match lhs.getAppFn.constName? with
  | some ``indexedExprMatches =>
      unless lhsArgs.size == 5 do
        throwError "symbolic_kernel_decide: malformed indexedExprMatches application"
      decideAccepted expected
  | some ``nextRegMatches =>
      unless lhsArgs.size == 8 do
        throwError "symbolic_kernel_decide: malformed nextRegMatches application"
      proveNextReg lhsArgs[0]! lhsArgs[1]! lhsArgs[2]! lhsArgs[3]!
        lhsArgs[4]! lhsArgs[5]! lhsArgs[6]! lhsArgs[7]!
  | some ``nextRulesMatches =>
      unless lhsArgs.size == 8 do
        throwError "symbolic_kernel_decide: malformed nextRulesMatches application"
      proveNextRules lhsArgs[0]! lhsArgs[1]! lhsArgs[2]! lhsArgs[3]!
        lhsArgs[4]! lhsArgs[5]! lhsArgs[6]! lhsArgs[7]!
  | some ``WholePlan.planMatches =>
      unless lhsArgs.size == 7 do
        throwError "symbolic_kernel_decide: malformed planMatches application"
      proveWholePlan lhsArgs[0]! lhsArgs[1]! lhsArgs[2]! lhsArgs[3]!
        lhsArgs[4]! lhsArgs[5]! lhsArgs[6]!
  | some ``WholePlan.rulesMatch =>
      unless lhsArgs.size == 7 do
        throwError "symbolic_kernel_decide: malformed rulesMatch application"
      proveWholeRules lhsArgs[0]! lhsArgs[1]! lhsArgs[2]! lhsArgs[3]!
        lhsArgs[4]! lhsArgs[5]! lhsArgs[6]!
  | some ``WholePlan.blockMatches =>
      unless lhsArgs.size == 8 do
        throwError "symbolic_kernel_decide: malformed blockMatches application"
      proveWholeBlock lhsArgs[0]! lhsArgs[1]! lhsArgs[2]! lhsArgs[3]!
        lhsArgs[4]! lhsArgs[6]! lhsArgs[7]!
  | some ``nextRulesMatchesCovered =>
      unless lhsArgs.size == 9 do
        throwError "symbolic_kernel_decide: malformed nextRulesMatchesCovered application"
      proveNextRulesCovered lhsArgs[0]! lhsArgs[1]! lhsArgs[2]! lhsArgs[3]!
        lhsArgs[4]! lhsArgs[5]! lhsArgs[6]! lhsArgs[7]! lhsArgs[8]!
  | some ``nextPortMatches =>
      unless lhsArgs.size == 10 do
        throwError "symbolic_kernel_decide: malformed nextPortMatches application"
      proveNextPort lhsArgs[0]! lhsArgs[1]! lhsArgs[2]! lhsArgs[3]!
        lhsArgs[4]! lhsArgs[5]! lhsArgs[6]! lhsArgs[7]! lhsArgs[8]! lhsArgs[9]!
  | some ``nextPortRulesMatches =>
      unless lhsArgs.size == 10 do
        throwError "symbolic_kernel_decide: malformed nextPortRulesMatches application"
      proveNextPortRules lhsArgs[0]! lhsArgs[1]! lhsArgs[2]! lhsArgs[3]!
        lhsArgs[4]! lhsArgs[5]! lhsArgs[6]! lhsArgs[7]! lhsArgs[8]! lhsArgs[9]!
  | _ => throwError "symbolic_kernel_decide expected a register or port certificate"

end Loom.Release.Symbolic
