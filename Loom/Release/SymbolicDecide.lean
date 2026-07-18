-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate
import Loom.Release.SymbolicElaborate
import Loom.Hw.CompileCorrect
import Lean.Elab.Term
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

private def expose (value : Expr) : MetaM (Name × Array Expr) := do
  let reduced ← withTransparency .all <| whnf value
  let some name := reduced.getAppFn.constName?
    | throwError "symbolic_kernel_decide: expected constructor, got {reduced}"
  pure (name, reduced.getAppArgs)

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
