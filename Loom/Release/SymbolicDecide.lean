-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate
import Loom.Release.SymbolicElaborate
import Lean.Elab.Term
import Lean.Meta.Tactic.AuxLemma
import Lean.Meta.Tactic.Simp

/-!
# Compositional symbolic release proofs

Large source actions are checked a subtree at a time. Each recursive proof is
installed as an auxiliary theorem before its parent is constructed, so kernel
checking a parent uses the child's statement without normalizing its proof.
-/

open Lean Elab Term Meta
open Loom.Release

namespace Loom.Release.Symbolic

private def cacheClosedProof (type proof : Expr) : MetaM Expr := do
  let lemma ← withOptions (Elab.async.set · false) do
    mkAuxLemma [] type proof (kind? := `_symbolicNoWrite)
  pure (.const lemma [])

private def cachePropProof (type : Expr) (proof : MetaM Expr) : MetaM Expr := do
  cacheClosedProof type (← proof)

private abbrev ProofCache := IO.Ref (Std.HashMap Expr Expr)

private def cachePropProofMemo (cache : ProofCache) (type : Expr)
    (proof : MetaM Expr) : MetaM Expr := do
  if let some cached := (← cache.get).get? type then
    return cached
  let cached ← cachePropProof type proof
  cache.modify (fun entries => entries.insert type cached)
  pure cached

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

private partial def proveHwExprRegistersValid (cache : ProofCache)
    (program expression : Expr) : MetaM Expr := do
  let reduced ← exposeHwExpr expression
  let args := reduced.getAppArgs
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

private partial def proveActRegistersValid (cache : ProofCache)
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

private partial def proveSourceRegistersValid (program sources : Expr) : MetaM Expr := do
  let (name, args) ← exposeList sources
  if name == ``List.nil then
    return mkConst ``True.intro
  let source := args[args.size - 2]!
  let rest := args[args.size - 1]!
  let oneType ← mkAppM ``SourceRegisterValid #[program, source]
  let check ← mkAppM ``sourceRegisterValidB #[program, source]
  let acceptedType ← mkEq check (mkConst ``Bool.true)
  let accepted ← cachePropProof acceptedType (mkDecideProof acceptedType)
  let oneProof ← mkAppM ``sourceRegisterValidB_sound #[source, accepted]
  let oneProof ← cacheClosedProof oneType oneProof
  -- Keep the list composition in one linear proof term. Caching every tail
  -- would repeat all remaining declarations in auxiliary theorem statements.
  mkAndProof oneProof (← proveSourceRegistersValid program rest)

private partial def proveRulesRegistersValid (cache : ProofCache)
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
def elabRulesReadsValid : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "rules_reads_valid requires an expected RulesRegistersValid proposition"
  let expected ← instantiateMVars expected
  if expected.hasFVar || expected.hasMVar then
    throwError "rules_reads_valid requires a closed proposition"
  let args := expected.getAppArgs
  unless expected.getAppFn.constName? == some ``RulesRegistersValid && args.size == 2 do
    throwError "rules_reads_valid expected RulesRegistersValid program rules"
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  proveRulesRegistersValid cache args[0]! args[1]!

/-- Build the complete source-read certificate from separately named
constructor and list proofs. The generator is not trusted: every auxiliary
declaration and the composed result are checked by the kernel. -/
syntax (name := designReadsValidTerm) "design_reads_valid" : term

@[term_elab designReadsValidTerm]
def elabDesignReadsValid : TermElab := fun _ expected? => do
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
  let sources ← mkAppM ``Loom.Hw.Design.regs #[design]
  let rules ← mkAppM ``Loom.Hw.Design.rules #[design]
  let sourceType ← mkAppM ``SourceRegistersValid #[program, sources]
  let rulesType ← mkAppM ``RulesRegistersValid #[program, rules]
  let sourceProof ← cachePropProof sourceType
    (proveSourceRegistersValid program sources)
  let rulesProof ← cachePropProof rulesType
    (proveRulesRegistersValid cache program rules)
  mkAppM ``DesignReadsValid.ofLists #[sourceProof, rulesProof]

private partial def expandListFoldr (function initial values : Expr) : MetaM Expr := do
  let values ← withTransparency .all <| whnf values
  let args := values.getAppArgs
  match values.getAppFn.constName? with
  | some ``List.nil => pure initial
  | some ``List.cons =>
      let head := args[args.size - 2]!
      let tail := args[args.size - 1]!
      pure (mkApp2 function head (← expandListFoldr function initial tail))
  | _ => throwError "no_reg_write: List.foldr input did not reduce to a list: {values}"

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
    let noWriteType ← mkAppM ``NoRegWrite #[register, width, action]
    let noWriteProof ← cacheClosedProof noWriteType
      (← proveNoRegWrite register width action)
    return ← mkAppM ``nextRegMatches_same_of_noWrite
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
    let writesValue ← mkAppM ``Bool.or #[
      ← mkAppM ``Loom.Hw.Compile.writesRegB #[register, width, thenAction],
      ← mkAppM ``Loom.Hw.Compile.writesRegB #[register, width, elseAction]]
    let writesType ← mkBoolAccepted writesValue
    let writesProof ← decideAccepted writesType
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

/-- Kernel-check a closed symbolic register or rule-fold certificate by
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
  | _ => throwError "symbolic_kernel_decide expected nextRegMatches or nextRulesMatches"

end Loom.Release.Symbolic
