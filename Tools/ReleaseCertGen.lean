-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.NamedCertificate
import Loom.Release.SymbolicCertificate
import Loom.Release.ActionWideRegister
import Loom.Hw.WholeRegisterPlan
import Tools.RuntimeSsa
import Std.Data.HashMap

/-!
# Untrusted compact-certificate synthesis

This executable-side helper derives name-only proof data from a source design
and a concrete SSA environment. Nothing here is used by the soundness proof:
generated data is accepted only by `ssaNamedMatches` in the kernel.
-/

namespace Tools.ReleaseCertGen

open Loom.Hw
open Loom.Emit.MicroVerilog
open Loom.Release

abbrev HashMemo := Std.HashMap USize UInt64
structure ExprIndex where
  hashed : Std.HashMap UInt64 String
  values : List (String × Sigma Loom.Emit.MicroVerilog.Expr)
  rhsNames : Std.HashMap String String
  nameHashes : Std.HashMap String UInt64
  muxAliases : Std.HashMap (Nat × UInt64 × UInt64 × UInt64)
    String
structure GenState where
  nextLookup : Nat := 0
  hashMemo : HashMemo := {}
  actionSummaries : Std.HashMap USize Symbolic.ActionWide.Summary := {}

abbrev GenM := StateT GenState Option

structure RuleSummary where
  rule : Rule
  regWrites : Std.HashMap (String × Nat) Unit

private def summarizeRule (rule : Rule) : RuleSummary where
  rule := rule
  regWrites := rule.body.regWrites.foldl (fun index key => index.insert key ()) {}

private def summarizes (rules : List Rule) : List RuleSummary :=
  rules.map summarizeRule

private def finalRegNames (program : SSA.Program) :
    Std.HashMap (String × Nat) String :=
  program.regs.foldl (fun index reg =>
    index.insert (reg.name, reg.width) reg.next) {}

private def rhsKey (width : Nat) (rhs : SSA.Rhs) : String :=
  s!"{width}:{reprStr rhs}"

private def addWireNames : Loom.Release.Rope (List SSA.Wire) →
    Std.HashMap String String → Std.HashMap String String
  | .leaf wires, index => wires.foldl (fun index wire =>
      index.insert (rhsKey wire.width wire.rhs) wire.name) index
  | .node left right, index =>
      addWireNames right (addWireNames left index)

private def findRhs (index : ExprIndex) (width : Nat) (rhs : SSA.Rhs) :
    Option String :=
  index.rhsNames[rhsKey width rhs]?

private def tagged (tag width : Nat) : UInt64 :=
  mixHash (hash tag) (hash width)

private def addMuxAliases (nameHashes : Std.HashMap String UInt64) :
    Loom.Release.Rope (List SSA.Wire) →
      Std.HashMap (Nat × UInt64 × UInt64 × UInt64)
        String →
      Std.HashMap (Nat × UInt64 × UInt64 × UInt64)
        String
  | .leaf wires, aliases => wires.foldl (fun aliases wire =>
      match wire.rhs with
      | .mux guard yes no =>
          match nameHashes[guard]?, nameHashes[yes]?, nameHashes[no]? with
          | some guardHash, some yesHash, some noHash =>
              aliases.insert (wire.width, guardHash, yesHash, noHash)
                wire.name
          | _, _, _ => aliases
      | _ => aliases) aliases
  | .node left right, aliases =>
      addMuxAliases nameHashes right (addMuxAliases nameHashes left aliases)

private unsafe def exprHash : {w : Nat} →
    Loom.Emit.MicroVerilog.Expr w → StateM HashMemo UInt64
  | w, expr => do
      let pointer := ptrAddrUnsafe expr
      if let some cached := (← get)[pointer]? then return cached
      let base := tagged (match expr with
        | .lit .. => 0 | .reg .. => 1 | .memRead .. => 2
        | .and .. => 3 | .or .. => 4 | .xor .. => 5 | .not .. => 6
        | .add .. => 7 | .sub .. => 8 | .shl .. => 9 | .shr .. => 10
        | .eq .. => 11 | .ult .. => 12 | .slt .. => 13 | .mux .. => 14
        | .slice .. => 15 | .zext .. => 16 | .sext .. => 17) w
      let result ← match expr with
        | .lit value => pure (mixHash base (hash value.toNat))
        | .reg width name => pure (mixHash (mixHash base (hash width)) (hash name))
        | .memRead width mem address => do
            pure (mixHash (mixHash (mixHash base (hash width)) (hash mem))
              (← exprHash address))
        | .and left right | .or left right | .xor left right
        | .add left right | .sub left right | .shl left right
        | .shr left right | .eq left right | .ult left right
        | .slt left right => do
            pure (mixHash (mixHash base (← exprHash left)) (← exprHash right))
        | .not value => do pure (mixHash base (← exprHash value))
        | .mux guard yes no => do
            pure (mixHash (mixHash (mixHash base (← exprHash guard))
              (← exprHash yes)) (← exprHash no))
        | .slice value lo width => do
            pure (mixHash (mixHash (mixHash base (hash lo)) (hash width))
              (← exprHash value))
        | .zext value width | .sext value width => do
            pure (mixHash (mixHash base (hash width)) (← exprHash value))
      modify fun memo => memo.insert pointer result
      pure result

private unsafe def buildIndex (program : SSA.Program) (env : SSA.Env) :
    ExprIndex × HashMemo := Id.run do
  let values := env.toList
  let mut hashed : Std.HashMap UInt64 String := {}
  let mut nameHashes : Std.HashMap String UInt64 := {}
  let mut memo : HashMemo := {}
  for (name, ⟨_, value⟩) in values do
    let (key, nextMemo) := (exprHash value).run memo
    memo := nextMemo
    nameHashes := nameHashes.insert name key
    hashed := hashed.insert key name
  for register in program.regs do
    let key := mixHash (mixHash (tagged 1 register.width)
      (hash register.width)) (hash register.name)
    nameHashes := nameHashes.insert register.name key
    unless hashed.contains key do
      hashed := hashed.insert key register.name
  return (⟨hashed, values, addWireNames program.wires {}, nameHashes,
    addMuxAliases nameHashes program.wires {}⟩, memo)

private def findExprLinear {w : Nat}
    (target : Loom.Emit.MicroVerilog.Expr w) :
    List (String × Sigma Loom.Emit.MicroVerilog.Expr) → Option String
  | [] => none
  | (name, ⟨actual, value⟩) :: rest =>
      if h : actual = w then
        if _hvalue : h ▸ value = target then some name
        else findExprLinear target rest
      else findExprLinear target rest

/-- Find the SSA/register name denoting an elaborated expression. Hash
collisions are harmless: the kernel-facing checker rejects a wrong name. -/
private unsafe def findExpr? (index : ExprIndex) {w : Nat}
    (target : Loom.Emit.MicroVerilog.Expr w) : GenM (Option String) := do
  match target with
  | .reg _ name => pure (some name)
  | _ =>
      -- Required expressions may be independently constructed, so pointer
      -- identities must not escape this one hash traversal.
      let (key, _) := (exprHash target).run {}
      modify fun state => { state with nextLookup := state.nextLookup + 1 }
      match index.hashed[key]? with
      | some name => pure (some name)
      | none =>
          pure (findExprLinear target index.values)

/-- Required references must occur in the concrete SSA graph. -/
private unsafe def findExpr (index : ExprIndex) {w : Nat}
    (target : Loom.Emit.MicroVerilog.Expr w) : GenM String := do
  match ← findExpr? index target with
  | some name => pure name
  | none =>
      dbg_trace s!"release certificate: missing required SSA expression width={w}"
      failure

/-- Fast optional lookup for sequence intermediates. Unlike `findExpr?`, this
does not scan the entire SSA environment when lowering did not name the
intermediate; the symbolic checker can often validate such a sequence through
its liveness alternatives. -/
private unsafe def findIntermediate? (index : ExprIndex) {w : Nat}
    (target : Loom.Emit.MicroVerilog.Expr w) : GenM (Option String) := do
  match target with
  | .reg _ name => pure (some name)
  | _ =>
      let state ← get
      let (key, hashMemo) := (exprHash target).run state.hashMemo
      set { state with
        nextLookup := state.nextLookup + 1
        hashMemo := hashMemo }
      pure index.hashed[key]?

private def nextRegDependsOnCurrent (rn : String) (w : Nat) : Act → Bool
  | .skip => true
  | .seq left right =>
      nextRegDependsOnCurrent rn w left && nextRegDependsOnCurrent rn w right
  | .ite _ thenAct elseAct =>
      nextRegDependsOnCurrent rn w thenAct ||
        nextRegDependsOnCurrent rn w elseAct
  | .write actualWidth name _ => !(name == rn && actualWidth == w)
  | .memWrite .. => true

private def rulesDependOnCurrent (rn : String) (w : Nat) :
    List RuleSummary → Bool
  | [] => true
  | summary :: rules =>
      nextRegDependsOnCurrent rn w summary.rule.body &&
        rulesDependOnCurrent rn w rules

private unsafe def synthNextReg (index : ExprIndex) (rn : String) (w : Nat) :
    Act → Loom.Emit.MicroVerilog.Expr w → Bool →
      GenM (Bool × Loom.Emit.MicroVerilog.Expr w × Named.NextRegCert w)
  | .skip, cur, _ => some (false, cur, .same)
  | .seq left right, cur, outputNeeded => do
      let midNeeded := outputNeeded && nextRegDependsOnCurrent rn w right
      let (leftWrites, mid, leftCert) ←
        synthNextReg index rn w left cur midNeeded
      let (rightWrites, out, rightCert) ←
        synthNextReg index rn w right mid outputNeeded
      if leftWrites || rightWrites then
        let midName ← if midNeeded then
            findIntermediate? index mid
          else pure none
        pure (true, out, .seq midName leftCert rightCert)
      else pure (false, cur, .same)
  | .ite guard thenAct elseAct, cur, outputNeeded =>
      do
      let (thenWrites, thenOut, thenCert) ←
          synthNextReg index rn w thenAct cur outputNeeded
      let (elseWrites, elseOut, elseCert) ←
          synthNextReg index rn w elseAct cur outputNeeded
      if thenWrites || elseWrites then
          pure (true, .mux (Compile.compileExprFast guard) thenOut elseOut,
            .ite thenCert elseCert)
        else pure (false, cur, .same)
  | .write actualWidth name value, cur, _ =>
      if _hname : name = rn then
        if hwidth : actualWidth = w then
          some (true, Compile.compileExprFast (hwidth ▸ value), .write)
        else some (false, cur, .same)
      else some (false, cur, .same)
  | .memWrite .., cur, _ => some (false, cur, .same)

private unsafe def synthNextRules (index : ExprIndex) (rn : String) (w : Nat) :
    List RuleSummary → String → Loom.Emit.MicroVerilog.Expr w → Option String →
      GenM (Loom.Emit.MicroVerilog.Expr w × Named.NextRulesCert w)
  | [], _, cur, _ => some (cur, .nil)
  | summary :: rules, finalName, cur, curName =>
      if summary.regWrites[(rn, w)]?.isSome then do
        let midNeeded := rulesDependOnCurrent rn w rules
        let (_, mid, head) ← synthNextReg index rn w summary.rule.body cur midNeeded
        let midName ← if midNeeded then
            if rules.isEmpty then pure (some finalName)
            else findIntermediate? index mid
          else pure none
        let (out, tail) ← synthNextRules index rn w rules finalName mid midName
        pure (out, .cons midName head tail)
      else do
        let (out, tail) ← synthNextRules index rn w rules finalName cur curName
        pure (out, .cons curName .same tail)

private unsafe def synthRegs (index : ExprIndex)
    (rules : List RuleSummary) (finalNames : Std.HashMap (String × Nat) String) :
    (regs : List RegDecl) → GenM (Named.RegsCert regs)
  | [] => some .nil
  | reg :: regs => do
      modify fun state => { state with hashMemo := {} }
      let some finalName := finalNames[(reg.name, reg.width)]? | failure
      let (_, rulesCert) ← synthNextRules index reg.name reg.width rules
        finalName (.reg reg.width reg.name) (some reg.name)
      modify fun state => { state with hashMemo := {} }
      pure (.cons ⟨rulesCert⟩ (← synthRegs index rules finalNames regs))

private unsafe def findPort (index : ExprIndex) {aw dw : Nat}
    (port : Compile.Port aw dw) : GenM Named.PortNames := do
  pure { en := ← findExpr index port.en
         addr := ← findExpr index port.addr
         data := ← findExpr index port.data }

private unsafe def findPort? (index : ExprIndex) {aw dw : Nat}
    (port : Compile.Port aw dw) : GenM (Option Named.PortNames) := do
  let en ← findExpr? index port.en
  let addr ← findExpr? index port.addr
  let data ← findExpr? index port.data
  pure <| match en, addr, data with
    | some en, some addr, some data => some { en, addr, data }
    | _, _, _ => none

private def findLiteral (index : ExprIndex) (width value : Nat) : Option String :=
  findRhs index width (.lit width value)

private def muxNames (index : ExprIndex) (aw dw : Nat) (guard : String)
    (yes no : Named.PortNames) : Option Named.PortNames := do
  pure { en := ← findRhs index 1 (.mux guard yes.en no.en)
         addr := ← findRhs index aw (.mux guard yes.addr no.addr)
         data := ← findRhs index dw (.mux guard yes.data no.data) }

private unsafe def synthNextPort (index : ExprIndex) (mn : String) (aw dw p : Nat) :
    Act → Named.PortNames →
      GenM (Bool × Named.PortNames × Named.NextPortCert aw dw)
  | .skip, cur => pure (false, cur, .same)
  | .seq left right, cur => do
      let (leftWrites, mid, leftCert) ← synthNextPort index mn aw dw p left cur
      let (rightWrites, out, rightCert) ← synthNextPort index mn aw dw p right mid
      if leftWrites || rightWrites then
        pure (true, out, .seq (some mid) leftCert rightCert)
      else pure (false, cur, .same)
  | .ite guard thenAct elseAct, cur =>
      do
        let (thenWrites, thenPort, thenCert) ←
          synthNextPort index mn aw dw p thenAct cur
        let (elseWrites, elsePort, elseCert) ←
          synthNextPort index mn aw dw p elseAct cur
        if thenWrites || elseWrites then
          let guardName ← findExpr index (Compile.compileExprFast guard)
          let out ← muxNames index aw dw guardName thenPort elsePort
          pure (true, out,
            .ite guardName thenPort elsePort thenCert elseCert)
        else pure (false, cur, .same)
  | .write .., cur => some (false, cur, .same)
  | .memWrite actualAw actualDw name port address value, cur =>
      if _hport : name = mn ∧ port = p then
        if hwidth : actualAw = aw ∧ actualDw = dw then do
          let en ← findLiteral index 1 1
          let addr ← findExpr index (Compile.compileExprFast (hwidth.1 ▸ address))
          let data ← findExpr index (Compile.compileExprFast (hwidth.2 ▸ value))
          let out : Named.PortNames :=
            { en, addr, data }
          some (true, out, .write)
        else some (false, cur, .same)
      else some (false, cur, .same)

private unsafe def synthPortRules (index : ExprIndex) (mn : String) (aw dw p : Nat) :
    List Rule → Named.PortNames →
      GenM (Named.PortNames × Named.NextPortRulesCert aw dw)
  | [], cur => pure (cur, .nil)
  | rule :: rules, cur => do
      let (_, mid, head) ← synthNextPort index mn aw dw p rule.body cur
      let (out, tail) ← synthPortRules index mn aw dw p rules mid
      pure (out, .cons (some mid) head tail)

private unsafe def synthPorts (index : ExprIndex) (rules : List Rule)
    (mn : String) (aw dw : Nat) : (n p : Nat) →
      GenM (Named.PortsCert aw dw n)
  | 0, _ => some .nil
  | n + 1, p => do
      let start : Named.PortNames :=
        { en := ← findLiteral index 1 0
          addr := ← findLiteral index aw 0
          data := ← findLiteral index dw 0 }
      let (_, head) ← synthPortRules index mn aw dw p rules start
      pure (.cons head (← synthPorts index rules mn aw dw n (p + 1)))

private unsafe def synthMems (index : ExprIndex) (d : Design) :
    (mems : List MemDecl) → GenM (Named.MemsCert d mems)
  | [] => some .nil
  | mem :: mems => do
      let ports ← synthPorts index d.rules mem.name mem.addrWidth mem.dataWidth
        (Compile.numPorts d mem.name) 0
      pure (.cons ⟨Compile.numPorts d mem.name, ports⟩
        (← synthMems index d mems))

/-- Synthesize compact untrusted proof data. `none` means some required
intermediate expression was absent from the concrete SSA graph. -/
unsafe def synthesize (design : Design) (program : SSA.Program) :
    Option (Named.ModuleCert design) := do
  let env ← program.elaborateEnv
  let (index, _) := buildIndex program env
  let ruleSummaries := summarizes design.rules
  let names := finalRegNames program
  let action : GenM (Named.ModuleCert design) := do
    pure { regs := ← synthRegs index ruleSummaries names design.regs
           mems := ← synthMems index design design.mems }
  -- Pointer identities are meaningful only within one live expression graph.
  -- The index graph and the independently compiled target graph therefore use
  -- disjoint memo tables; reusing addresses across them would be unsound.
  (action.run {}).map (·.1)

/-! ## Compact shared-plan certificate synthesis -/

private def nameRef (name : String) : Symbolic.Ref :=
  if name.startsWith "n" then
    match (name.drop 1).toNat? with
    | some number => .wire number
    | none => .reg name
  else .reg name

private def planRulesDependOnCurrent {width : Nat} :
    List (Compile.RegPlan width) → Bool
  | [] => true
  | plan :: plans =>
      plan.dependsOnCurrent && planRulesDependOnCurrent plans

private unsafe def synthPlan (index : ExprIndex) {width : Nat} :
    Compile.RegPlan width → Loom.Emit.MicroVerilog.Expr width → Bool →
      GenM (Bool × Loom.Emit.MicroVerilog.Expr width × Symbolic.NextRegCert)
  | .same, current, _ => pure (false, current, .same)
  | .write value, _, _ =>
      pure (true, Compile.compileExprFast value, .write)
  | .seq left right, current, outputNeeded => do
      let midNeeded := outputNeeded && right.dependsOnCurrent
      let (leftWrites, mid, leftCert) ← synthPlan index left current midNeeded
      let (rightWrites, out, rightCert) ← synthPlan index right mid outputNeeded
      let midName ← if midNeeded then findIntermediate? index mid else pure none
      pure (leftWrites || rightWrites, out,
        .seq (midName.map nameRef) leftCert rightCert)
  | .ite guard thenPlan elsePlan, current, outputNeeded => do
      let (thenWrites, thenOut, thenCert) ←
        synthPlan index thenPlan current outputNeeded
      let (elseWrites, elseOut, elseCert) ←
        synthPlan index elsePlan current outputNeeded
      pure (thenWrites || elseWrites,
        .mux (Compile.compileExprFast guard) thenOut elseOut,
        .ite thenCert elseCert)

private unsafe def synthPlanRules (index : ExprIndex) {width : Nat} :
    List (Compile.RegPlan width) → String →
      Loom.Emit.MicroVerilog.Expr width → Option String →
      GenM (Loom.Emit.MicroVerilog.Expr width × Symbolic.NextRulesCert)
  | [], _, current, _ => pure (current, .nil)
  | plan :: plans, finalName, current, currentName => do
      let midNeeded := planRulesDependOnCurrent plans
      let (_, mid, head) ← synthPlan index plan current midNeeded
      let midName ← if midNeeded then
          if plans.isEmpty then pure (some finalName)
          else match plan with
            | .same => pure currentName
            | _ => findIntermediate? index mid
        else pure none
      let (out, tail) ← synthPlanRules index plans finalName mid midName
      pure (out, .cons (midName.map nameRef) head tail)

private unsafe def synthPlanRegisters (index : ExprIndex)
    (finalNames : Std.HashMap (String × Nat) String) :
    Nat → {registers : List RegDecl} → Compile.RulePlans registers →
      GenM (List Symbolic.NextRulesCert)
  | 0, _, _ => pure []
  | _ + 1, [], .nil => pure []
  | remaining + 1, register :: _, .cons plans rest => do
      modify fun state => { state with hashMemo := {} }
      let some finalName := finalNames[(register.name, register.width)]? | failure
      let (_, cert) ← synthPlanRules index plans finalName
        (.reg register.width register.name) (some register.name)
      modify fun state => { state with hashMemo := {} }
      pure (cert :: (← synthPlanRegisters index finalNames remaining rest))

/-- Generate one compact plan certificate per declared register.  This
executable is untrusted; the plan checker validates every emitted term. -/
unsafe def synthesizePlanRegisterCerts (design : Design) (program : SSA.Program) :
    Option (List Symbolic.NextRulesCert) := do
  let env ← program.elaborateEnv
  let (index, _) := buildIndex program env
  let names := finalRegNames program
  let plans := Compile.RulePlans.ofRules design.regs design.rules
  (synthPlanRegisters index names design.regs.length plans).run {} |>.map (·.1)

/-- Prefix form used for bounded generation and performance probes. -/
unsafe def synthesizePlanRegisterCertPrefix (count : Nat) (design : Design)
    (program : SSA.Program) : Option (List Symbolic.NextRulesCert) := do
  let env ← program.elaborateEnv
  let (index, _) := buildIndex program env
  let names := finalRegNames program
  let plans := Compile.RulePlans.ofRules design.regs design.rules
  (synthPlanRegisters index names count plans).run {} |>.map (·.1)

/-! ## Action-wide sparse register certificate synthesis -/

private structure ActionWideIndex where
  hashed : Std.HashMap UInt64 String
  nameHashes : Std.HashMap String UInt64
  wireHashes : Array UInt64 := #[]
  muxAliases : Std.HashMap (Nat × UInt64 × UInt64 × UInt64)
    String

private def ExprIndex.toActionWideIndex (index : ExprIndex) : ActionWideIndex :=
  { hashed := index.hashed
    nameHashes := index.nameHashes
    wireHashes := #[]
    muxAliases := index.muxAliases }

private def ActionWideIndex.refHash? (index : ActionWideIndex)
    (reference : Symbolic.Ref) : Option UInt64 :=
  match reference with
  | .wire number => index.wireHashes[number]? <|> index.nameHashes[reference.render]?
  | .reg name => index.nameHashes[name]?

private unsafe def findActionWideExpr (index : ActionWideIndex) {width : Nat}
    (target : Loom.Emit.MicroVerilog.Expr width) : GenM String := do
  match target with
  | .reg _ name => pure name
  | _ =>
      let (key, _) := (exprHash target).run {}
      modify fun state => { state with nextLookup := state.nextLookup + 1 }
      match index.hashed[key]? with
      | some name => pure name
      | none => failure

private structure ActionWideResult where
  refs : Array Symbolic.Ref
  changed : List Nat

private def registerIndices (registers : List RegDecl) :
    Std.HashMap (String × Nat) Nat := Id.run do
  let mut result := {}
  for h : index in [:registers.length] do
    let register := registers[index]
    result := result.insert (register.name, register.width) index
  return result

private unsafe def actionSummary
    (registerIndex : Std.HashMap (String × Nat) Nat) (action : Act) :
    GenM Symbolic.ActionWide.Summary := do
  let pointer := ptrAddrUnsafe action
  if let some cached := (← get).actionSummaries[pointer]? then return cached
  let summary ← match action with
    | .skip | .memWrite .. => pure { possible := 0, definite := 0 }
    | .write width name _ =>
        let some index := registerIndex[(name, width)]? | failure
        let mask : Nat := 1 <<< index
        pure { possible := mask, definite := mask }
    | .seq left right =>
        let leftSummary ← actionSummary registerIndex left
        let rightSummary ← actionSummary registerIndex right
        pure { possible := leftSummary.possible ||| rightSummary.possible
               definite := leftSummary.definite ||| rightSummary.definite }
    | .ite _ thenAction elseAction =>
        let thenSummary ← actionSummary registerIndex thenAction
        let elseSummary ← actionSummary registerIndex elseAction
        pure { possible := thenSummary.possible ||| elseSummary.possible
               definite := thenSummary.definite &&& elseSummary.definite }
  modify fun state => { state with
    actionSummaries := state.actionSummaries.insert pointer summary }
  pure summary

private unsafe def neededSourceRuleInputs
    (registerIndex : Std.HashMap (String × Nat) Nat) :
    List Rule → List Nat → GenM (List Nat)
  | [], needed => pure needed
  | rule :: rules, needed => do
      let tailNeeded ← neededSourceRuleInputs registerIndex rules needed
      let summary ← actionSummary registerIndex rule.body
      pure (Symbolic.ActionWide.neededInputs summary tailNeeded)

private unsafe def synthActionWideJoins (index : ActionWideIndex)
    (registers : Array RegDecl) (guard : Symbolic.Ref)
    (thenResult elseResult : ActionWideResult) :
    List Nat → GenM (List Symbolic.ActionWide.Join)
  | [] => pure []
  | changedIndex :: changed => do
      let some source := registers[changedIndex]? |
        dbg_trace s!"action-wide: missing register {changedIndex}"; failure
      let some thenRef := thenResult.refs[changedIndex]? |
        dbg_trace s!"action-wide: missing then ref {changedIndex}"; failure
      let some elseRef := elseResult.refs[changedIndex]? |
        dbg_trace s!"action-wide: missing else ref {changedIndex}"; failure
      let some guardHash := index.refHash? guard | failure
      let some thenHash := index.refHash? thenRef | failure
      let some elseHash := index.refHash? elseRef | failure
      let some outputName :=
          index.muxAliases[(source.width, guardHash, thenHash, elseHash)]? |
        dbg_trace s!"action-wide: missing semantic mux for " ++
          s!"{source.name}:{source.width}"
        failure
      pure ({ index := changedIndex
              width := source.width
              guard := guard
              thenInput := thenRef
              elseInput := elseRef
              output := nameRef outputName } ::
        (← synthActionWideJoins index registers guard thenResult elseResult
          changed))

private unsafe def synthActionWide (index : ActionWideIndex)
    (registers : Array RegDecl)
    (registerIndex : Std.HashMap (String × Nat) Nat) :
    Act → Array Symbolic.Ref → List Nat →
      GenM (ActionWideResult × Symbolic.ActionWide.ActionCert)
  | .skip, refs, _ => pure (⟨refs, []⟩, .skip)
  | .memWrite .., refs, _ => pure (⟨refs, []⟩, .memWrite)
  | .write width name value, refs, needed => do
      let some target := registerIndex[(name, width)]? |
        dbg_trace s!"action-wide: undeclared write {name}:{width}"; failure
      let valueName ← if target ∈ needed then
        findActionWideExpr index (Compile.compileExprFast value)
      else pure name
      let valueRef := nameRef valueName
      if target ∉ needed then
        pure (⟨refs, []⟩, .write target valueRef)
      else if target < refs.size then
        pure (⟨refs.set! target valueRef, [target]⟩,
          .write target valueRef)
      else failure
  | .seq left right, refs, needed => do
      let rightSummary ← actionSummary registerIndex right
      let leftNeeded := Symbolic.ActionWide.neededInputs rightSummary needed
      let (leftResult, leftCert) ←
        synthActionWide index registers registerIndex left refs leftNeeded
      let (rightResult, rightCert) ←
        synthActionWide index registers registerIndex right leftResult.refs needed
      let summary ← actionSummary registerIndex (.seq left right)
      pure (⟨rightResult.refs,
        Symbolic.ActionWide.changedOutputs summary needed⟩,
        .seq summary leftCert rightCert)
  | action@(.ite guard thenAction elseAction), refs, needed => do
      let guardName ← findActionWideExpr index (Compile.compileExprFast guard)
      let guardRef := nameRef guardName
      let summary ← actionSummary registerIndex action
      let changed := Symbolic.ActionWide.changedOutputs summary needed
      let (thenResult, thenCert) ←
        synthActionWide index registers registerIndex thenAction refs changed
      let (elseResult, elseCert) ←
        synthActionWide index registers registerIndex elseAction refs changed
      let joins ← synthActionWideJoins index registers guardRef thenResult
        elseResult changed
      let output := joins.foldl (fun output join =>
        output.set! join.index join.output) refs
      pure (⟨output, changed⟩,
        .ite summary guardRef joins thenCert elseCert)

private unsafe def synthActionWideRules (index : ActionWideIndex)
    (registers : Array RegDecl)
    (registerIndex : Std.HashMap (String × Nat) Nat) :
    List Rule → Array Symbolic.Ref → List Nat →
      GenM (Array Symbolic.Ref × Symbolic.ActionWide.RulesCert)
  | [], refs, _ => pure (refs, [])
  | rule :: rules, refs, needed => do
      let headNeeded ← neededSourceRuleInputs registerIndex rules needed
      let (result, cert) ← synthActionWide index registers registerIndex
        rule.body refs headNeeded
      let (finalRefs, certs) ← synthActionWideRules index registers
        registerIndex rules result.refs needed
      pure (finalRefs, cert :: certs)

private structure RuntimeIndexState where
  registerHashes : Std.HashMap String UInt64 := {}
  registerWidths : Std.HashMap String Nat := {}
  wireHashes : Array UInt64 := #[]
  wireWidths : Array Nat := #[]

private def binaryTag : Loom.Release.SSA.BinOp → Nat
  | .and => 3 | .or => 4 | .xor => 5 | .add => 7 | .sub => 8
  | .shl => 9 | .shr => 10 | .eq => 11 | .ult => 12

private def runtimeRefData (state : RuntimeIndexState)
    (reference : Symbolic.Ref) : Option (UInt64 × Nat) := do
  match reference with
  | .wire number =>
      pure (← state.wireHashes[number]?, ← state.wireWidths[number]?)
  | .reg name =>
      pure (← state.registerHashes[name]?, ← state.registerWidths[name]?)

private def runtimeRhsHash (state : RuntimeIndexState) (width : Nat) :
    Symbolic.IndexedRhs → Option UInt64
  | .lit _ value => pure (mixHash (tagged 0 width) (hash value))
  | .ident value => do
      let (valueHash, valueWidth) ← runtimeRefData state value
      if valueWidth == width then pure valueHash
      else if valueWidth < width then
        pure (mixHash (mixHash (tagged 16 width) (hash width)) valueHash)
      else none
  | .memRead memory address => do
      let (addressHash, _) ← runtimeRefData state address
      pure (mixHash (mixHash (mixHash (tagged 2 width) (hash width))
        (hash memory)) addressHash)
  | .slice value _hi lo => do
      let (valueHash, _) ← runtimeRefData state value
      pure (mixHash (mixHash (mixHash (tagged 15 width) (hash lo))
        (hash width)) valueHash)
  | .not value => do
      let (valueHash, _) ← runtimeRefData state value
      pure (mixHash (tagged 6 width) valueHash)
  | .bin op left right => do
      let (leftHash, _) ← runtimeRefData state left
      let (rightHash, _) ← runtimeRefData state right
      pure (mixHash (mixHash (tagged (binaryTag op) width) leftHash)
        rightHash)
  | .slt left right => do
      let (leftHash, _) ← runtimeRefData state left
      let (rightHash, _) ← runtimeRefData state right
      pure (mixHash (mixHash (tagged 13 width) leftHash) rightHash)
  | .mux guard yes no => do
      let (guardHash, _) ← runtimeRefData state guard
      let (yesHash, _) ← runtimeRefData state yes
      let (noHash, _) ← runtimeRefData state no
      pure (mixHash (mixHash (mixHash (tagged 14 width) guardHash)
        yesHash) noHash)
  | .sext _ value _ => do
      let (valueHash, _) ← runtimeRefData state value
      pure (mixHash (mixHash (tagged 17 width) (hash width)) valueHash)

private def buildRuntimeIndex (program : Tools.RuntimeSsa.Program) :
    Option ActionWideIndex := Id.run do
  let mut hashed : Std.HashMap UInt64 String := {}
  let mut registerHashes : Std.HashMap String UInt64 := {}
  let mut registerWidths : Std.HashMap String Nat := {}
  for register in program.regs do
    let key := mixHash (mixHash (tagged 1 register.width)
      (hash register.width)) (hash register.name)
    hashed := hashed.insert key register.name
    registerHashes := registerHashes.insert register.name key
    registerWidths := registerWidths.insert register.name register.width
  let mut wireHashes : Array UInt64 := #[]
  let mut wireWidths : Array Nat := #[]
  let mut muxAliases : Std.HashMap (Nat × UInt64 × UInt64 × UInt64)
      String := {}
  let mut valid := true
  let mut number := 0
  while valid && number < program.wires.size do
    if number % 10000 == 0 then
      dbg_trace s!"action-wide runtime: indexed {number}/{program.wires.size} wires"
    let wire := program.wires[number]!
    let state : RuntimeIndexState :=
      { registerHashes, registerWidths, wireHashes, wireWidths }
    match wire.rhs.toIndexed? with
    | none => valid := false
    | some indexed =>
        match runtimeRhsHash state wire.width indexed with
        | none => valid := false
        | some key =>
            let expectedName := (Symbolic.Ref.wire number).render
            if wire.name != expectedName then valid := false
            else
              hashed := hashed.insert key wire.name
              match indexed with
              | .mux guard yes no =>
                  match runtimeRefData state guard, runtimeRefData state yes,
                      runtimeRefData state no with
                  | some (guardHash, _), some (yesHash, _), some (noHash, _) =>
                      muxAliases := muxAliases.insert
                        (wire.width, guardHash, yesHash, noHash)
                        wire.name
                  | _, _, _ => valid := false
              | _ => pure ()
              wireHashes := wireHashes.push key
              wireWidths := wireWidths.push wire.width
    number := number + 1
  if valid then
    some {
      hashed := hashed
      nameHashes := registerHashes
      wireHashes := wireHashes
      muxAliases := muxAliases
    }
  else none

/-- Synthesize one sparse certificate which checks all register roots in one
source-action traversal.  The returned data is untrusted until accepted by
`ActionWide.registersMatch`. -/
unsafe def synthesizeActionWideRegisterCert (design : Design)
    (program : SSA.Program) : Option Symbolic.ActionWide.RulesCert := do
  let env ← program.elaborateEnv
  let (index, _) := buildIndex program env
  let index := index.toActionWideIndex
  let registers := design.regs.toArray
  let initial := registers.map fun register => Symbolic.Ref.reg register.name
  let indices := registerIndices design.regs
  let needed := List.range registers.size
  let action := synthActionWideRules index registers indices design.rules initial
    needed
  ((action.run {}).map (·.1.2))

/-- Runtime-data variant used by the fast native generator.  It never imports
or compiles the large kernel-facing generated root. -/
unsafe def synthesizeActionWideRegisterCertRuntime (design : Design)
    (program : Tools.RuntimeSsa.Program) :
    Option Symbolic.ActionWide.RulesCert := do
  dbg_trace "action-wide runtime: indexing SSA"
  let index ← buildRuntimeIndex program
  dbg_trace "action-wide runtime: forcing design registers"
  let registers := design.regs.toArray
  guard (program.regs.size == registers.size)
  let initial := registers.map fun register => Symbolic.Ref.reg register.name
  let indices := registerIndices design.regs
  let needed := List.range registers.size
  dbg_trace "action-wide runtime: traversing source actions"
  let action := synthActionWideRules index registers indices design.rules initial
    needed
  let result := (action.run {}).map (·.1.2)
  dbg_trace "action-wide runtime: traversal complete"
  result

private def quote (value : String) : String := reprStr value

private def actionRefToLean : Symbolic.Ref → String
  | .reg name => s!".reg {quote name}"
  | .wire number => s!".wire {number}"

/-- Render a bounded reference array for generated action-segment states. -/
def actionWideRefsToLean (refs : Array Symbolic.Ref) : String :=
  "#[" ++ String.intercalate ", " (refs.toList.map actionRefToLean) ++ "]"

private def collectActionWideJoins : Symbolic.ActionWide.ActionCert →
    List Symbolic.ActionWide.Join → List Symbolic.ActionWide.Join
  | .skip | .memWrite | .write .. => fun tail => tail
  | .seq _ left right => fun tail =>
      collectActionWideJoins left (collectActionWideJoins right tail)
  | .ite _ _ joins thenCert elseCert => fun tail =>
      joins.foldr (· :: ·) (collectActionWideJoins thenCert
        (collectActionWideJoins elseCert tail))

/-- All concrete mux joins mentioned by an action-wide certificate. -/
def actionWideJoins (cert : Symbolic.ActionWide.RulesCert) :
    List Symbolic.ActionWide.Join :=
  cert.foldr collectActionWideJoins []

private def actionWideJoinToLean (join : Symbolic.ActionWide.Join) : String :=
  "{ index := " ++ toString join.index ++
    ", width := " ++ toString join.width ++
    ", guard := " ++ actionRefToLean join.guard ++
    ", thenInput := " ++ actionRefToLean join.thenInput ++
    ", elseInput := " ++ actionRefToLean join.elseInput ++
    ", output := " ++ actionRefToLean join.output ++ " }"

private def actionWideJoinName (join : Symbolic.ActionWide.Join) : String :=
  match join.output with
  | .wire number => "actionJoin" ++ toString number ++ "_" ++
      toString join.index
  | .reg name => "invalidActionJoin_" ++ name

/-- Render named join constants followed by their shared list. -/
def actionWideNamedJoinBlockToLean (blockName : String)
    (joins : List Symbolic.ActionWide.Join) : String :=
  let declarations := Id.run do
    let mut seen : Std.HashSet String := {}
    let mut result : List String := []
    for join in joins do
      let name := actionWideJoinName join
      if !seen.contains name then
        seen := seen.insert name
        result := ("noncomputable def " ++ name ++
          " : Symbolic.ActionWide.Join :=\n  " ++ actionWideJoinToLean join) :: result
    pure result.reverse
  String.intercalate "\n\n" declarations ++ "\n\n" ++
    "noncomputable def " ++ blockName ++ " : List Symbolic.ActionWide.Join := [" ++
    String.intercalate ", " (joins.map actionWideJoinName) ++ "]"

/-- Render a bounded join block as typed Lean data. -/
def actionWideJoinBlockToLean (joins : List Symbolic.ActionWide.Join) : String :=
  "[\n  " ++ String.intercalate ",\n  " (joins.map actionWideJoinToLean) ++
    "\n]"

private def actionWideSummaryToLean (summary : Symbolic.ActionWide.Summary) :
    String :=
  "{ possible := " ++ toString summary.possible ++
    ", definite := " ++ toString summary.definite ++ " }"

private structure NamedActionState where
  next : Nat := 0
  declarations : Array String := #[]

private abbrev NamedActionM := StateM NamedActionState

private def namedActionName (index : Nat) : String :=
  "actionCertNode" ++ toString index

private def emitNamedAction (expression : String) : NamedActionM String := do
  let state ← get
  let name := namedActionName state.next
  let declarations := state.declarations.push
    ("noncomputable def " ++ name ++ " : Symbolic.ActionWide.ActionCert :=\n  " ++
      expression ++ "\n")
  set ({ next := state.next + 1, declarations } : NamedActionState)
  pure name

/-- Render a certificate as bounded named subtrees.  The generator remains
untrusted; naming only controls elaboration sharing and the kernel checks the
resulting constant graph. -/
private def actionWideActionNamed : Symbolic.ActionWide.ActionCert →
    NamedActionM (String × Nat)
  | .skip => pure (".skip", 1)
  | .memWrite => pure (".memWrite", 1)
  | .write index value =>
      pure (".write " ++ toString index ++ " (" ++ actionRefToLean value ++
        ")", 1)
  | .seq summary left right => do
      let (leftExpr, leftSize) ← actionWideActionNamed left
      let (rightExpr, rightSize) ← actionWideActionNamed right
      let expression := ".seq " ++ actionWideSummaryToLean summary ++
        " (" ++ leftExpr ++ ") (" ++ rightExpr ++ ")"
      let size := leftSize + rightSize + 1
      if size ≥ 64 then pure (← emitNamedAction expression, 1)
      else pure (expression, size)
  | .ite summary guard joins thenCert elseCert => do
      let (thenExpr, _) ← actionWideActionNamed thenCert
      let (elseExpr, _) ← actionWideActionNamed elseCert
      let expression := ".ite " ++ actionWideSummaryToLean summary ++
        " (" ++ actionRefToLean guard ++ ") (" ++
        "[" ++ String.intercalate ", " (joins.map actionWideJoinName) ++
        "]) (" ++ thenExpr ++ ") (" ++
        elseExpr ++ ")"
      pure (← emitNamedAction expression, 1)

/-- Complete Lean source fragment for a bounded, named typed certificate. -/
def actionWideNamedCertificateToLean
    (cert : Symbolic.ActionWide.RulesCert) : String :=
  let ((roots, state) : List String × NamedActionState) := Id.run do
    let mut state : NamedActionState := {}
    let mut roots : List String := []
    for action in cert do
      let ((expression, _), nextState) := (actionWideActionNamed action).run state
      state := nextState
      let (name, nextState) := (emitNamedAction expression).run state
      state := nextState
      roots := name :: roots
    pure (roots.reverse, state)
  String.intercalate "\n" state.declarations.toList ++ "\n" ++
    "noncomputable def actionWideCert : Symbolic.ActionWide.RulesCert := [" ++
    String.intercalate ", " roots ++ "]\n"

structure ActionWideLeanSource where
  data : String

private abbrev WordM := StateT (Array Nat) Option

private def pushWord (word : Nat) : WordM Unit :=
  modify (·.push word)

private def encodeActionRef (registers : Std.HashMap String Nat) :
    Symbolic.Ref → Option Nat
  | .wire number => some (2 * number)
  | .reg name => do pure (2 * (← registers[name]?) + 1)

private def encodeMask (registerCount mask : Nat) : WordM Unit := do
  let indices := (List.range registerCount).filter mask.testBit
  pushWord indices.length
  for index in indices do pushWord index

private def encodeSummary (registerCount : Nat)
    (summary : Symbolic.ActionWide.Summary) : WordM Unit := do
  encodeMask registerCount summary.possible
  encodeMask registerCount summary.definite

private def encodeAction (registers : Std.HashMap String Nat)
    (registerCount : Nat) :
    Symbolic.ActionWide.ActionCert → WordM Unit
  | .skip => pushWord 0
  | .memWrite => pushWord 1
  | .write index value => do
      pushWord 2
      pushWord index
      pushWord (← encodeActionRef registers value)
  | .seq summary left right => do
      pushWord 3
      encodeSummary registerCount summary
      encodeSummary registerCount right.summary
      encodeAction registers registerCount left
      encodeAction registers registerCount right
  | cert@(.ite _ guard joins thenCert elseCert) => do
      pushWord 4
      encodeSummary registerCount cert.summary
      pushWord (← encodeActionRef registers guard)
      pushWord joins.length
      encodeAction registers registerCount thenCert
      encodeAction registers registerCount elseCert
      for join in joins do
        pushWord join.index
        match join.output with
        | .wire number => pushWord number
        | .reg _ => failure

private def encodeRules (sourceRegisters : List RegDecl)
    (cert : Symbolic.ActionWide.RulesCert) : Option (Array Nat) := do
  let mut indices : Std.HashMap String Nat := {}
  for h : index in [:sourceRegisters.length] do
    indices := indices.insert sourceRegisters[index].name index
  let (_, words) ← (do
    pushWord cert.length
    for action in cert do encodeSummary sourceRegisters.length action.summary
    for action in cert do
      encodeAction indices sourceRegisters.length action).run #[]
  pure words

/-- Encode compact certificate words as four printable base-64 bytes each.
The generated data is untrusted; `decodeRules` reconstructs and validates all
summaries in the kernel. -/
def actionWideRulesToLean (sourceRegisters : List RegDecl)
    (cert : Symbolic.ActionWide.RulesCert) : Option ActionWideLeanSource := do
  let words ← encodeRules sourceRegisters cert
  let mut data := ""
  for word in words do
    guard (word < 16777216)
    data := data.push (Char.ofNat (33 + (word / 262144) % 64))
    data := data.push (Char.ofNat (33 + (word / 4096) % 64))
    data := data.push (Char.ofNat (33 + (word / 64) % 64))
    data := data.push (Char.ofNat (33 + word % 64))
  pure { data }

private def optionStringToLean : Option String → String
  | none => "none"
  | some value => "(some " ++ quote value ++ ")"

private def nextRegToLean {w : Nat} : Named.NextRegCert w → String
  | .same => ".same"
  | .write => ".write"
  | .seq mid left right =>
      s!".seq {optionStringToLean mid} ({nextRegToLean left}) ({nextRegToLean right})"
  | .ite thenCert elseCert =>
      s!".ite ({nextRegToLean thenCert}) ({nextRegToLean elseCert})"

private def nextRulesToLean {w : Nat} : Named.NextRulesCert w → String
  | .nil => ".nil"
  | .cons mid head tail =>
      s!".cons {optionStringToLean mid} ({nextRegToLean head}) ({nextRulesToLean tail})"

private def regsToLean : {regs : List RegDecl} → Named.RegsCert regs → String
  | [], .nil => ".nil"
  | _ :: _, .cons head tail =>
      s!".cons ⟨{nextRulesToLean head.rules}⟩ ({regsToLean tail})"

private def regCertName (index : Nat) : String :=
  s!"releaseRegCert{index}"

private def indexedRegCertName (index : Nat) : String :=
  s!"indexedReleaseRegCert{index}"

private def refToLean (name : String) : String :=
  if name.startsWith "n" then
    match (name.drop 1).toNat? with
    | some number => s!".wire {number}"
    | none => s!".reg {quote name}"
  else s!".reg {quote name}"

private def optionalRefToLean (name : Option String) : String :=
  match name with
  | some name => s!"some ({refToLean name})"
  | none => "none"

private def indexedNextRegToLean {w : Nat} : Named.NextRegCert w → String
  | .same => ".same"
  | .write => ".write"
  | .seq mid left right =>
      s!".seq ({optionalRefToLean mid}) ({indexedNextRegToLean left}) " ++
        s!"({indexedNextRegToLean right})"
  | .ite thenCert elseCert =>
      s!".ite ({indexedNextRegToLean thenCert}) ({indexedNextRegToLean elseCert})"

private def indexedNextRulesToLean {w : Nat} : Named.NextRulesCert w → String
  | .nil => ".nil"
  | .cons mid head tail =>
      s!".cons ({optionalRefToLean mid}) ({indexedNextRegToLean head}) " ++
        s!"({indexedNextRulesToLean tail})"

private def symbolicRefToLean : Symbolic.Ref → String
  | .reg name => s!".reg {quote name}"
  | .wire number => s!".wire {number}"

private def symbolicOptionalRefToLean : Option Symbolic.Ref → String
  | none => "none"
  | some reference => s!"some ({symbolicRefToLean reference})"

private def symbolicNextRegToLean : Symbolic.NextRegCert → String
  | .same => ".same"
  | .write => ".write"
  | .seq mid left right =>
      s!".seq ({symbolicOptionalRefToLean mid}) ({symbolicNextRegToLean left}) " ++
        s!"({symbolicNextRegToLean right})"
  | .ite thenCert elseCert =>
      s!".ite ({symbolicNextRegToLean thenCert}) ({symbolicNextRegToLean elseCert})"

private def symbolicNextRulesToLean : Symbolic.NextRulesCert → String
  | .nil => ".nil"
  | .cons mid head tail =>
      s!".cons ({symbolicOptionalRefToLean mid}) ({symbolicNextRegToLean head}) " ++
        s!"({symbolicNextRulesToLean tail})"

private def planRegDeclarationList : List Symbolic.NextRulesCert → Nat →
    List String
  | [], _ => []
  | cert :: certs, index =>
      (s!"def wholePlanReleaseRegCert{index} : Symbolic.NextRulesCert := " ++
        symbolicNextRulesToLean cert) ::
      planRegDeclarationList certs (index + 1)

/-- Serialize shared-plan register certificates into bounded declaration
batches. -/
def planDeclarationBatchesToLean (certs : List Symbolic.NextRulesCert)
    (batchSize : Nat := 16) : List String :=
  (planRegDeclarationList certs 0).toChunks batchSize |>.map fun declarations =>
    String.intercalate "\n" declarations ++ "\n"

private def indexedPortRefsToLean (names : Named.PortNames) : String :=
  "{ en := " ++ refToLean names.en ++ ", addr := " ++ refToLean names.addr ++
    ", data := " ++ refToLean names.data ++ " }"

private def indexedOptionalPortRefsToLean : Option Named.PortNames → String
  | some names => indexedPortRefsToLean names
  | none => "{ en := .reg \"\", addr := .reg \"\", data := .reg \"\" }"

private def indexedNextPortToLean {aw dw : Nat} :
    Named.NextPortCert aw dw → String
  | .same => ".same"
  | .write => ".write"
  | .seq mid left right =>
      s!".seq ({indexedOptionalPortRefsToLean mid}) " ++
        s!"({indexedNextPortToLean left}) ({indexedNextPortToLean right})"
  | .ite guard thenPort elsePort thenCert elseCert =>
      s!".ite ({refToLean guard}) ({indexedPortRefsToLean thenPort}) " ++
        s!"({indexedPortRefsToLean elsePort}) ({indexedNextPortToLean thenCert}) " ++
        s!"({indexedNextPortToLean elseCert})"

private def indexedPortRulesToLean {aw dw : Nat} :
    Named.NextPortRulesCert aw dw → String
  | .nil => ".nil"
  | .cons mid head tail =>
      s!".cons ({indexedOptionalPortRefsToLean mid}) " ++
        s!"({indexedNextPortToLean head}) ({indexedPortRulesToLean tail})"

private def regDeclarationList : {regs : List RegDecl} →
    Named.RegsCert regs → Nat → List String
  | [], .nil, _ => []
  | reg :: _, .cons head tail, index =>
      (s!"def {regCertName index} : Named.NextRulesCert {reg.width} := " ++
        nextRulesToLean head.rules) ::
        regDeclarationList tail (index + 1)

private def indexedRegDeclarationList : {regs : List RegDecl} →
    Named.RegsCert regs → Nat → List String
  | [], .nil, _ => []
  | _ :: _, .cons head tail, index =>
      (s!"def {indexedRegCertName index} : Symbolic.NextRulesCert := " ++
        indexedNextRulesToLean head.rules) ::
        indexedRegDeclarationList tail (index + 1)

private def indexedPortCertName (memoryIndex portIndex : Nat) : String :=
  s!"indexedReleaseMem{memoryIndex}PortCert{portIndex}"

private def indexedPortDeclarationList : {aw dw n : Nat} →
    Named.PortsCert aw dw n → Nat → Nat → List String
  | _, _, 0, .nil, _, _ => []
  | _, _, _ + 1, .cons head tail, memoryIndex, portIndex =>
      (s!"def {indexedPortCertName memoryIndex portIndex} : " ++
        "Symbolic.NextPortRulesCert := " ++ indexedPortRulesToLean head) ::
      indexedPortDeclarationList tail memoryIndex (portIndex + 1)

private def indexedMemoryPortDeclarationList (design : Design) :
    {mems : List MemDecl} → Named.MemsCert design mems → Nat → List String
  | [], .nil, _ => []
  | _ :: _, .cons head tail, memoryIndex =>
      indexedPortDeclarationList head.ports memoryIndex 0 ++
        indexedMemoryPortDeclarationList design tail (memoryIndex + 1)

private def namedRegsToLean : {regs : List RegDecl} →
    Named.RegsCert regs → Nat → String
  | [], .nil, _ => ".nil"
  | _ :: _, .cons _ tail, index =>
      s!".cons ⟨{regCertName index}⟩ ({namedRegsToLean tail (index + 1)})"

private def portNamesToLean (names : Named.PortNames) : String :=
  "{ en := " ++ quote names.en ++ ", addr := " ++ quote names.addr ++
    ", data := " ++ quote names.data ++ " }"

private def optionPortNamesToLean : Option Named.PortNames → String
  | none => "none"
  | some names => "(some " ++ portNamesToLean names ++ ")"

private def nextPortToLean {aw dw : Nat} : Named.NextPortCert aw dw → String
  | .same => ".same"
  | .write => ".write"
  | .seq mid left right =>
      s!".seq {optionPortNamesToLean mid} ({nextPortToLean left}) ({nextPortToLean right})"
  | .ite guard thenPort elsePort thenCert elseCert =>
      s!".ite {quote guard} {portNamesToLean thenPort} {portNamesToLean elsePort} " ++
        s!"({nextPortToLean thenCert}) ({nextPortToLean elseCert})"

private def portRulesToLean {aw dw : Nat} :
    Named.NextPortRulesCert aw dw → String
  | .nil => ".nil"
  | .cons mid head tail =>
      s!".cons {optionPortNamesToLean mid} ({nextPortToLean head}) ({portRulesToLean tail})"

private def portsToLean : {aw dw n : Nat} → Named.PortsCert aw dw n → String
  | _, _, 0, .nil => ".nil"
  | _, _, _ + 1, .cons head tail =>
      s!".cons ({portRulesToLean head}) ({portsToLean tail})"

private def memsToLean (d : Design) :
    {mems : List MemDecl} → Named.MemsCert d mems → String
  | [], .nil => ".nil"
  | _ :: _, .cons head tail =>
      s!".cons ⟨{head.numPorts}, {portsToLean head.ports}⟩ ({memsToLean d tail})"

/-- Serialize synthesized proof data as a Lean structure body. The serializer
is untrusted; parsing and kernel acceptance of its output are the checks. -/
def toLean {design : Design} (cert : Named.ModuleCert design) : String :=
  "{ regs := " ++ namedRegsToLean cert.regs 0 ++
    ", mems := " ++ memsToLean design cert.mems ++ " }"

/-- Emit each large register proof tree as its own declaration. The final
dependent certificate list names these constants, preventing elaboration of
one monolithic multi-megabyte term. -/
def declarationsToLean {design : Design}
    (cert : Named.ModuleCert design) : String :=
  String.intercalate "\n" (regDeclarationList cert.regs 0) ++ "\n"

/-- Split large generated declaration sets into independently compiled module
bodies. Later certificate modules reference these public constants by name. -/
def declarationBatchesToLean {design : Design}
    (cert : Named.ModuleCert design) (batchSize : Nat := 16) : List String :=
  (regDeclarationList cert.regs 0).toChunks batchSize |>.map fun declarations =>
    String.intercalate "\n" declarations ++ "\n"

/-- String-free action-fold certificates for the bounded symbolic checker. -/
def indexedDeclarationBatchesToLean {design : Design}
    (cert : Named.ModuleCert design) (batchSize : Nat := 16) : List String :=
  (indexedRegDeclarationList cert.regs 0).toChunks batchSize |>.map fun declarations =>
    String.intercalate "\n" declarations ++ "\n"

/-- String-free memory-port fold certificates, emitted separately so adding
ports never perturbs the stable register batch numbering. -/
def indexedPortDeclarationBatchesToLean {design : Design}
    (cert : Named.ModuleCert design) (batchSize : Nat := 16) : List String :=
  (indexedMemoryPortDeclarationList design cert.mems 0).toChunks batchSize |>.map
    fun declarations => String.intercalate "\n" declarations ++ "\n"

end Tools.ReleaseCertGen
