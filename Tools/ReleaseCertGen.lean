-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.NamedCertificate
import Loom.Release.SymbolicCertificate
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
structure GenState where
  nextLookup : Nat := 0
  hashMemo : HashMemo := {}

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
  let mut memo : HashMemo := {}
  for (name, ⟨_, value⟩) in values do
    let (key, nextMemo) := (exprHash value).run memo
    memo := nextMemo
    hashed := hashed.insert key name
  return (⟨hashed, values, addWireNames program.wires {}⟩, memo)

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

private def quote (value : String) : String := reprStr value

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

end Tools.ReleaseCertGen
