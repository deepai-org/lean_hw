-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Hw.FastEval
import Loom.Hw.Semantics
import Lean.Elab.Command
import Lean.Elab.Tactic
import Lean.Elab.Term

/-!
# Pretty hardware quotations

This is the opt-in syntax layer specified by `PRETTY.md`.  It lowers directly
to the existing width-indexed `Expr` and `Act` values; importing lower-level
hardware modules does not activate or depend on it.

The first implementation slice deliberately provides the scalar quotation
core used by Acc8.  The syntax categories are separate from Lean terms, and
ordinary Lean is entered only through `$(...)` / `$stmt(...)`.
-/

namespace Loom.Hw

/-- Read-only authoring handle for an environment-driven input. It lowers to
the same named `Expr.reg` coordinate as the established input declaration,
but deliberately exposes no state-write operation. -/
structure Input (width : Nat) where
  name : String
  deriving Repr, DecidableEq, Inhabited

namespace Input

def rd {width : Nat} (input : Input width) : Expr width :=
  .reg width input.name

def reg {width : Nat} (input : Input width) : Reg width :=
  ⟨input.name⟩

instance {width : Nat} : CoeHead (Input width) (Expr width) := ⟨rd⟩

end Input

/-- Declaration wrapper paired with the read-only `Input` handle. -/
def Declarations.addWireInput {width : Nat} (declarations : Declarations)
    (input : Input width) : Declarations :=
  declarations.addInput input.reg

end Loom.Hw

namespace Loom.Hw.Dsl

open Lean Macro Elab Term Meta Command Tactic

/-- Ordered elaboration-time action generation. The result has exactly the
same left-to-right `Act.seq` shape as a handwritten brace block. -/
def actFor {α : Type} (values : List α) (body : α → Loom.Hw.Act) : Loom.Hw.Act :=
  match values with
  | [] => .skip
  | [value] => body value
  | value :: rest => .seq (body value) (actFor rest body)

inductive DeclarationKind where
  | register | stateRegister | input | wire | constant | stateValue
  deriving Repr, DecidableEq, Inhabited

structure SourceSpan where
  fileName : String
  startByte : Nat
  endByte : Nat
  deriving Repr, DecidableEq, Inhabited

structure DeclarationMetadata where
  name : Name
  kind : DeclarationKind
  width : Nat
  source : SourceSpan
  deriving Repr, DecidableEq, Inhabited

structure RuleMetadata where
  name : Name
  source : SourceSpan
  deriving Repr, DecidableEq, Inhabited

structure SuppressionMetadata where
  ruleName : Name
  lintName : Name
  reason : String
  source : SourceSpan
  deriving Repr, DecidableEq, Inhabited

structure HardwareMetadata where
  designName : Name
  moduleName : String
  declarations : Array DeclarationMetadata
  rules : Array RuleMetadata
  suppressions : Array SuppressionMetadata
  deriving Repr, Inhabited

initialize hardwareMetadataExt : SimplePersistentEnvExtension HardwareMetadata
    (Array HardwareMetadata) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun imported => imported.foldl (init := #[]) (fun all entries => all ++ entries)
    addEntryFn := fun entries entry => entries.push entry
  }

def findHardwareMetadata? (environment : Environment) (designName : Name) :
    Option HardwareMetadata :=
  (hardwareMetadataExt.getState environment).findRev? (fun metadata =>
    metadata.designName == designName)

declare_syntax_cat hwexpr
declare_syntax_cat hwstmt
declare_syntax_cat hwcasearm

/-- Prevent a leading case-arm `|` on the next line from being consumed as a
bitwise OR. Ordinary multiline expressions remain available by parenthesizing
the continuation, which is clearer at this already-sensitive boundary. -/
def checkNoLinebreakBefore : Lean.Parser.Parser where
  info := Lean.Parser.epsilonInfo
  fn := fun _ state =>
    if Lean.Parser.checkTailLinebreak state.stxStack.back then
      state.mkError "bitwise `|` must remain on the same line as its left operand"
    else state

@[combinator_formatter checkNoLinebreakBefore]
def checkNoLinebreakBefore.formatter : Lean.PrettyPrinter.Formatter := pure ()

@[combinator_parenthesizer checkNoLinebreakBefore]
def checkNoLinebreakBefore.parenthesizer : Lean.PrettyPrinter.Parenthesizer := pure ()

/-! Expression grammar. Precedences match the public table. Comparison is
non-associative because both operands must bind more tightly than level 40. -/

syntax:max num : hwexpr
syntax:max ident : hwexpr
syntax:max "(" hwexpr ")" : hwexpr
syntax:80 hwexpr:80 "[" num "]" : hwexpr
syntax:80 hwexpr:80 "[" num ":" num "]" : hwexpr
syntax:80 ident "[" num ":" num "]" : hwexpr
syntax:80 ident "[" hwexpr "]" : hwexpr
syntax:75 "~" hwexpr:75 : hwexpr
syntax:75 "zext" hwexpr:76 "to" num : hwexpr
syntax:75 "sext" hwexpr:76 "to" num : hwexpr
syntax:70 hwexpr:70 " * " hwexpr:71 : hwexpr
syntax:70 hwexpr:70 " / " hwexpr:71 : hwexpr
syntax:70 hwexpr:70 " % " hwexpr:71 : hwexpr
syntax:65 hwexpr:65 " + " hwexpr:66 : hwexpr
syntax:65 hwexpr:65 " - " hwexpr:66 : hwexpr
syntax:60 hwexpr:60 " << " hwexpr:61 : hwexpr
syntax:60 hwexpr:60 " >> " hwexpr:61 : hwexpr
syntax:55 hwexpr:56 " ++ " hwexpr:55 : hwexpr
syntax:50 hwexpr:50 " & " hwexpr:51 : hwexpr
syntax:48 hwexpr:48 " ^ " hwexpr:49 : hwexpr
@[hwexpr_parser] def bitwiseOrParser := trailing_parser:46
  checkNoLinebreakBefore >> " | " >> Lean.Parser.categoryParser `hwexpr 47
syntax:40 hwexpr:41 " == " hwexpr:41 : hwexpr
syntax:40 hwexpr:41 " <u " hwexpr:41 : hwexpr
syntax:40 hwexpr:41 " <s " hwexpr:41 : hwexpr
syntax:20 "if " hwexpr " then " hwexpr " else " hwexpr : hwexpr

syntax:max (name := hwLit) "hw_lit% " num : term
syntax:max (name := hwAtom) "hw_atom% " term:max : term
syntax:max (name := hwIndexLit) "hw_index_lit% " term:max num : term
syntax:max (name := hwMemRead) "hw_mem_read% " term:max term:max : term
syntax:max (name := hwShift) "hw_shift% " str term:max term:max : term

/-- Elaborate a bare hardware name from its own declared type. This avoids the
result-width ambiguity of `a == b`: a `Reg w` becomes its read expression,
while an existing `Expr w` remains unchanged. -/
@[term_elab hwAtom] def elabHwAtom : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_atom% $valueSyntax:term) =>
      let value ← elabTerm valueSyntax none
      let valueType ← Meta.whnf (← Meta.inferType value)
      let result ←
        if valueType.isAppOfArity ``Loom.Hw.Expr 1 then
          pure value
        else if valueType.isAppOfArity ``Loom.Hw.Reg 1 then
          Meta.mkAppM ``Loom.Hw.Reg.rd #[value]
        else if valueType.isAppOfArity ``Loom.Hw.Input 1 then
          Meta.mkAppM ``Loom.Hw.Input.rd #[value]
        else
          throwErrorAt valueSyntax
            "hardware identifier must name a typed register, input, or expression"
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwIndexLit] def elabHwIndexLit : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_index_lit% $containerSyntax:term $index:num) =>
      let container ← elabTerm containerSyntax none
      let containerType ← Meta.whnf (← Meta.inferType container)
      let result ←
        if containerType.isAppOfArity ``Loom.Hw.Reg 1 then
          let value ← Meta.mkAppM ``Loom.Hw.Reg.rd #[container]
          Meta.mkAppM ``Loom.Hw.Expr.slice
            #[value, .lit (.natVal index.getNat), .lit (.natVal 1)]
        else if containerType.isAppOfArity ``Loom.Hw.Expr 1 then
          Meta.mkAppM ``Loom.Hw.Expr.slice
            #[container, .lit (.natVal index.getNat), .lit (.natVal 1)]
        else if containerType.isAppOfArity ``Loom.Hw.Mem 2 then
          let addressWidth := containerType.getAppArgs[0]!
          let addressType := .app (.const ``Loom.Hw.Expr []) addressWidth
          let addressSyntax ← `(hw_lit% $index)
          let address ← elabTerm addressSyntax (some addressType)
          Meta.mkAppM ``Loom.Hw.Mem.rd #[container, address]
        else
          throwErrorAt containerSyntax
            "indexed hardware value must be a register, expression, or memory"
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwMemRead] def elabHwMemRead : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_mem_read% $memorySyntax:term $addressSyntax:term) =>
      let memory ← elabTerm memorySyntax none
      let memoryType ← Meta.whnf (← Meta.inferType memory)
      unless memoryType.isAppOfArity ``Loom.Hw.Mem 2 do
        throwErrorAt memorySyntax
          "a dynamic hardware index is only available on a typed memory; dynamic bit select is not supported"
      let addressWidth := memoryType.getAppArgs[0]!
      let addressType := .app (.const ``Loom.Hw.Expr []) addressWidth
      let address ← elabTerm addressSyntax (some addressType)
      let result ← Meta.mkAppM ``Loom.Hw.Mem.rd #[memory, address]
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwShift] def elabHwShift : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_shift% $operation:str $leftSyntax:term $rightSyntax:term) =>
      let left ← elabTerm leftSyntax expectedType?
      let leftType ← Meta.whnf (← Meta.inferType left)
      unless leftType.isAppOfArity ``Loom.Hw.Expr 1 do
        throwErrorAt leftSyntax "shift left operand must be a typed hardware expression"
      let widthExpr ← Meta.whnf leftType.getAppArgs[0]!
      let liftStatic (amount : Nat) : TermElabM Lean.Expr := do
          let width? : Option Nat ← getNatValue? widthExpr
          let some width := width?
            | throwErrorAt rightSyntax "shift width must reduce before lifting a static amount"
          let limit := 2 ^ width
          if width == 0 || amount ≥ limit then
            throwErrorAt rightSyntax
              s!"shift amount {amount} does not fit the {width}-bit shift operand"
          let literalSyntax ← `(Loom.Hw.Expr.lit
            (BitVec.ofNat $(quote width) $(quote amount)))
          elabTerm literalSyntax (some leftType)
      let right ← match rightSyntax.raw.isNatLit? with
        | some amount => liftStatic amount
        | none => do
            let rightValue ← elabTerm rightSyntax none
            let rightType ← Meta.whnf (← Meta.inferType rightValue)
            if rightType.isConstOf ``Nat then
              let amount? : Option Nat ← getNatValue? (← Meta.whnf rightValue)
              let some amount := amount?
                | throwErrorAt rightSyntax
                    "static shift amount must reduce to a numeral; use a typed expression for a dynamic shift"
              liftStatic amount
            else if rightType.isAppOfArity ``Loom.Hw.Reg 1 then
              let read ← Meta.mkAppM ``Loom.Hw.Reg.rd #[rightValue]
              ensureHasType (some leftType) read
            else
              ensureHasType (some leftType) rightValue
      let constructor ← if operation.getString == "shl" then pure ``Loom.Hw.Expr.shl
        else if operation.getString == "shr" then pure ``Loom.Hw.Expr.shr
        else throwErrorAt operation "unknown shift operation"
      let result ← Meta.mkAppM constructor #[left, right]
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

/-- Range-checked hardware literal. Unlike the legacy `OfNat (Expr w)`
instance, this elaborator refuses truncation and refuses an unknown width. -/
@[term_elab hwLit] def elabHwLit : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_lit% $n:num) =>
      let some expected := expectedType?
        | throwErrorAt n "hardware literal requires an expected `Expr width` type"
      let expected ← instantiateMVars expected
      let expectedWhnf ← Meta.whnf expected
      unless expectedWhnf.isAppOfArity ``Loom.Hw.Expr 1 do
        throwErrorAt n "hardware literal requires an expected `Expr width` type"
      let widthExpr ← Meta.whnf expectedWhnf.getAppArgs[0]!
      let width? : Option Nat ← getNatValue? widthExpr
      let some width := width?
        | throwErrorAt n
            "hardware literal width must reduce before range checking; use an explicit typed `$(...)` splice"
      let value := n.getNat
      let limit : Nat := 2 ^ width
      let maxValue : Nat := limit - 1
      if width == 0 || value ≥ limit then
        throwErrorAt n
          "literal {value} does not fit in {width} bits; expected 0 through {maxValue}"
      let literal ← `(Loom.Hw.Expr.lit (BitVec.ofNat $(quote width) $(quote value)))
      elabTermEnsuringType literal (some expected)
  | _ => throwUnsupportedSyntax

syntax "[hwexpr| " hwexpr "]" : term

private inductive InfixFamily where
  | arithmetic | shift | concat | bitwise | comparison
  deriving BEq

private def infixFamily : TSyntax `hwexpr → Option InfixFamily
  | `(hwexpr| $_:hwexpr * $_:hwexpr) | `(hwexpr| $_:hwexpr / $_:hwexpr)
  | `(hwexpr| $_:hwexpr % $_:hwexpr) | `(hwexpr| $_:hwexpr + $_:hwexpr)
  | `(hwexpr| $_:hwexpr - $_:hwexpr) => some .arithmetic
  | `(hwexpr| $_:hwexpr << $_:hwexpr) | `(hwexpr| $_:hwexpr >> $_:hwexpr) => some .shift
  | `(hwexpr| $_:hwexpr ++ $_:hwexpr) => some .concat
  | `(hwexpr| $_:hwexpr & $_:hwexpr) | `(hwexpr| $_:hwexpr ^ $_:hwexpr)
  | `(hwexpr| $_:hwexpr | $_:hwexpr) => some .bitwise
  | `(hwexpr| $_:hwexpr == $_:hwexpr) | `(hwexpr| $_:hwexpr <u $_:hwexpr)
  | `(hwexpr| $_:hwexpr <s $_:hwexpr) => some .comparison
  | _ => none

private def validateInfixBoundary (parent : InfixFamily)
    (left right : TSyntax `hwexpr) : MacroM Unit := do
  for child in #[left, right] do
    let some childFamily := infixFamily child | continue
    if (parent == .comparison && childFamily == .bitwise) ||
        (parent == .bitwise && childFamily == .comparison) then
      Macro.throwErrorAt child
        "comparison and bitwise operators require parentheses; parenthesize the intended grouping"
    if (parent == .shift && childFamily == .arithmetic) ||
        (parent == .arithmetic && childFamily == .shift) then
      Macro.throwErrorAt child
        "shift and arithmetic operators require parentheses; parenthesize the intended grouping"
    if (parent == .concat && childFamily != .concat) ||
        (parent != .concat && childFamily == .concat) then
      Macro.throwErrorAt child
        "concatenation and other infix operators require parentheses; parenthesize the intended grouping"

private def shiftOperandTerm (operand : TSyntax `hwexpr) : MacroM (TSyntax `term) :=
  match operand with
  | `(hwexpr| $value:num) => pure ⟨value.raw⟩
  | `(hwexpr| $name:ident) => pure ⟨name.raw⟩
  | _ => `([hwexpr| $operand])

macro_rules
  | `([hwexpr| $n:num]) => `(hw_lit% $n)
  | `([hwexpr| $id:ident]) => `(hw_atom% $id)
  | `([hwexpr| ($e:hwexpr)]) => `([hwexpr| $e])
  | `([hwexpr| $id:ident[$bit:num]]) => `(hw_index_lit% $id $bit)
  | `([hwexpr| $id:ident[$hi:num:$lo:num]]) => do
      let hiValue := hi.getNat
      let loValue := lo.getNat
      if hiValue < loValue then
        Macro.throwErrorAt hi "slice high bit must be greater than or equal to its low bit"
      `(Loom.Hw.Expr.slice (hw_atom% $id) $(quote loValue) $(quote (hiValue - loValue + 1)))
  | `([hwexpr| $memory:ident[$address:hwexpr]]) =>
      `(hw_mem_read% $memory [hwexpr| $address])
  | `([hwexpr| $e:hwexpr[$bit:num]]) =>
      `(Loom.Hw.Expr.slice [hwexpr| $e] $(quote bit.getNat) 1)
  | `([hwexpr| $e:hwexpr[$hi:num:$lo:num]]) => do
      let hiValue := hi.getNat
      let loValue := lo.getNat
      if hiValue < loValue then
        Macro.throwErrorAt hi "slice high bit must be greater than or equal to its low bit"
      `(Loom.Hw.Expr.slice [hwexpr| $e] $(quote loValue) $(quote (hiValue - loValue + 1)))
  | `([hwexpr| ~ $e:hwexpr]) => `(Loom.Hw.Expr.not [hwexpr| $e])
  | `([hwexpr| zext $e:hwexpr to $width:num]) =>
      `(Loom.Hw.Expr.zext [hwexpr| $e] $width)
  | `([hwexpr| sext $e:hwexpr to $width:num]) =>
      `(Loom.Hw.Expr.sext [hwexpr| $e] $width)
  | `([hwexpr| $a:hwexpr * $b:hwexpr]) => do validateInfixBoundary .arithmetic a b; `(Loom.Hw.Expr.mul [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr / $b:hwexpr]) => do validateInfixBoundary .arithmetic a b; `(Loom.Hw.Expr.udiv [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr % $b:hwexpr]) => do validateInfixBoundary .arithmetic a b; `(Loom.Hw.Expr.urem [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr + $b:hwexpr]) => do validateInfixBoundary .arithmetic a b; `(Loom.Hw.Expr.add [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr - $b:hwexpr]) => do validateInfixBoundary .arithmetic a b; `(Loom.Hw.Expr.sub [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr << $b:hwexpr]) => do
      validateInfixBoundary .shift a b
      `(hw_shift% "shl" [hwexpr| $a] $(← shiftOperandTerm b))
  | `([hwexpr| $a:hwexpr >> $b:hwexpr]) => do
      validateInfixBoundary .shift a b
      `(hw_shift% "shr" [hwexpr| $a] $(← shiftOperandTerm b))
  | `([hwexpr| $a:hwexpr ++ $b:hwexpr]) => do validateInfixBoundary .concat a b; `(Loom.Hw.Expr.concat [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr & $b:hwexpr]) => do validateInfixBoundary .bitwise a b; `(Loom.Hw.Expr.and [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr ^ $b:hwexpr]) => do validateInfixBoundary .bitwise a b; `(Loom.Hw.Expr.xor [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr | $b:hwexpr]) => do validateInfixBoundary .bitwise a b; `(Loom.Hw.Expr.or [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr == $b:hwexpr]) => do validateInfixBoundary .comparison a b; `(Loom.Hw.Expr.eq [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr <u $b:hwexpr]) => do validateInfixBoundary .comparison a b; `(Loom.Hw.Expr.ult [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr <s $b:hwexpr]) => do validateInfixBoundary .comparison a b; `(Loom.Hw.Expr.slt [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| if $c:hwexpr then $t:hwexpr else $f:hwexpr]) =>
      `(Loom.Hw.Expr.mux [hwexpr| $c] [hwexpr| $t] [hwexpr| $f])
  | `([hwexpr| $e:hwexpr]) => do
      if e.raw.getKind.toString.endsWith "pseudo.antiquot" then
        return e.raw[2][1]
      Macro.throwErrorAt e "unsupported hardware expression"

/-! Statement grammar for scalar state and explicit escapes. Blocks are
semicolon-separated in quotations for now; the enclosing `hardware` command
will own newline-separated source statements and preserve their locations. -/

syntax "skip" : hwstmt
syntax (name := hwStmtSplice) "$stmt" "(" term ")" : hwstmt
syntax ident " <- " hwexpr : hwstmt
syntax ident "[" "port" num "," hwexpr "]" " <- " hwexpr : hwstmt
syntax "let" ident ":" num ":=" hwexpr : hwstmt
syntax "let" ident ":=" hwexpr : hwstmt
syntax "suppress" ident "because" str "in" hwstmt : hwstmt
syntax "for" ident "in" term "generate" hwstmt : hwstmt
syntax "if " hwexpr " then " hwstmt " else " hwstmt : hwstmt
syntax "if " hwexpr " then " hwstmt : hwstmt
syntax "|" hwexpr "=>" hwstmt : hwcasearm
syntax "|" "default" "=>" hwstmt : hwcasearm
syntax "case" hwexpr "of" withPosition(many1Indent(ppLine hwcasearm)) : hwstmt
syntax "{" hwstmt,* "}" : hwstmt

mutual
  private partial def expandCase (scrutinee : TSyntax `hwexpr)
      (arms : List (TSyntax `hwcasearm)) : MacroM (TSyntax `term) :=
    match arms with
    | [] => `(Loom.Hw.Act.skip)
    | arm :: rest =>
        match arm with
        | `(hwcasearm| | default => $body:hwstmt) => do
            if !rest.isEmpty then
              Macro.throwErrorAt arm "the default case arm must be last"
            expandStmt body
        | `(hwcasearm| | $value:hwexpr => $body:hwstmt) => do
            `(Loom.Hw.Act.ite
              (Loom.Hw.Expr.eq [hwexpr| $scrutinee] [hwexpr| $value])
              $(← expandStmt body) $(← expandCase scrutinee rest))
        | _ => Macro.throwErrorAt arm "unsupported hardware case arm"

  private partial def expandStmt : TSyntax `hwstmt → MacroM (TSyntax `term)
    | `(hwstmt| skip) => `(Loom.Hw.Act.skip)
    | `(hwstmt| $target:ident <- $value:hwexpr) =>
        `(Loom.Hw.Reg.set $target [hwexpr| $value])
    | `(hwstmt| $memory:ident[port $portIndex:num, $address:hwexpr] <- $value:hwexpr) =>
        `(Loom.Hw.Mem.write $memory $portIndex [hwexpr| $address] [hwexpr| $value])
    | stx@`(hwstmt| let $_:ident : $_:num := $_:hwexpr) =>
        Macro.throwErrorAt stx "a hardware let must be followed by another statement in the same block"
    | stx@`(hwstmt| let $_:ident := $_:hwexpr) =>
        Macro.throwErrorAt stx "a hardware let must be followed by another statement in the same block"
    | `(hwstmt| suppress $_:ident because $_:str in $body:hwstmt) => expandStmt body
    | `(hwstmt| for $binder:ident in $values:term generate $body:hwstmt) => do
        let values : TSyntax `term :=
          if values.raw.getKind.toString.endsWith "pseudo.antiquot" then
            ⟨values.raw[2][1]⟩
          else values
        let loweredBody ← expandStmt body
        `(Loom.Hw.Dsl.actFor $values (fun $binder => $loweredBody))
    | `(hwstmt| if $condition:hwexpr then $yes:hwstmt else $no:hwstmt) => do
        `(Loom.Hw.Act.ite [hwexpr| $condition]
          $(← expandStmt yes) $(← expandStmt no))
    | `(hwstmt| if $condition:hwexpr then $yes:hwstmt) => do
        `(Loom.Hw.Act.ite [hwexpr| $condition]
          $(← expandStmt yes) Loom.Hw.Act.skip)
    | `(hwstmt| case $scrutinee:hwexpr of $arms:hwcasearm*) =>
        expandCase scrutinee arms.toList
    | `(hwstmt| {$statements:hwstmt,*}) => expandSeq statements.getElems.toList
    | stx =>
        if stx.raw.getKind == ``hwStmtSplice then
          pure ⟨stx.raw[2]⟩
        else
          Macro.throwErrorAt stx "unsupported hardware statement"

  private partial def expandSeq : List (TSyntax `hwstmt) → MacroM (TSyntax `term)
    | [] => `(Loom.Hw.Act.skip)
    | [statement] => expandStmt statement
    | statement :: rest =>
        match statement with
        | `(hwstmt| let $name:ident : $width:num := $value:hwexpr) => do
            `(let $name : Loom.Hw.Expr $width := [hwexpr| $value]
              $(← expandSeq rest))
        | `(hwstmt| let $name:ident := $value:hwexpr) => do
            `(let $name := [hwexpr| $value]
              $(← expandSeq rest))
        | _ => do
            `(Loom.Hw.Act.seq $(← expandStmt statement) $(← expandSeq rest))
end

syntax "[hwstmt| " hwstmt "]" : term

macro_rules
  | `([hwstmt| $statement:hwstmt]) => expandStmt statement

/-! ## Minimal scalar design command

This first command slice intentionally supports only scalar registers and
rules.  Later declaration forms extend the item category; they do not change
the generated `Declarations`/`Design` shape established here. -/

declare_syntax_cat hwitem
syntax ident ident ":" num : hwitem
syntax ident ident ":" num ":=" num : hwitem
syntax ident ident ident ":" num : hwitem
syntax ident ident ident ":" num ":=" num : hwitem
syntax ident ident ident ":" num ":=" hwexpr : hwitem
syntax ident ident ":" "{" ident,* "}" : hwitem
syntax ident ident ":" "{" ident,* "}" ":=" ident : hwitem
syntax ident ident ":" num "{" ident,* "}" : hwitem
syntax ident ident ":" num "{" ident,* "}" ":=" ident : hwitem
syntax ident ident ident ":" "{" ident,* "}" : hwitem
syntax ident ident ident ":" "{" ident,* "}" ":=" ident : hwitem
syntax ident ident ident ":" num "{" ident,* "}" : hwitem
syntax ident ident ident ":" num "{" ident,* "}" ":=" ident : hwitem
syntax ident ident ":=" hwstmt : hwitem
syntax ident ident "suppress" ident "because" str ":=" hwstmt : hwitem
syntax (name := hardwareCmd) (docComment)? "hardware" ident "where" hwitem* : command

private structure ScalarRegItem where
  name : TSyntax `ident
  width : TSyntax `num
  exported : Bool
  init : Nat := 0

private structure ConstItem where
  name : TSyntax `ident
  width : TSyntax `num
  value : TSyntax `num

private structure InputItem where
  name : TSyntax `ident
  width : TSyntax `num

private structure WireItem where
  name : TSyntax `ident
  width : TSyntax `num
  value : TSyntax `hwexpr

private structure RuleItem where
  name : TSyntax `ident
  body : TSyntax `hwstmt
  suppressedLint : Option Name := none
  suppressionReason : Option String := none

private structure StateDomain where
  register : TSyntax `ident
  members : Array (TSyntax `ident)

private structure WrittenTarget where
  name : Name
  source : Syntax
  overrideExpected : Bool

private structure LintFinding where
  source : Syntax
  message : String

private def knownLint (name : Name) : Bool :=
  name == `read_after_write || name == `multiple_write || name == `unguarded_channel

private partial def expressionReads : TSyntax `hwexpr → List (TSyntax `ident)
  | `(hwexpr| $_:num) => []
  | `(hwexpr| $name:ident) => [name]
  | `(hwexpr| ($value:hwexpr)) => expressionReads value
  | `(hwexpr| $name:ident[$_:num]) => [name]
  | `(hwexpr| $name:ident[$_:num:$__:num]) => [name]
  | `(hwexpr| $memory:ident[$address:hwexpr]) => memory :: expressionReads address
  | `(hwexpr| $value:hwexpr[$_:num]) => expressionReads value
  | `(hwexpr| $value:hwexpr[$_:num:$__:num]) => expressionReads value
  | `(hwexpr| ~ $value:hwexpr) => expressionReads value
  | `(hwexpr| zext $value:hwexpr to $_:num) => expressionReads value
  | `(hwexpr| sext $value:hwexpr to $_:num) => expressionReads value
  | `(hwexpr| $left:hwexpr * $right:hwexpr)
  | `(hwexpr| $left:hwexpr / $right:hwexpr)
  | `(hwexpr| $left:hwexpr % $right:hwexpr)
  | `(hwexpr| $left:hwexpr + $right:hwexpr)
  | `(hwexpr| $left:hwexpr - $right:hwexpr)
  | `(hwexpr| $left:hwexpr << $right:hwexpr)
  | `(hwexpr| $left:hwexpr >> $right:hwexpr)
  | `(hwexpr| $left:hwexpr ++ $right:hwexpr)
  | `(hwexpr| $left:hwexpr & $right:hwexpr)
  | `(hwexpr| $left:hwexpr ^ $right:hwexpr)
  | `(hwexpr| $left:hwexpr | $right:hwexpr)
  | `(hwexpr| $left:hwexpr == $right:hwexpr)
  | `(hwexpr| $left:hwexpr <u $right:hwexpr)
  | `(hwexpr| $left:hwexpr <s $right:hwexpr) =>
      expressionReads left ++ expressionReads right
  | `(hwexpr| if $condition:hwexpr then $yes:hwexpr else $no:hwexpr) =>
      expressionReads condition ++ expressionReads yes ++ expressionReads no
  | _ => []

private def readAfterWriteFindings (registers : Array Name)
    (suppressed : Array Name) (written : List WrittenTarget)
    (expression : TSyntax `hwexpr) : List LintFinding :=
  if suppressed.contains `read_after_write then []
  else
    (expressionReads expression).filterMap fun (read : TSyntax `ident) =>
      if registers.contains read.getId && written.any (fun prior => prior.name == read.getId) then
        some ⟨read.raw,
          s!"'{read.getId}' reads its start-of-cycle value; an earlier write takes effect next cycle"⟩
      else none

private partial def analyzeStatement (registers : Array Name) (suppressed : Array Name)
    (statement : TSyntax `hwstmt) (written : List WrittenTarget) :
    List WrittenTarget × List LintFinding :=
  match statement with
  | `(hwstmt| skip) => (written, [])
  | `(hwstmt| $target:ident <- $value:hwexpr) =>
      let readFindings := readAfterWriteFindings registers suppressed written value
      let prior := written.filter (fun earlier => earlier.name == target.getId)
      let suppressMultiple := suppressed.contains `multiple_write
      let multipleFinding :=
        if !prior.isEmpty && !suppressMultiple && prior.any (fun earlier => !earlier.overrideExpected) then
          [⟨target, s!"'{target.getId}' may be written more than once in one cycle; the later write wins"⟩]
        else []
      (written ++ [⟨target.getId, target, suppressMultiple⟩], readFindings ++ multipleFinding)
  | `(hwstmt| $_:ident[port $_:num, $address:hwexpr] <- $value:hwexpr) =>
      (written, readAfterWriteFindings registers suppressed written address ++
        readAfterWriteFindings registers suppressed written value)
  | `(hwstmt| let $_:ident : $_:num := $value:hwexpr)
  | `(hwstmt| let $_:ident := $value:hwexpr) =>
      (written, readAfterWriteFindings registers suppressed written value)
  | `(hwstmt| suppress $lint:ident because $_:str in $body:hwstmt) =>
      analyzeStatement registers (suppressed.push lint.getId) body written
  | `(hwstmt| for $_:ident in $_:term generate $body:hwstmt) =>
      analyzeStatement registers suppressed body written
  | `(hwstmt| if $condition:hwexpr then $yes:hwstmt else $no:hwstmt) =>
      let conditionFindings := readAfterWriteFindings registers suppressed written condition
      let (yesWrites, yesFindings) := analyzeStatement registers suppressed yes written
      let (noWrites, noFindings) := analyzeStatement registers suppressed no written
      (yesWrites ++ noWrites, conditionFindings ++ yesFindings ++ noFindings)
  | `(hwstmt| if $condition:hwexpr then $yes:hwstmt) =>
      let conditionFindings := readAfterWriteFindings registers suppressed written condition
      let (yesWrites, yesFindings) := analyzeStatement registers suppressed yes written
      (yesWrites ++ written, conditionFindings ++ yesFindings)
  | `(hwstmt| case $scrutinee:hwexpr of $arms:hwcasearm*) =>
      let initialFindings := readAfterWriteFindings registers suppressed written scrutinee
      arms.foldl (fun (allWrites, allFindings) arm =>
        let body? := match arm with
          | `(hwcasearm| | default => $body:hwstmt)
          | `(hwcasearm| | $_:hwexpr => $body:hwstmt) => some body
          | _ => none
        match body? with
        | none => (allWrites, allFindings)
        | some body =>
            let (armWrites, armFindings) := analyzeStatement registers suppressed body written
            (allWrites ++ armWrites, allFindings ++ armFindings)) ([], initialFindings)
  | `(hwstmt| {$statements:hwstmt,*}) =>
      statements.getElems.foldl (fun (priorWrites, priorFindings) next =>
        let (nextWrites, nextFindings) := analyzeStatement registers suppressed next priorWrites
        (nextWrites, priorFindings ++ nextFindings)) (written, [])
  | _ => (written, [])

private def hardwareLintFindings (registers : Array ScalarRegItem)
    (rules : Array RuleItem) : List LintFinding :=
  let registerNames := registers.map (fun register => register.name.getId)
  let (_, findings) := rules.foldl (fun (written, priorFindings) ruleItem =>
    let suppressed := ruleItem.suppressedLint.toArray
    let (nextWritten, nextFindings) :=
      analyzeStatement registerNames suppressed ruleItem.body written
    (nextWritten, priorFindings ++ nextFindings)) ([], [])
  findings

private def checkedValue (width value : TSyntax `num) : MacroM Nat := do
  let widthValue := width.getNat
  let valueNat := value.getNat
  let limit := 2 ^ widthValue
  if widthValue == 0 || valueNat ≥ limit then
    Macro.throwErrorAt value
      s!"literal {valueNat} does not fit in {widthValue} bits; expected 0 through {limit - 1}"
  pure valueNat

private partial def validateWriteTargets (writable : Array Name) : TSyntax `hwstmt → MacroM Unit
  | `(hwstmt| skip) => pure ()
  | `(hwstmt| $target:ident <- $_:hwexpr) =>
      unless writable.contains target.getId do
        Macro.throwErrorAt target
          s!"'{target.getId}' is not a writable register in this hardware block"
  | `(hwstmt| $_:ident[port $_:num, $_:hwexpr] <- $_:hwexpr) => pure ()
  | `(hwstmt| let $_:ident : $_:num := $_:hwexpr) => pure ()
  | `(hwstmt| let $_:ident := $_:hwexpr) => pure ()
  | `(hwstmt| suppress $lint:ident because $reason:str in $body:hwstmt) => do
      unless knownLint lint.getId do
        Macro.throwErrorAt lint
          "unknown hardware lint; expected `read_after_write`, `multiple_write`, or `unguarded_channel`"
      if reason.getString.isEmpty then
        Macro.throwErrorAt reason "lint suppression requires a nonempty reason"
      validateWriteTargets writable body
  | `(hwstmt| for $_:ident in $_:term generate $body:hwstmt) =>
      validateWriteTargets writable body
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt else $no:hwstmt) => do
      validateWriteTargets writable yes
      validateWriteTargets writable no
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt) => validateWriteTargets writable yes
  | `(hwstmt| case $_:hwexpr of $arms:hwcasearm*) =>
      for arm in arms do
        match arm with
        | `(hwcasearm| | default => $body:hwstmt)
        | `(hwcasearm| | $_:hwexpr => $body:hwstmt) => validateWriteTargets writable body
        | _ => pure ()
  | `(hwstmt| {$statements:hwstmt,*}) =>
      for statement in statements.getElems do
        validateWriteTargets writable statement
  | _ => pure ()

private partial def validateCases (domains : Array StateDomain) : TSyntax `hwstmt → MacroM Unit
  | `(hwstmt| case $scrutinee:hwexpr of $arms:hwcasearm*) => do
      let domain? := match scrutinee with
        | `(hwexpr| $name:ident) => domains.find? (fun domain => domain.register.getId == name.getId)
        | _ => none
      let mut namedArms : Array (TSyntax `ident) := #[]
      let mut hasDefault := false
      for arm in arms do
        match arm with
        | `(hwcasearm| | default => $body:hwstmt) =>
            hasDefault := true
            validateCases domains body
        | `(hwcasearm| | $name:ident => $body:hwstmt) =>
            if namedArms.any (fun prior => prior.getId == name.getId) then
              Macro.throwErrorAt name s!"duplicate case arm '{name.getId}'"
            namedArms := namedArms.push name
            validateCases domains body
        | `(hwcasearm| | $_:hwexpr => $body:hwstmt) => validateCases domains body
        | _ => pure ()
      match domain? with
      | none =>
          unless hasDefault do
            Macro.throwErrorAt scrutinee
              "case without a default is allowed only for a declared states register"
      | some domain =>
          for armName in namedArms do
            unless domain.members.any (fun member => member.getId == armName.getId) do
              Macro.throwErrorAt armName
                s!"'{armName.getId}' is not a declared state of '{domain.register.getId}'"
          let covered := domain.members.all fun member =>
            namedArms.any (fun armName => armName.getId == member.getId)
          if !hasDefault && !covered then
            let missing := domain.members.filter (fun member =>
              !namedArms.any (fun armName => armName.getId == member.getId))
            Macro.throwErrorAt scrutinee
              s!"non-exhaustive state case; missing {String.intercalate ", " (missing.toList.map (toString ·.getId))}"
          -- A later command-elaboration pass reports a dead-default warning;
          -- macro expansion itself has no logging capability.
          pure ()
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt else $no:hwstmt) => do
      validateCases domains yes
      validateCases domains no
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt) => validateCases domains yes
  | `(hwstmt| suppress $_:ident because $_:str in $body:hwstmt) =>
      validateCases domains body
  | `(hwstmt| for $_:ident in $_:term generate $body:hwstmt) => validateCases domains body
  | `(hwstmt| {$statements:hwstmt,*}) =>
      for statement in statements.getElems do
        validateCases domains statement
  | _ => pure ()

private partial def inferredStateWidthLoop (count capacity width : Nat) : Nat :=
  if capacity ≥ count then width
  else inferredStateWidthLoop count (capacity * 2) (width + 1)

private def inferredStateWidth (count : Nat) : Nat :=
  inferredStateWidthLoop count 2 1

private def stateItems (stateName : TSyntax `ident) (width? : Option (TSyntax `num))
    (members : Array (TSyntax `ident)) (reset? : Option (TSyntax `ident))
    (exported : Bool) : MacroM (ScalarRegItem × Array ConstItem) := do
  if members.isEmpty then
    Macro.throwErrorAt stateName "a state declaration requires at least one named state"
  let inferred := inferredStateWidth members.size
  let width := width?.getD ⟨Syntax.mkNumLit (toString inferred)⟩
  let widthValue := width.getNat
  if 2 ^ widthValue < members.size then
    Macro.throwErrorAt width
      s!"state register width {widthValue} cannot encode {members.size} declared states"
  let resetIndex ← match reset? with
    | none => pure 0
    | some reset =>
        let some index := members.findIdx? (fun member => member.getId == reset.getId)
          | Macro.throwErrorAt reset "reset state is not a member of this state declaration"
        pure index
  let constants := members.mapIdx fun index member =>
    { name := member, width := width, value := ⟨Syntax.mkNumLit (toString index)⟩ }
  pure (⟨stateName, width, exported, resetIndex⟩, constants)

private def parseHardwareItems (items : Array (TSyntax `hwitem)) :
    MacroM (Array ScalarRegItem × Array ConstItem × Array InputItem ×
      Array WireItem × Array StateDomain × Array RuleItem) := do
  let mut registers : Array ScalarRegItem := #[]
  let mut constants : Array ConstItem := #[]
  let mut inputs : Array InputItem := #[]
  let mut wires : Array WireItem := #[]
  let mut stateDomains : Array StateDomain := #[]
  let mut rules : Array RuleItem := #[]
  for item in items do
    match item with
    | `(hwitem| $kind:ident $name:ident : $width:num) =>
        if kind.getId == `reg then registers := registers.push ⟨name, width, false, 0⟩
        else if kind.getId == `input then inputs := inputs.push ⟨name, width⟩
        else Macro.throwErrorAt kind "expected `reg` or `input`"
    | `(hwitem| $kind:ident $name:ident : $width:num := $value:num) =>
        if kind.getId == `reg then
          registers := registers.push ⟨name, width, false, ← checkedValue width value⟩
        else if kind.getId == `const then constants := constants.push ⟨name, width, value⟩
        else Macro.throwErrorAt kind "expected `reg` or `const`"
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $width:num) =>
        unless qualifier.getId == `output && kind.getId == `reg do
          Macro.throwErrorAt qualifier "expected `output reg`"
        registers := registers.push ⟨name, width, true, 0⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $width:num := $value:num) =>
        unless qualifier.getId == `output && kind.getId == `reg do
          Macro.throwErrorAt qualifier "expected `output reg`"
        registers := registers.push ⟨name, width, true, ← checkedValue width value⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $width:num := $value:hwexpr) =>
        unless qualifier.getId == `output && kind.getId == `wire do
          Macro.throwErrorAt qualifier "expected `output wire`"
        wires := wires.push ⟨name, width, value⟩
    | `(hwitem| $kind:ident $name:ident : {$members:ident,*}) =>
        unless kind.getId == `states do Macro.throwErrorAt kind "expected `states`"
        let (register, stateConstants) ← stateItems name none members.getElems none false
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| $kind:ident $name:ident : {$members:ident,*} := $reset:ident) =>
        unless kind.getId == `states do Macro.throwErrorAt kind "expected `states`"
        let (register, stateConstants) ← stateItems name none members.getElems (some reset) false
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| $kind:ident $name:ident : $width:num {$members:ident,*}) =>
        unless kind.getId == `states do Macro.throwErrorAt kind "expected `states`"
        let (register, stateConstants) ← stateItems name (some width) members.getElems none false
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| $kind:ident $name:ident : $width:num {$members:ident,*} := $reset:ident) =>
        unless kind.getId == `states do Macro.throwErrorAt kind "expected `states`"
        let (register, stateConstants) ← stateItems name (some width) members.getElems (some reset) false
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : {$members:ident,*}) =>
        unless qualifier.getId == `output && kind.getId == `states do
          Macro.throwErrorAt qualifier "expected `output states`"
        let (register, stateConstants) ← stateItems name none members.getElems none true
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : {$members:ident,*} := $reset:ident) =>
        unless qualifier.getId == `output && kind.getId == `states do
          Macro.throwErrorAt qualifier "expected `output states`"
        let (register, stateConstants) ← stateItems name none members.getElems (some reset) true
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $width:num {$members:ident,*}) =>
        unless qualifier.getId == `output && kind.getId == `states do
          Macro.throwErrorAt qualifier "expected `output states`"
        let (register, stateConstants) ← stateItems name (some width) members.getElems none true
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $width:num {$members:ident,*} := $reset:ident) =>
        unless qualifier.getId == `output && kind.getId == `states do
          Macro.throwErrorAt qualifier "expected `output states`"
        let (register, stateConstants) ← stateItems name (some width) members.getElems (some reset) true
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| $kind:ident $name:ident := $body:hwstmt) =>
        unless kind.getId == `rule do Macro.throwErrorAt kind "expected `rule`"
        rules := rules.push ⟨name, body, none, none⟩
    | `(hwitem| $kind:ident $name:ident suppress $lint:ident because $reason:str := $body:hwstmt) =>
        unless kind.getId == `rule do
          Macro.throwErrorAt kind "expected `rule name suppress lint because \"reason\" := ...`"
        unless knownLint lint.getId do
          Macro.throwErrorAt lint
            "unknown hardware lint; expected `read_after_write`, `multiple_write`, or `unguarded_channel`"
        if reason.getString.isEmpty then Macro.throwErrorAt reason "lint suppression requires a nonempty reason"
        rules := rules.push ⟨name, body, some lint.getId, some reason.getString⟩
    | _ => Macro.throwErrorAt item "unsupported hardware declaration"
  let locals := registers.map (fun item => item.name) ++ constants.map (fun item => item.name) ++
    inputs.map (fun item => item.name) ++ wires.map (fun item => item.name) ++
    rules.map (fun item => item.name)
  for localName in locals do
    if localName.getId == `design || localName.getId == `declarations ||
        localName.getId.toString.endsWith "_name" then
      Macro.throwErrorAt localName
        "this name is reserved by the hardware command; choose a name without the `_name` suffix"
  for i in [:locals.size] do
    for j in [i + 1:locals.size] do
      if locals[i]!.getId == locals[j]!.getId then
        Macro.throwErrorAt locals[j]! s!"duplicate design-local name '{locals[j]!.getId}'"
  let writable := registers.map (fun item => item.name.getId)
  for ruleItem in rules do
    validateWriteTargets writable ruleItem.body
    validateCases stateDomains ruleItem.body
  pure (registers, constants, inputs, wires, stateDomains, rules)

private def sourceSpan (fileName : String) (sourceSyntax : Syntax) : SourceSpan where
  fileName := fileName
  startByte := sourceSyntax.getPos?.map (fun position => position.byteIdx) |>.getD 0
  endByte := sourceSyntax.getTailPos?.map (fun position => position.byteIdx) |>.getD 0

private partial def statementSuppressions (fileName : String) (ruleName : Name) :
    TSyntax `hwstmt → Array SuppressionMetadata
  | statement@`(hwstmt| suppress $lint:ident because $reason:str in $body:hwstmt) =>
      #[⟨ruleName, lint.getId, reason.getString, sourceSpan fileName statement⟩] ++
        statementSuppressions fileName ruleName body
  | `(hwstmt| for $_:ident in $_:term generate $body:hwstmt) =>
      statementSuppressions fileName ruleName body
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt else $no:hwstmt) =>
      statementSuppressions fileName ruleName yes ++ statementSuppressions fileName ruleName no
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt) => statementSuppressions fileName ruleName yes
  | `(hwstmt| case $_:hwexpr of $arms:hwcasearm*) =>
      arms.foldl (fun suppressions arm =>
        match arm with
        | `(hwcasearm| | default => $body:hwstmt)
        | `(hwcasearm| | $_:hwexpr => $body:hwstmt) =>
            suppressions ++ statementSuppressions fileName ruleName body
        | _ => suppressions) #[]
  | `(hwstmt| {$statements:hwstmt,*}) =>
      statements.getElems.foldl (fun suppressions statement =>
        suppressions ++ statementSuppressions fileName ruleName statement) #[]
  | _ => #[]

private def makeHardwareMetadata (fileName : String) (namespaceName : Name)
    (moduleName : TSyntax `ident) (registers : Array ScalarRegItem)
    (constants : Array ConstItem) (inputs : Array InputItem) (wires : Array WireItem)
    (domains : Array StateDomain) (rules : Array RuleItem) : HardwareMetadata := Id.run do
  let mut declarations := #[]
  for register in registers do
    let kind := if domains.any (fun domain => domain.register.getId == register.name.getId)
      then DeclarationKind.stateRegister else .register
    declarations := declarations.push
      ⟨register.name.getId, kind, register.width.getNat, sourceSpan fileName register.name⟩
  for inputItem in inputs do
    declarations := declarations.push
      ⟨inputItem.name.getId, .input, inputItem.width.getNat, sourceSpan fileName inputItem.name⟩
  for wireItem in wires do
    declarations := declarations.push
      ⟨wireItem.name.getId, .wire, wireItem.width.getNat, sourceSpan fileName wireItem.name⟩
  for constant in constants do
    let kind := if domains.any (fun domain =>
        domain.members.any (fun member => member.getId == constant.name.getId))
      then DeclarationKind.stateValue else .constant
    declarations := declarations.push
      ⟨constant.name.getId, kind, constant.width.getNat, sourceSpan fileName constant.name⟩
  let ruleMetadata := rules.map fun ruleItem =>
    ⟨ruleItem.name.getId, sourceSpan fileName ruleItem.name⟩
  let mut suppressions := #[]
  for ruleItem in rules do
    match ruleItem.suppressedLint, ruleItem.suppressionReason with
    | some lint, some reason =>
        suppressions := suppressions.push
          ⟨ruleItem.name.getId, lint, reason, sourceSpan fileName ruleItem.name⟩
    | _, _ => pure ()
    suppressions := suppressions ++ statementSuppressions fileName ruleItem.name.getId ruleItem.body
  return {
    designName := namespaceName ++ `design
    moduleName := moduleName.getId.toString
    declarations := declarations
    rules := ruleMetadata
    suppressions := suppressions
  }

private def expandHardwareCommand
    (documentation : Option (TSyntax ``Lean.Parser.Command.docComment))
    (moduleName : TSyntax `ident)
    (items : Array (TSyntax `hwitem)) : MacroM Syntax := do
  let (registers, constants, inputs, wires, _, rules) ← parseHardwareItems items
  let mut commands : Array Syntax := #[]
  for register in registers do
    let sourceName := Syntax.mkStrLit register.name.getId.toString
    let command ← `(command|
      def $(register.name) : Loom.Hw.Reg $(register.width) :=
        ⟨$sourceName⟩)
    commands := commands.push command
    let lemmaName := mkIdentFrom register.name
      (Name.mkSimple (register.name.getId.toString ++ "_name"))
    let lemmaCommand ← `(command|
      @[simp] theorem $lemmaName : $(register.name).name = $sourceName := rfl)
    commands := commands.push lemmaCommand
  for inputItem in inputs do
    let sourceName := Syntax.mkStrLit inputItem.name.getId.toString
    let command ← `(command|
      def $(inputItem.name) : Loom.Hw.Input $(inputItem.width) := ⟨$sourceName⟩)
    commands := commands.push command
    let lemmaName := mkIdentFrom inputItem.name
      (Name.mkSimple (inputItem.name.getId.toString ++ "_name"))
    let lemmaCommand ← `(command|
      @[simp] theorem $lemmaName : $(inputItem.name).name = $sourceName := rfl)
    commands := commands.push lemmaCommand
  for constant in constants do
    let command ← `(command|
      def $(constant.name) : Loom.Hw.Expr $(constant.width) :=
        hw_lit% $(constant.value))
    commands := commands.push command
  for wireItem in wires do
    let command ← `(command|
      def $(wireItem.name) : Loom.Hw.Expr $(wireItem.width) := [hwexpr| $(wireItem.value)])
    commands := commands.push command
  for ruleItem in rules do
    let command ← `(command|
      def $(ruleItem.name) : Loom.Hw.Act := [hwstmt| $(ruleItem.body)])
    commands := commands.push command
  let mut declarations : TSyntax `term ← `(Loom.Hw.Declarations.empty)
  for register in registers do
    if register.exported then
      declarations ← `($declarations |>.addReg $(register.name)
        (BitVec.ofNat $(register.width) $(quote register.init)) (exported := true))
    else
      declarations ← `($declarations |>.addReg $(register.name)
        (BitVec.ofNat $(register.width) $(quote register.init)))
  for inputItem in inputs do
    declarations ← `($declarations |>.addWireInput $(inputItem.name))
  for wireItem in wires do
    let sourceName := Syntax.mkStrLit wireItem.name.getId.toString
    declarations ← `($declarations |>.addCombOutput $sourceName $(wireItem.name))
  let declarationsName := mkIdentFrom moduleName `declarations
  let declarationsCommand ← `(command|
    def $declarationsName : Loom.Hw.Declarations := $declarations)
  commands := commands.push declarationsCommand
  let mut ruleList : TSyntax `term ← `([])
  for ruleItem in rules.reverse do
    let sourceName := Syntax.mkStrLit ruleItem.name.getId.toString
    ruleList ← `(⟨$sourceName, $(ruleItem.name)⟩ :: $ruleList)
  let emittedName := Syntax.mkStrLit moduleName.getId.toString
  let designName := mkIdentFrom moduleName `design
  let designCommand ← `(command|
    $[$documentation]?
    def $designName : Loom.Hw.Design :=
      Loom.Hw.Design.ofDecls $emittedName $declarationsName $ruleList)
  commands := commands.push designCommand
  pure (Lean.mkNullNode commands)

@[command_elab hardwareCmd] def elabHardwareCommand : CommandElab := fun stx => do
  match stx with
  | `($[$documentation:docComment]? hardware $moduleName:ident where $items:hwitem*) => do
      let (registers, constants, inputs, wires, domains, rules) ←
        liftMacroM <| parseHardwareItems items
      let namespaceName ← getCurrNamespace
      let environment ← getEnv
      let localNames := registers.map (fun item => item.name) ++
        constants.map (fun item => item.name) ++ inputs.map (fun item => item.name) ++
        wires.map (fun item => item.name) ++ rules.map (fun item => item.name)
      for localName in localNames do
        let fullName := namespaceName ++ localName.getId
        if environment.contains fullName then
          throwErrorAt localName s!"'{fullName}' has already been declared"
      for handleName in registers.map (fun item => item.name) ++ inputs.map (fun item => item.name) do
        let lemmaName := namespaceName ++
          Name.mkSimple (handleName.getId.toString ++ "_name")
        if environment.contains lemmaName then
          throwErrorAt handleName s!"generated name lemma '{lemmaName}' has already been declared"
      for generatedName in #[namespaceName ++ `declarations, namespaceName ++ `design] do
        if environment.contains generatedName then
          throwErrorAt moduleName s!"generated declaration '{generatedName}' has already been declared"
      for finding in hardwareLintFindings registers rules do
        logWarningAt finding.source finding.message
      let metadata := makeHardwareMetadata (← getFileName) namespaceName moduleName
        registers constants inputs wires domains rules
      let expanded ← liftMacroM <| expandHardwareCommand documentation moduleName items
      elabCommand expanded
      modifyEnv (hardwareMetadataExt.addEntry · metadata)
  | _ => throwUnsupportedSyntax

private def DeclarationKind.label : DeclarationKind → String
  | .register => "register"
  | .stateRegister => "state register"
  | .input => "input"
  | .wire => "combinational output"
  | .constant => "constant"
  | .stateValue => "state value"

syntax (name := showHardwareCmd) "#show_hardware" ident : command

@[command_elab showHardwareCmd] def elabShowHardware : CommandElab := fun stx => do
  match stx with
  | `(#show_hardware $designSyntax:ident) => do
      let designName ← resolveGlobalConstNoOverload designSyntax
      let some metadata := findHardwareMetadata? (← getEnv) designName
        | throwErrorAt designSyntax
            "no pretty-hardware metadata is registered for this Design"
      let declarationLines := metadata.declarations.toList.map fun declaration =>
        s!"  {declaration.name}: {declaration.kind.label} {declaration.width} bits"
      let ruleLines := metadata.rules.toList.map fun ruleMetadata =>
        s!"  {ruleMetadata.name}"
      let suppressionLines := metadata.suppressions.toList.map fun suppression =>
        s!"  {suppression.ruleName}: suppress {suppression.lintName} because \"{suppression.reason}\""
      let lines :=
        [s!"hardware {metadata.moduleName}", "declarations:"] ++ declarationLines ++
        ["rules:"] ++ ruleLines ++
        (if suppressionLines.isEmpty then [] else ["lint suppressions:"] ++ suppressionLines)
      logInfoAt designSyntax (String.intercalate "\n" lines)
  | _ => throwUnsupportedSyntax

syntax (name := hwUnfoldTactic) "hw_unfold" ident : tactic

@[tactic hwUnfoldTactic] def elabHwUnfold : Tactic := fun stx => do
  match stx with
  | `(tactic| hw_unfold $designSyntax:ident) => withMainContext do
      let designName ← resolveGlobalConstNoOverload designSyntax
      let some metadata := findHardwareMetadata? (← getEnv) designName
        | throwErrorAt designSyntax
            "no pretty-hardware metadata is registered for this Design"
      let namespaceName := designName.getPrefix
      let generatedNames :=
        #[designName, namespaceName ++ `declarations] ++
        metadata.rules.map (fun ruleMetadata => namespaceName ++ ruleMetadata.name) ++
        metadata.declarations.map (fun declaration => namespaceName ++ declaration.name)
      let simpArguments : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
        generatedNames.mapM fun name =>
          let identifier := mkIdent name
          `(Lean.Parser.Tactic.simpLemma| $identifier:term)
      let tactic ← `(tactic| simp [$simpArguments,*])
      evalTactic tactic
  | _ => throwUnsupportedSyntax

/-! ## One-cycle teaching trace

The renderer delegates every state update to `Act.run`; it only follows the
same guards to report which leaf writes fired. It is therefore an inspection
view over the existing semantics, not another simulator. -/

private abbrev NamedNat := String × Nat

private def lookupNamed (bindings : List NamedNat) (name : String) : Option Nat :=
  (bindings.find? (fun binding => binding.1 == name)).map (fun binding => binding.2)

private def initializeTraceState (design : Loom.Hw.Design)
    (bindings : List NamedNat) : Except String Loom.Hw.St := do
  for binding in bindings do
    let some declaration := design.regs.find? (fun declaration => declaration.name == binding.1)
      | throw s!"unknown initial register '{binding.1}'"
    if binding.2 ≥ 2 ^ declaration.width then
      throw s!"initial value {binding.2} does not fit register '{binding.1}' ({declaration.width} bits)"
  pure { design.reset with
    regs := bindings.foldl (fun registers binding =>
      match design.regs.find? (fun declaration => declaration.name == binding.1) with
      | some declaration => registers.set binding.1 (BitVec.ofNat declaration.width binding.2)
      | none => registers) design.reset.regs }

private def traceInputs (design : Loom.Hw.Design) (bindings : List NamedNat) :
    Except String Loom.Hw.InEnv := do
  for binding in bindings do
    let some declaration := design.inputs.find? (fun declaration => declaration.name == binding.1)
      | throw s!"unknown input '{binding.1}'"
    if binding.2 ≥ 2 ^ declaration.width then
      throw s!"input value {binding.2} does not fit '{binding.1}' ({declaration.width} bits)"
  pure fun name width => BitVec.ofNat width ((lookupNamed bindings name).getD 0)

private def traceAct (pre : Loom.Hw.St) (ruleName : String) :
    Loom.Hw.Act → Loom.Hw.St → Loom.Hw.St × List String
  | .skip, accumulator => (accumulator, [])
  | .seq first second, accumulator =>
      let (middle, firstEvents) := traceAct pre ruleName first accumulator
      let (result, secondEvents) := traceAct pre ruleName second middle
      (result, firstEvents ++ secondEvents)
  | .ite condition yes no, accumulator =>
      if condition.eval pre = 1#1 then traceAct pre ruleName yes accumulator
      else traceAct pre ruleName no accumulator
  | action@(.write width name _), accumulator =>
      let before := accumulator.regs name width
      let result := action.run pre accumulator
      let after := result.regs name width
      (result, [s!"rule {ruleName}: {name} {before.toNat} -> {after.toNat}"])
  | action@(.writeSlice totalWidth name _ _ _ _), accumulator =>
      let before := accumulator.regs name totalWidth
      let result := action.run pre accumulator
      let after := result.regs name totalWidth
      (result, [s!"rule {ruleName}: {name} {before.toNat} -> {after.toNat} (slice write)"])
  | action@(.memWrite _ dataWidth name portIndex address _), accumulator =>
      let addressValue := (address.eval pre).toNat
      let before := accumulator.mems name addressValue dataWidth
      let result := action.run pre accumulator
      let after := result.mems name addressValue dataWidth
      (result, [s!"rule {ruleName}: {name}[port {portIndex}, {addressValue}] {before.toNat} -> {after.toNat}"])

def traceCycle (design : Loom.Hw.Design) (inputValues initialValues : List NamedNat) : IO Unit := do
  let initial ← IO.ofExcept (initializeTraceState design initialValues)
  let inputs ← IO.ofExcept (traceInputs design inputValues)
  let pre := initial.setInputs design.inputs inputs
  let (result, events) := design.rules.foldl (fun (accumulator, priorEvents) designRule =>
    let (next, events) := traceAct pre designRule.name designRule.body accumulator
    (next, priorEvents ++ events)) (pre, [])
  let expected := design.cycle pre
  for declaration in design.regs do
    unless result.regs declaration.name declaration.width =
        expected.regs declaration.name declaration.width do
      throw <| IO.userError
        s!"internal trace mismatch at register '{declaration.name}'"
  if events.isEmpty then IO.println "no writes fired"
  else for event in events do IO.println event
  IO.println "final registers:"
  for declaration in design.regs do
    IO.println s!"  {declaration.name} = {(result.regs declaration.name declaration.width).toNat}"

declare_syntax_cat hwtracebind
syntax ident ":=" num : hwtracebind
syntax (name := traceCycleCmd) "#trace_cycle" term:max
  "with" "{" hwtracebind,* "}" "from" "{" hwtracebind,* "}" : command

private def traceBindingTerm (binding : TSyntax `hwtracebind) : MacroM (TSyntax `term) :=
  match binding with
  | `(hwtracebind| $name:ident := $value:num) =>
      let sourceName := Syntax.mkStrLit name.getId.toString
      `(($sourceName, $value))
  | _ => Macro.throwErrorAt binding "invalid trace binding"

macro_rules
  | `(#trace_cycle $design:term with {$inputs:hwtracebind,*} from {$initial:hwtracebind,*}) => do
      let inputTerms ← inputs.getElems.mapM traceBindingTerm
      let initialTerms ← initial.getElems.mapM traceBindingTerm
      `(#eval Loom.Hw.Dsl.traceCycle $design [$inputTerms,*] [$initialTerms,*])

/-! ## Certified teaching run

This compact command uses `FastEval.VerifiedSimulator`, not a second
hand-maintained cycle function.  The generated proof obligation is checked when
the command elaborates; the displayed coordinates are the Design's declarations.
-/

def runHardware {design : Loom.Hw.Design}
    (simulator : Loom.Hw.FastEval.VerifiedSimulator design) (cycles : Nat) : IO Unit := do
  let final := simulator.run cycles simulator.reset
  IO.println s!"after {cycles} cycles:"
  for (name, value) in design.fastRegs final do
    IO.println s!"  {name} = {value}"

syntax (name := runHardwareCmd) "#run_hardware" term:max "for" num ident : command

macro_rules
  | `(#run_hardware $design:term for $count:num $unit:ident) => do
      unless unit.getId == `cycles do
        Macro.throwErrorAt unit "expected `cycles`"
      `(#eval Loom.Hw.Dsl.runHardware
        (design := $design)
        ({ wf := by native_decide } : Loom.Hw.FastEval.VerifiedSimulator $design)
        $count)

end Loom.Hw.Dsl
