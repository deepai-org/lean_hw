-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
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

open Lean Macro Elab Term Meta

declare_syntax_cat hwexpr
declare_syntax_cat hwstmt
declare_syntax_cat hwcasearm

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
syntax:46 hwexpr:46 " | " hwexpr:47 : hwexpr
syntax:40 hwexpr:41 " == " hwexpr:41 : hwexpr
syntax:40 hwexpr:41 " <u " hwexpr:41 : hwexpr
syntax:40 hwexpr:41 " <s " hwexpr:41 : hwexpr
syntax:20 "if " hwexpr " then " hwexpr " else " hwexpr : hwexpr

syntax:max (name := hwLit) "hw_lit% " num : term
syntax:max (name := hwAtom) "hw_atom% " term:max : term
syntax:max (name := hwIndexLit) "hw_index_lit% " term:max num : term
syntax:max (name := hwMemRead) "hw_mem_read% " term:max term:max : term

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
  | `([hwexpr| $a:hwexpr << $b:hwexpr]) => do validateInfixBoundary .shift a b; `(Loom.Hw.Expr.shl [hwexpr| $a] [hwexpr| $b])
  | `([hwexpr| $a:hwexpr >> $b:hwexpr]) => do validateInfixBoundary .shift a b; `(Loom.Hw.Expr.shr [hwexpr| $a] [hwexpr| $b])
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
syntax "reg" ident ":" num : hwitem
syntax "reg" ident ":" num ":=" num : hwitem
syntax "output" "reg" ident ":" num : hwitem
syntax "output" "reg" ident ":" num ":=" num : hwitem
syntax "input" ident ":" num : hwitem
syntax "output" "wire" ident ":" num ":=" hwexpr : hwitem
syntax "const" ident ":" num ":=" num : hwitem
syntax "states" ident ":" "{" ident,* "}" : hwitem
syntax "states" ident ":" "{" ident,* "}" ":=" ident : hwitem
syntax "states" ident ":" num "{" ident,* "}" : hwitem
syntax "states" ident ":" num "{" ident,* "}" ":=" ident : hwitem
syntax "output" "states" ident ":" "{" ident,* "}" : hwitem
syntax "output" "states" ident ":" "{" ident,* "}" ":=" ident : hwitem
syntax "output" "states" ident ":" num "{" ident,* "}" : hwitem
syntax "output" "states" ident ":" num "{" ident,* "}" ":=" ident : hwitem
syntax "rule" ident ":=" hwstmt : hwitem
syntax (name := hardwareCmd) "hardware" ident "where" hwitem* : command

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

private structure StateDomain where
  register : TSyntax `ident
  members : Array (TSyntax `ident)

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
    | `(hwitem| reg $name:ident : $width:num) =>
        registers := registers.push ⟨name, width, false, 0⟩
    | `(hwitem| reg $name:ident : $width:num := $value:num) =>
        registers := registers.push ⟨name, width, false, ← checkedValue width value⟩
    | `(hwitem| output reg $name:ident : $width:num) =>
        registers := registers.push ⟨name, width, true, 0⟩
    | `(hwitem| output reg $name:ident : $width:num := $value:num) =>
        registers := registers.push ⟨name, width, true, ← checkedValue width value⟩
    | `(hwitem| input $name:ident : $width:num) =>
        inputs := inputs.push ⟨name, width⟩
    | `(hwitem| output wire $name:ident : $width:num := $value:hwexpr) =>
        wires := wires.push ⟨name, width, value⟩
    | `(hwitem| const $name:ident : $width:num := $value:num) =>
        constants := constants.push ⟨name, width, value⟩
    | `(hwitem| states $name:ident : {$members:ident,*}) =>
        let (register, stateConstants) ← stateItems name none members.getElems none false
        registers := registers.push register
        constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| states $name:ident : {$members:ident,*} := $reset:ident) =>
        let (register, stateConstants) ← stateItems name none members.getElems (some reset) false
        registers := registers.push register
        constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| states $name:ident : $width:num {$members:ident,*}) =>
        let (register, stateConstants) ← stateItems name (some width) members.getElems none false
        registers := registers.push register
        constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| states $name:ident : $width:num {$members:ident,*} := $reset:ident) =>
        let (register, stateConstants) ← stateItems name (some width) members.getElems (some reset) false
        registers := registers.push register
        constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| output states $name:ident : {$members:ident,*}) =>
        let (register, stateConstants) ← stateItems name none members.getElems none true
        registers := registers.push register
        constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| output states $name:ident : {$members:ident,*} := $reset:ident) =>
        let (register, stateConstants) ← stateItems name none members.getElems (some reset) true
        registers := registers.push register
        constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| output states $name:ident : $width:num {$members:ident,*}) =>
        let (register, stateConstants) ← stateItems name (some width) members.getElems none true
        registers := registers.push register
        constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| output states $name:ident : $width:num {$members:ident,*} := $reset:ident) =>
        let (register, stateConstants) ← stateItems name (some width) members.getElems (some reset) true
        registers := registers.push register
        constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems⟩
    | `(hwitem| rule $name:ident := $body:hwstmt) =>
        rules := rules.push ⟨name, body⟩
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

macro_rules
  | `(hardware $moduleName:ident where $items:hwitem*) => do
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
        def $designName : Loom.Hw.Design :=
          Loom.Hw.Design.ofDecls $emittedName $declarationsName $ruleList)
      commands := commands.push designCommand
      pure (Lean.mkNullNode commands)

end Loom.Hw.Dsl
