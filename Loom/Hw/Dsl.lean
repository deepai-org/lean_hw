-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Hw.FastEval
import Loom.Hw.Multiclock
import Loom.Hw.Packed
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

/-- Technology-neutral declaration policy for a Loom memory. This is only a
readable argument to `Declarations.addMem`; it does not select a vendor macro. -/
structure MemoryPolicy where
  syncRead : Bool := false
  ackInit : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace Memory

/-- Ordinary asynchronous-read Loom memory policy. -/
def asynchronousRead : MemoryPolicy := {}

/-- Declare the memory as a synchronous-read/macro candidate. The target, if
any, remains an explicit emission/evidence choice. -/
def synchronousRead : MemoryPolicy := { syncRead := true }

end Memory

/-! Discoverable system vocabulary. These are aliases over the existing
multiclock values, not syntax-owned policies or implementations. -/

namespace Clock

def asynchronous : ClockRel := ClockRel.asynchronous
def interleaved : ClockRel := ClockRel.interleaved
def aligned (left right : ClockHandle) : ClockRel :=
  ClockRel.aligned left.name right.name

private def intersect (left right : ClockRel) : ClockRel where
  accepts := fun events => left.accepts events && right.accepts events
  prefixClosed := by
    intro first rest accepted
    have parts := Bool.and_eq_true_iff.mp accepted
    exact Bool.and_eq_true_iff.mpr
      ⟨left.prefixClosed first rest parts.1,
        right.prefixClosed first rest parts.2⟩

private def alignGroup (base : ClockRel) : List ClockHandle → ClockRel
  | [] => base
  | first :: rest => rest.foldl
      (fun relation clock => intersect relation (aligned first clock)) base

/-- Add all-tick-together constraints within each group while retaining the
base relation between groups and every unlisted clock. This is proof-schedule
composition only; it does not select or authorize a physical realization. -/
def alignGroups (base : ClockRel) (groups : List (List ClockHandle)) : ClockRel :=
  groups.foldl alignGroup base

end Clock

namespace Reset

def together : SystemResetPolicy := .coordinated
def independentFlush : SystemResetPolicy := .independentFlush

end Reset

namespace Chan

/-- Accept a push on a full queue when the same event also removes its head. -/
def exchange : FullCoTickPolicy := .exchange

/-- Refuse a push observed against a pre-event full queue, even on a co-tick. -/
def refusePush : FullCoTickPolicy := .refusePush

end Chan

namespace Cdc

def synchronousFifo : RealizationKind := .synchronous
def grayFifo : RealizationKind := .portableAsync
def recoverableGrayFifo : RealizationKind := .recoveryPortableAsync

end Cdc

end Loom.Hw

namespace Loom.Hw.Dsl

open Lean Macro Elab Term Meta Command Tactic

/-- Explicit opt-in for a shared compile-time hardware constant. Ordinary
`Nat` definitions are never lifted merely because they happen to be in scope. -/
initialize hwConstAttr : TagAttribute ←
  registerTagAttribute `hw_const
    "allow this Nat declaration to be range-checked and lifted in hardware expressions"
    (fun declaration => do
      let info ← getConstInfo declaration
      unless info.type.isConstOf ``Nat do
        throwError "@[hw_const] requires a declaration of type Nat")

/-- Ordered elaboration-time action generation. The result has exactly the
same left-to-right `Act.seq` shape as a handwritten brace block. -/
def actFor {α : Type} (values : List α) (body : α → Loom.Hw.Act) : Loom.Hw.Act :=
  match values with
  | [] => .skip
  | [value] => body value
  | value :: rest => .seq (body value) (actFor rest body)

/-! Small codec helpers used by generated packed records. Keeping the split
opaque at call sites prevents elaboration from expanding a middle-field read
into large bit arithmetic, while these three lemmas close the inverse laws by
linear structural rewriting rather than bit-blasting. -/

def packedHigh {highWidth lowWidth : Nat}
    (bits : BitVec (highWidth + lowWidth)) : BitVec highWidth :=
  bits.extractLsb' lowWidth highWidth

def packedLow {highWidth lowWidth : Nat}
    (bits : BitVec (highWidth + lowWidth)) : BitVec lowWidth :=
  bits.extractLsb' 0 lowWidth

@[simp] theorem packedHigh_append {highWidth lowWidth : Nat}
    (high : BitVec highWidth) (low : BitVec lowWidth) :
    packedHigh (high ++ low) = high :=
  BitVec.extractLsb'_append_eq_left

@[simp] theorem packedLow_append {highWidth lowWidth : Nat}
    (high : BitVec highWidth) (low : BitVec lowWidth) :
    packedLow (high ++ low) = low :=
  BitVec.extractLsb'_append_eq_right

theorem packedHigh_append_low {highWidth lowWidth : Nat}
    (bits : BitVec (highWidth + lowWidth)) :
    packedHigh bits ++ packedLow bits = bits := by
  simp [packedHigh, packedLow]

inductive DeclarationKind where
  | register | registerFamily | stateRegister | memory | input | wire | constant | stateValue
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
declare_syntax_cat hwrecordfield

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
syntax ident ":=" hwexpr : hwrecordfield
syntax:max ident "{" hwrecordfield,* "}" : hwexpr
syntax:max "{" hwexpr "with" hwrecordfield,* "}" : hwexpr
syntax:max ident "(" hwexpr ")" : hwexpr
syntax:80 hwexpr:80 "[" num "]" : hwexpr
syntax:80 hwexpr:80 "[" num ":" num "]" : hwexpr
syntax:80 ident "[" num ":" num "]" : hwexpr
syntax:80 ident "[" hwexpr "]" : hwexpr
syntax:80 hwexpr:80 "." ident : hwexpr
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
syntax:max (name := hwDottedAtom) "hw_dotted_atom% " ident : term
syntax:max (name := hwIndexLit) "hw_index_lit% " term:max num : term
syntax:max (name := hwMemRead) "hw_mem_read% " term:max term:max : term
syntax:max (name := hwMemWrite) "hw_mem_write% " term:max num term:max term:max : term
syntax:max (name := hwShift) "hw_shift% " str term:max term:max : term
syntax:max (name := hwPackedField) "hw_packed_field% " term:max ident : term
syntax:max (name := hwPackedWrite) "hw_packed_write% " term:max ident term:max : term
syntax:max (name := hwPackedConstruct) "hw_packed_construct% " ident
  "{" hwrecordfield,* "}" : term
syntax:max (name := hwPackedUpdate) "hw_packed_update% " term:max
  "{" hwrecordfield,* "}" : term
syntax:max (name := hwPackedFromBits) "hw_packed_from_bits% " ident term:max : term
syntax:max (name := hwEq) "hw_eq% " term:max term:max : term
syntax:max (name := hwWrite) "hw_write% " term:max term:max : term
syntax:max (name := hwArrayWrite) "hw_array_write% " term:max term:max term:max : term
syntax:max (name := hwChannelObserve) "hw_channel_observe% " term:max ident : term
syntax:max (name := hwSend) "hw_send% " term:max term:max : term
syntax:max (name := hwConsume) "hw_consume% " term:max : term
syntax:max (name := hwExactConst) "hw_exact_const% " ident : term
syntax "[hwexpr| " hwexpr "]" : term

@[term_elab hwExactConst] private def elabHwExactConst : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_exact_const% $name:ident) =>
      ensureHasType expectedType? (.const name.getId [])
  | _ => throwUnsupportedSyntax

private def checkedHardwareLiteral (source : Syntax) (value : Nat)
    (expectedType? : Option Lean.Expr) : TermElabM Lean.Expr := do
  let some expected := expectedType?
    | throwErrorAt source "hardware literal requires an expected `Expr width` type"
  let expected ← instantiateMVars expected
  let expectedWhnf ← Meta.whnf expected
  unless expectedWhnf.isAppOfArity ``Loom.Hw.Expr 1 do
    throwErrorAt source "hardware literal requires an expected `Expr width` type"
  let widthExpr ← Meta.whnf expectedWhnf.getAppArgs[0]!
  let some width ← getNatValue? widthExpr
    | throwErrorAt source
        "hardware literal width must reduce before range checking; use an explicit typed `$(...)` splice"
  let limit : Nat := 2 ^ width
  let maxValue : Nat := limit - 1
  if width == 0 || value ≥ limit then
    throwErrorAt source
      s!"literal {value} does not fit in {width} bits; expected 0 through {maxValue}"
  let literal ← `(Loom.Hw.Expr.lit (BitVec.ofNat $(quote width) $(quote value)))
  elabTermEnsuringType literal (some expected)

private def coerceHardwareAtom (valueSyntax : Syntax) (expectedType? : Option Lean.Expr) :
    TermElabM Lean.Expr := do
  let value ← elabTerm valueSyntax none
  let valueType ← Meta.whnf (← Meta.inferType value)
  let result ←
    if valueType.isAppOfArity ``Loom.Hw.Expr 1 then pure value
    else if valueType.isAppOfArity ``Loom.Hw.Reg 1 then Meta.mkAppM ``Loom.Hw.Reg.rd #[value]
    else if valueType.isAppOfArity ``Loom.Hw.Input 1 then Meta.mkAppM ``Loom.Hw.Input.rd #[value]
    else if valueType.isAppOfArity ``Loom.Hw.PackedExpr 2 then pure value
    else if valueType.isAppOfArity ``Loom.Hw.PackedReg 2 then Meta.mkAppM ``Loom.Hw.PackedReg.rd #[value]
    else if valueType.isAppOfArity ``Loom.Hw.PackedInput 2 then Meta.mkAppM ``Loom.Hw.PackedInput.rd #[value]
    else if valueType.isConstOf ``Nat then
      let some declaration := value.getAppFn.constName?
        | throwErrorAt valueSyntax
            "a lifted hardware constant must be a named declaration marked @[hw_const]"
      unless hwConstAttr.hasTag (← getEnv) declaration do
        throwErrorAt valueSyntax
          "Nat values are not implicitly hardware expressions; mark a shared constant @[hw_const] or use a design-local `const`"
      let some literalValue ← getNatValue? (← Meta.whnf value)
        | throwErrorAt valueSyntax
            "@[hw_const] value must reduce to a numeral for range checking"
      checkedHardwareLiteral valueSyntax literalValue expectedType?
    else throwErrorAt valueSyntax
      "hardware identifier must name a typed register, input, expression, or packed value"
  ensureHasType expectedType? result

/-- Elaborate a bare hardware name from its own declared type. This avoids the
result-width ambiguity of `a == b`: a `Reg w` becomes its read expression,
while an existing `Expr w` remains unchanged. -/
@[term_elab hwAtom] def elabHwAtom : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_atom% $valueSyntax:term) => coerceHardwareAtom valueSyntax expectedType?
  | _ => throwUnsupportedSyntax

/-- A dotted token is first treated as an ordinary qualified Lean name. Only
when that fails is its final component interpreted as a packed field. -/
@[term_elab hwDottedAtom] def elabHwDottedAtom : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_dotted_atom% $whole:ident) =>
      try
        let _ ← resolveGlobalConstNoOverload whole
        coerceHardwareAtom whole expectedType?
      catch _ =>
        let name := whole.getId
        if name.isAtomic then throwErrorAt whole "expected a qualified name or packed field"
        let base := mkIdentFrom whole name.getPrefix
        let field := mkIdentFrom whole (Name.mkSimple name.getString!)
        let projection ← `(hw_packed_field% (hw_atom% $base) $field)
        elabTerm projection expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab hwPackedField] def elabHwPackedField : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_packed_field% $valueSyntax:term $fieldName:ident) => do
      let value ← elabTerm valueSyntax none
      let valueType ← Meta.whnf (← Meta.inferType value)
      unless valueType.isAppOfArity ``Loom.Hw.PackedExpr 2 do
        throwErrorAt valueSyntax "field projection requires a packed hardware value"
      if fieldName.getId.eraseMacroScopes == `bits then
        let result ← Meta.mkAppM ``Loom.Hw.PackedExpr.bits #[value]
        return ← ensureHasType expectedType? result
      let semanticType := valueType.getAppArgs[0]!
      let some typeName := semanticType.constName? | throwErrorAt valueSyntax
        "packed field projection requires a named packed struct type"
      let descriptorName := typeName ++
        Name.mkSimple (fieldName.getId.toString ++ "Field")
      unless (← getEnv).contains descriptorName do
        throwErrorAt fieldName
          s!"'{fieldName.getId}' is not a generated field of '{typeName}'"
      let descriptor := .const descriptorName []
      let result ← Meta.mkAppM ``Loom.Hw.PackedField.read #[descriptor, value]
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

private def recordFieldParts (field : TSyntax `hwrecordfield) :
    TermElabM (TSyntax `ident × TSyntax `hwexpr) :=
  match field with
  | `(hwrecordfield| $name:ident := $value:hwexpr) => pure (name, value)
  | _ => throwErrorAt field "expected `field := expression`"

private def packedDescriptor (typeName : Name) (field : TSyntax `ident) :
    TermElabM (Lean.Expr × Lean.Expr) := do
  let descriptorName := typeName ++
    Name.mkSimple (field.getId.eraseMacroScopes.toString ++ "Field")
  unless (← getEnv).contains descriptorName do
    throwErrorAt field s!"'{field.getId.eraseMacroScopes}' is not a packed field of '{typeName}'"
  let descriptor := Lean.Expr.const descriptorName []
  let descriptorType ← Meta.whnf (← Meta.inferType descriptor)
  unless descriptorType.isAppOfArity ``Loom.Hw.PackedField 3 do
    throwErrorAt field "generated packed field has an invalid descriptor type"
  pure (descriptor, descriptorType.getAppArgs[2]!)

private def elaboratePackedFields (typeName : Name)
    (fields : Array (TSyntax `hwrecordfield)) : TermElabM (Array Lean.Expr) := do
  let some structureInfo := Lean.getStructureInfo? (← getEnv) typeName
    | throwError "'{typeName}' is not a packed struct"
  let parts ← fields.mapM recordFieldParts
  for index in [:parts.size] do
    for later in [index + 1:parts.size] do
      if parts[index]!.1.getId.eraseMacroScopes == parts[later]!.1.getId.eraseMacroScopes then
        throwErrorAt parts[later]!.1
          s!"duplicate packed field '{parts[later]!.1.getId.eraseMacroScopes}'"
  for supplied in parts do
    unless structureInfo.fieldNames.any (fun declared =>
        declared.getString! == supplied.1.getId.eraseMacroScopes.getString!) do
      throwErrorAt supplied.1
        s!"unknown packed field '{supplied.1.getId.eraseMacroScopes}' for '{typeName}'"
  let mut values := #[]
  for declared in structureInfo.fieldNames do
    let shortName := declared.getString!
    let some supplied := parts.find? (fun part =>
        part.1.getId.eraseMacroScopes.getString! == shortName)
      | throwError s!"missing packed field '{shortName}' for '{typeName}'"
    let (_, width) ← packedDescriptor typeName supplied.1
    let expected := Lean.Expr.app (.const ``Loom.Hw.Expr []) width
    let valueSyntax := supplied.2
    let quoted ← `(term| [hwexpr| $valueSyntax])
    values := values.push (← elabTerm quoted (some expected))
  pure values

@[term_elab hwPackedConstruct] def elabHwPackedConstruct : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_packed_construct% $typeSyntax:ident {$fields:hwrecordfield,*}) => do
      let typeName ← resolveGlobalConstNoOverload typeSyntax
      let values ← elaboratePackedFields typeName fields.getElems
      let some first := values[0]?
        | throwErrorAt typeSyntax "a packed struct requires at least one field"
      let mut bits := first
      for value in values.toList.drop 1 do
        bits ← Meta.mkAppM ``Loom.Hw.Expr.concat #[bits, value]
      let result ← Meta.mkAppOptM ``Loom.Hw.PackedExpr.fromBits
        #[some (.const typeName []), none, some bits]
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwPackedUpdate] def elabHwPackedUpdate : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_packed_update% $baseSyntax:term {$fields:hwrecordfield,*}) => do
      let base ← elabTerm baseSyntax none
      let baseType ← Meta.whnf (← Meta.inferType base)
      unless baseType.isAppOfArity ``Loom.Hw.PackedExpr 2 do
        throwErrorAt baseSyntax "packed update requires a packed hardware value"
      let semanticType := baseType.getAppArgs[0]!
      let some typeName := semanticType.constName?
        | throwErrorAt baseSyntax "packed update requires a named packed struct type"
      let parts ← fields.getElems.mapM recordFieldParts
      for index in [:parts.size] do
        for later in [index + 1:parts.size] do
          if parts[index]!.1.getId.eraseMacroScopes == parts[later]!.1.getId.eraseMacroScopes then
            throwErrorAt parts[later]!.1
              s!"duplicate packed field '{parts[later]!.1.getId.eraseMacroScopes}'"
      let mut result := base
      for part in parts do
        let (descriptor, width) ← packedDescriptor typeName part.1
        let expected := Lean.Expr.app (.const ``Loom.Hw.Expr []) width
        let valueSyntax := part.2
        let quoted ← `(term| [hwexpr| $valueSyntax])
        let replacement ← elabTerm quoted (some expected)
        result ← Meta.mkAppM ``Loom.Hw.PackedExpr.setField #[result, descriptor, replacement]
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwEq] def elabHwEq : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_eq% $leftSyntax:term $rightSyntax:term) => do
      let left ← elabTerm leftSyntax none
      let leftType ← Meta.whnf (← Meta.inferType left)
      let right ← elabTerm rightSyntax (some leftType)
      let result ←
        if leftType.isAppOfArity ``Loom.Hw.Expr 1 then
          Meta.mkAppM ``Loom.Hw.Expr.eq #[left, right]
        else if leftType.isAppOfArity ``Loom.Hw.PackedExpr 2 then
          Meta.mkAppM ``Loom.Hw.PackedExpr.eq #[left, right]
        else
          throwErrorAt leftSyntax "hardware equality requires scalar or same-type packed expressions"
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwPackedFromBits] def elabHwPackedFromBits : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_packed_from_bits% $typeSyntax:ident $bitsSyntax:term) => do
      let typeName ← resolveGlobalConstNoOverload typeSyntax
      let width ← Meta.whnf (← Meta.mkAppOptM ``Loom.Hw.HwPacked.width
        #[some (.const typeName []), none])
      let bits ← elabTerm bitsSyntax
        (some (Lean.Expr.app (.const ``Loom.Hw.Expr []) width))
      let result ← Meta.mkAppOptM ``Loom.Hw.PackedExpr.fromBits
        #[some (.const typeName []), none, some bits]
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwPackedWrite] def elabHwPackedWrite : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_packed_write% $registerSyntax:term $fieldName:ident $valueSyntax:term) => do
      let register ← elabTerm registerSyntax none
      let registerType ← Meta.whnf (← Meta.inferType register)
      unless registerType.isAppOfArity ``Loom.Hw.PackedReg 2 do
        throwErrorAt registerSyntax "packed field assignment requires a packed register"
      let semanticType := registerType.getAppArgs[0]!
      let some typeName := semanticType.constName? | throwErrorAt registerSyntax
        "packed field assignment requires a named packed struct type"
      let descriptorName := typeName ++
        Name.mkSimple (fieldName.getId.toString ++ "Field")
      unless (← getEnv).contains descriptorName do
        throwErrorAt fieldName
          s!"'{fieldName.getId}' is not a generated field of '{typeName}'"
      let descriptor := Lean.Expr.const descriptorName []
      let descriptorType ← Meta.whnf (← Meta.inferType descriptor)
      unless descriptorType.isAppOfArity ``Loom.Hw.PackedField 3 do
        throwErrorAt fieldName "generated packed field has an invalid descriptor type"
      let fieldWidth := descriptorType.getAppArgs[2]!
      let valueType := Lean.Expr.app (.const ``Loom.Hw.Expr []) fieldWidth
      let value ← elabTerm valueSyntax (some valueType)
      let result ← Meta.mkAppM ``Loom.Hw.PackedReg.setField #[register, descriptor, value]
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwWrite] def elabHwWrite : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_write% $targetSyntax:term $valueSyntax:term) => do
      let target ← elabTerm targetSyntax none
      let targetType ← Meta.whnf (← Meta.inferType target)
      let result ←
        if targetType.isAppOfArity ``Loom.Hw.Reg 1 then
          let width := targetType.getAppArgs[0]!
          let valueType := Lean.Expr.app (.const ``Loom.Hw.Expr []) width
          let value ← elabTerm valueSyntax (some valueType)
          Meta.mkAppM ``Loom.Hw.Reg.set #[target, value]
        else if targetType.isAppOfArity ``Loom.Hw.PackedReg 2 then
          let read ← Meta.mkAppM ``Loom.Hw.PackedReg.rd #[target]
          let packedType ← Meta.inferType read
          let value ← elabTerm valueSyntax (some packedType)
          Meta.mkAppM ``Loom.Hw.PackedReg.set #[target, value]
        else
          throwErrorAt targetSyntax "assignment target must be a scalar or packed register"
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwArrayWrite] def elabHwArrayWrite : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_array_write% $familySyntax:term $indexSyntax:term $valueSyntax:term) => do
      let family ← elabTerm familySyntax none
      let familyType ← Meta.whnf (← Meta.inferType family)
      unless familyType.isAppOfArity ``Loom.Hw.RegArray 2 do
        throwErrorAt familySyntax "indexed assignment requires a typed register family"
      let elementWidth := familyType.getAppArgs[0]!
      let countExpr ← Meta.whnf familyType.getAppArgs[1]!
      let valueType := Lean.Expr.app (.const ``Loom.Hw.Expr []) elementWidth
      let value ← elabTerm valueSyntax (some valueType)
      let index ← elabTerm indexSyntax none
      let indexType ← Meta.whnf (← Meta.inferType index)
      let result ← if indexType.isConstOf ``Nat then
        let some indexValue ← getNatValue? (← Meta.whnf index)
          | throwErrorAt indexSyntax "static register-family index must reduce to a numeral"
        let some count ← getNatValue? countExpr
          | throwErrorAt familySyntax "register-family size must reduce to a numeral"
        if indexValue ≥ count then
          throwErrorAt indexSyntax
            s!"register-family index {indexValue} is outside 0 through {count - 1}"
        let direct ← `(Loom.Hw.RegArray.set $familySyntax
          ⟨$(quote indexValue), by decide⟩ $valueSyntax)
        elabTerm direct expectedType?
      else
        unless indexType.isAppOfArity ``Loom.Hw.Expr 1 do
          throwErrorAt indexSyntax "dynamic register-family index must be a hardware expression"
        Meta.mkAppM ``Loom.Hw.RegArray.dynSet #[family, index, value]
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwChannelObserve] def elabHwChannelObserve : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_channel_observe% $endpointSyntax:term $operation:ident) => do
      let endpoint ← elabTerm endpointSyntax none
      let endpointType ← Meta.whnf (← Meta.inferType endpoint)
      -- Quotation gives this identifier a macro scope; erase it before
      -- inspecting the atomic operation name.
      let op := operation.getId.eraseMacroScopes.getString!
      let result ←
        if endpointType.isAppOfArity ``Loom.Hw.Chan.SourceEndpoint 1 then
          if op == "canSend" then Meta.mkAppM ``Loom.Hw.Chan.SourceEndpoint.canSend #[endpoint]
          else throwErrorAt operation "a channel source exposes only `canSend`"
        else if endpointType.isAppOfArity ``Loom.Hw.Chan.SinkEndpoint 1 then
          if op == "hasData" then Meta.mkAppM ``Loom.Hw.Chan.SinkEndpoint.hasData #[endpoint]
          else if op == "data" then Meta.mkAppM ``Loom.Hw.Chan.SinkEndpoint.data #[endpoint]
          else throwErrorAt operation "a channel sink exposes `hasData` and `data`"
        else if endpointType.isAppOfArity ``Loom.Hw.PackedChan.SourceEndpoint 2 then
          if op == "canSend" then Meta.mkAppM ``Loom.Hw.PackedChan.SourceEndpoint.canSend #[endpoint]
          else throwErrorAt operation "a packed channel source exposes only `canSend`"
        else if endpointType.isAppOfArity ``Loom.Hw.PackedChan.SinkEndpoint 2 then
          if op == "hasData" then Meta.mkAppM ``Loom.Hw.PackedChan.SinkEndpoint.hasData #[endpoint]
          else if op == "data" then Meta.mkAppM ``Loom.Hw.PackedChan.SinkEndpoint.data #[endpoint]
          else throwErrorAt operation "a packed channel sink exposes `hasData` and `data`"
        else throwErrorAt endpointSyntax "channel observation requires a directional endpoint"
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwSend] def elabHwSend : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_send% $endpointSyntax:term $payloadSyntax:term) => do
      let endpoint ← elabTerm endpointSyntax none
      let endpointType ← Meta.whnf (← Meta.inferType endpoint)
      let result ←
        if endpointType.isAppOfArity ``Loom.Hw.Chan.SourceEndpoint 1 then
          let width := endpointType.getAppArgs[0]!
          let payload ← elabTerm payloadSyntax
            (some (Lean.Expr.app (.const ``Loom.Hw.Expr []) width))
          Meta.mkAppM ``Loom.Hw.Chan.SourceEndpoint.send #[endpoint, payload]
        else if endpointType.isAppOfArity ``Loom.Hw.PackedChan.SourceEndpoint 2 then
          let channel ← Meta.mkAppM ``Loom.Hw.PackedChan.SourceEndpoint.channel #[endpoint]
          let sample ← Meta.mkAppM ``Loom.Hw.PackedChan.deq #[channel]
          let payload ← elabTerm payloadSyntax (some (← Meta.inferType sample))
          Meta.mkAppM ``Loom.Hw.PackedChan.SourceEndpoint.send #[endpoint, payload]
        else throwErrorAt endpointSyntax "send requires a directional channel source"
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwConsume] def elabHwConsume : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_consume% $endpointSyntax:term) => do
      let endpoint ← elabTerm endpointSyntax none
      let endpointType ← Meta.whnf (← Meta.inferType endpoint)
      let result ←
        if endpointType.isAppOfArity ``Loom.Hw.Chan.SinkEndpoint 1 then
          Meta.mkAppM ``Loom.Hw.Chan.SinkEndpoint.consume #[endpoint]
        else if endpointType.isAppOfArity ``Loom.Hw.PackedChan.SinkEndpoint 2 then
          Meta.mkAppM ``Loom.Hw.PackedChan.SinkEndpoint.consume #[endpoint]
        else throwErrorAt endpointSyntax "consume requires a directional channel sink"
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
        else if containerType.isAppOfArity ``Loom.Hw.PackedMem 3 then
          let addressWidth := containerType.getAppArgs[0]!
          let addressType := .app (.const ``Loom.Hw.Expr []) addressWidth
          let addressSyntax ← `(hw_lit% $index)
          let address ← elabTerm addressSyntax (some addressType)
          Meta.mkAppM ``Loom.Hw.PackedMem.rd #[container, address]
        else if containerType.isAppOfArity ``Loom.Hw.RegArray 2 then
          let countExpr ← Meta.whnf containerType.getAppArgs[1]!
          let some count ← getNatValue? countExpr
            | throwErrorAt containerSyntax "register-family size must reduce to a numeral"
          if index.getNat ≥ count then
            throwErrorAt index s!"register-family index {index.getNat} is outside 0 through {count - 1}"
          let readSyntax ← `(Loom.Hw.RegArray.rd $containerSyntax
            ⟨$(quote index.getNat), by decide⟩)
          elabTerm readSyntax expectedType?
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
      let result ← if memoryType.isAppOfArity ``Loom.Hw.Mem 2 then
        let addressWidth := memoryType.getAppArgs[0]!
        let addressType := .app (.const ``Loom.Hw.Expr []) addressWidth
        let address ← elabTerm addressSyntax (some addressType)
        Meta.mkAppM ``Loom.Hw.Mem.rd #[memory, address]
      else if memoryType.isAppOfArity ``Loom.Hw.PackedMem 3 then
        let addressWidth := memoryType.getAppArgs[0]!
        let addressType := .app (.const ``Loom.Hw.Expr []) addressWidth
        let address ← elabTerm addressSyntax (some addressType)
        Meta.mkAppM ``Loom.Hw.PackedMem.rd #[memory, address]
      else if memoryType.isAppOfArity ``Loom.Hw.RegArray 2 then
        let address ← elabTerm addressSyntax none
        let addressType ← Meta.whnf (← Meta.inferType address)
        unless addressType.isAppOfArity ``Loom.Hw.Expr 1 do
          throwErrorAt addressSyntax "dynamic register-family index must be a hardware expression"
        let elementWidth := memoryType.getAppArgs[0]!
        let zeroBits ← Meta.mkAppM ``BitVec.ofNat #[elementWidth, .lit (.natVal 0)]
        let zero ← Meta.mkAppM ``Loom.Hw.Expr.lit #[zeroBits]
        Meta.mkAppM ``Loom.Hw.RegArray.dynRd #[memory, address, zero]
      else
        throwErrorAt memorySyntax
          "a dynamic hardware index is available only on a typed memory or register family; dynamic bit select is not supported"
      ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[term_elab hwMemWrite] def elabHwMemWrite : TermElab := fun stx expectedType? => do
  match stx with
  | `(hw_mem_write% $memorySyntax:term $port:num $addressSyntax:term $valueSyntax:term) =>
      let memory ← elabTerm memorySyntax none
      let memoryType ← Meta.whnf (← Meta.inferType memory)
      let result ← if memoryType.isAppOfArity ``Loom.Hw.Mem 2 then
        let addressWidth := memoryType.getAppArgs[0]!
        let dataWidth := memoryType.getAppArgs[1]!
        let address ← elabTerm addressSyntax
          (some (.app (.const ``Loom.Hw.Expr []) addressWidth))
        let value ← elabTerm valueSyntax
          (some (.app (.const ``Loom.Hw.Expr []) dataWidth))
        Meta.mkAppM ``Loom.Hw.Mem.write #[memory, .lit (.natVal port.getNat), address, value]
      else if memoryType.isAppOfArity ``Loom.Hw.PackedMem 3 then
        let addressWidth := memoryType.getAppArgs[0]!
        let address ← elabTerm addressSyntax
          (some (.app (.const ``Loom.Hw.Expr []) addressWidth))
        let sample ← Meta.mkAppM ``Loom.Hw.PackedMem.rd #[memory, address]
        let expectedValue ← Meta.inferType sample
        let value ← elabTerm valueSyntax (some expectedValue)
        Meta.mkAppM ``Loom.Hw.PackedMem.write
          #[memory, .lit (.natVal port.getNat), address, value]
      else
        throwErrorAt memorySyntax "memory write requires a typed scalar or packed memory"
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
  | `(hw_lit% $n:num) => checkedHardwareLiteral n n.getNat expectedType?
  | _ => throwUnsupportedSyntax

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
  | `([hwexpr| $typeName:ident {$fields:hwrecordfield,*}]) =>
      `(hw_packed_construct% $typeName {$fields,*})
  | `([hwexpr| {$base:hwexpr with $fields:hwrecordfield,*}]) =>
      `(hw_packed_update% [hwexpr| $base] {$fields,*})
  | `([hwexpr| $operation:ident ($bits:hwexpr)]) => do
      let name := operation.getId.eraseMacroScopes
      unless !name.isAtomic && name.getString! == "fromBits" do
        Macro.throwErrorAt operation "the only hardware expression application is `PackedType.fromBits(value)`"
      let typeName := mkIdentFrom operation name.getPrefix
      `(hw_packed_from_bits% $typeName [hwexpr| $bits])
  | `([hwexpr| $n:num]) => `(hw_lit% $n)
  | `([hwexpr| $id:ident]) => do
      let name := id.getId
      if name.isAtomic then
        `(hw_atom% $id)
      else
        let final := name.getString!
        if final == "canSend" || final == "hasData" || final == "data" then
          let base := mkIdentFrom id name.getPrefix
          let operation := mkIdentFrom id (Name.mkSimple final)
          `(hw_channel_observe% $base $operation)
        else `(hw_dotted_atom% $id)
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
  | `([hwexpr| $value:hwexpr.$field:ident]) =>
      `(hw_packed_field% [hwexpr| $value] $field)
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
  | `([hwexpr| $a:hwexpr == $b:hwexpr]) => do
      validateInfixBoundary .comparison a b
      `(hw_eq% [hwexpr| $a] [hwexpr| $b])
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
syntax ident "[" hwexpr "]" " <- " hwexpr : hwstmt
syntax "send" hwexpr "to" ident : hwstmt
syntax "send" hwexpr "to" ident "then" hwstmt : hwstmt
syntax "consume" ident : hwstmt
syntax "receive" ident "from" ident "then" hwstmt : hwstmt
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
    | `(hwstmt| $target:ident <- $value:hwexpr) => do
        let name := target.getId
        if name.isAtomic then
          `(hw_write% $target [hwexpr| $value])
        else
          let register := mkIdentFrom target name.getPrefix
          let field := mkIdentFrom target (Name.mkSimple name.getString!)
          `(hw_packed_write% $register $field [hwexpr| $value])
    | `(hwstmt| $memory:ident[port $portIndex:num, $address:hwexpr] <- $value:hwexpr) =>
        `(hw_mem_write% $memory $portIndex [hwexpr| $address] [hwexpr| $value])
    | `(hwstmt| $family:ident[$index:hwexpr] <- $value:hwexpr) =>
        match index with
        | `(hwexpr| $literal:num) =>
            `(hw_array_write% $family ($literal : Nat) [hwexpr| $value])
        | _ => `(hw_array_write% $family [hwexpr| $index] [hwexpr| $value])
    | `(hwstmt| send $payload:hwexpr to $endpoint:ident then $body:hwstmt) => do
        `(Loom.Hw.Act.ite (hw_channel_observe% $endpoint canSend)
          (Loom.Hw.Act.seq (hw_send% $endpoint [hwexpr| $payload]) $(← expandStmt body))
          Loom.Hw.Act.skip)
    | `(hwstmt| send $payload:hwexpr to $endpoint:ident) =>
        `(hw_send% $endpoint [hwexpr| $payload])
    | `(hwstmt| consume $endpoint:ident) => `(hw_consume% $endpoint)
    | `(hwstmt| receive $valueName:ident from $endpoint:ident then $body:hwstmt) => do
        let loweredBody ← expandStmt body
        `(Loom.Hw.Act.ite (hw_channel_observe% $endpoint hasData)
          (let $valueName := (hw_channel_observe% $endpoint data)
           Loom.Hw.Act.seq $loweredBody (hw_consume% $endpoint))
          Loom.Hw.Act.skip)
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

/-! ## Packed semantic records

The command below generates an ordinary Lean record and a structural
`HwPacked` codec. The inverse proof is assembled from `packedHigh_append_low`;
it is linear in the field count and never invokes a bit-vector SAT tactic. -/

declare_syntax_cat hwpackedfield
syntax ident ":" num : hwpackedfield
syntax (name := packedStructCmd) (docComment)? ident ident ident "where"
  withPosition(many1Indent(ppLine hwpackedfield)) : command

private def packedFieldParts (field : TSyntax `hwpackedfield) :
    MacroM (TSyntax `ident × TSyntax `num) :=
  match field with
  | `(hwpackedfield| $name:ident : $width:num) => pure (name, width)
  | _ => Macro.throwErrorAt field "expected `field : width`"

private def packedProjection (value field : TSyntax `ident) : MacroM (TSyntax `term) :=
  `($value.$field)

private partial def packedAppendTerm (value : TSyntax `ident) :
    List (TSyntax `ident) → MacroM (TSyntax `term)
  | [] => `(0#0)
  | [field] => packedProjection value field
  | field :: rest => do
      let head ← packedProjection value field
      `($head ++ $(← packedAppendTerm value rest))

private def packedUnpackTerms (bits : TSyntax `ident)
    (widths : List Nat) : MacroM (Array (TSyntax `term)) := do
  let mut result := #[]
  let mut tail : TSyntax `term := ⟨bits.raw⟩
  for index in [:widths.length] do
    let width := widths[index]!
    let restWidth := (widths.drop (index + 1)).foldl (· + ·) 0
    if index + 1 == widths.length then
      result := result.push tail
    else
      let high ← `(Loom.Hw.Dsl.packedHigh
        (highWidth := $(quote width)) (lowWidth := $(quote restWidth)) $tail)
      result := result.push high
      tail ← `(Loom.Hw.Dsl.packedLow
        (highWidth := $(quote width)) (lowWidth := $(quote restWidth)) $tail)
  pure result

private partial def packedRejoinProof (bits : TSyntax `term) :
    List Nat → MacroM (TSyntax `term)
  | [] => `(rfl)
  | [_] => `(rfl)
  | width :: rest => do
      let restWidth := rest.foldl (· + ·) 0
      let high ← `(Loom.Hw.Dsl.packedHigh
        (highWidth := $(quote width)) (lowWidth := $(quote restWidth)) $bits)
      let low ← `(Loom.Hw.Dsl.packedLow
        (highWidth := $(quote width)) (lowWidth := $(quote restWidth)) $bits)
      let tailProof ← packedRejoinProof low rest
      `(Eq.trans
        (congrArg (fun remainder => $high ++ remainder) $tailProof)
        (Loom.Hw.Dsl.packedHigh_append_low
          (highWidth := $(quote width)) (lowWidth := $(quote restWidth)) $bits))

private def expandPackedStruct
    (documentation : Option (TSyntax ``Lean.Parser.Command.docComment))
    (typeName : TSyntax `ident) (fields : Array (TSyntax `hwpackedfield)) : MacroM Syntax := do
  if fields.isEmpty then
    Macro.throwErrorAt typeName "a packed struct requires at least one field"
  let parts ← fields.mapM packedFieldParts
  let names : Array (TSyntax `ident) := parts.map fun part => part.1
  let widthSyntax : Array (TSyntax `num) := parts.map fun part => part.2
  let widths := widthSyntax.toList.map (·.getNat)
  for index in [:widths.length] do
    if widths[index]! == 0 then
      Macro.throwErrorAt widthSyntax[index]! "packed fields must have positive width"
    for later in [index + 1:widths.length] do
      if names[index]!.getId == names[later]!.getId then
        Macro.throwErrorAt names[later]!
          s!"duplicate packed field '{names[later]!.getId}'"
  let totalWidth := widths.foldl (· + ·) 0
  let packName := mkIdentFrom typeName (typeName.getId ++ `packBits)
  let unpackName := mkIdentFrom typeName (typeName.getId ++ `unpackBits)
  let layoutName := mkIdentFrom typeName (typeName.getId ++ `layout)
  let valueName := mkIdent `value
  let bitsName := mkIdent `bits
  let packTerm ← packedAppendTerm valueName names.toList
  let unpackTerms ← packedUnpackTerms bitsName widths
  let bitsTerm : TSyntax `term := ⟨bitsName.raw⟩
  let rejoinProof ← packedRejoinProof bitsTerm widths
  let structureCommand ← `(command|
    $[$documentation]?
    structure $typeName where
      $[$names:ident : BitVec $widthSyntax:num]*
      deriving DecidableEq, Repr)
  let packCommand ← `(command|
    def $packName ($valueName : $typeName) : BitVec $(quote totalWidth) :=
      $packTerm)
  let unpackCommand ← `(command|
    def $unpackName ($bitsName : BitVec $(quote totalWidth)) : $typeName :=
      { $[$names:ident := $unpackTerms:term],* })
  let instanceCommand ← `(command|
    instance : Loom.Hw.HwPacked $typeName where
      width := $(quote totalWidth)
      pack := $packName
      unpack := $unpackName
      unpack_pack := by
        intro value
        cases value
        unfold $packName $unpackName
        simp only [
          Loom.Hw.Dsl.packedHigh_append, Loom.Hw.Dsl.packedLow_append]
      pack_unpack := fun $bitsName => by
        unfold $packName $unpackName
        exact $rejoinProof)
  let mut spans : Array (TSyntax `term) := #[]
  let mut fieldCommands : Array Syntax := #[]
  for index in [:names.size] do
    let fieldName := names[index]!
    let width := widths[index]!
    let lo := (widths.drop (index + 1)).foldl (· + ·) 0
    let sourceName := Syntax.mkStrLit fieldName.getId.toString
    let span ← `(term| (⟨$sourceName, $(quote width), $(quote lo)⟩ :
      Loom.Hw.PackedSpan))
    spans := spans.push span
    let descriptorName := mkIdentFrom fieldName
      (typeName.getId ++ Name.mkSimple (fieldName.getId.toString ++ "Field"))
    let descriptorCommand ← `(command|
      def $descriptorName : Loom.Hw.PackedField $typeName $(quote width) :=
        { name := $sourceName
          lo := $(quote lo)
          inBounds := by decide })
    fieldCommands := fieldCommands.push descriptorCommand
  let layoutCommand ← `(command|
    def $layoutName : Loom.Hw.PackedLayout $typeName where
      fields := [$spans,*]
      namesUnique := by native_decide
      inBounds := by native_decide
      disjoint := by native_decide
      complete := by native_decide
      msbFirst := by native_decide)
  let layoutInstanceCommand ← `(command|
    instance : Loom.Hw.HwPackedLayout $typeName := ⟨$layoutName⟩)
  pure <| Lean.mkNullNode <|
    #[structureCommand, packCommand, unpackCommand, instanceCommand,
      layoutCommand, layoutInstanceCommand] ++ fieldCommands

@[command_elab packedStructCmd] def elabPackedStruct : CommandElab := fun stx => do
  match stx with
  | `($[$documentation:docComment]? $packedKeyword:ident $structKeyword:ident
        $typeName:ident where $fields:hwpackedfield*) => do
      unless packedKeyword.getId == `packed && structKeyword.getId == `struct do
        throwErrorAt packedKeyword "expected `packed struct`"
      let expanded ← liftMacroM <| expandPackedStruct documentation typeName fields
      elabCommand expanded
  | _ => throwUnsupportedSyntax

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
syntax ident ident ":" ident : hwitem
syntax ident ident ident ":" ident : hwitem
syntax ident ident ident ":" ident ":=" hwexpr : hwitem
syntax ident ident ":" "{" ident,* "}" : hwitem
syntax ident ident ":" "{" ident,* "}" ":=" ident : hwitem
syntax ident ident ":" num "{" ident,* "}" : hwitem
syntax ident ident ":" num "{" ident,* "}" ":=" ident : hwitem
syntax ident ident ident ":" "{" ident,* "}" : hwitem
syntax ident ident ident ":" "{" ident,* "}" ":=" ident : hwitem
syntax ident ident ident ":" num "{" ident,* "}" : hwitem
syntax ident ident ident ":" num "{" ident,* "}" ":=" ident : hwitem
syntax ident ident ":" num "[" num "]" : hwitem
syntax ident ident ":" num "[" num "]" "using" term:max : hwitem
syntax ident ident ":" ident "[" num "]" : hwitem
syntax ident ident ":" ident "[" num "]" "using" term:max : hwitem
syntax ident ident ident ":" num "[" num "]" : hwitem
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

private structure MemoryItem where
  name : TSyntax `ident
  dataWidth : TSyntax `num
  depth : TSyntax `num
  addrWidth : Nat
  policy : Option (TSyntax `term) := none

private structure PackedMemoryItem where
  name : TSyntax `ident
  typeName : TSyntax `ident
  depth : TSyntax `num
  addrWidth : Nat
  policy : Option (TSyntax `term) := none

private structure PackedRegItem where
  name : TSyntax `ident
  typeName : TSyntax `ident
  exported : Bool

private structure PackedInputItem where
  name : TSyntax `ident
  typeName : TSyntax `ident

private structure PackedWireItem where
  name : TSyntax `ident
  typeName : TSyntax `ident
  value : TSyntax `hwexpr

private structure RegArrayItem where
  name : TSyntax `ident
  width : TSyntax `num
  count : TSyntax `num
  exported : Bool

private structure RuleItem where
  name : TSyntax `ident
  body : TSyntax `hwstmt
  suppressedLint : Option Name := none
  suppressionReason : Option String := none

private structure StateDomain where
  register : TSyntax `ident
  members : Array (TSyntax `ident)
  width : Nat

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

private inductive ChannelGuardKind where
  | canSend
  | hasData
  deriving DecidableEq

private structure ChannelGuard where
  endpoint : Name
  kind : ChannelGuardKind
  deriving DecidableEq

private def channelObservation? (name : Name) : Option ChannelGuard :=
  let clean := name.eraseMacroScopes
  if clean.isAtomic then none
  else
    let operation := clean.getString!
    if operation == "canSend" then some ⟨clean.getPrefix, .canSend⟩
    else if operation == "hasData" then some ⟨clean.getPrefix, .hasData⟩
    else none

/-- Exact, deliberately syntactic dominance facts contributed by a condition.
Only conjunction preserves them; accepting disjunction or inferred shadow state
would make this informational lint pretend to be a theorem prover. -/
private partial def conjunctiveChannelGuards : TSyntax `hwexpr → Array ChannelGuard
  | `(hwexpr| ($condition:hwexpr)) => conjunctiveChannelGuards condition
  | `(hwexpr| $left:hwexpr & $right:hwexpr) =>
      conjunctiveChannelGuards left ++ conjunctiveChannelGuards right
  | `(hwexpr| $name:ident) => (channelObservation? name.getId).toArray
  | _ => #[]

private def guardPresent (guards : Array ChannelGuard) (endpoint : TSyntax `ident)
    (kind : ChannelGuardKind) : Bool :=
  guards.contains ⟨endpoint.getId.eraseMacroScopes, kind⟩

private partial def unguardedDataFindings (suppressed : Array Name)
    (guards : Array ChannelGuard) : TSyntax `hwexpr → List LintFinding
  | expression@`(hwexpr| $name:ident) =>
      if suppressed.contains `unguarded_channel then []
      else
        let clean := name.getId.eraseMacroScopes
        if !clean.isAtomic && clean.getString! == "data" then
          let endpoint := clean.getPrefix
          if guards.contains ⟨endpoint, .hasData⟩ then []
          else [⟨expression, s!"'{endpoint}.data' is read without a dominating '{endpoint}.hasData' guard; an empty channel has no valid payload"⟩]
        else []
  | `(hwexpr| ($value:hwexpr))
  | `(hwexpr| ~ $value:hwexpr)
  | `(hwexpr| zext $value:hwexpr to $_:num)
  | `(hwexpr| sext $value:hwexpr to $_:num)
  | `(hwexpr| $value:hwexpr[$_:num])
  | `(hwexpr| $value:hwexpr[$_:num:$__:num]) => unguardedDataFindings suppressed guards value
  | `(hwexpr| $_:ident[$address:hwexpr]) =>
      unguardedDataFindings suppressed guards address
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
      unguardedDataFindings suppressed guards left ++
        unguardedDataFindings suppressed guards right
  | `(hwexpr| if $condition:hwexpr then $yes:hwexpr else $no:hwexpr) =>
      unguardedDataFindings suppressed guards condition ++
        unguardedDataFindings suppressed (guards ++ conjunctiveChannelGuards condition) yes ++
        unguardedDataFindings suppressed guards no
  | _ => []

private def expressionFindings (registers : Array Name) (suppressed : Array Name)
    (guards : Array ChannelGuard) (written : List WrittenTarget)
    (expression : TSyntax `hwexpr) : List LintFinding :=
  readAfterWriteFindings registers suppressed written expression ++
    unguardedDataFindings suppressed guards expression

private partial def analyzeStatement (registers : Array Name) (suppressed : Array Name)
    (guards : Array ChannelGuard) (statement : TSyntax `hwstmt)
    (written : List WrittenTarget) :
    List WrittenTarget × List LintFinding :=
  match statement with
  | `(hwstmt| skip) => (written, [])
  | `(hwstmt| $target:ident <- $value:hwexpr) =>
      let readFindings := expressionFindings registers suppressed guards written value
      let prior := written.filter (fun earlier => earlier.name == target.getId)
      let suppressMultiple := suppressed.contains `multiple_write
      let multipleFinding :=
        if !prior.isEmpty && !suppressMultiple && prior.any (fun earlier => !earlier.overrideExpected) then
          [⟨target, s!"'{target.getId}' may be written more than once in one cycle; the later write wins"⟩]
        else []
      (written ++ [⟨target.getId, target, suppressMultiple⟩], readFindings ++ multipleFinding)
  | `(hwstmt| $_:ident[port $_:num, $address:hwexpr] <- $value:hwexpr) =>
      (written, expressionFindings registers suppressed guards written address ++
        expressionFindings registers suppressed guards written value)
  | `(hwstmt| $_:ident[$index:hwexpr] <- $value:hwexpr) =>
      (written, expressionFindings registers suppressed guards written index ++
        expressionFindings registers suppressed guards written value)
  | statement@`(hwstmt| send $payload:hwexpr to $endpoint:ident) =>
      let guardFinding :=
        if suppressed.contains `unguarded_channel || guardPresent guards endpoint .canSend then []
        else [⟨statement, s!"send to '{endpoint.getId.eraseMacroScopes}' is not dominated by its `canSend` guard; a full channel drops the payload"⟩]
      (written, expressionFindings registers suppressed guards written payload ++ guardFinding)
  | `(hwstmt| send $payload:hwexpr to $endpoint:ident then $body:hwstmt) =>
      let payloadFindings := expressionFindings registers suppressed guards written payload
      let guarded := guards.push ⟨endpoint.getId.eraseMacroScopes, .canSend⟩
      let (next, bodyFindings) := analyzeStatement registers suppressed guarded body written
      (next, payloadFindings ++ bodyFindings)
  | `(hwstmt| consume $_:ident) => (written, [])
  | `(hwstmt| receive $_:ident from $endpoint:ident then $body:hwstmt) =>
      analyzeStatement registers suppressed
        (guards.push ⟨endpoint.getId.eraseMacroScopes, .hasData⟩) body written
  | `(hwstmt| let $_:ident : $_:num := $value:hwexpr)
  | `(hwstmt| let $_:ident := $value:hwexpr) =>
      (written, expressionFindings registers suppressed guards written value)
  | `(hwstmt| suppress $lint:ident because $_:str in $body:hwstmt) =>
      analyzeStatement registers (suppressed.push lint.getId) guards body written
  | `(hwstmt| for $_:ident in $_:term generate $body:hwstmt) =>
      analyzeStatement registers suppressed guards body written
  | `(hwstmt| if $condition:hwexpr then $yes:hwstmt else $no:hwstmt) =>
      let conditionFindings := expressionFindings registers suppressed guards written condition
      let thenGuards := guards ++ conjunctiveChannelGuards condition
      let (yesWrites, yesFindings) := analyzeStatement registers suppressed thenGuards yes written
      let (noWrites, noFindings) := analyzeStatement registers suppressed guards no written
      (yesWrites ++ noWrites, conditionFindings ++ yesFindings ++ noFindings)
  | `(hwstmt| if $condition:hwexpr then $yes:hwstmt) =>
      let conditionFindings := expressionFindings registers suppressed guards written condition
      let thenGuards := guards ++ conjunctiveChannelGuards condition
      let (yesWrites, yesFindings) := analyzeStatement registers suppressed thenGuards yes written
      (yesWrites ++ written, conditionFindings ++ yesFindings)
  | `(hwstmt| case $scrutinee:hwexpr of $arms:hwcasearm*) =>
      let initialFindings := expressionFindings registers suppressed guards written scrutinee
      arms.foldl (fun (allWrites, allFindings) arm =>
        let body? := match arm with
          | `(hwcasearm| | default => $body:hwstmt)
          | `(hwcasearm| | $_:hwexpr => $body:hwstmt) => some body
          | _ => none
        match body? with
        | none => (allWrites, allFindings)
        | some body =>
            let (armWrites, armFindings) := analyzeStatement registers suppressed guards body written
            (allWrites ++ armWrites, allFindings ++ armFindings)) ([], initialFindings)
  | `(hwstmt| {$statements:hwstmt,*}) =>
      statements.getElems.foldl (fun (priorWrites, priorFindings) next =>
        let (nextWrites, nextFindings) := analyzeStatement registers suppressed guards next priorWrites
        (nextWrites, priorFindings ++ nextFindings)) (written, [])
  | _ => (written, [])

private def hardwareLintFindings (registers : Array ScalarRegItem)
    (rules : Array RuleItem) : List LintFinding :=
  let registerNames := registers.map (fun register => register.name.getId)
  let (_, findings) := rules.foldl (fun (written, priorFindings) ruleItem =>
    let suppressed := ruleItem.suppressedLint.toArray
    let (nextWritten, nextFindings) :=
      analyzeStatement registerNames suppressed #[] ruleItem.body written
    (nextWritten, priorFindings ++ nextFindings)) ([], [])
  findings

private partial def deadDefaultFindings (domains : Array StateDomain) :
    TSyntax `hwstmt → List LintFinding
  | `(hwstmt| case $scrutinee:hwexpr of $arms:hwcasearm*) =>
      let nested := arms.toList.flatMap fun (arm : TSyntax `hwcasearm) =>
        match arm with
        | `(hwcasearm| | default => $body:hwstmt)
        | `(hwcasearm| | $_:hwexpr => $body:hwstmt) => deadDefaultFindings domains body
        | _ => []
      let domain? := match scrutinee with
        | `(hwexpr| $name:ident) =>
            domains.find? (fun domain => domain.register.getId == name.getId)
        | _ => none
      match domain? with
      | none => nested
      | some domain =>
          let named := arms.foldl (fun names arm =>
            match arm with
            | `(hwcasearm| | $name:ident => $_:hwstmt) => names.push name.getId
            | _ => names) #[]
          let default? := arms.find? fun arm =>
            match arm with
            | `(hwcasearm| | default => $_:hwstmt) => true
            | _ => false
          let allEncodingsDeclared := domain.members.size == 2 ^ domain.width
          let allMembersCovered := domain.members.all fun member => named.contains member.getId
          match default? with
          | some defaultArm =>
              if allEncodingsDeclared && allMembersCovered then
                ⟨defaultArm,
                  "default arm is unreachable: the declared states cover every register encoding"⟩ :: nested
              else nested
          | none => nested
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt else $no:hwstmt) =>
      deadDefaultFindings domains yes ++ deadDefaultFindings domains no
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt) => deadDefaultFindings domains yes
  | `(hwstmt| suppress $_:ident because $_:str in $body:hwstmt)
  | `(hwstmt| for $_:ident in $_:term generate $body:hwstmt)
  | `(hwstmt| send $_:hwexpr to $_:ident then $body:hwstmt)
  | `(hwstmt| receive $_:ident from $_:ident then $body:hwstmt) =>
      deadDefaultFindings domains body
  | `(hwstmt| {$statements:hwstmt,*}) =>
      statements.getElems.toList.flatMap (deadDefaultFindings domains)
  | _ => []

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
      let targetName := target.getId
      let registerName := if targetName.isAtomic then targetName else targetName.getPrefix
      unless writable.contains registerName do
        Macro.throwErrorAt target
          s!"'{target.getId}' is not a writable register in this hardware block"
  | `(hwstmt| $_:ident[port $_:num, $_:hwexpr] <- $_:hwexpr) => pure ()
  | `(hwstmt| $family:ident[$_:hwexpr] <- $_:hwexpr) =>
      unless writable.contains family.getId do
        Macro.throwErrorAt family
          s!"'{family.getId}' is not a writable register family in this hardware block"
  | `(hwstmt| send $_:hwexpr to $_:ident) => pure ()
  | `(hwstmt| send $_:hwexpr to $_:ident then $body:hwstmt) =>
      validateWriteTargets writable body
  | `(hwstmt| consume $_:ident) => pure ()
  | `(hwstmt| receive $_:ident from $_:ident then $body:hwstmt) =>
      validateWriteTargets writable body
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

private partial def validateLocalBinders (designLocals : Array Name) :
    TSyntax `hwstmt → MacroM Unit
  | `(hwstmt| let $name:ident : $_:num := $_:hwexpr)
  | `(hwstmt| let $name:ident := $_:hwexpr) => do
      if designLocals.contains name.getId then
        Macro.throwErrorAt name
          s!"local alias '{name.getId}' conflicts with a design-local declaration"
  | `(hwstmt| for $name:ident in $_:term generate $body:hwstmt) => do
      if designLocals.contains name.getId then
        Macro.throwErrorAt name
          s!"generate binder '{name.getId}' conflicts with a design-local declaration"
      validateLocalBinders designLocals body
  | `(hwstmt| receive $name:ident from $_:ident then $body:hwstmt) => do
      if designLocals.contains name.getId then
        Macro.throwErrorAt name
          s!"receive binder '{name.getId}' conflicts with a design-local declaration"
      validateLocalBinders designLocals body
  | `(hwstmt| send $_:hwexpr to $_:ident then $body:hwstmt)
  | `(hwstmt| suppress $_:ident because $_:str in $body:hwstmt) =>
      validateLocalBinders designLocals body
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt else $no:hwstmt) => do
      validateLocalBinders designLocals yes
      validateLocalBinders designLocals no
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt) => validateLocalBinders designLocals yes
  | `(hwstmt| case $_:hwexpr of $arms:hwcasearm*) =>
      for arm in arms do
        match arm with
        | `(hwcasearm| | default => $body:hwstmt)
        | `(hwcasearm| | $_:hwexpr => $body:hwstmt) =>
            validateLocalBinders designLocals body
        | _ => pure ()
  | `(hwstmt| {$statements:hwstmt,*}) =>
      for statement in statements.getElems do
        validateLocalBinders designLocals statement
  | _ => pure ()

private partial def validateCases (domains : Array StateDomain)
    (constants : Array ConstItem) : TSyntax `hwstmt → MacroM Unit
  | `(hwstmt| case $scrutinee:hwexpr of $arms:hwcasearm*) => do
      let domain? := match scrutinee with
        | `(hwexpr| $name:ident) => domains.find? (fun domain => domain.register.getId == name.getId)
        | _ => none
      let mut namedArms : Array (TSyntax `ident) := #[]
      let mut normalizedArms : Array (Nat × Syntax) := #[]
      let mut hasDefault := false
      let recordNormalized (priorArms : Array (Nat × Syntax))
          (source : Syntax) (value : Nat) : MacroM (Array (Nat × Syntax)) := do
        if priorArms.any (fun prior => prior.1 == value) then
          Macro.throwErrorAt source
            s!"duplicate case label after normalization; both arms equal {value}"
        pure <| priorArms.push (value, source)
      for arm in arms do
        match arm with
        | `(hwcasearm| | default => $body:hwstmt) =>
            hasDefault := true
            validateCases domains constants body
        | `(hwcasearm| | $value:num => $body:hwstmt) =>
            normalizedArms ← recordNormalized normalizedArms value value.getNat
            validateCases domains constants body
        | `(hwcasearm| | $name:ident => $body:hwstmt) =>
            if namedArms.any (fun prior => prior.getId == name.getId) then
              Macro.throwErrorAt name s!"duplicate case arm '{name.getId}'"
            namedArms := namedArms.push name
            if let some constant := constants.find? (fun item => item.name.getId == name.getId) then
              normalizedArms ← recordNormalized normalizedArms name constant.value.getNat
            validateCases domains constants body
        | `(hwcasearm| | $value:hwexpr => $_:hwstmt) =>
            Macro.throwErrorAt value
              "case label must be a compile-time literal or named hardware constant"
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
      validateCases domains constants yes
      validateCases domains constants no
  | `(hwstmt| if $_:hwexpr then $yes:hwstmt) => validateCases domains constants yes
  | `(hwstmt| suppress $_:ident because $_:str in $body:hwstmt) =>
      validateCases domains constants body
  | `(hwstmt| for $_:ident in $_:term generate $body:hwstmt) =>
      validateCases domains constants body
  | `(hwstmt| send $_:hwexpr to $_:ident then $body:hwstmt) =>
      validateCases domains constants body
  | `(hwstmt| receive $_:ident from $_:ident then $body:hwstmt) =>
      validateCases domains constants body
  | `(hwstmt| {$statements:hwstmt,*}) =>
      for statement in statements.getElems do
        validateCases domains constants statement
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

private partial def exactAddrWidthLoop (depth capacity width : Nat) : Option Nat :=
  if depth == capacity then some width
  else if depth < capacity then none
  else exactAddrWidthLoop depth (capacity * 2) (width + 1)

private def exactAddrWidth (depth : TSyntax `num) : MacroM Nat := do
  let value := depth.getNat
  if value == 0 then
    Macro.throwErrorAt depth "memory depth must be positive"
  match exactAddrWidthLoop value 1 0 with
  | some width => pure width
  | none =>
      Macro.throwErrorAt depth
        s!"memory depth {value} is not a power of two; the current Mem core represents exactly 2^addressWidth cells"

private def parseHardwareItems (items : Array (TSyntax `hwitem)) :
    MacroM (Array ScalarRegItem × Array ConstItem × Array InputItem ×
      Array MemoryItem × Array PackedMemoryItem × Array WireItem × Array PackedRegItem ×
      Array PackedInputItem × Array PackedWireItem × Array RegArrayItem ×
      Array StateDomain × Array RuleItem) := do
  let mut registers : Array ScalarRegItem := #[]
  let mut constants : Array ConstItem := #[]
  let mut inputs : Array InputItem := #[]
  let mut memories : Array MemoryItem := #[]
  let mut packedMemories : Array PackedMemoryItem := #[]
  let mut wires : Array WireItem := #[]
  let mut packedRegisters : Array PackedRegItem := #[]
  let mut packedInputs : Array PackedInputItem := #[]
  let mut packedWires : Array PackedWireItem := #[]
  let mut registerArrays : Array RegArrayItem := #[]
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
    | `(hwitem| $kind:ident $name:ident : $typeName:ident) =>
        if kind.getId == `reg then packedRegisters := packedRegisters.push ⟨name, typeName, false⟩
        else if kind.getId == `input then packedInputs := packedInputs.push ⟨name, typeName⟩
        else Macro.throwErrorAt kind "expected packed `reg` or `input` declaration"
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $typeName:ident) =>
        if qualifier.getId == `output && kind.getId == `reg then
          packedRegisters := packedRegisters.push ⟨name, typeName, true⟩
        else if qualifier.getId == `input && kind.getId == `wire then
          packedInputs := packedInputs.push ⟨name, typeName⟩
        else Macro.throwErrorAt qualifier "expected packed `output reg` or `input wire` declaration"
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $typeName:ident := $value:hwexpr) =>
        unless qualifier.getId == `output && kind.getId == `wire do
          Macro.throwErrorAt qualifier "expected packed `output wire`"
        packedWires := packedWires.push ⟨name, typeName, value⟩
    | `(hwitem| $kind:ident $name:ident : {$members:ident,*}) =>
        unless kind.getId == `states do Macro.throwErrorAt kind "expected `states`"
        let (register, stateConstants) ← stateItems name none members.getElems none false
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems, register.width.getNat⟩
    | `(hwitem| $kind:ident $name:ident : {$members:ident,*} := $reset:ident) =>
        unless kind.getId == `states do Macro.throwErrorAt kind "expected `states`"
        let (register, stateConstants) ← stateItems name none members.getElems (some reset) false
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems, register.width.getNat⟩
    | `(hwitem| $kind:ident $name:ident : $width:num {$members:ident,*}) =>
        unless kind.getId == `states do Macro.throwErrorAt kind "expected `states`"
        let (register, stateConstants) ← stateItems name (some width) members.getElems none false
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems, register.width.getNat⟩
    | `(hwitem| $kind:ident $name:ident : $width:num {$members:ident,*} := $reset:ident) =>
        unless kind.getId == `states do Macro.throwErrorAt kind "expected `states`"
        let (register, stateConstants) ← stateItems name (some width) members.getElems (some reset) false
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems, register.width.getNat⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : {$members:ident,*}) =>
        unless qualifier.getId == `output && kind.getId == `states do
          Macro.throwErrorAt qualifier "expected `output states`"
        let (register, stateConstants) ← stateItems name none members.getElems none true
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems, register.width.getNat⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : {$members:ident,*} := $reset:ident) =>
        unless qualifier.getId == `output && kind.getId == `states do
          Macro.throwErrorAt qualifier "expected `output states`"
        let (register, stateConstants) ← stateItems name none members.getElems (some reset) true
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems, register.width.getNat⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $width:num {$members:ident,*}) =>
        unless qualifier.getId == `output && kind.getId == `states do
          Macro.throwErrorAt qualifier "expected `output states`"
        let (register, stateConstants) ← stateItems name (some width) members.getElems none true
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems, register.width.getNat⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $width:num {$members:ident,*} := $reset:ident) =>
        unless qualifier.getId == `output && kind.getId == `states do
          Macro.throwErrorAt qualifier "expected `output states`"
        let (register, stateConstants) ← stateItems name (some width) members.getElems (some reset) true
        registers := registers.push register; constants := constants ++ stateConstants
        stateDomains := stateDomains.push ⟨name, members.getElems, register.width.getNat⟩
    | `(hwitem| $kind:ident $name:ident : $dataWidth:num [$depth:num]) =>
        if kind.getId == `memory then
          memories := memories.push
            ⟨name, dataWidth, depth, ← exactAddrWidth depth, none⟩
        else if kind.getId == `reg then
          registerArrays := registerArrays.push ⟨name, dataWidth, depth, false⟩
        else Macro.throwErrorAt kind "expected `memory` or register-family `reg`"
    | `(hwitem| $kind:ident $name:ident : $dataWidth:num [$depth:num] using $policy:term) =>
        unless kind.getId == `memory do Macro.throwErrorAt kind "expected `memory`"
        memories := memories.push
          ⟨name, dataWidth, depth, ← exactAddrWidth depth, some policy⟩
    | `(hwitem| $kind:ident $name:ident : $typeName:ident [$depth:num]) =>
        unless kind.getId == `memory do Macro.throwErrorAt kind "expected packed `memory`"
        packedMemories := packedMemories.push
          ⟨name, typeName, depth, ← exactAddrWidth depth, none⟩
    | `(hwitem| $kind:ident $name:ident : $typeName:ident [$depth:num] using $policy:term) =>
        unless kind.getId == `memory do Macro.throwErrorAt kind "expected packed `memory`"
        packedMemories := packedMemories.push
          ⟨name, typeName, depth, ← exactAddrWidth depth, some policy⟩
    | `(hwitem| $qualifier:ident $kind:ident $name:ident : $width:num [$count:num]) =>
        unless qualifier.getId == `output && kind.getId == `reg do
          Macro.throwErrorAt qualifier "expected `output reg` family declaration"
        registerArrays := registerArrays.push ⟨name, width, count, true⟩
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
    inputs.map (fun item => item.name) ++ memories.map (fun item => item.name) ++
    packedMemories.map (fun item => item.name) ++
    wires.map (fun item => item.name) ++ packedRegisters.map (fun item => item.name) ++
    packedInputs.map (fun item => item.name) ++ packedWires.map (fun item => item.name) ++
    registerArrays.map (fun item => item.name) ++
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
  let writable := registers.map (fun item => item.name.getId) ++
    packedRegisters.map (fun item => item.name.getId) ++
    registerArrays.map (fun item => item.name.getId)
  for ruleItem in rules do
    validateWriteTargets writable ruleItem.body
    validateLocalBinders (locals.map (·.getId)) ruleItem.body
    validateCases stateDomains constants ruleItem.body
  pure (registers, constants, inputs, memories, packedMemories, wires, packedRegisters,
    packedInputs, packedWires, registerArrays, stateDomains, rules)

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
    (constants : Array ConstItem) (inputs : Array InputItem) (memories : Array MemoryItem)
    (packedMemories : Array PackedMemoryItem)
    (wires : Array WireItem) (packedRegisters : Array PackedRegItem)
    (packedInputs : Array PackedInputItem) (packedWires : Array PackedWireItem)
    (registerArrays : Array RegArrayItem)
    (packedMemoryWidths packedRegisterWidths packedInputWidths packedWireWidths : Array Nat)
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
  for memory in memories do
    declarations := declarations.push
      ⟨memory.name.getId, .memory, memory.dataWidth.getNat,
        sourceSpan fileName memory.name⟩
  for (memory, packedWidth) in packedMemories.zip packedMemoryWidths do
    declarations := declarations.push
      ⟨memory.name.getId, .memory, packedWidth, sourceSpan fileName memory.name⟩
  for wireItem in wires do
    declarations := declarations.push
      ⟨wireItem.name.getId, .wire, wireItem.width.getNat, sourceSpan fileName wireItem.name⟩
  for (packedRegister, packedWidth) in packedRegisters.zip packedRegisterWidths do
    declarations := declarations.push
      ⟨packedRegister.name.getId, .register, packedWidth,
        sourceSpan fileName packedRegister.name⟩
  for (packedInput, packedWidth) in packedInputs.zip packedInputWidths do
    declarations := declarations.push
      ⟨packedInput.name.getId, .input, packedWidth,
        sourceSpan fileName packedInput.name⟩
  for (packedWire, packedWidth) in packedWires.zip packedWireWidths do
    declarations := declarations.push
      ⟨packedWire.name.getId, .wire, packedWidth,
        sourceSpan fileName packedWire.name⟩
  for registerArray in registerArrays do
    declarations := declarations.push
      ⟨registerArray.name.getId, .registerFamily, registerArray.width.getNat,
        sourceSpan fileName registerArray.name⟩
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
    declarations := declarations.insertionSort fun left right =>
      left.source.startByte < right.source.startByte
    rules := ruleMetadata
    suppressions := suppressions
  }

private def expandHardwareCommand
    (documentation : Option (TSyntax ``Lean.Parser.Command.docComment))
    (moduleName : TSyntax `ident)
    (items : Array (TSyntax `hwitem)) : MacroM Syntax := do
  let (registers, constants, inputs, memories, packedMemories, wires, packedRegisters,
    packedInputs, packedWires, registerArrays, _, rules) ← parseHardwareItems items
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
  for memory in memories do
    let sourceName := Syntax.mkStrLit memory.name.getId.toString
    let addressWidth := quote memory.addrWidth
    let command ← `(command|
      def $(memory.name) : Loom.Hw.Mem $addressWidth $(memory.dataWidth) := ⟨$sourceName⟩)
    commands := commands.push command
    let lemmaName := mkIdentFrom memory.name
      (Name.mkSimple (memory.name.getId.toString ++ "_name"))
    let lemmaCommand ← `(command|
      @[simp] theorem $lemmaName : $(memory.name).name = $sourceName := rfl)
    commands := commands.push lemmaCommand
  for memory in packedMemories do
    let sourceName := Syntax.mkStrLit memory.name.getId.toString
    let addressWidth := quote memory.addrWidth
    let command ← `(command|
      def $(memory.name) : Loom.Hw.PackedMem $addressWidth $(memory.typeName) :=
        Loom.Hw.PackedMem.named $sourceName)
    commands := commands.push command
    let lemmaName := mkIdentFrom memory.name
      (Name.mkSimple (memory.name.getId.toString ++ "_name"))
    let lemmaCommand ← `(command|
      @[simp] theorem $lemmaName : $(memory.name).name = $sourceName := rfl)
    commands := commands.push lemmaCommand
  for register in packedRegisters do
    let sourceName := Syntax.mkStrLit register.name.getId.toString
    let command ← `(command|
      def $(register.name) : Loom.Hw.PackedReg $(register.typeName) :=
        Loom.Hw.PackedReg.named $sourceName)
    commands := commands.push command
  for inputItem in packedInputs do
    let sourceName := Syntax.mkStrLit inputItem.name.getId.toString
    let command ← `(command|
      def $(inputItem.name) : Loom.Hw.PackedInput $(inputItem.typeName) :=
        Loom.Hw.PackedInput.named $sourceName)
    commands := commands.push command
  for registerArray in registerArrays do
    let sourceName := Syntax.mkStrLit registerArray.name.getId.toString
    let command ← `(command|
      def $(registerArray.name) : Loom.Hw.RegArray $(registerArray.width) $(registerArray.count) :=
        ⟨$sourceName⟩)
    commands := commands.push command
  for constant in constants do
    let command ← `(command|
      def $(constant.name) : Loom.Hw.Expr $(constant.width) :=
        hw_lit% $(constant.value))
    commands := commands.push command
  for wireItem in wires do
    let command ← `(command|
      def $(wireItem.name) : Loom.Hw.Expr $(wireItem.width) := [hwexpr| $(wireItem.value)])
    commands := commands.push command
  for wireItem in packedWires do
    let command ← `(command|
      def $(wireItem.name) : Loom.Hw.PackedExpr $(wireItem.typeName) :=
        [hwexpr| $(wireItem.value)])
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
  for memory in memories do
    match memory.policy with
    | none => declarations ← `($declarations |>.addMem $(memory.name))
    | some policy =>
        declarations ← `($declarations |>.addMem $(memory.name)
          (syncRead := ($policy : Loom.Hw.MemoryPolicy).syncRead)
          (ackInit := ($policy : Loom.Hw.MemoryPolicy).ackInit))
  for memory in packedMemories do
    let zero ← `(fun _ => Loom.Hw.HwPacked.unpack
      (α := $(memory.typeName))
      (BitVec.ofNat (Loom.Hw.HwPacked.width $(memory.typeName)) 0))
    match memory.policy with
    | none => declarations ← `($declarations |>.addPackedMem $(memory.name) $zero)
    | some policy =>
        declarations ← `($declarations |>.addPackedMem $(memory.name) $zero
          (syncRead := ($policy : Loom.Hw.MemoryPolicy).syncRead)
          (ackInit := ($policy : Loom.Hw.MemoryPolicy).ackInit))
  for register in packedRegisters do
    let zero ← `(Loom.Hw.HwPacked.unpack
      (α := $(register.typeName))
      (BitVec.ofNat (Loom.Hw.HwPacked.width $(register.typeName)) 0))
    declarations ← `($declarations |>.addPackedReg $(register.name) $zero
      (exported := $(quote register.exported)))
  for inputItem in packedInputs do
    declarations ← `($declarations |>.addPackedInput $(inputItem.name))
  for wireItem in packedWires do
    let sourceName := Syntax.mkStrLit wireItem.name.getId.toString
    declarations ← `($declarations |>.addPackedCombOutput $sourceName $(wireItem.name))
  for registerArray in registerArrays do
    declarations ← `($declarations |>.addRegArray $(registerArray.name)
      (exported := $(quote registerArray.exported)))
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
      let (registers, constants, inputs, memories, packedMemories, wires, packedRegisters,
        packedInputs, packedWires, registerArrays, domains, rules) ←
        liftMacroM <| parseHardwareItems items
      let namespaceName ← getCurrNamespace
      let environment ← getEnv
      let localNames := registers.map (fun item => item.name) ++
        constants.map (fun item => item.name) ++ inputs.map (fun item => item.name) ++
        memories.map (fun item => item.name) ++ packedMemories.map (fun item => item.name) ++
        wires.map (fun item => item.name) ++
        packedRegisters.map (fun item => item.name) ++
        packedInputs.map (fun item => item.name) ++ packedWires.map (fun item => item.name) ++
        registerArrays.map (fun item => item.name) ++
        rules.map (fun item => item.name)
      for localName in localNames do
        let fullName := namespaceName ++ localName.getId
        if environment.contains fullName then
          throwErrorAt localName s!"'{fullName}' has already been declared"
      for handleName in registers.map (fun item => item.name) ++ inputs.map (fun item => item.name) ++
          memories.map (fun item => item.name) ++ packedRegisters.map (fun item => item.name) ++
          packedMemories.map (fun item => item.name) ++
          packedInputs.map (fun item => item.name) ++ registerArrays.map (fun item => item.name) do
        let lemmaName := namespaceName ++
          Name.mkSimple (handleName.getId.toString ++ "_name")
        if environment.contains lemmaName then
          throwErrorAt handleName s!"generated name lemma '{lemmaName}' has already been declared"
      for generatedName in #[namespaceName ++ `declarations, namespaceName ++ `design] do
        if environment.contains generatedName then
          throwErrorAt moduleName s!"generated declaration '{generatedName}' has already been declared"
      for finding in hardwareLintFindings registers rules do
        logWarningAt finding.source finding.message
      for ruleItem in rules do
        for finding in deadDefaultFindings domains ruleItem.body do
          logWarningAt finding.source finding.message
      let packedWidth (typeName : TSyntax `ident) : CommandElabM Nat :=
        liftTermElabM do
          let widthSyntax ← `(Loom.Hw.HwPacked.width $typeName)
          let widthExpr ← elabTerm widthSyntax (some (.const ``Nat []))
          let some width ← getNatValue? (← Meta.whnf widthExpr)
            | throwErrorAt typeName "packed type width must reduce to a numeral"
          pure width
      let packedRegisterWidths ← packedRegisters.mapM (packedWidth ·.typeName)
      let packedMemoryWidths ← packedMemories.mapM (packedWidth ·.typeName)
      let packedInputWidths ← packedInputs.mapM (packedWidth ·.typeName)
      let packedWireWidths ← packedWires.mapM (packedWidth ·.typeName)
      let metadata := makeHardwareMetadata (← getFileName) namespaceName moduleName
        registers constants inputs memories packedMemories wires packedRegisters packedInputs packedWires
        registerArrays packedMemoryWidths packedRegisterWidths packedInputWidths packedWireWidths domains rules
      let expanded ← liftMacroM <| expandHardwareCommand documentation moduleName items
      elabCommand expanded
      modifyEnv (hardwareMetadataExt.addEntry · metadata)
  | _ => throwUnsupportedSyntax

private def DeclarationKind.label : DeclarationKind → String
  | .register => "register"
  | .registerFamily => "register family element"
  | .stateRegister => "state register"
  | .memory => "memory element"
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
    if design.outputs.contains name then
      IO.println s!"  {name} = {value}"

def runHardwareOpen {design : Loom.Hw.Design}
    (simulator : Loom.Hw.FastEval.VerifiedSimulator design) (cycles : Nat)
    (inputs : Nat → Loom.Hw.InEnv) : IO Unit := do
  let final := simulator.runOpen inputs cycles simulator.reset
  IO.println s!"after {cycles} cycles:"
  if !design.inputs.isEmpty then
    IO.println "inputs:"
    for cycle in List.range cycles do
      let values := design.inputs.map fun declaration =>
        s!"{declaration.name}={(inputs cycle declaration.name declaration.width).toNat}"
      IO.println s!"  cycle {cycle}: {String.intercalate ", " values}"
  IO.println "outputs:"
  for (name, value) in design.fastRegs final do
    if design.outputs.contains name then
      IO.println s!"  {name} = {value}"

syntax (name := runHardwareCmd) "#run_hardware" term:max "for" num ident : command
syntax (name := runHardwareOpenCmd) "#run_hardware" term:max "for" num ident
  "inputs" "$" "(" term ")" : command

macro_rules
  | `(#run_hardware $design:term for $count:num $unit:ident) => do
      unless unit.getId == `cycles do
        Macro.throwErrorAt unit "expected `cycles`"
      `(#eval Loom.Hw.Dsl.runHardware
        (design := $design)
        ({ wf := by native_decide } : Loom.Hw.FastEval.VerifiedSimulator $design)
        $count)
  | `(#run_hardware $design:term for $count:num $unit:ident inputs $($trace:term)) => do
      unless unit.getId == `cycles do
        Macro.throwErrorAt unit "expected `cycles`"
      `(#eval Loom.Hw.Dsl.runHardwareOpen
        (design := $design)
        ({ wf := by native_decide } : Loom.Hw.FastEval.VerifiedSimulator $design)
        $count $trace)

/-! ## Checked multiclock system command

This first surface accepts existing ordinary `Design` values. Inline island
hardware reuses the `hardware` command in the next slice; topology and
realization already lower through the same checked System APIs. -/

declare_syntax_cat hwsystemitem

private def systemSameLine : Lean.Parser.Parser where
  info := Lean.Parser.epsilonInfo
  fn := fun _ state =>
    if Lean.Parser.checkTailLinebreak state.stxStack.back then
      state.mkError "each system declaration must remain on one line"
    else state

@[combinator_formatter systemSameLine]
private def systemSameLine.formatter : Lean.PrettyPrinter.Formatter := pure ()

@[combinator_parenthesizer systemSameLine]
private def systemSameLine.parenthesizer : Lean.PrettyPrinter.Parenthesizer := pure ()

syntax (priority := low) ident systemSameLine ident : hwsystemitem
syntax (priority := high) ident systemSameLine "$" "(" term ")" : hwsystemitem
syntax (priority := high) ident systemSameLine ident systemSameLine ":" num systemSameLine ident num : hwsystemitem
syntax (priority := high) ident systemSameLine ident systemSameLine ":" ident systemSameLine ident num : hwsystemitem
syntax (priority := high) ident systemSameLine ident systemSameLine ":" num systemSameLine ident num systemSameLine ident term:max : hwsystemitem
syntax (priority := high) ident systemSameLine ident systemSameLine ":" ident systemSameLine ident num systemSameLine ident term:max : hwsystemitem
syntax (priority := high) ident systemSameLine ident "on" ident ":=" term : hwsystemitem
syntax (priority := high) ident systemSameLine ident "on" ident
  systemSameLine "module" ident ":=" term : hwsystemitem
syntax (priority := high) ident systemSameLine ident "on" ident
  (systemSameLine "module" ident)? "where"
  withPosition(many1Indent(ppLine hwitem)) : hwsystemitem
syntax (priority := high) ident systemSameLine ident "from" ident "to" ident : hwsystemitem
syntax (priority := high) ident systemSameLine ident,+ "with" term : hwsystemitem
syntax (name := systemCmd) (docComment)? ident ident "where"
  withPosition(many1Indent(ppLine hwsystemitem)) : command

private structure PrettyClock where
  name : TSyntax `ident

private structure PrettyChannel where
  name : TSyntax `ident
  width : Option (TSyntax `num) := none
  packedType : Option (TSyntax `ident) := none
  depth : TSyntax `num
  policy : Option (TSyntax `term) := none

private structure PrettyIsland where
  name : TSyntax `ident
  clock : TSyntax `ident
  design : Option (TSyntax `term) := none
  moduleName : Option (TSyntax `ident) := none
  body : Array (TSyntax `hwitem) := #[]

private structure PrettyConnection where
  channel : TSyntax `ident
  source : TSyntax `ident
  sink : TSyntax `ident

private structure PrettyRealization where
  channel : TSyntax `ident
  kind : TSyntax `term

private def duplicateNameCheck (kind : String) (names : Array (TSyntax `ident)) : MacroM Unit := do
  for index in [:names.size] do
    for later in [index + 1:names.size] do
      if names[index]!.getId == names[later]!.getId then
        Macro.throwErrorAt names[later]! s!"duplicate {kind} name '{names[later]!.getId}'"

private def listElements (stx : Syntax) : Option (Array Syntax) := do
  let args := stx.getArgs
  guard (args.size == 3)
  let middle := args[1]!
  pure <| middle.getArgs.filter (fun item => !item.isAtom)

/-- Recognize the documented `Clock.alignGroups base [[...], ...]` shape for
source-local well-formedness diagnostics. Arbitrary clock-relation terms remain
valid escapes and are checked only by their own library constructors. -/
private def clockGroups? (relation : TSyntax `term) :
    Option (Array (Array (TSyntax `ident))) := do
  let appArgs := relation.raw.getArgs
  guard (relation.raw.getKind == ``Lean.Parser.Term.app && appArgs.size == 2)
  let function := appArgs[0]!
  guard (function.isIdent && function.getId.toString.endsWith "Clock.alignGroups")
  let arguments := appArgs[1]!.getArgs.filter (fun item => !item.isAtom)
  guard (arguments.size == 2)
  let groups ← listElements arguments[1]!
  groups.mapM fun group => do
    let members ← listElements group
    members.mapM fun member => do
      guard member.isIdent
      pure ⟨member⟩

private def validateClockGroups (declared : Array PrettyClock)
    (relation : TSyntax `term) : MacroM Unit := do
  let some groups := clockGroups? relation | pure ()
  let mut seen : Array (TSyntax `ident) := #[]
  for group in groups do
    if group.isEmpty then
      Macro.throwErrorAt relation "an aligned clock group cannot be empty"
    let mut within : Array (TSyntax `ident) := #[]
    for clock in group do
      unless declared.any (fun item => item.name.getId == clock.getId) do
        Macro.throwErrorAt clock s!"undeclared clock '{clock.getId}' in aligned group"
      if within.any (fun prior => prior.getId == clock.getId) then
        Macro.throwErrorAt clock s!"clock '{clock.getId}' appears twice in one aligned group"
      if seen.any (fun prior => prior.getId == clock.getId) then
        Macro.throwErrorAt clock s!"clock '{clock.getId}' appears in more than one aligned group"
      within := within.push clock
      seen := seen.push clock

private def simpleTermName? (term : TSyntax `term) : Option Name :=
  if term.raw.isIdent then some term.raw.getId else none

private def realizationNameIs (realization : PrettyRealization) (suffix : String) : Bool :=
  (simpleTermName? realization.kind).any (fun name => name.toString.endsWith suffix)

private def expandSystemCommand
    (documentation : Option (TSyntax ``Lean.Parser.Command.docComment))
    (namespaceName : Name) (systemName : TSyntax `ident)
    (items : Array (TSyntax `hwsystemitem)) : MacroM Syntax := do
  let mut clocks : Array PrettyClock := #[]
  let mut relation : Option (TSyntax `term) := none
  let mut resetPolicy : Option (TSyntax `term) := none
  let mut channels : Array PrettyChannel := #[]
  let mut islands : Array PrettyIsland := #[]
  let mut connections : Array PrettyConnection := #[]
  let mut realizations : Array PrettyRealization := #[]
  let mut priorPhase := 0
  for item in items do
    let phase ← match item with
      | `(hwsystemitem| $kind:ident $name:ident) =>
          if kind.getId == `clock then
            clocks := clocks.push ⟨name⟩; pure 0
          else if kind.getId == `clocks then
            if relation.isSome then Macro.throwErrorAt item "a system has exactly one clock relation"
            relation := some ⟨name.raw⟩; pure 1
          else if kind.getId == `reset then
            if resetPolicy.isSome then Macro.throwErrorAt item "a system has exactly one reset policy"
            resetPolicy := some ⟨name.raw⟩; pure 2
          else Macro.throwErrorAt kind "expected `clock`, `clocks`, or `reset`"
      | `(hwsystemitem| $kind:ident $($value:term)) =>
          if kind.getId == `clocks then
            if relation.isSome then Macro.throwErrorAt item "a system has exactly one clock relation"
            relation := some value; pure 1
          else if kind.getId == `reset then
            if resetPolicy.isSome then Macro.throwErrorAt item "a system has exactly one reset policy"
            resetPolicy := some value; pure 2
          else Macro.throwErrorAt kind "only `clocks` and `reset` accept a Lean term escape"
      | `(hwsystemitem| $kind:ident $name:ident : $width:num $depthKeyword:ident $depth:num) =>
          unless kind.getId == `channel && depthKeyword.getId == `depth do
            Macro.throwErrorAt kind "expected `channel name : width depth amount`"
          if width.getNat == 0 then Macro.throwErrorAt width "channel width must be positive"
          if depth.getNat == 0 then Macro.throwErrorAt depth "channel depth must be positive"
          channels := channels.push { name, width := some width, depth }; pure 3
      | `(hwsystemitem| $kind:ident $name:ident : $typeName:ident $depthKeyword:ident $depth:num) =>
          unless kind.getId == `channel && depthKeyword.getId == `depth do
            Macro.throwErrorAt kind "expected `channel name : PackedType depth amount`"
          if depth.getNat == 0 then Macro.throwErrorAt depth "channel depth must be positive"
          channels := channels.push { name, packedType := some typeName, depth }; pure 3
      | `(hwsystemitem| $kind:ident $name:ident : $width:num $depthKeyword:ident $depth:num $policyKeyword:ident $policy:term) =>
          unless kind.getId == `channel && depthKeyword.getId == `depth &&
              policyKeyword.getId == `policy do
            Macro.throwErrorAt kind "expected `channel name : width depth amount policy Chan.exchange`"
          if width.getNat == 0 then Macro.throwErrorAt width "channel width must be positive"
          if depth.getNat == 0 then Macro.throwErrorAt depth "channel depth must be positive"
          channels := channels.push { name, width := some width, depth, policy := some policy }; pure 3
      | `(hwsystemitem| $kind:ident $name:ident : $typeName:ident $depthKeyword:ident $depth:num $policyKeyword:ident $policy:term) =>
          unless kind.getId == `channel && depthKeyword.getId == `depth &&
              policyKeyword.getId == `policy do
            Macro.throwErrorAt kind "expected `channel name : PackedType depth amount policy Chan.exchange`"
          if depth.getNat == 0 then Macro.throwErrorAt depth "channel depth must be positive"
          channels := channels.push
            { name, packedType := some typeName, depth, policy := some policy }; pure 3
      | `(hwsystemitem| $kind:ident $name:ident on $clock:ident := $design:term) =>
          unless kind.getId == `island do
            Macro.throwErrorAt kind "expected `island name on clock := design`"
          islands := islands.push { name, clock, design := some design }; pure 4
      | `(hwsystemitem| $kind:ident $name:ident on $clock:ident module $moduleName:ident := $design:term) =>
          unless kind.getId == `island do
            Macro.throwErrorAt kind "expected `island name on clock module moduleName := design`"
          islands := islands.push { name, clock, design := some design, moduleName := some moduleName }
          pure 4
      | `(hwsystemitem| $kind:ident $name:ident on $clock:ident $[module $moduleName:ident]? where $body:hwitem*) =>
          unless kind.getId == `island do
            Macro.throwErrorAt kind "expected `island name on clock where ...`"
          islands := islands.push { name, clock, moduleName, body }; pure 4
      | `(hwsystemitem| $kind:ident $channel:ident from $source:ident to $sink:ident) =>
          unless kind.getId == `connect do
            Macro.throwErrorAt kind "expected `connect channel from source to sink`"
          connections := connections.push ⟨channel, source, sink⟩; pure 5
      | `(hwsystemitem| $keyword:ident $routeChannels:ident,* with $kind:term) =>
          unless keyword.getId == `realize do
            Macro.throwErrorAt keyword "expected `realize channel, ... with implementation`"
          for channel in routeChannels.getElems do
            realizations := realizations.push ⟨channel, kind⟩
          pure 6
      | _ => Macro.throwErrorAt item "unsupported system declaration"
    if phase < priorPhase then
      Macro.throwErrorAt item
        "system items must appear as clocks, clock relation, reset, channels, islands, connections, then realizations"
    priorPhase := phase
  if clocks.isEmpty then Macro.throwErrorAt systemName "a system requires at least one clock"
  let some clockRelation := relation
    | Macro.throwErrorAt systemName "a system requires one `clocks` relation"
  let some reset := resetPolicy
    | Macro.throwErrorAt systemName "a system requires one explicit `reset` policy"
  duplicateNameCheck "clock" (clocks.map (·.name))
  validateClockGroups clocks clockRelation
  duplicateNameCheck "channel" (channels.map (·.name))
  duplicateNameCheck "island" (islands.map (·.name))
  for island in islands do
    unless clocks.any (fun clock => clock.name.getId == island.clock.getId) do
      Macro.throwErrorAt island.clock s!"undeclared clock '{island.clock.getId}'"
  for clock in clocks do
    unless islands.any (fun island => island.clock.getId == clock.name.getId) do
      Macro.throwErrorAt clock.name s!"clock '{clock.name.getId}' is not used by an island"
  for connection in connections do
    unless channels.any (fun channel => channel.name.getId == connection.channel.getId) do
      Macro.throwErrorAt connection.channel s!"undeclared channel '{connection.channel.getId}'"
    unless islands.any (fun island => island.name.getId == connection.source.getId) do
      Macro.throwErrorAt connection.source s!"undeclared source island '{connection.source.getId}'"
    unless islands.any (fun island => island.name.getId == connection.sink.getId) do
      Macro.throwErrorAt connection.sink s!"undeclared sink island '{connection.sink.getId}'"
  for channel in channels do
    let routes := connections.filter (fun connection => connection.channel.getId == channel.name.getId)
    if routes.size != 1 then
      Macro.throwErrorAt channel.name
        s!"channel '{channel.name.getId}' must have exactly one connection; found {routes.size}"
    let choices := realizations.filter (fun choice => choice.channel.getId == channel.name.getId)
    if choices.size != 1 then
      Macro.throwErrorAt channel.name
        s!"channel '{channel.name.getId}' must have exactly one realization; found {choices.size}"
  for realization in realizations do
    unless channels.any (fun channel => channel.name.getId == realization.channel.getId) do
      Macro.throwErrorAt realization.channel s!"undeclared channel '{realization.channel.getId}'"
    let some connection := connections.find? (fun route =>
      route.channel.getId == realization.channel.getId) | unreachable!
    let some source := islands.find? (fun island =>
      island.name.getId == connection.source.getId) | unreachable!
    let some sink := islands.find? (fun island =>
      island.name.getId == connection.sink.getId) | unreachable!
    let some channel := channels.find? (fun declaration =>
      declaration.name.getId == realization.channel.getId) | unreachable!
    let distinctClocks := source.clock.getId != sink.clock.getId
    if realizationNameIs realization "Cdc.synchronousFifo" && distinctClocks then
      Macro.throwErrorAt realization.kind
        "alignment is a schedule assumption, not a timing-closure fact; the synchronous realization requires one shared physical clock. Select a certified crossing realization or use the same clock handle"
    let gray := realizationNameIs realization "Cdc.grayFifo"
    let recoverable := realizationNameIs realization "Cdc.recoverableGrayFifo"
    if gray || recoverable then
      let depth := channel.depth.getNat
      if depth < 2 || (exactAddrWidthLoop depth 1 0).isNone then
        Macro.throwErrorAt channel.depth
          s!"portable Gray FIFO depth must be a power of two at least 2; declared {depth}"
    let resetName := simpleTermName? reset
    let independent := resetName.any (fun name => name.toString.endsWith "Reset.independentFlush")
    if independent && !recoverable then
      Macro.throwErrorAt realization.kind
        "independent-flush reset requires Cdc.recoverableGrayFifo on every channel"
    if !independent && recoverable then
      Macro.throwErrorAt realization.kind
        "Cdc.recoverableGrayFifo requires Reset.independentFlush"

  let mut commands : Array Syntax := #[]
  let nestedName (localName : Name) := mkIdent (systemName.getId ++ localName)
  let qualifiedNestedName (localName : Name) :=
    mkIdent (namespaceName ++ systemName.getId ++ localName)
  for clock in clocks do
    let sourceName := Syntax.mkStrLit clock.name.getId.toString
    let declarationName := nestedName clock.name.getId
    commands := commands.push (← `(command|
      def $declarationName : Loom.Hw.ClockHandle := .named $sourceName))
  for channel in channels do
    let sourceName := Syntax.mkStrLit channel.name.getId.toString
    let declarationName := nestedName channel.name.getId
    match channel.width, channel.packedType with
    | some width, none =>
        let policy := channel.policy.getD (← `(term| Loom.Hw.Chan.exchange))
        commands := commands.push (← `(command|
          def $declarationName : Loom.Hw.Chan $width :=
            ⟨$sourceName, $(channel.depth), $policy⟩))
    | none, some typeName =>
        let policy := channel.policy.getD (← `(term| Loom.Hw.Chan.exchange))
        commands := commands.push (← `(command|
          def $declarationName : Loom.Hw.PackedChan $typeName :=
            Loom.Hw.PackedChan.named $sourceName $(channel.depth) $policy))
    | _, _ => Macro.throwErrorAt channel.name "invalid channel payload declaration"
  for island in islands do
    let declarationName := nestedName island.name.getId
    let designTerm ← match island.design with
      | some supplied => do
          let baseTerm ← match supplied with
            | `(term| $name:ident) =>
                let resolvedName := if name.getId.isAtomic then
                  namespaceName ++ name.getId else name.getId
                let resolved := mkIdentFrom name resolvedName
                `(term| hw_exact_const% $resolved)
            | _ => pure supplied
          let namedTerm ← match island.moduleName with
            | none => pure baseTerm
            | some moduleName =>
                let emittedName := Syntax.mkStrLit moduleName.getId.toString
                `(term| { $baseTerm with name := $emittedName })
          let mut scopedTerm := namedTerm
          for channel in channels.reverse do
            let channelName := nestedName channel.name.getId
            scopedTerm ← `(let $(channel.name) := $channelName; let _ := $(channel.name); $scopedTerm)
          pure scopedTerm
      | none => do
          let implementationNamespace := mkIdent
            (systemName.getId ++ island.name.getId ++ `Hardware)
          commands := commands.push (← `(command| namespace $implementationNamespace))
          for connection in connections do
            if connection.source.getId == island.name.getId ||
                connection.sink.getId == island.name.getId then
              if connection.source.getId == connection.sink.getId then
                Macro.throwErrorAt connection.channel
                  "an inline island cannot use one short channel name as both source and sink"
              let endpointName := connection.channel
              let channelName := qualifiedNestedName connection.channel.getId
              if connection.source.getId == island.name.getId then
                commands := commands.push (← `(command|
                  def $endpointName := (hw_exact_const% $channelName).source))
              else
                commands := commands.push (← `(command|
                  def $endpointName := (hw_exact_const% $channelName).sink))
          let emittedModuleName := island.moduleName.getD <| mkIdent
            (Name.mkSimple (systemName.getId.toString ++ "_" ++ island.name.getId.toString))
          let body := island.body
          let hardwareCommand ← `(command| hardware $emittedModuleName where $body*)
          commands := commands.push hardwareCommand
          commands := commands.push (← `(command| end $implementationNamespace))
          let implementationDesign := mkIdent
            (namespaceName ++ systemName.getId ++ island.name.getId ++ `Hardware ++ `design)
          pure (← `(term| hw_exact_const% $implementationDesign))
    commands := commands.push (← `(command|
      def $declarationName : Loom.Hw.Design := $designTerm))
    let handleName := nestedName
      (Name.mkSimple (island.name.getId.toString ++ "Island"))
    let clockName := nestedName island.clock.getId
    let sourceName := Syntax.mkStrLit island.name.getId.toString
    commands := commands.push (← `(command|
      def $handleName : Loom.Hw.IslandHandle :=
        .named $sourceName $declarationName $clockName))
  for connection in connections do
    let routeName := nestedName
      (Name.mkSimple (connection.channel.getId.toString ++ "Route"))
    let sourceHandle := nestedName
      (Name.mkSimple (connection.source.getId.toString ++ "Island"))
    let sinkHandle := nestedName
      (Name.mkSimple (connection.sink.getId.toString ++ "Island"))
    let channelName := nestedName connection.channel.getId
    commands := commands.push (← `(command|
      def $routeName :=
        ($channelName).between $sourceHandle $sinkHandle))
  let mut builder : TSyntax `term ← `(Loom.Hw.System.empty)
  for island in islands do
    let handleName := nestedName
      (Name.mkSimple (island.name.getId.toString ++ "Island"))
    builder ← `($builder |>.addIsland $handleName)
  for connection in connections do
    let routeName := nestedName
      (Name.mkSimple (connection.channel.getId.toString ++ "Route"))
    builder ← `($builder |>.addChannel $routeName)
  let mut scopedClockRelation := clockRelation
  for clock in clocks.reverse do
    let clockName := nestedName clock.name.getId
    scopedClockRelation ← `(let $(clock.name) := $clockName; let _ := $(clock.name); $scopedClockRelation)
  builder ← `($builder |>.withClockRel ($scopedClockRelation : Loom.Hw.ClockRel))
  builder ← `({ $builder with resetPolicy := ($reset : Loom.Hw.SystemResetPolicy) })
  let builderName := nestedName `builder
  commands := commands.push (← `(command|
    def $builderName : Loom.Hw.SystemBuilder := $builder))
  let valueName := nestedName `value
  commands := commands.push (← `(command|
    def $valueName : Loom.Hw.System := ($builderName).certify (by decide)))

  let qualifiedSystem := mkIdent (namespaceName ++ systemName.getId)
  let qualifiedValue := mkIdent
    (namespaceName ++ systemName.getId ++ `value)
  commands := commands.push (← `(command|
    $[$documentation]?
    def $systemName : Loom.Hw.System := hw_exact_const% $qualifiedValue))
  let mut plan : TSyntax `term ← `(Loom.Hw.RealizationPlan.portable)
  for realization in realizations do
    let routeName := nestedName
      (Name.mkSimple (realization.channel.getId.toString ++ "Route"))
    plan ← `($plan |>.set $routeName ($(realization.kind) : Loom.Hw.RealizationKind))
  let planName := nestedName `realizationPlan
  commands := commands.push (← `(command|
    def $planName : Loom.Hw.RealizationPlan := $plan))
  let applicationName := nestedName `application
  commands := commands.push (← `(command|
    def $applicationName : Loom.Hw.System.Application $qualifiedSystem :=
      (hw_exact_const% $qualifiedValue).realizeWith $planName (by decide)))
  let certifiedName := nestedName `certified
  commands := commands.push (← `(command|
    abbrev $certifiedName : Loom.Hw.CertifiedSystem $qualifiedSystem :=
      ($applicationName).certified))
  pure (Lean.mkNullNode commands)

@[command_elab systemCmd] def elabSystemCommand : CommandElab := fun stx => do
  match stx with
  | `($[$documentation:docComment]? $keyword:ident $systemName:ident where $items:hwsystemitem*) => do
      unless keyword.getId == `system do throwErrorAt keyword "expected `system`"
      for item in items do
        match item with
        | `(hwsystemitem| $kind:ident $($relation:term)) =>
            if kind.getId == `clocks then
              if let some groups := clockGroups? relation then
                for group in groups do
                  if group.size == 1 then
                    logWarningAt group[0]!
                      "singleton aligned clock group is redundant; unlisted clocks are already independent singletons"
        | _ => pure ()
      let expanded ← liftMacroM <|
        expandSystemCommand documentation (← getCurrNamespace) systemName items
      elabCommand expanded
  | _ => throwUnsupportedSyntax

private def coTickPolicyName : Loom.Hw.FullCoTickPolicy → String
  | .exchange => "exchange"
  | .refusePush => "refuse-push"

def showSystemLogical (system : Loom.Hw.System) : IO Unit := do
  IO.println "system architecture"
  IO.println s!"reset: {repr system.resetPolicy}"
  IO.println "islands:"
  for island in system.islands do
    IO.println s!"  {island.name} on {island.clock}: {island.design.name}"
  IO.println "channels:"
  for crossing in system.crossingInventory do
    IO.println s!"  {crossing.channel}: {crossing.width} bits, depth {crossing.depth}, {coTickPolicyName crossing.policy}"
    IO.println s!"    {crossing.source} ({crossing.sourceClock.getD "?"}) -> {crossing.sink} ({crossing.sinkClock.getD "?"})"

def showSystemTiming {system : Loom.Hw.System}
    (application : Loom.Hw.System.Application system) : IO Unit :=
  IO.println application.timingReport

def showSystemPhysical {system : Loom.Hw.System}
    (application : Loom.Hw.System.Application system) : IO Unit := do
  let artifacts := application.artifact.realized.artifacts
  IO.println artifacts.constraintFile.renderNeutral
  IO.println (Loom.Hw.System.renderResetIntents artifacts.resetIntents)

def showSystemBackend {system : Loom.Hw.System}
    (application : Loom.Hw.System.Application system)
    (report : Loom.Hw.System.PhysicalCheckReport application.artifact.realized.artifacts) : IO Unit :=
  IO.println report.render

syntax (name := showSystemCmd) "#show_system" ident (ident)? : command
syntax (name := showSystemReportCmd) "#show_system" ident ident term:max : command

macro_rules
  | `(#show_system $system:ident $view:ident $report:term) => do
      unless view.getId == `backend do
        Macro.throwErrorAt view "expected `backend` before a physical-check report"
      let application := mkIdentFrom system (system.getId ++ `application)
      `(#eval Loom.Hw.Dsl.showSystemBackend $application $report)
  | `(#show_system $system:ident) =>
      `(#eval Loom.Hw.Dsl.showSystemLogical $system)
  | `(#show_system $system:ident $view:ident) => do
      let application := mkIdentFrom system (system.getId ++ `application)
      if view.getId == `timing then
        `(#eval Loom.Hw.Dsl.showSystemTiming $application)
      else if view.getId == `physical then
        `(#eval Loom.Hw.Dsl.showSystemPhysical $application)
      else Macro.throwErrorAt view "expected `timing` or `physical`"

def runSystem {system : Loom.Hw.System}
    (application : Loom.Hw.System.Application system)
    (events : Loom.Hw.SchedulePrefix) : IO Unit := do
  match application.runChecked events with
  | .error message => throw (IO.userError message)
  | .ok final =>
      IO.println s!"after {events.size} clock events:"
      for island in system.islands do
        IO.println s!"  island {island.name} ({island.clock})"
        for output in island.design.outputs do
          unless output.startsWith "__loom_chan_" do
            match island.design.regs.find? (fun declaration => declaration.name == output) with
            | some declaration =>
                let value := (final.semantic.island island.name).regs
                  declaration.name declaration.width |>.toNat
                IO.println s!"    {output} = {value}"
            | none => pure ()
      for connection in system.connections do
        let occupancy := (application.readChannel final connection.chan).length
        IO.println s!"  channel {connection.chan.name}: occupancy {occupancy}"

declare_syntax_cat hwsystemevent
syntax ident ident,+ : hwsystemevent
syntax (name := runSystemCmd) "#run_system" ident "where"
  withPosition(many1Indent(ppLine hwsystemevent)) : command

macro_rules
  | `(#run_system $system:ident where $events:hwsystemevent*) => do
      let application := mkIdentFrom system (system.getId ++ `application)
      let mut eventTerms : Array (TSyntax `term) := #[]
      for event in events do
        match event with
        | `(hwsystemevent| $keyword:ident $clocks:ident,*) =>
            unless keyword.getId == `tick do
              Macro.throwErrorAt keyword "expected `tick`"
            let clockNames := clocks.getElems.map fun clock =>
              mkIdentFrom clock (system.getId ++ clock.getId)
            let tickTerms ← clockNames.mapM fun clock => `(term| ($clock).name)
            eventTerms := eventTerms.push (← `(term|
              ({ clocks := [$tickTerms,*] } : Loom.Hw.NamedClockEvent)))
        | _ => Macro.throwErrorAt event "expected `tick clock` or `tick clockA, clockB`"
      `(#eval Loom.Hw.Dsl.runSystem $application #[$eventTerms,*])

end Loom.Hw.Dsl
