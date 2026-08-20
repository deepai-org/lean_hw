-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Component
import Loom.Clock
import Loom.Artifact

/-!
# Neutral, module-preserving hardware import IR

This IR is deliberately independent of Verilog, Yosys, and any one parser.
Frontends populate source-located data; the checked lowering below accepts
only constructs whose semantics map exactly onto an ordinary Loom `Design`.
Unsupported constructs fail closed.  Successful lowering does **not** prove
that an untrusted frontend interpreted its source language correctly; exact
source/artifact identities and external equivalence evidence remain required.
-/

namespace Loom.Hw.ImportIR

structure SourceLocation where
  file : String
  startLine : Nat
  startColumn : Nat := 0
  endLine : Nat
  endColumn : Nat := 0
  deriving Repr, DecidableEq, BEq

namespace SourceLocation

def render (location : SourceLocation) : String :=
  s!"{location.file}:{location.startLine}:{location.startColumn}-{location.endLine}:{location.endColumn}"

def validB (location : SourceLocation) : Bool :=
  !location.file.isEmpty && location.startLine > 0 &&
    location.endLine ≥ location.startLine

end SourceLocation

inductive PortDirection where
  | input
  | output
  | inout
  deriving Repr, DecidableEq, BEq

structure Port where
  name : String
  direction : PortDirection
  width : Nat
  semanticType : String := "bits"
  source : SourceLocation
  deriving Repr, DecidableEq, BEq

inductive ResetKind where
  | resetless
  | synchronous
  | asynchronous
  | asynchronousAssertSynchronousRelease
  deriving Repr, DecidableEq, BEq

structure Reset where
  kind : ResetKind
  port : Option String := none
  activeHigh : Bool := true
  source : Option SourceLocation := none
  deriving Repr, DecidableEq, BEq

structure ClockDomain where
  name : String
  clockPort : String
  edge : Loom.ClockEdge
  reset : Reset := { kind := .resetless }
  source : SourceLocation
  deriving Repr, DecidableEq, BEq

inductive UnaryOp where
  | bitNot
  | negate
  deriving Repr, DecidableEq, BEq

inductive BinaryOp where
  | bitAnd
  | bitOr
  | bitXor
  | add
  | sub
  | mul
  | unsignedDiv
  | unsignedRem
  | shiftLeft
  | logicalShiftRight
  | equal
  | unsignedLessThan
  | signedLessThan
  deriving Repr, DecidableEq, BEq

/-- Widths remain explicit at the import boundary.  This is intentionally a
first-order serializable tree rather than Lean's intrinsically indexed
`Hw.Expr`; `lowerExpr?` is the checked dependent-typing boundary. -/
inductive Expr where
  | literal (width value : Nat) (source : SourceLocation)
  | signal (width : Nat) (name : String) (source : SourceLocation)
  | unary (width : Nat) (op : UnaryOp) (value : Expr) (source : SourceLocation)
  | binary (width : Nat) (op : BinaryOp) (left right : Expr)
      (source : SourceLocation)
  | mux (width : Nat) (condition yes no : Expr) (source : SourceLocation)
  | slice (width : Nat) (value : Expr) (offset : Nat) (source : SourceLocation)
  | zeroExtend (width : Nat) (value : Expr) (source : SourceLocation)
  | signExtend (width : Nat) (value : Expr) (source : SourceLocation)
  | concat (width : Nat) (high low : Expr) (source : SourceLocation)
  | memoryRead (width : Nat) (memory : String) (address : Expr)
      (source : SourceLocation)
  deriving Repr, DecidableEq

namespace Expr

def width : Expr → Nat
  | .literal width .. | .signal width .. | .unary width ..
  | .binary width .. | .mux width .. | .slice width ..
  | .zeroExtend width .. | .signExtend width .. | .concat width ..
  | .memoryRead width .. => width

def source : Expr → SourceLocation
  | .literal _ _ source | .signal _ _ source | .unary _ _ _ source
  | .binary _ _ _ _ source | .mux _ _ _ _ source | .slice _ _ _ source
  | .zeroExtend _ _ source | .signExtend _ _ source | .concat _ _ _ source
  | .memoryRead _ _ _ source => source

end Expr

structure Register where
  name : String
  width : Nat
  init : Nat
  next : Expr
  source : SourceLocation
  deriving Repr, DecidableEq

structure MemoryWrite where
  port : Nat
  enable : Expr
  address : Expr
  data : Expr
  source : SourceLocation
  deriving Repr, DecidableEq

structure Memory where
  name : String
  addressWidth : Nat
  dataWidth : Nat
  init : List Nat := []
  writes : List MemoryWrite := []
  source : SourceLocation
  deriving Repr, DecidableEq

structure Output where
  name : String
  width : Nat
  value : Expr
  source : SourceLocation
  deriving Repr, DecidableEq

structure InstanceConnection where
  port : String
  signal : String
  width : Nat
  source : SourceLocation
  deriving Repr, DecidableEq, BEq

structure Instance where
  name : String
  moduleName : String
  parameters : List (String × String) := []
  connections : List InstanceConnection
  source : SourceLocation
  deriving Repr, DecidableEq, BEq

structure UnsupportedConstruct where
  kind : String
  detail : String
  source : SourceLocation
  deriving Repr, DecidableEq, BEq

/-- One recognizable source module. `instances` are retained rather than
flattened; `lowerLocalDesign?` handles the module-owned logic and hierarchy
assembly handles child instances separately. -/
structure Module where
  name : String
  ports : List Port
  domains : List ClockDomain
  registers : List Register
  memories : List Memory
  outputs : List Output
  instances : List Instance := []
  unsupported : List UnsupportedConstruct := []
  source : SourceLocation
  deriving Repr, DecidableEq

/-- Exact byte identity supplied by an external frontend adapter.  The
frontend's digest is diagnostic; `identity` remains collision-free inside
Loom because it retains the bytes themselves. -/
structure ArtifactBinding where
  role : String
  path : String
  sha256 : String
  identity : Loom.Artifact.Identity

structure ImportManifest where
  schema : Nat := 1
  frontend : String
  version : String
  invocation : List String
  sources : List ArtifactBinding
  neutralArtifact : ArtifactBinding
  assumptions : List String

namespace ImportManifest

private def sha256Like (digest : String) : Bool :=
  digest.length == 64 && digest.toList.all fun c =>
    c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def validB (manifest : ImportManifest) : Bool :=
  manifest.schema == 1 && !manifest.frontend.isEmpty &&
    !manifest.version.isEmpty && !manifest.invocation.isEmpty &&
    !manifest.sources.isEmpty &&
    Inventory.uniqueB (manifest.sources.map (·.path)) &&
    manifest.sources.all (fun artifact =>
      artifact.role == "source" && !artifact.path.isEmpty &&
        sha256Like artifact.sha256 && artifact.identity.byteCount > 0) &&
    manifest.neutralArtifact.role == "neutral_import_ir" &&
    !manifest.neutralArtifact.path.isEmpty &&
    sha256Like manifest.neutralArtifact.sha256 &&
    manifest.neutralArtifact.identity.byteCount > 0 &&
    !manifest.assumptions.isEmpty

end ImportManifest

structure LoweredExpr where
  width : Nat
  value : Loom.Hw.Expr width

private def failAt {α : Type} (source : SourceLocation) (message : String) :
    Except String α :=
  throw s!"{source.render}: {message}"

private def expectWidth (expected : Nat) (expression : LoweredExpr)
    (source : SourceLocation) : Except String (Loom.Hw.Expr expected) := do
  if equal : expression.width = expected then
    return equal ▸ expression.value
  else
    failAt source s!"expression width {expression.width} does not match expected width {expected}"

private def lowerExpr? : Expr → Except String LoweredExpr
  | .literal width value source => do
      if width == 0 then failAt source "zero-width literal"
      return ⟨width, .lit (BitVec.ofNat width value)⟩
  | .signal width name source => do
      if width == 0 || name.isEmpty then failAt source "invalid signal reference"
      return ⟨width, .reg width name⟩
  | .unary width op value source => do
      let lowered ← lowerExpr? value
      let value ← expectWidth width lowered source
      match op with
      | .bitNot => return ⟨width, .not value⟩
      | .negate => return ⟨width, .sub (.lit (BitVec.ofNat width 0)) value⟩
  | .binary width op left right source => do
      let left ← lowerExpr? left
      let right ← lowerExpr? right
      match op with
      | .equal | .unsignedLessThan | .signedLessThan =>
          if width != 1 then failAt source "comparison result width must be one"
          else
            let leftValue ← expectWidth left.width left source
            let rightValue ← expectWidth left.width right source
            match op with
            | .equal => return ⟨1, .eq leftValue rightValue⟩
            | .unsignedLessThan => return ⟨1, .ult leftValue rightValue⟩
            | .signedLessThan => return ⟨1, .slt leftValue rightValue⟩
            | _ => failAt source "internal comparison lowering error"
      | _ =>
          let left ← expectWidth width left source
          let right ← expectWidth width right source
          let value : Loom.Hw.Expr width := match op with
            | .bitAnd => .and left right
            | .bitOr => .or left right
            | .bitXor => .xor left right
            | .add => .add left right
            | .sub => .sub left right
            | .mul => .mul left right
            | .unsignedDiv => .udiv left right
            | .unsignedRem => .urem left right
            | .shiftLeft => .shl left right
            | .logicalShiftRight => .shr left right
            | _ => .lit 0
          return ⟨width, value⟩
  | .mux width condition yes no source => do
      let condition ← lowerExpr? condition >>= fun value => expectWidth 1 value source
      let yes ← lowerExpr? yes >>= fun value => expectWidth width value source
      let no ← lowerExpr? no >>= fun value => expectWidth width value source
      return ⟨width, .mux condition yes no⟩
  | .slice width value offset source => do
      let value ← lowerExpr? value
      if width == 0 || offset + width > value.width then
        failAt source "slice is empty or outside its operand"
      else return ⟨width, .slice value.value offset width⟩
  | .zeroExtend width value source => do
      let value ← lowerExpr? value
      if width < value.width then failAt source "zero extension narrows its operand"
      else return ⟨width, .zext value.value width⟩
  | .signExtend width value source => do
      let value ← lowerExpr? value
      if width < value.width then failAt source "sign extension narrows its operand"
      else return ⟨width, .sext value.value width⟩
  | .concat width high low source => do
      let high ← lowerExpr? high
      let low ← lowerExpr? low
      if equal : high.width + low.width = width then
        return ⟨width, equal ▸ Loom.Hw.Expr.concat high.value low.value⟩
      else failAt source "concatenation result width is inconsistent"
  | .memoryRead width memory address source => do
      let address ← lowerExpr? address
      if width == 0 || memory.isEmpty then failAt source "invalid memory read"
      return ⟨width, .memRead width memory address.value⟩

private def lowerWrite? (memory : Memory) (write : MemoryWrite) : Except String Act := do
  let enable ← lowerExpr? write.enable >>= fun value => expectWidth 1 value write.source
  let address ← lowerExpr? write.address >>= fun value =>
    expectWidth memory.addressWidth value write.source
  let data ← lowerExpr? write.data >>= fun value =>
    expectWidth memory.dataWidth value write.source
  return .ite enable
    (.memWrite memory.addressWidth memory.dataWidth memory.name write.port address data)
    .skip

private def sequence (actions : List Act) : Act :=
  actions.foldl .seq .skip

private def inputPort (domain : ClockDomain) (port : Port) : Bool :=
  port.direction == .input && port.name != domain.clockPort &&
    domain.reset.port.all (· != port.name)

private def checkModuleBoundary (module : Module) : Except String ClockDomain := do
  unless module.source.validB do failAt module.source "invalid module source location"
  if module.name.isEmpty then failAt module.source "module name is empty"
  match module.unsupported with
  | first :: _ =>
      failAt first.source s!"unsupported imported construct '{first.kind}': {first.detail}"
  | [] => pure ()
  unless module.domains.length == 1 do
    failAt module.source s!"ordinary Design lowering requires exactly one clock domain, found {module.domains.length}"
  let some domain := module.domains[0]?
    | failAt module.source "clock domain disappeared after exact-count check"
  if domain.name.isEmpty || domain.clockPort.isEmpty then
    failAt domain.source "clock domain name/port is empty"
  unless module.ports.any (fun port =>
      port.name == domain.clockPort && port.direction == .input && port.width == 1) do
    failAt domain.source s!"clock port '{domain.clockPort}' is absent or not a one-bit input"
  match domain.reset.kind with
  | .asynchronous | .asynchronousAssertSynchronousRelease =>
      failAt domain.source "asynchronous-reset state must remain behind an ExternalComponent contract"
  | .synchronous =>
      let some resetPort := domain.reset.port
        | failAt domain.source "synchronous reset has no port"
      unless module.ports.any (fun port =>
          port.name == resetPort && port.direction == .input && port.width == 1) do
        failAt domain.source s!"reset port '{resetPort}' is absent or not a one-bit input"
      if resetPort == domain.clockPort then
        failAt domain.source "clock and reset ports must be distinct"
  | .resetless =>
      failAt domain.source "resetless import requires resetless µVerilog emission"
  if module.ports.any (·.direction == .inout) then
    failAt module.source "inout ports require an explicit external pad/tri-state contract"
  if !Inventory.uniqueB (module.ports.map (·.name)) then
    failAt module.source "duplicate port names"
  if !Inventory.uniqueB (module.registers.map (·.name)) then
    failAt module.source "duplicate register names"
  if !Inventory.uniqueB (module.memories.map (·.name)) then
    failAt module.source "duplicate memory names"
  if !Inventory.uniqueB (module.outputs.map (·.name)) then
    failAt module.source "duplicate output drivers"
  return domain

structure LoweredModule where
  design : Design
  edge : Loom.ClockEdge
  clockPort : String
  reset : Reset
  source : SourceLocation

/-- Checked lowering of module-owned logic. Child instances remain in the IR
for hierarchy-preserving assembly and do not get flattened into this Design. -/
def Module.lowerLocalDesign? (module : Module) : Except String LoweredModule := do
  let domain ← checkModuleBoundary module
  let mut regs : List RegDecl := []
  let mut actions : List Act := []
  for register in module.registers do
    if register.width == 0 || register.name.isEmpty then
      failAt register.source "invalid register declaration"
    let next ← lowerExpr? register.next >>= fun value =>
      expectWidth register.width value register.source
    regs := regs ++ [⟨register.name, register.width,
      BitVec.ofNat register.width register.init⟩]
    actions := actions ++ [.write register.width register.name next]
  let mut memories : List MemDecl := []
  for memory in module.memories do
    if memory.name.isEmpty || memory.addressWidth == 0 || memory.dataWidth == 0 then
      failAt memory.source "invalid memory declaration"
    memories := memories ++
      [{ name := memory.name, addrWidth := memory.addressWidth,
         dataWidth := memory.dataWidth,
         init := fun address => BitVec.ofNat memory.dataWidth (memory.init.getD address 0) }]
    for write in memory.writes do
      actions := actions ++ [← lowerWrite? memory write]
  let mut outputs : List CombOutput := []
  for output in module.outputs do
    let value ← lowerExpr? output.value >>= fun value =>
      expectWidth output.width value output.source
    outputs := outputs ++ [⟨output.name, output.width, value⟩]
  let design : Design :=
    { name := module.name
      regs := regs
      mems := memories
      rules := [⟨"imported_next_state", sequence actions⟩]
      inputs := (module.ports.filter (inputPort domain)).map fun port =>
        ⟨port.name, port.width⟩
      outputs := []
      combOutputs := outputs }
  design.emitCheck
  return ⟨design, domain.edge, domain.clockPort, domain.reset, module.source⟩

/-- Build the erased-but-checked component boundary used by dynamic importers.
Nominally typed authored designs should continue to use `DomainComponent`. -/
def Module.lowerComponent? (module : Module) : Except String Component.Sealed := do
  let lowered ← module.lowerLocalDesign?
  let some domain := module.domains[0]?
    | failAt module.source "clock domain disappeared after checked lowering"
  let interface : ComponentInterface :=
    ⟨module.ports.filterMap fun port =>
      if port.name == domain.clockPort || domain.reset.port.any (· == port.name) then none
      else match port.direction with
        | .input => some ⟨port.name, .input, port.width, port.semanticType, domain.name⟩
        | .output => some ⟨port.name, .output, port.width, port.semanticType, domain.name⟩
        | .inout => none⟩
  Component.seal?
    { name := module.name, interface := interface, design := lowered.design }

end Loom.Hw.ImportIR
