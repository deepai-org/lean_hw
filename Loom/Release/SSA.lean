-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Emit.MicroVerilog.Ast
import Loom.Release.Rope
import Std.Data.TreeMap

/-!
# Concrete SSA release language

This is the concrete witness language used at the release boundary. It is
deliberately smaller than Verilog and preserves every byte-relevant choice in
the emitted files: identifiers, ordering, widths, literals, and SSA layout.

`render` is structural and line-oriented. `elaborate` independently rebuilds
the intrinsically typed µVerilog AST. Generated release proofs connect bounded
render leaves to exact disk chunks and connect arbitrary witness elaboration to
the already-proved compiler validator.
-/

namespace Loom.Release.SSA

open Loom.Emit.MicroVerilog

/-- Binary operators admitted by the release subset. -/
inductive BinOp where
  | and | or | xor | add | sub | shl | shr | eq | ult
  deriving Repr, DecidableEq

/-- One nonrecursive SSA right-hand side. Operands are previously declared
wire names or source register names. -/
inductive Rhs where
  | lit (width value : Nat)
  | ident (name : String)
  | memRead (mem addr : String)
  | slice (value : String) (hi lo : Nat)
  | not (value : String)
  | bin (op : BinOp) (left right : String)
  | slt (left right : String)
  | mux (cond yes no : String)
  | sext (amount : Nat) (value : String) (signBit : Nat)
  deriving Repr, DecidableEq

/-- A named, explicitly sized SSA wire. -/
structure Wire where
  width : Nat
  name : String
  rhs : Rhs
  deriving Repr, DecidableEq

/-- A register declaration plus reset literal. -/
structure Reg where
  name : String
  width : Nat
  init : Nat
  next : String
  deriving Repr, DecidableEq

/-- One guarded memory write, represented by SSA identifiers. -/
structure Write where
  en : String
  addr : String
  data : String
  deriving Repr, DecidableEq

/-- A memory declaration, full addressable initialization image, and ordered
write ports. -/
structure Mem where
  name : String
  addrWidth : Nat
  dataWidth : Nat
  init : Loom.Release.Rope (List Nat)
  writes : List Write
  deriving Repr, DecidableEq

/-- An output declaration and its driving SSA/register identifier. -/
structure Out where
  name : String
  width : Nat
  value : String
  deriving Repr, DecidableEq

/-- A complete concrete release program. -/
structure Program where
  name : String
  regs : List Reg
  mems : List Mem
  wires : Loom.Release.Rope (List Wire)
  outs : List Out
  deriving Repr, DecidableEq

/-! ## Structural renderer -/

/-- One logical output line represented by already-separated canonical
fragments.  Keeping concatenation out of leaf certificate statements avoids
quadratic kernel reduction on large artifacts; byte flattening happens only
under congruence at the release theorem root. -/
structure Line where
  fragments : List String
  deriving Repr, DecidableEq

def Line.render (line : Line) : String := String.join line.fragments

def BinOp.token : BinOp → String
  | .and => "&"
  | .or => "|"
  | .xor => "^"
  | .add => "+"
  | .sub => "-"
  | .shl => "<<"
  | .shr => ">>"
  | .eq => "=="
  | .ult => "<"

/-- Render one SSA right-hand side, including its terminating semicolon. -/
def Rhs.render : Rhs → String
  | .lit width value => s!"{width}'d{value};"
  | .ident name => s!"{name};"
  | .memRead mem addr => s!"{mem}[{addr}];"
  | .slice value hi lo => s!"{value}[{hi}:{lo}];"
  | .not value => s!"~{value};"
  | .bin op left right => s!"{left} {op.token} {right};"
  | .slt left right => s!"$signed({left}) < $signed({right});"
  | .mux cond yes no => s!"{cond} ? {yes} : {no};"
  | .sext amount value signBit =>
      "{{" ++ toString amount ++ "{" ++ value ++ "[" ++
        toString signBit ++ "]}}, " ++ value ++ "};"

def Rhs.renderLine : Rhs → List String
  | .lit width value => [toString width, "'d", toString value, ";"]
  | .ident name => [name, ";"]
  | .memRead mem addr => [mem, "[", addr, "];" ]
  | .slice value hi lo => [value, "[", toString hi, ":", toString lo, "];" ]
  | .not value => ["~", value, ";"]
  | .bin op left right => [left, " ", op.token, " ", right, ";"]
  | .slt left right => ["$signed(", left, ") < $signed(", right, ");"]
  | .mux cond yes no => [cond, " ? ", yes, " : ", no, ";"]
  | .sext amount value signBit =>
      ["{{", toString amount, "{", value, "[", toString signBit,
        "]}}, ", value, "};"]

def Wire.renderLine (wire : Wire) : Line :=
  ⟨["  wire [", toString (wire.width - 1), ":0] ", wire.name, " = "] ++
    wire.rhs.renderLine⟩

/-- Render one wire declaration. -/
def Wire.render (wire : Wire) : String :=
  wire.renderLine.render

theorem wireRenderTree_factor (tree : Loom.Release.Rope (List Wire)) :
    (tree.map (fun wires => wires.map Wire.renderLine)).map
        (fun lines => lines.map Line.render) =
      tree.map (fun wires => wires.map Wire.render) := by
  rw [Loom.Release.Rope.map_map]
  congr 1
  funext wires
  simp [Function.comp_def, List.map_map, Wire.render]

private def outHeaderLines : List Out → List String
  | [] => []
  | [out] => [s!"  output wire [{out.width - 1}:0] {out.name}"]
  | out :: outs =>
      s!"  output wire [{out.width - 1}:0] {out.name}," ::
        outHeaderLines outs

def headerLines (program : Program) : List String :=
  [s!"module {program.name}(", "  input wire clk,"] ++
  match program.outs with
  | [] => ["  input wire rst", ");"]
  | outs =>
      ["  input wire rst,"] ++ outHeaderLines outs ++ [");"]

def declLines (program : Program) : List String :=
  program.regs.map (fun reg =>
    s!"  reg [{reg.width - 1}:0] {reg.name};") ++
  program.mems.map (fun mem =>
    s!"  reg [{mem.dataWidth - 1}:0] {mem.name} " ++
      s!"[0:{2 ^ mem.addrWidth - 1}];")

/-- Render one bounded memory-initialization leaf at its absolute address
offset. Generated release proofs invoke this independently for each leaf. -/
def Mem.renderInitLines (mem : Mem) (start : Nat) (values : List Nat) :
    List String :=
  ((List.range values.length).zip values).map fun ⟨offset, value⟩ =>
    s!"    {mem.name}[{start + offset}] = {mem.dataWidth}'d{value};"

def alwaysLines (program : Program) : List String :=
  ["  always @(posedge clk) begin", "    if (rst) begin"] ++
  program.regs.map (fun reg =>
    s!"      {reg.name} <= {reg.width}'d{reg.init};") ++
  ["    end else begin"] ++
  program.regs.map (fun reg => s!"      {reg.name} <= {reg.next};") ++
  program.mems.flatMap (fun mem => mem.writes.map fun write =>
    s!"      if ({write.en}) {mem.name}[{write.addr}] <= {write.data};") ++
  ["    end", "  end"]

/-- Header and declarations, kept as one small release rope leaf. -/
def Program.renderPrefix (program : Program) : List String :=
  headerLines program ++ declLines program

/-- Sequential block, output assignments, and module terminator. -/
def Program.renderSuffix (program : Program) : List String :=
  alwaysLines program ++ program.outs.map (fun out =>
    s!"  assign {out.name} = {out.value};") ++ ["endmodule"]

/-- Balanced rendering of one concrete memory initialization image. -/
def Mem.renderTree (mem : Mem) : Loom.Release.Rope (List String) :=
  .node (.leaf ["  initial begin"])
    (.node (mem.init.mapWithOffset mem.renderInitLines 0) (.leaf ["  end"]))

/-- Render memory declarations in source order without flattening their
initialization ropes. -/
def renderMemTrees : List Mem → Loom.Release.Rope (List String)
  | [] => .leaf []
  | [mem] => mem.renderTree
  | mem :: mems => .node mem.renderTree (renderMemTrees mems)

/-- Render without ever constructing a flat full-artifact list. Witness wire
and initialization blocks remain bounded rope leaves all the way to the exact
byte theorem. -/
def Program.renderTree (program : Program) :
    Loom.Release.Rope (List String) :=
  .node (.leaf program.renderPrefix)
    (.node (renderMemTrees program.mems)
      (.node (program.wires.map (fun wires => wires.map Wire.render))
        (.leaf program.renderSuffix)))

/-- Flat logical lines, retained for small examples. Full release theorems use
`renderTree` directly and never normalize this projection. -/
def Program.render (program : Program) : List String :=
  program.renderTree.flattenLists

/-! ## Typed elaborator -/

structure RegHdr where
  name : String
  width : Nat

structure MemHdr where
  name : String
  addrWidth : Nat
  dataWidth : Nat

abbrev Env := Std.TreeMap String (Sigma Expr)

/-- Internal elaborator primitive, exposed so release-certificate soundness can
reason about name resolution without trusting evaluator execution. -/
def resolveAny (regs : List RegHdr) (env : Env)
    (name : String) : Option (Sigma Expr) :=
  match env[name]? with
  | some entry => some entry
  | none =>
      match regs.find? (fun reg => reg.name == name) with
      | some reg => some ⟨reg.width, .reg reg.width name⟩
      | none => none

/-- Width-checked internal name resolution used by the concrete elaborator. -/
def resolveAt (regs : List RegHdr) (env : Env)
    (name : String) (width : Nat) : Option (Expr width) := do
  let ⟨actual, value⟩ ← resolveAny regs env name
  if h : actual = width then pure (h ▸ value) else none

/-- Resolve a concrete SSA/register name at a requested width. This is public
for compact generated certificates, which name intermediate values instead of
serializing their potentially enormous expression trees. -/
def Program.resolve (program : Program) (env : Env) (name : String)
    (width : Nat) : Option (Expr width) :=
  resolveAt (program.regs.map fun reg => ⟨reg.name, reg.width⟩) env name width

def binSame (regs : List RegHdr) (env : Env) (width : Nat)
    (left right : String) (make : Expr width → Expr width → Expr width) :
    Option (Expr width) := do
  pure (make (← resolveAt regs env left width) (← resolveAt regs env right width))

def comparison (regs : List RegHdr) (env : Env) (width : Nat)
    (left right : String)
    (make : {w : Nat} → Expr w → Expr w → Expr 1) : Option (Expr width) := do
  guard (width == 1)
  let ⟨operandWidth, a⟩ ← resolveAny regs env left
  let b ← resolveAt regs env right operandWidth
  if h : (1 : Nat) = width then pure (h ▸ make a b) else none

/-- Elaborate one concrete RHS at its declared result width. -/
def Rhs.elaborate (regs : List RegHdr) (mems : List MemHdr) (env : Env)
    (width : Nat) : Rhs → Option (Expr width)
  | .lit literalWidth value => do
      guard (literalWidth == width)
      pure (.lit (BitVec.ofNat width value))
  | .ident name => do
      let ⟨_, value⟩ ← resolveAny regs env name
      pure (.zext value width)
  | .memRead mem addr => do
      let header ← mems.find? (fun candidate => candidate.name == mem)
      let address ← resolveAt regs env addr header.addrWidth
      if h : header.dataWidth = width then
        pure (h ▸ Expr.memRead header.dataWidth mem address)
      else none
  | .slice value hi lo => do
      guard (lo ≤ hi && hi + 1 - lo == width)
      let ⟨_, input⟩ ← resolveAny regs env value
      pure (.slice input lo width)
  | .not value => do
      pure (.not (← resolveAt regs env value width))
  | .bin op left right =>
      match op with
      | .and => binSame regs env width left right .and
      | .or => binSame regs env width left right .or
      | .xor => binSame regs env width left right .xor
      | .add => binSame regs env width left right .add
      | .sub => binSame regs env width left right .sub
      | .shl => binSame regs env width left right .shl
      | .shr => binSame regs env width left right .shr
      | .eq => comparison regs env width left right (fun a b => .eq a b)
      | .ult => comparison regs env width left right (fun a b => .ult a b)
  | .slt left right =>
      comparison regs env width left right (fun a b => .slt a b)
  | .mux cond yes no => do
      pure (.mux (← resolveAt regs env cond 1) (← resolveAt regs env yes width)
        (← resolveAt regs env no width))
  | .sext amount value signBit => do
      let ⟨inputWidth, input⟩ ← resolveAny regs env value
      guard (signBit + 1 == inputWidth && inputWidth + amount == width &&
        inputWidth < width)
      pure (.sext input width)

def elaborateWires (regs : List RegHdr) (mems : List MemHdr) :
    List Wire → Env → Option Env
  | [], env => some env
  | wire :: wires, env => do
      let value ← wire.rhs.elaborate regs mems env wire.width
      elaborateWires regs mems wires
        (env.insert wire.name ⟨wire.width, value⟩)

def elaborateWireTree (regs : List RegHdr) (mems : List MemHdr) :
    Loom.Release.Rope (List Wire) → Env → Option Env
  | .leaf wires, env => elaborateWires regs mems wires env
  | .node left right, env => do
      let env ← elaborateWireTree regs mems left env
      elaborateWireTree regs mems right env

private def elaborateRegs (headers : List RegHdr) (env : Env) :
    List Reg → Option (List RegDef)
  | [] => some []
  | reg :: regs => do
      let next ← resolveAt headers env reg.next reg.width
      let rest ← elaborateRegs headers env regs
      pure (({ name := reg.name, width := reg.width,
               init := BitVec.ofNat reg.width reg.init,
               next := next } : RegDef) :: rest)

private def elaborateWrites (regs : List RegHdr) (env : Env)
    (aw dw : Nat) : List Write → Option (List (WritePort aw dw))
  | [] => some []
  | write :: writes => do
      let port : WritePort aw dw := {
        en := ← resolveAt regs env write.en 1
        addr := ← resolveAt regs env write.addr aw
        data := ← resolveAt regs env write.data dw }
      pure (port :: (← elaborateWrites regs env aw dw writes))

private def elaborateMems (regs : List RegHdr) (env : Env) :
    List Mem → Option (List MemDef)
  | [] => some []
  | mem :: mems => do
      guard (mem.init.listLength == 2 ^ mem.addrWidth)
      let writes ← elaborateWrites regs env mem.addrWidth mem.dataWidth mem.writes
      let rest ← elaborateMems regs env mems
      pure (({ name := mem.name, addrWidth := mem.addrWidth,
               dataWidth := mem.dataWidth,
               init := fun address =>
                 BitVec.ofNat mem.dataWidth (mem.init.getD address 0),
               wrPorts := writes } : MemDef) :: rest)

private def elaborateOuts (regs : List RegHdr) (env : Env) :
    List Out → Option (List OutDef)
  | [] => some []
  | out :: outs => do
      let value ← resolveAt regs env out.value out.width
      let rest ← elaborateOuts regs env outs
      pure (({ name := out.name, width := out.width,
               val := value } : OutDef) :: rest)

/-- Elaborate an arbitrary concrete witness to the formal µVerilog module.
No generator property is assumed. -/
def Program.elaborateEnv (program : Program) : Option Env := do
  let regs := program.regs.map fun reg => ⟨reg.name, reg.width⟩
  let mems := program.mems.map fun mem => ⟨mem.name, mem.addrWidth, mem.dataWidth⟩
  elaborateWireTree regs mems program.wires {}

/-- Finish elaboration from an already-built SSA environment. Named release
certificates share this environment across all constant-time name lookups. -/
def Program.elaborateWithEnv (program : Program) (env : Env) : Option Module := do
  let regs := program.regs.map fun reg => ⟨reg.name, reg.width⟩
  let regDefs ← elaborateRegs regs env program.regs
  let memDefs ← elaborateMems regs env program.mems
  let outDefs ← elaborateOuts regs env program.outs
  pure ({ name := program.name, regs := regDefs, mems := memDefs,
          outs := outDefs } : Module)

/-- Elaborate an arbitrary concrete witness to the formal µVerilog module.
No generator property is assumed. -/
def Program.elaborate (program : Program) : Option Module := do
  program.elaborateWithEnv (← program.elaborateEnv)

end Loom.Release.SSA
