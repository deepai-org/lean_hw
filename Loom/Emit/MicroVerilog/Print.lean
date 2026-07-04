import Std.Data.HashMap
import Loom.Emit.MicroVerilog.Ast

/-!
# The µVerilog printer (task 2.3, print half)

Emits the subset in fully explicit form: **every expression node becomes an
explicitly-sized wire** (SSA style). Widths are therefore pinned by wire
declarations everywhere, slices index named wires only, and extensions are
explicit concatenations — no reliance on Verilog's context-determined width
rules, which is precisely the latitude the subset excludes.

The parser (`Parse.lean`) and the round-trip theorem close the loop in task
2.3's second half; until then the printed text is corroborated by
simulator lockstep (`scripts/lockstep_*.sh`).
-/

namespace Loom.Emit.MicroVerilog.Print

open Loom.Emit.MicroVerilog

structure PSt where
  lines : Array String := #[]
  n : Nat := 0

private def emit (s : String) : StateM PSt Unit :=
  modify fun st => { st with lines := st.lines.push s }

private def fresh (w : Nat) (rhs : String) : StateM PSt String := do
  let st ← get
  let name := s!"n{st.n}"
  set { st with
        n := st.n + 1
        lines := st.lines.push s!"  wire [{w-1}:0] {name} = {rhs};" }
  pure name

/-- Print an expression as SSA wires; returns the wire (or identifier)
carrying its value. -/
def pExpr : {w : Nat} → Expr w → StateM PSt String
  | w, .lit v => fresh w s!"{w}'d{v.toNat}"
  | _, .reg _ n => pure n
  | dw, .memRead _ m addr => do
      let a ← pExpr addr
      fresh dw s!"{m}[{a}]"
  | w, .and a b => do fresh w s!"{← pExpr a} & {← pExpr b}"
  | w, .or a b => do fresh w s!"{← pExpr a} | {← pExpr b}"
  | w, .xor a b => do fresh w s!"{← pExpr a} ^ {← pExpr b}"
  | w, .not a => do fresh w s!"~{← pExpr a}"
  | w, .add a b => do fresh w s!"{← pExpr a} + {← pExpr b}"
  | w, .sub a b => do fresh w s!"{← pExpr a} - {← pExpr b}"
  | w, .shl a b => do fresh w s!"{← pExpr a} << {← pExpr b}"
  | w, .shr a b => do fresh w s!"{← pExpr a} >> {← pExpr b}"
  | _, .eq a b => do fresh 1 s!"{← pExpr a} == {← pExpr b}"
  | _, .ult a b => do fresh 1 s!"{← pExpr a} < {← pExpr b}"
  | _, .slt a b => do fresh 1 s!"$signed({← pExpr a}) < $signed({← pExpr b})"
  | w, .mux c t f => do fresh w s!"{← pExpr c} ? {← pExpr t} : {← pExpr f}"
  | _, @Expr.slice _ a lo w' => do
      let x ← pExpr a
      fresh w' s!"{x}[{lo + w' - 1}:{lo}]"
  | w', .zext a _ => do
      let x ← pExpr a
      fresh w' s!"{x}"   -- assignment context zero-extends / truncates
  | w', @Expr.sext w a _ => do
      let x ← pExpr a
      let sb := "{" ++ toString (w' - w) ++ "{" ++ x ++ "[" ++ toString (w-1) ++ "]}}"
      if w' > w then fresh w' ("{" ++ sb ++ ", " ++ x ++ "}")
      else if w' = w then fresh w' s!"{x}"
      else fresh w' s!"{x}[{w'-1}:0]"

/-! ### Fast printing (pointer-memoized + hash-consed; same output subset)

`pExpr` walks the expression as a tree: on modules whose expressions share
nodes (the compiler's memoized build preserves the sharing the source
design's `let`s create), that unfolds the DAG — exponentially in the worst
case (LNP64-µ's pointer-doubling circuits). The implementation below gives
each *structurally distinct* node one wire and reuses its name on every
further occurrence: a pointer-identity memo short-circuits shared nodes,
and `freshM`'s `(width, rendered RHS)` table hash-conses the rest
(separately-built-but-equal nodes, interned constants; since operands are
canonical wire names by the time an RHS is rendered, the merging cascades
bottom-up). Output stays inside the same µVerilog subset (operands are
wire/register identifiers either way), so the parser and the round-trip
checker are unaffected; `parseCheck` (compiled) checks exactly this
printer's output. Kernel-level proofs (the `demo` round trip in
`RoundTrip.lean`) reduce the reference `print` above, which this
implementation replaces for compiled evaluation only. -/

private structure MSt where
  lines : Array String := #[]
  n : Nat := 0
  /-- Pointer-identity memo: node address ↦ wire name. -/
  memo : Std.HashMap USize String := {}
  /-- Structural hash-consing: `(width, rendered RHS)` ↦ wire name. Operand
  names inside an RHS are already canonical (each operand is resolved
  bottom-up before the RHS is rendered), so equal keys mean structurally
  equal subcircuits and the CSE cascades: constants are interned, and any
  node whose operands dedup to the same wires dedups too. -/
  cse : Std.HashMap (Nat × String) String := {}

private def emitM (s : String) : StateM MSt Unit :=
  modify fun st => { st with lines := st.lines.push s }

private def freshM (w : Nat) (rhs : String) : StateM MSt String := do
  if let some nm := (← get).cse[(w, rhs)]? then
    return nm
  let st ← get
  let name := s!"n{st.n}"
  set { st with
        n := st.n + 1
        lines := st.lines.push s!"  wire [{w-1}:0] {name} = {rhs};"
        cse := st.cse.insert (w, rhs) name }
  pure name

mutual

private unsafe def pExprMGo : {w : Nat} → Expr w → StateM MSt String
  | w, .lit v => freshM w s!"{w}'d{v.toNat}"
  | _, .reg _ n => pure n
  | dw, .memRead _ m addr => do
      let a ← pExprM addr
      freshM dw s!"{m}[{a}]"
  | w, .and a b => do freshM w s!"{← pExprM a} & {← pExprM b}"
  | w, .or a b => do freshM w s!"{← pExprM a} | {← pExprM b}"
  | w, .xor a b => do freshM w s!"{← pExprM a} ^ {← pExprM b}"
  | w, .not a => do freshM w s!"~{← pExprM a}"
  | w, .add a b => do freshM w s!"{← pExprM a} + {← pExprM b}"
  | w, .sub a b => do freshM w s!"{← pExprM a} - {← pExprM b}"
  | w, .shl a b => do freshM w s!"{← pExprM a} << {← pExprM b}"
  | w, .shr a b => do freshM w s!"{← pExprM a} >> {← pExprM b}"
  | _, .eq a b => do freshM 1 s!"{← pExprM a} == {← pExprM b}"
  | _, .ult a b => do freshM 1 s!"{← pExprM a} < {← pExprM b}"
  | _, .slt a b => do freshM 1 s!"$signed({← pExprM a}) < $signed({← pExprM b})"
  | w, .mux c t f => do freshM w s!"{← pExprM c} ? {← pExprM t} : {← pExprM f}"
  | _, @Expr.slice _ a lo w' => do
      let x ← pExprM a
      freshM w' s!"{x}[{lo + w' - 1}:{lo}]"
  | w', .zext a _ => do
      let x ← pExprM a
      freshM w' s!"{x}"   -- assignment context zero-extends / truncates
  | w', @Expr.sext w a _ => do
      let x ← pExprM a
      let sb := "{" ++ toString (w' - w) ++ "{" ++ x ++ "[" ++ toString (w-1) ++ "]}}"
      if w' > w then freshM w' ("{" ++ sb ++ ", " ++ x ++ "}")
      else if w' = w then freshM w' s!"{x}"
      else freshM w' s!"{x}[{w'-1}:0]"

private unsafe def pExprM {w : Nat} (e : Expr w) : StateM MSt String := do
  let k := ptrAddrUnsafe e
  if let some nm := (← get).memo[k]? then
    return nm
  let nm ← pExprMGo e
  modify fun st => { st with memo := st.memo.insert k nm }
  return nm

end

private unsafe def printImpl (m : Module) : String := Id.run do
  let header :=
    s!"module {m.name}(\n  input wire clk,\n  input wire rst" ++
    String.join (m.outs.map fun o =>
      s!",\n  output wire [{o.width-1}:0] {o.name}") ++
    "\n);"
  let decls :=
    (m.regs.map fun r => s!"  reg [{r.width-1}:0] {r.name};") ++
    (m.mems.map fun mm =>
      s!"  reg [{mm.dataWidth-1}:0] {mm.name} [0:{2^mm.addrWidth - 1}];")
  let inits := m.mems.flatMap fun mm =>
    ["  initial begin"] ++
    ((List.range (2^mm.addrWidth)).map fun a =>
      s!"    {mm.name}[{a}] = {mm.dataWidth}'d{(mm.init a).toNat};") ++
    ["  end"]
  -- expression wires (each pointer-distinct node printed once)
  let body : MSt := (do
    let mut regNexts : Array (String × String) := #[]
    for r in m.regs do
      let nw ← pExprM r.next
      regNexts := regNexts.push (r.name, nw)
    let mut memPorts : Array (String × String × String × String) := #[]
    for mm in m.mems do
      for p in mm.wrPorts do
        let en ← pExprM p.en
        let ad ← pExprM p.addr
        let dt ← pExprM p.data
        memPorts := memPorts.push (mm.name, en, ad, dt)
    let mut outAssigns : Array String := #[]
    for o in m.outs do
      let v ← pExprM o.val
      outAssigns := outAssigns.push s!"  assign {o.name} = {v};"
    -- the single always block
    emitM "  always @(posedge clk) begin"
    emitM "    if (rst) begin"
    for r in m.regs do
      emitM s!"      {r.name} <= {r.width}'d{r.init.toNat};"
    emitM "    end else begin"
    for (r, nw) in regNexts do
      emitM s!"      {r} <= {nw};"
    for (mn, en, ad, dt) in memPorts do
      emitM s!"      if ({en}) {mn}[{ad}] <= {dt};"
    emitM "    end"
    emitM "  end"
    for a in outAssigns do
      emitM a
    : StateM MSt Unit).run {} |>.2
  let all := [header] ++ decls ++ inits ++ body.lines.toList ++ ["endmodule"]
  return String.intercalate "\n" all

/-- Print a whole module. -/
@[implemented_by printImpl]
def print (m : Module) : String := Id.run do
  let header :=
    s!"module {m.name}(\n  input wire clk,\n  input wire rst" ++
    String.join (m.outs.map fun o =>
      s!",\n  output wire [{o.width-1}:0] {o.name}") ++
    "\n);"
  let decls :=
    (m.regs.map fun r => s!"  reg [{r.width-1}:0] {r.name};") ++
    (m.mems.map fun mm =>
      s!"  reg [{mm.dataWidth-1}:0] {mm.name} [0:{2^mm.addrWidth - 1}];")
  let inits := m.mems.flatMap fun mm =>
    ["  initial begin"] ++
    ((List.range (2^mm.addrWidth)).map fun a =>
      s!"    {mm.name}[{a}] = {mm.dataWidth}'d{(mm.init a).toNat};") ++
    ["  end"]
  -- expression wires
  let body : PSt := (do
    let mut regNexts : List (String × String) := []
    for r in m.regs do
      let nw ← pExpr r.next
      regNexts := regNexts ++ [(r.name, nw)]
    let mut memPorts : List (String × String × String × String) := []
    for mm in m.mems do
      for p in mm.wrPorts do
        let en ← pExpr p.en
        let ad ← pExpr p.addr
        let dt ← pExpr p.data
        memPorts := memPorts ++ [(mm.name, en, ad, dt)]
    let mut outAssigns : List String := []
    for o in m.outs do
      let v ← pExpr o.val
      outAssigns := outAssigns ++ [s!"  assign {o.name} = {v};"]
    -- the single always block
    emit "  always @(posedge clk) begin"
    emit "    if (rst) begin"
    for r in m.regs do
      emit s!"      {r.name} <= {r.width}'d{r.init.toNat};"
    emit "    end else begin"
    for (r, nw) in regNexts do
      emit s!"      {r} <= {nw};"
    for (mn, en, ad, dt) in memPorts do
      emit s!"      if ({en}) {mn}[{ad}] <= {dt};"
    emit "    end"
    emit "  end"
    for a in outAssigns do
      emit a
    : StateM PSt Unit).run {} |>.2
  let all := [header] ++ decls ++ inits ++ body.lines.toList ++ ["endmodule"]
  return String.intercalate "\n" all

end Loom.Emit.MicroVerilog.Print
