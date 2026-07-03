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

/-- Print a whole module. -/
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
      let en ← pExpr mm.wrEn
      let ad ← pExpr mm.wrAddr
      let dt ← pExpr mm.wrData
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
