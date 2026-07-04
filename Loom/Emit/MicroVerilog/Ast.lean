-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
/-!
# µVerilog: the formalized subset (L4)

A deliberately minimal synthesizable Verilog subset: one module, one clock,
synchronous reset, `always_ff` registers with explicit next-value
expressions, memory arrays with ordered synchronous write ports and in-expression
asynchronous reads (`mem[addr]` — LUTRAM-shaped at these sizes), and
combinational expressions with no inference-sensitive constructs. No
latches, no tri-states, no tasks, no delays, no multiple drivers: where the
standard leaves latitude, the construct is excluded.

Expressions mirror `Loom.Hw.Expr` deliberately (decision D10): the emitter
is structural, and the netlist IR is introduced as a separate layer only
when optimization passes need one (Rule 2 applied to the boundary). The
subset grows only by formalized construct, each addition carrying its
semantics and its emission-theorem extension; owned by one person.
-/

namespace Loom.Emit.MicroVerilog

/-- Width-indexed combinational expressions. Everything unsigned unless
noted; widths explicit; extension/truncation always explicit. -/
inductive Expr : Nat → Type where
  | lit     {w : Nat} (v : BitVec w) : Expr w
  | reg     (w : Nat) (name : String) : Expr w
  | memRead (dw : Nat) (mem : String) {aw : Nat} (addr : Expr aw) : Expr dw
  | and     {w : Nat} (a b : Expr w) : Expr w
  | or      {w : Nat} (a b : Expr w) : Expr w
  | xor     {w : Nat} (a b : Expr w) : Expr w
  | not     {w : Nat} (a : Expr w) : Expr w
  | add     {w : Nat} (a b : Expr w) : Expr w
  | sub     {w : Nat} (a b : Expr w) : Expr w
  | shl     {w : Nat} (a b : Expr w) : Expr w
  | shr     {w : Nat} (a b : Expr w) : Expr w
  | eq      {w : Nat} (a b : Expr w) : Expr 1
  | ult     {w : Nat} (a b : Expr w) : Expr 1
  | slt     {w : Nat} (a b : Expr w) : Expr 1
  | mux     {w : Nat} (c : Expr 1) (t f : Expr w) : Expr w
  | slice   {w : Nat} (a : Expr w) (lo width : Nat) : Expr width
  | zext    {w : Nat} (a : Expr w) (w' : Nat) : Expr w'
  | sext    {w : Nat} (a : Expr w) (w' : Nat) : Expr w'

/-- A register: `always @(posedge clk) r <= rst ? init : next;`. -/
structure RegDef where
  name  : String
  width : Nat
  init  : BitVec width
  next  : Expr width

/-- One synchronous write port: `if (en) mem[addr] <= data;`. -/
structure WritePort (aw dw : Nat) where
  en   : Expr 1
  addr : Expr aw
  data : Expr dw

/-- A memory array: synchronous write ports, committed in list order (on a
same-cycle address collision the LAST port wins — the ports are emitted as
successive guarded nonblocking assignments to the same array in one
`always @(posedge clk)` block, and IEEE 1800 gives last-update-wins for
multiple nonblocking updates to the same variable in the same time step);
reads appear inside expressions. Initial contents via an `initial` block
(bounded, explicit). -/
structure MemDef where
  name      : String
  addrWidth : Nat
  dataWidth : Nat
  init      : Nat → BitVec dataWidth
  wrPorts   : List (WritePort addrWidth dataWidth)

/-- An observability output port (a named combinational view). -/
structure OutDef where
  name  : String
  width : Nat
  val   : Expr width

/-- A flat µVerilog module: ports are `clk`, `rst`, and the outputs. -/
structure Module where
  name : String
  regs : List RegDef
  mems : List MemDef
  outs : List OutDef

end Loom.Emit.MicroVerilog
