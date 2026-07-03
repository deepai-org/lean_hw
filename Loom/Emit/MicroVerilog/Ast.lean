/-!
# µVerilog: the formalized subset (L4, drafted at task 0.19)

A deliberately minimal synthesizable Verilog subset — flat structural
modules, `assign` continuous assignments, single-clock `always_ff`
registers, explicit memory arrays. No inference-sensitive constructs, no
latches, no tool-dependent idioms: the subset is chosen so that every
serious tool, FPGA or ASIC, agrees on its meaning; where the standard
leaves latitude, the construct is excluded.

Draft status: shape frozen enough for the emitter design; the port/width
discipline tightens with the emission theorem (task 2.4). The subset grows
only by formalized construct, each addition carrying its semantics and its
emission-theorem extension (charter §8, "subset expressiveness"), and the
file is owned by one person so it does not grow by committee.
-/

namespace Loom.Emit.MicroVerilog

/-- A width-indexed combinational expression. Everything is unsigned;
widths are explicit; there is no implicit extension or truncation — the
emitter inserts explicit `zext`/`slice` nodes. -/
inductive Expr : Nat → Type where
  | lit     {w : Nat} (v : BitVec w) : Expr w
  | var     {w : Nat} (name : String) : Expr w   -- port, net, or reg, by name
  | and     {w : Nat} (a b : Expr w) : Expr w
  | or      {w : Nat} (a b : Expr w) : Expr w
  | xor     {w : Nat} (a b : Expr w) : Expr w
  | not     {w : Nat} (a : Expr w) : Expr w
  | add     {w : Nat} (a b : Expr w) : Expr w
  | sub     {w : Nat} (a b : Expr w) : Expr w
  | eq      {w : Nat} (a b : Expr w) : Expr 1
  | lt      {w : Nat} (a b : Expr w) : Expr 1    -- unsigned
  | mux     {w : Nat} (c : Expr 1) (t f : Expr w) : Expr w
  | slice   {w : Nat} (a : Expr w) (lo width : Nat) : Expr width
  | zext    {w : Nat} (a : Expr w) (w' : Nat) : Expr w'
  | concat  {w v : Nat} (a : Expr w) (b : Expr v) : Expr (v + w)

/-- A signal declaration. -/
structure Sig where
  name  : String
  width : Nat
deriving Repr, DecidableEq

/-- One `assign` statement: `assign net = e;`. Nets must be ordered so
each reads only ports, registers, and earlier nets (acyclicity by
construction — combinational loops are unrepresentable). -/
structure Assign where
  lhs : Sig
  rhs : Expr lhs.width

/-- One registered assignment inside the single `always_ff @(posedge clk)`
block: `r <= e;`. -/
structure RegAssign where
  reg  : Sig
  init : BitVec reg.width          -- reset value (synchronous reset)
  next : Expr reg.width

/-- A memory array with one synchronous write port and one asynchronous
read port (the one shape all FPGA and ASIC flows map identically at these
sizes; more ports = a future formalized construct). -/
structure Mem where
  name      : String
  addrWidth : Nat
  dataWidth : Nat
  wrEnable  : Expr 1
  wrAddr    : Expr addrWidth
  wrData    : Expr dataWidth
  rdAddr    : Expr addrWidth
  rdNet     : String               -- net carrying the read value

/-- A flat µVerilog module: one clock, no instances, no parameters. -/
structure Module where
  name    : String
  inputs  : List Sig
  outputs : List Sig
  nets    : List Assign            -- in dependency order
  regs    : List RegAssign
  mems    : List Mem

end Loom.Emit.MicroVerilog
