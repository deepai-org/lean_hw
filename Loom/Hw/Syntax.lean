/-!
# The hardware EDSL: expressions, actions, rules, designs (L3)

Rule-based synchronous designs (Hw/DESIGN.md). v1 discipline (decision D9):
every read observes the *pre-cycle* state; writes commit at cycle end;
across the ordered rule list, the last write to a signal wins — exactly
nonblocking-assignment semantics, mapping 1:1 onto netlist register-input
mux trees. Kôika-style intra-cycle ports arrive only with a consuming core
(Rule 2).

Name-based signals with widths checked at evaluation (and a decidable `WF`
for the compiler); intrinsic typing revisited if the C-HW proof demands it
— recorded in DESIGN.md.
-/

namespace Loom.Hw

/-- A register declaration with reset value. -/
structure RegDecl where
  name  : String
  width : Nat
  init  : BitVec width

/-- A memory declaration (one sync write port, async read). -/
structure MemDecl where
  name      : String
  addrWidth : Nat
  dataWidth : Nat
  /-- Initial contents (ROMs carry their image; RAMs are zero). -/
  init      : Nat → BitVec dataWidth

/-- Width-indexed combinational expressions over the pre-cycle state. -/
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

/-- Guarded write actions. Sequencing is syntactic only: all reads are
pre-cycle (D9). -/
inductive Act where
  | skip
  | seq (a b : Act)
  | ite (c : Expr 1) (t e : Act)
  | write (w : Nat) (reg : String) (v : Expr w)
  | memWrite (aw dw : Nat) (mem : String) (addr : Expr aw) (data : Expr dw)

/-- A named atomic rule. -/
structure Rule where
  name : String
  body : Act

/-- A closed synchronous design. -/
structure Design where
  name  : String
  regs  : List RegDecl
  mems  : List MemDecl
  /-- Rules run in order each cycle; later writes win (D9). -/
  rules : List Rule

end Loom.Hw
