-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
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

/-- A memory declaration (sync write ports, async read). The number of
write ports is derived by the compiler from the largest `Act.memWrite`
port index the design uses (at least one). -/
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
  | mul     {w : Nat} (a b : Expr w) : Expr w
  /-- Total unsigned division: `a / 0 = 0`. -/
  | udiv    {w : Nat} (a b : Expr w) : Expr w
  /-- Total unsigned remainder: `a % 0 = a`. -/
  | urem    {w : Nat} (a b : Expr w) : Expr w
  | shl     {w : Nat} (a b : Expr w) : Expr w
  | shr     {w : Nat} (a b : Expr w) : Expr w
  | eq      {w : Nat} (a b : Expr w) : Expr 1
  | ult     {w : Nat} (a b : Expr w) : Expr 1
  | slt     {w : Nat} (a b : Expr w) : Expr 1
  | mux     {w : Nat} (c : Expr 1) (t f : Expr w) : Expr w
  | slice   {w : Nat} (a : Expr w) (lo width : Nat) : Expr width
  | zext    {w : Nat} (a : Expr w) (w' : Nat) : Expr w'
  | sext    {w : Nat} (a : Expr w) (w' : Nat) : Expr w'

/-- Concatenate high and low bit vectors. This typed smart constructor lowers
to the primitive algebra, so it adds no separate compiler or certificate case. -/
def Expr.concat {hi lo : Nat} (msbs : Expr hi) (lsbs : Expr lo) : Expr (hi + lo) :=
  .or (.shl (.zext msbs (hi + lo)) (.lit (BitVec.ofNat (hi + lo) lo)))
    (.zext lsbs (hi + lo))

/-- The complete unsigned product. The result is wide enough to retain every
product bit. This is a smart constructor over same-width modular `mul`, so all
existing semantics, compilation, and certification results apply directly. -/
def Expr.umulWide {wa wb : Nat} (a : Expr wa) (b : Expr wb) : Expr (wa + wb) :=
  .mul (.zext a (wa + wb)) (.zext b (wa + wb))

/-- The complete two's-complement signed product. Both operands are
sign-extended to the full result width before the existing modular multiply. -/
def Expr.smulWide {wa wb : Nat} (a : Expr wa) (b : Expr wb) : Expr (wa + wb) :=
  .mul (.sext a (wa + wb)) (.sext b (wa + wb))

/-- Guarded write actions. Sequencing is syntactic only: all reads are
pre-cycle (D9).

`memWrite` carries an explicit write-port index `port` (a design with a
single write per memory per cycle uses port 0 everywhere). The port index
does not affect the EDSL semantics — `Act.run` applies memory writes in
rule order, last write wins — it only tells the compiler which physical
write port of the emitted memory carries this write. The compiler's
correctness precondition (`Compile.MemWriteWF`) requires port indices to
respect the syntactic write order per memory, so the µVerilog port-commit
order (ascending index) reproduces the run order. -/
inductive Act where
  | skip
  | seq (a b : Act)
  | ite (c : Expr 1) (t e : Act)
  | write (w : Nat) (reg : String) (v : Expr w)
  | memWrite (aw dw : Nat) (mem : String) (port : Nat) (addr : Expr aw) (data : Expr dw)

/-- A named atomic rule. -/
structure Rule where
  name : String
  body : Act

/-- An input-port declaration (D15). Inputs are *environment-owned state
coordinates*: expressions read them with the ordinary `Expr.reg`, no rule
may write them (`DesignWF.regWrites` already forbids writes to undeclared
registers, and input names must not be declared as registers), and the
open-system semantics lets the environment drive them each cycle
(`Design.cycleOpen`). A design with `inputs = []` is closed and behaves
exactly as before. -/
structure InputDecl where
  name  : String
  width : Nat

/-- A synchronous design. Closed when `inputs = []` (the default). -/
structure Design where
  name  : String
  regs  : List RegDecl
  mems  : List MemDecl
  /-- Rules run in order each cycle; later writes win (D9). -/
  rules : List Rule
  /-- Input ports (D15): environment-owned coordinates, read via `Expr.reg`. -/
  inputs : List InputDecl := []
  /-- **D37**: memories whose non-zero reset image the target flow provably
  does *not* deliver, and whose loss is a known, recorded exception. Naming
  a memory here records that loss as an accepted implementation assumption.
  `Design.checkTarget` and `Design.emitFor` refuse an unacknowledged loss;
  target-neutral `Design.emit` does not select an implementation profile.
  The acknowledgement lives beside the memory rather than in a downstream
  command line. -/
  ackMemInit : List String := []
  /-- **D19 — declared synchronous-read memories.** Memories this design
  requires to be read only through a register-latch site so an explicit
  implementation profile may classify them as macro candidates.

  This is a *policy* the design owns, not something Loom can infer: whether
  a 512x64 bank must be BRAM depends on how much of the part the rest of
  the design is using. `lnp64mini` names `rf`, `dmem` and `uart_mem`, and
  deliberately omits `rx_mem` (256x8, read combinationally inside a write
  data path — LUTRAM is the right implementation for it).

  The declaration lives beside the memory so `Design.emit` can enforce the
  target-neutral structural obligation at every emission site. -/
  syncReadMems : List String := []
  /-- **D39 — declared observability.** Which registers this design exports
  as `o_<name>` output ports.

  **This field is mandatory** (D39a). Inputs and outputs are both explicit;
  a design that genuinely exports everything says so with
  `outputs := <its regs>.map (·.name)`.

  * `ns` = exactly the declared registers named in `ns`. A register
    absent from the selection is **internal**: it is declared in the module
    body and driven as usual, but it appears at no port, so nothing above
    the design boundary can read it. That is what lets a design hold a key
    in a register (`Machines/CapWalk/Engine.lean`).

  Observability is a property of the design's *interface*, so the selection
  lives here rather than as a flag on `RegDecl`: it composes with D16 (a
  `par`/`connect` may rewrite what the composite exports without touching a
  register declaration), it mirrors µVerilog's own `Module.outs`, and it
  survives `Fin n`-generated register lists.

  **Honesty boundary.** This prevents *architectural* disclosure only — the
  value sits at no module port. It does **not** prevent physical extraction:
  a bitstream can be read back on most FPGAs and a reset value is
  recoverable from it. The claim is "not exported at the interface", never
  "unrecoverable from the device" (`Loom/Hw/OUTPUTS_SPEC.md`).

  A name here that is not a declared register is refused by `Design.emit`
  (`Loom/Hw/Outputs.lean`). -/
  outputs : List String

/-- **D39.** The registers `d` exports, in declaration order: exactly the
ones the design names. This is the single place the selection is interpreted — `Compile.compile` and its `implemented_by` twin both read it,
so they cannot drift apart. -/
def Design.exportedRegs (d : Design) : List RegDecl :=
  d.regs.filter fun r => d.outputs.contains r.name

/-- The names of the exported registers (a sublist of the declared ones). -/
def Design.exportedNames (d : Design) : List String :=
  d.exportedRegs.map (·.name)

end Loom.Hw
