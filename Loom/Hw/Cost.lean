-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Syntax
import Loom.Hw.MemTarget

/-!
# W6 — the abstract implementation-cost vector

The division of labour, and it is the whole design:

* **Loom proves** that a transformation does not make the abstract cost
  vector worse (componentwise `≤`). That statement is technology-free, so
  it needs no calibration and can never be invalidated by a vendor tool
  release.
* **Calibration maps** that vector to a target's resources and to a
  closure-risk estimate. Those weights are empirical metadata carrying
  provenance, tool version and the design family they were fitted on.
* **Capacity and closure are reported separately.** "It fits" and "the
  tools will close it" are different claims; the second is a calibrated
  threshold on one part with one tool version, never a universal constant.

**This predicts risk, not P&R success.** A cost model can say you are near
the cliff; only a build says which side you landed on. Same honesty
boundary required of any external timing and place-and-route evidence.

## Why a vector and not a number

Collapsing to one scalar needs weights, and weights are exactly the part
that is target-specific and uncertain. Keeping the dimensions separate
means the *provable* half stays exact and the *estimated* half stays
visibly separate from it. The dimensions are the ones that mean the same
thing on both technologies:

| dimension | FPGA reading | ASIC reading |
|---|---|---|
| `stateBits` | flip-flops | sequential cells |
| `bitOps` | LUT-shaped combinational work | combinational gate-equivalents |
| `macroBits` | block RAM bits | SRAM macro bits |
| `softBits` | distributed/LUT RAM + flop arrays | synthesized register files |
| `maxFanout` | routing congestion / duplication pressure | buffer-tree and congestion pressure |

`macroBits` versus `softBits` is a separate dimension rather than a
weighting because the split is where the order-of-magnitude lives:
CapWalk measured **9 523 → 671 LUT on identical logic** (CE9/CE10) purely
by moving banks across it. A model that folded memory into an operation
count would have been wrong by 14× at the one moment it mattered, so the
realization verdict `MemTarget` already computes is consumed here rather
than re-derived.
-/

namespace Loom.Hw

/-- The abstract implementation-cost vector: what Loom can count exactly
from a `Design`, with no target knowledge. -/
structure Cost where
  /-- Register bits + memory bits: state, on any technology. -/
  stateBits : Nat := 0
  /-- Combinational bit-work: the width-weighted count of *distinct*
  (hash-consed) operator nodes — what the emitter turns into wires, not
  what the syntax tree happens to repeat. -/
  bitOps    : Nat := 0
  /-- Memory bits predicted into the target's dedicated macro. -/
  macroBits : Nat := 0
  /-- Memory bits predicted into soft logic (the 14× dimension). -/
  softBits  : Nat := 0
  /-- The largest number of syntactic read sites any one register has:
  duplication/congestion pressure, the thing that goes superlinear. -/
  maxFanout : Nat := 0
  deriving Repr, DecidableEq

namespace Cost

/-- Componentwise order. "This transformation does not make the cost
vector worse" is `Cost.le c' c` — the statement Loom proves, and the only
cost claim that needs no calibration. -/
def le (a b : Cost) : Prop :=
  a.stateBits ≤ b.stateBits ∧ a.bitOps ≤ b.bitOps ∧
  a.macroBits ≤ b.macroBits ∧ a.softBits ≤ b.softBits ∧
  a.maxFanout ≤ b.maxFanout

instance : LE Cost := ⟨le⟩

def leB (a b : Cost) : Bool :=
  a.stateBits ≤ b.stateBits && a.bitOps ≤ b.bitOps &&
  a.macroBits ≤ b.macroBits && a.softBits ≤ b.softBits &&
  a.maxFanout ≤ b.maxFanout

theorem leB_iff (a b : Cost) : leB a b = true ↔ a ≤ b := by
  constructor
  · intro h
    simp only [leB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · intro h
    simp only [leB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2.1⟩, h.2.2.2.2⟩

theorem le_refl (a : Cost) : a ≤ a :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem le_trans {a b c : Cost} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2.1 h₂.2.1,
   Nat.le_trans h₁.2.2.1 h₂.2.2.1, Nat.le_trans h₁.2.2.2.1 h₂.2.2.2.1,
   Nat.le_trans h₁.2.2.2.2 h₂.2.2.2.2⟩

/-- Sum, for composing designs. `maxFanout` maxes rather than adds: it is a
per-signal pressure, not a quantity. -/
def add (a b : Cost) : Cost :=
  { stateBits := a.stateBits + b.stateBits
    bitOps    := a.bitOps + b.bitOps
    macroBits := a.macroBits + b.macroBits
    softBits  := a.softBits + b.softBits
    maxFanout := max a.maxFanout b.maxFanout }

instance : Add Cost := ⟨add⟩

/-- Composition is monotone, so a transformation proved non-worsening on a
part stays non-worsening in the whole. -/
theorem add_le_add {a a' b b' : Cost} (ha : a ≤ a') (hb : b ≤ b') :
    a + b ≤ a' + b' :=
  ⟨Nat.add_le_add ha.1 hb.1, Nat.add_le_add ha.2.1 hb.2.1,
   Nat.add_le_add ha.2.2.1 hb.2.2.1, Nat.add_le_add ha.2.2.2.1 hb.2.2.2.1,
   by
     have h1 : a.maxFanout ≤ max a'.maxFanout b'.maxFanout :=
       Nat.le_trans ha.2.2.2.2 (Nat.le_max_left _ _)
     have h2 : b.maxFanout ≤ max a'.maxFanout b'.maxFanout :=
       Nat.le_trans hb.2.2.2.2 (Nat.le_max_right _ _)
     exact Nat.max_le.mpr ⟨h1, h2⟩⟩

end Cost

/-! ## Counting the vector out of a design

### The tree cost, and why it was wrong

The first version of this file billed combinational work by walking the
expression as a *tree*: `(and a a)` cost twice `a`. That is not what is
emitted. `Loom/Emit/MicroVerilog/Print.lean` gives each **structurally
distinct** node exactly one wire — a pointer-identity memo short-circuits
shared nodes and a `(width, rendered RHS)` table hash-conses the rest — so
a duplicated subexpression becomes ONE wire, and the operand names inside
an RHS are canonical by the time it is rendered, so the merging cascades
bottom-up.

Billing a DAG as a tree is not a conservative approximation, it gets
*signs* wrong on real transformations. Measured (yosys 0.33,
`synth_xilinx`, lnp64mini, `s_ex_body` priority select): the tree cost
says the balanced `priTree` form is +154 679 abstract bitOps worse than
the linear `priChain`, while synthesis says the tree is **357 LUTs
cheaper** — post-CSE netlists of 6 620 nodes / 116 784 width-weighted bits
(tree) against 7 685 / 145 764 (chain). The model had the sign backwards
because it charged the duplicated guard cones that the emitter shares.

`Expr.treeCost` below is kept, clearly labelled, because the tree
recursion is what the tree-builder theorems in `Loom/Hw/CostTransform.lean`
can state exactly, and because `Expr.cost ≤ Expr.treeCost` makes it a
usable upper bound. It is no longer what `Design.cost` reports.

### The hash-consed cost

`Expr.cost` interns every subexpression into a table of **`ENode`s** — a
flat, untyped mirror of `Expr` whose children are table *indices* — and
sums the operator weights over the table. Two subexpressions collapse to
one entry exactly when the emitter would give them one wire, because
`ENode` is a transcription of the emitter's `(width, rendered RHS)` key:

| emitter renders | `ENode` |
|---|---|
| `n` (a register/input needs no wire) | `sig n` |
| `w'd v` | `lit w v` |
| `m[a]` | `mem dw m a` |
| `a & b`, `a \| b`, … | `bin op w a b` |
| `~a` | `neg w a` |
| `a == b`, `a < b`, `$signed(a) < $signed(b)` | `cmp op iw a b` |
| `c ? t : f` | `sel w c t f` |
| `x[lo+w-1:lo]` | `slice a lo w` |
| `{x}` (a `zext`, or a `sext` to its own width) | `rewire w a` |
| `{{k{x[w-1]}}, x}` | `sextend w' w a` |

Three deliberate deviations, all stated rather than hidden:

* **`cmp` keeps its input width.** The emitter's key for a comparison is
  `(1, "a == b")` and drops the operand width; the cost key keeps it,
  because the weight of a comparison *is* its input width. The two keys
  differ only for comparisons whose operands render to the same wire at
  two different widths, i.e. for a design with one name at two widths,
  which well-formedness already refuses.
* **`mul` keeps meaningful operand widths.** Extension wiring is present in
  the emitted DAG, but a full-width `m × n` product must not be costed as an
  `(m+n) × (m+n)` multiplier. The cost key therefore records the widths below
  leading zero/sign extension. This can distinguish multiply nodes whose
  emitted operand wires coincide but whose extension provenance differs, so
  it is a conservative refinement of emitter CSE rather than an
  under-approximation. For ordinary and smart-constructor products with the
  same child expressions, sharing remains identical.
* **Wiring is free.** `slice`/`rewire`/`sextend` get a table entry (they
  are wires in the emitted text, and they matter as *operands* — sharing
  cascades through them) but weight `0`, as before.

Scope: an expression's cost dedups within that expression, and
`Act.cost` dedups across a whole rule body — guards, addresses and written
values share one table, which is where the priority-select duplication
lives. `Design.cost` then *sums over rules*: cross-rule sharing is real in
the emitter but is deliberately not modelled, because summing keeps
`Design.par` exactly additive (`par_bitOps`) and keeps the whole cost
algebra usable. The residual error therefore has a known sign —
`bitOps` over-approximates the emitted node count, never under.
-/

/-- Binary bit-operators corresponding to emitted operators. Multiplication
also carries technology-neutral operand-width cost metadata. -/
inductive EOp where
  | and | or | xor | add | sub | udiv | urem | shl | shr
  /-- A multiply whose operands contain `leftWidth` and `rightWidth`
  meaningful bits. The emitted result still has the enclosing node width. -/
  | mul (leftWidth rightWidth : Nat)
  deriving Repr, DecidableEq

/-- Comparison operators, as the emitter renders them. -/
inductive ECmp where
  | eq | ult | slt
  deriving Repr, DecidableEq

/-- A node of the hash-consed expression DAG: one emitted wire.

Children are *indices* into the intern table, so node equality is shallow
and is exactly the emitter's structural sharing rule (equal operand wires
plus equal rendered operator ⇒ one wire). -/
inductive ENode where
  /-- A literal of width `w` and value `v`. -/
  | lit     (w : Nat) (v : Nat)
  /-- A register/input read: the emitter uses the bare name, at any width. -/
  | sig     (name : String)
  /-- A memory read port. -/
  | mem     (dw : Nat) (name : String) (a : Nat)
  /-- A width-`w` binary bit-operator. -/
  | bin     (op : EOp) (w : Nat) (a b : Nat)
  /-- Bitwise negation at width `w`. -/
  | neg     (w : Nat) (a : Nat)
  /-- A comparison; `iw` is the *input* width, which is what it costs. -/
  | cmp     (op : ECmp) (iw : Nat) (a b : Nat)
  /-- A width-`w` mux. -/
  | sel     (w : Nat) (c t f : Nat)
  /-- A bit-slice `[lo + w - 1 : lo]`. -/
  | slice   (a : Nat) (lo w : Nat)
  /-- A bare re-assignment at width `w` (zero-extend / same-width sext). -/
  | rewire  (w : Nat) (a : Nat)
  /-- A sign-extension from `iw` up to `w`. -/
  | sextend (w : Nat) (iw : Nat) (a : Nat)
  deriving Repr, DecidableEq

/-- Width-weighted work of one emitted node.

Weights are deliberately crude and technology-free: one unit per output
bit for ordinary operators, comparisons cost their *input* width (a 64-bit
`eq` is 64 bits of work producing 1), and a multiply costs the product of
its operands' meaningful widths. Slices/extensions cost nothing because
they are wiring on every technology. Memory *banks* are counted in
`Cost.macroBits`/`Cost.softBits`, not here. Calibration is where a target
says what a unit is worth; it is not this function's business. -/
def ENode.weight : ENode → Nat
  | .lit _ _        => 0
  | .sig _          => 0
  | .mem _ _ _      => 0
  | .bin (.mul wa wb) _ _ _ => wa * wb
  | .bin _ w _ _    => w
  | .neg w _        => w
  | .cmp _ iw _ _   => iw
  | .sel w _ _ _    => w
  | .slice _ _ _    => 0
  | .rewire _ _     => 0
  | .sextend _ _ _  => 0

/-- Total weight of an intern table. -/
def nodesWeight (tbl : List ENode) : Nat :=
  tbl.foldl (fun acc n => acc + n.weight) 0

/-- Position of `n` in `tbl`, counting from `i`. -/
def ENode.find? (n : ENode) : List ENode → Nat → Option Nat
  | [],     _ => none
  | m :: t, i => if m = n then some i else n.find? t (i + 1)

/-- Hash-cons `n` into `tbl`: its index, and the (possibly extended) table.
This is `freshM`'s `cse` lookup, with the table in emission order. -/
def ENode.intern (n : ENode) (tbl : List ENode) : Nat × List ENode :=
  match n.find? tbl 0 with
  | some i => (i, tbl)
  | none   => (tbl.length, tbl ++ [n])

/-- Width that contributes independent information to a multiply operand.
Extension wiring does not turn an `n`-bit operand into an intrinsically wider
multiplier input. Other expressions conservatively use their full width. -/
def Expr.mulOperandWidth : {w : Nat} → Expr w → Nat
  | w, .zext a _ => min w a.mulOperandWidth
  | w, .sext a _ => min w a.mulOperandWidth
  | w, _ => w

/-- Intern every subexpression of `e` into `tbl`, returning `e`'s node
index and the extended table. Mirrors `Print.pExprM` one constructor at a
time. -/
def Expr.hc : {w : Nat} → Expr w → List ENode → Nat × List ENode
  | w, .lit v, t => ENode.intern (.lit w v.toNat) t
  | _, .reg _ n, t => ENode.intern (.sig n) t
  | dw, .memRead _ m a, t =>
      let r := Expr.hc a t
      ENode.intern (.mem dw m r.1) r.2
  | w, .and a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .and w ra.1 rb.1) rb.2
  | w, .or a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .or w ra.1 rb.1) rb.2
  | w, .xor a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .xor w ra.1 rb.1) rb.2
  | w, .not a, t =>
      let ra := Expr.hc a t
      ENode.intern (.neg w ra.1) ra.2
  | w, .add a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .add w ra.1 rb.1) rb.2
  | w, .sub a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .sub w ra.1 rb.1) rb.2
  | w, .mul a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin (.mul a.mulOperandWidth b.mulOperandWidth) w ra.1 rb.1) rb.2
  | w, .udiv a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .udiv w ra.1 rb.1) rb.2
  | w, .urem a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .urem w ra.1 rb.1) rb.2
  | w, .shl a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .shl w ra.1 rb.1) rb.2
  | w, .shr a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.bin .shr w ra.1 rb.1) rb.2
  | _, @Expr.eq w' a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.cmp .eq w' ra.1 rb.1) rb.2
  | _, @Expr.ult w' a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.cmp .ult w' ra.1 rb.1) rb.2
  | _, @Expr.slt w' a b, t =>
      let ra := Expr.hc a t; let rb := Expr.hc b ra.2
      ENode.intern (.cmp .slt w' ra.1 rb.1) rb.2
  | w, .mux c x y, t =>
      let rc := Expr.hc c t; let rx := Expr.hc x rc.2; let ry := Expr.hc y rx.2
      ENode.intern (.sel w rc.1 rx.1 ry.1) ry.2
  | _, @Expr.slice _ a lo w', t =>
      let ra := Expr.hc a t
      ENode.intern (.slice ra.1 lo w') ra.2
  | w', .zext a _, t =>
      let ra := Expr.hc a t
      ENode.intern (.rewire w' ra.1) ra.2
  | w', @Expr.sext w a _, t =>
      let ra := Expr.hc a t
      -- exactly the emitter's three renderings of a sign-extension
      if w < w' then ENode.intern (.sextend w' w ra.1) ra.2
      else if w = w' then ENode.intern (.rewire w' ra.1) ra.2
      else ENode.intern (.slice ra.1 0 w') ra.2

/-- Intern a whole rule body: guards, addresses and written values share
one table, so a guard cone reused by several arms is billed once. -/
def Act.hc : Act → List ENode → List ENode
  | .skip, t => t
  | .seq a b, t => b.hc (a.hc t)
  | .ite c x y, t => y.hc (x.hc ((Expr.hc c t).2))
  | .write _ _ v, t => (Expr.hc v t).2
  | .memWrite _ _ _ _ a d, t => (Expr.hc d (Expr.hc a t).2).2

/-- **Width-weighted combinational work of an expression**, counting each
structurally distinct (hash-consed) node once — the same sharing the
µVerilog emitter performs, so the number tracks what is emitted. -/
def Expr.cost {w : Nat} (e : Expr w) : Nat := nodesWeight (e.hc []).2

/-- Combinational work of an action, including its guards, deduplicated
across the whole rule body. -/
def Act.cost (a : Act) : Nat := nodesWeight (a.hc [])

/-! ### The old tree recursion, kept as an upper bound

`treeCost` is the pre-DAG metric: it bills a shared subexpression once per
syntactic occurrence. `Loom/Hw/CostTransform.lean` proves
`Expr.cost_le_treeCost`, so it remains a sound (sometimes wildly
pessimistic) over-approximation, and the exact tree-shape arithmetic the
balanced-builder theorems need is still available on it. Nothing in
`Design.cost` uses it. -/
def Expr.treeCost {w : Nat} : Expr w → Nat
  | .lit _        => 0
  | .reg _ _      => 0
  | .memRead _ _ a => a.treeCost      -- the bank is counted in Cost.mem*
  | .and a b      => w + a.treeCost + b.treeCost
  | .or a b       => w + a.treeCost + b.treeCost
  | .xor a b      => w + a.treeCost + b.treeCost
  | .not a        => w + a.treeCost
  | .add a b      => w + a.treeCost + b.treeCost
  | .sub a b      => w + a.treeCost + b.treeCost
  | .mul a b      => a.mulOperandWidth * b.mulOperandWidth + a.treeCost + b.treeCost
  | .udiv a b     => w + a.treeCost + b.treeCost
  | .urem a b     => w + a.treeCost + b.treeCost
  | .shl a b      => w + a.treeCost + b.treeCost
  | .shr a b      => w + a.treeCost + b.treeCost
  | @Expr.eq w' a b  => w' + a.treeCost + b.treeCost
  | @Expr.ult w' a b => w' + a.treeCost + b.treeCost
  | @Expr.slt w' a b => w' + a.treeCost + b.treeCost
  | .mux c t f    => w + c.treeCost + t.treeCost + f.treeCost
  | .slice a _ _  => a.treeCost
  | .zext a _     => a.treeCost
  | .sext a _     => a.treeCost

/-- Tree-recursion work of an action. -/
def Act.treeCost : Act → Nat
  | .skip => 0
  | .seq a b => a.treeCost + b.treeCost
  | .ite c t e => c.treeCost + t.treeCost + e.treeCost
  | .write _ _ v => v.treeCost
  | .memWrite _ _ _ _ a d => a.treeCost + d.treeCost

/-- How many syntactic sites read register `n` — the fanout dimension. -/
def Expr.regReads {w : Nat} (n : String) : Expr w → Nat
  | .lit _ => 0
  | .reg _ m => if m = n then 1 else 0
  | .memRead _ _ a => a.regReads n
  | .and a b | .or a b | .xor a b | .add a b | .sub a b | .mul a b
  | .udiv a b | .urem a b
  | .shl a b | .shr a b => a.regReads n + b.regReads n
  | @Expr.eq _ a b | @Expr.ult _ a b | @Expr.slt _ a b =>
      a.regReads n + b.regReads n
  | .not a => a.regReads n
  | .mux c t f => c.regReads n + t.regReads n + f.regReads n
  | .slice a _ _ => a.regReads n
  | .zext a _ => a.regReads n
  | .sext a _ => a.regReads n

def Act.regReads (n : String) : Act → Nat
  | .skip => 0
  | .seq a b => a.regReads n + b.regReads n
  | .ite c t e => c.regReads n + t.regReads n + e.regReads n
  | .write _ _ v => v.regReads n
  | .memWrite _ _ _ _ a d => a.regReads n + d.regReads n

/-- The design's cost vector on a declared target.

Only `macroBits`/`softBits` consult the target, and only through the
realization verdict `MemTarget` already computes for D38 — the same
verdict that refuses undeliverable reset images, so a design cannot be
predicted one way by the area model and another way by the emit gate. -/
def Design.cost (d : Design) (t : MemTarget) : Cost :=
  let regBits := d.regs.foldl (fun acc r => acc + r.width) 0
  let memBits := d.mems.foldl (fun acc m => acc + m.dataWidth * 2 ^ m.addrWidth) 0
  -- per-rule hash-consed node weight, summed: sharing inside a rule body is
  -- modelled exactly, sharing across rules is deliberately not (see above),
  -- which keeps `Design.par` additive and makes `bitOps` an upper bound.
  let ops := d.rules.foldl (fun acc r => acc + r.body.cost) 0
  let macroB := d.mems.foldl (fun acc m =>
    if t.classOf d m == MemClass.macro then acc + m.dataWidth * 2 ^ m.addrWidth else acc) 0
  let fan := d.regs.foldl (fun acc r =>
    max acc (d.rules.foldl (fun a rl => a + rl.body.regReads r.name) 0)) 0
  { stateBits := regBits + memBits
    bitOps    := ops
    macroBits := macroB
    softBits  := memBits - macroB
    maxFanout := fan }

end Loom.Hw
