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
boundary the post-synthesis equivalence checker states about timing and
place-and-route.

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
  /-- Combinational bit-work: the width-weighted operator count. -/
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

/-! ## Counting the vector out of a design -/

/-- Width-weighted combinational work of an expression.

Weights are deliberately crude and technology-free: one unit per output
bit per operator, with comparisons costing their *input* width (a 64-bit
`eq` is 64 bits of work producing 1), and `slice`/`zext`/`sext` costing
nothing because they are wiring on every technology. Calibration is where
a target says what a unit is worth; it is not this function's business. -/
def Expr.cost {w : Nat} : Expr w → Nat
  | .lit _        => 0
  | .reg _ _      => 0
  | .memRead _ _ a => a.cost          -- the bank is counted in Cost.mem*
  | .and a b      => w + a.cost + b.cost
  | .or a b       => w + a.cost + b.cost
  | .xor a b      => w + a.cost + b.cost
  | .not a        => w + a.cost
  | .add a b      => w + a.cost + b.cost
  | .sub a b      => w + a.cost + b.cost
  | .shl a b      => w + a.cost + b.cost
  | .shr a b      => w + a.cost + b.cost
  | @Expr.eq w' a b  => w' + a.cost + b.cost
  | @Expr.ult w' a b => w' + a.cost + b.cost
  | @Expr.slt w' a b => w' + a.cost + b.cost
  | .mux c t f    => w + c.cost + t.cost + f.cost
  | .slice a _ _  => a.cost
  | .zext a _     => a.cost
  | .sext a _     => a.cost

/-- Combinational work of an action, including its guards. -/
def Act.cost : Act → Nat
  | .skip => 0
  | .seq a b => a.cost + b.cost
  | .ite c t e => c.cost + t.cost + e.cost
  | .write _ _ v => v.cost
  | .memWrite _ _ _ _ a d => a.cost + d.cost

/-- How many syntactic sites read register `n` — the fanout dimension. -/
def Expr.regReads {w : Nat} (n : String) : Expr w → Nat
  | .lit _ => 0
  | .reg _ m => if m = n then 1 else 0
  | .memRead _ _ a => a.regReads n
  | .and a b | .or a b | .xor a b | .add a b | .sub a b
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
  let ops := d.rules.foldl (fun acc r => acc + r.body.cost) 0
  let macroB := d.mems.foldl (fun acc m =>
    if t.familyOf d m == MemFamily.bram then acc + m.dataWidth * 2 ^ m.addrWidth else acc) 0
  let fan := d.regs.foldl (fun acc r =>
    max acc (d.rules.foldl (fun a rl => a + rl.body.regReads r.name) 0)) 0
  { stateBits := regBits + memBits
    bitOps    := ops
    macroBits := macroB
    softBits  := memBits - macroB
    maxFanout := fan }

end Loom.Hw
