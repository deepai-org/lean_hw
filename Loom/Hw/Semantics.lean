-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Syntax
import Loom.Core.Ts

/-!
# EDSL semantics (L3)

One cycle: evaluate every rule against the *pre-cycle* state, accumulating
a write log; commit the log. Deterministic and total; the `TSys` instance
is the object the refinement proofs (A-R, R-MC) and the L2 engines talk
about, and the netlist compiler (C-HW) must preserve.
-/

namespace Loom.Hw

/-- Register valuation (name/width-indexed, like µVerilog's `Env`). -/
def RegEnv := String → (w : Nat) → BitVec w

/-- Memory contents. -/
def MemEnv := String → Nat → (w : Nat) → BitVec w

/-- Design state. -/
structure St where
  regs : RegEnv
  mems : MemEnv

def RegEnv.set (ρ : RegEnv) (name : String) {w : Nat} (v : BitVec w) : RegEnv :=
  fun n w' => if n = name then (if h : w = w' then h ▸ v else ρ n w') else ρ n w'

/-- A memory write touches exactly the written `(name, addr, width)` entry;
entries at other widths are junk (unobservable at declared widths) and are
preserved, mirroring `RegEnv.set` and the µVerilog write-port semantics. -/
def MemEnv.set (μ : MemEnv) (name : String) (a : Nat) {w : Nat} (v : BitVec w) :
    MemEnv :=
  fun n a' w' =>
    if n = name ∧ a' = a then (if h : w = w' then h ▸ v else μ n a' w')
    else μ n a' w'

/-- Evaluate an expression against the pre-cycle state. Total. -/
def Expr.eval (σ : St) : {w : Nat} → Expr w → BitVec w
  | _, .lit v => v
  | w, .reg _ n => σ.regs n w
  | dw, .memRead _ m addr => σ.mems m (addr.eval σ).toNat dw
  | _, .and a b => a.eval σ &&& b.eval σ
  | _, .or a b => a.eval σ ||| b.eval σ
  | _, .xor a b => a.eval σ ^^^ b.eval σ
  | _, .not a => ~~~(a.eval σ)
  | _, .add a b => a.eval σ + b.eval σ
  | _, .sub a b => a.eval σ - b.eval σ
  | _, .shl a b => a.eval σ <<< (b.eval σ).toNat
  | _, .shr a b => a.eval σ >>> (b.eval σ).toNat
  | _, .eq a b => if a.eval σ = b.eval σ then 1#1 else 0#1
  | _, .ult a b => if (a.eval σ).ult (b.eval σ) then 1#1 else 0#1
  | _, .slt a b => if (a.eval σ).slt (b.eval σ) then 1#1 else 0#1
  | _, .mux c t f => if c.eval σ = 1#1 then t.eval σ else f.eval σ
  | _, .slice a lo width => (a.eval σ).extractLsb' lo width
  | _, .zext a w' => (a.eval σ).setWidth w'
  | _, .sext a w' => (a.eval σ).signExtend w'

/-- Run an action: reads from the pre-cycle state `σ`, writes onto the
accumulator `acc` (last write wins — D9). -/
def Act.run (σ : St) : Act → St → St
  | .skip, acc => acc
  | .seq a b, acc => b.run σ (a.run σ acc)
  | .ite c t e, acc => if c.eval σ = 1#1 then t.run σ acc else e.run σ acc
  | .write _ r v, acc => { acc with regs := acc.regs.set r (v.eval σ) }
  | .memWrite _ _ m _ addr data, acc =>
      { acc with mems := acc.mems.set m (addr.eval σ).toNat (data.eval σ) }

/-- One cycle of a design. -/
def Design.cycle (d : Design) (σ : St) : St :=
  d.rules.foldl (fun acc r => r.body.run σ acc) σ

/-- The reset state. -/
def Design.reset (d : Design) : St where
  regs := d.regs.foldl (fun ρ r => ρ.set r.name r.init) (fun _ w => 0#w)
  mems := d.mems.foldl
    (fun μ m => fun n a w =>
      if n = m.name ∧ w = m.dataWidth then (m.init a).setWidth w else μ n a w)
    (fun _ _ w => 0#w)

/-- Run `n` cycles. -/
def Design.run (d : Design) : Nat → St → St
  | 0, σ => σ
  | n + 1, σ => d.run n (d.cycle σ)

/-- A design as a transition system (P2): the concrete side of A-R/R-MC
and the object C-HW preserves. -/
def Design.toTSys (d : Design) : Loom.TSys :=
  Loom.TSys.ofFun St (fun σ => σ = d.reset) d.cycle

end Loom.Hw
