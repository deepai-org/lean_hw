import Loom.Emit.MicroVerilog.Ast
import Loom.Core.Ts

/-!
# µVerilog semantics (L4)

A module denotes a synchronous transition system: state = register and
memory contents; one cycle = evaluate every register's next expression and
every memory's write port against the pre-cycle state, then commit. This is
the semantics the single trust axiom (`Axiom.lean`, task 2.4) asserts
downstream tools implement on the subset.
-/

namespace Loom.Emit.MicroVerilog

/-- Register valuation. -/
def RegEnv := String → (w : Nat) → BitVec w

/-- Memory contents. -/
def MemEnv := String → Nat → (w : Nat) → BitVec w

/-- Module state. -/
structure St where
  regs : RegEnv
  mems : MemEnv

def RegEnv.set (ρ : RegEnv) (name : String) {w : Nat} (v : BitVec w) : RegEnv :=
  fun n w' => if n = name then (if h : w = w' then h ▸ v else 0#w') else ρ n w'

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

/-- One clock cycle (reset deasserted). -/
def Module.cycle (m : Module) (σ : St) : St where
  regs := m.regs.foldl (fun ρ r => ρ.set r.name (r.next.eval σ)) σ.regs
  mems := m.mems.foldl
    (fun μ mem =>
      if mem.wrEn.eval σ = 1#1 then
        fun n a w =>
          if n = mem.name ∧ a = (mem.wrAddr.eval σ).toNat ∧ w = mem.dataWidth
          then (mem.wrData.eval σ).setWidth w
          else μ n a w
      else μ)
    σ.mems

/-- The reset state (what asserting `rst` for one cycle establishes,
together with the `initial` memory contents). -/
def Module.reset (m : Module) : St where
  regs := m.regs.foldl (fun ρ r => ρ.set r.name r.init) (fun _ w => 0#w)
  mems := m.mems.foldl
    (fun μ mem => fun n a w =>
      if n = mem.name ∧ w = mem.dataWidth then (mem.init a).setWidth w
      else μ n a w)
    (fun _ _ w => 0#w)

/-- Run `n` cycles. -/
def Module.run (m : Module) : Nat → St → St
  | 0, σ => σ
  | n + 1, σ => m.run n (m.cycle σ)

/-- A module as a transition system (P2): the right-hand side of the
emission theorem (E-V / A-EV). -/
def Module.toTSys (m : Module) : Loom.TSys :=
  Loom.TSys.ofFun St (fun σ => σ = m.reset) m.cycle

end Loom.Emit.MicroVerilog
