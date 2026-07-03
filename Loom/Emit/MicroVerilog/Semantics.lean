import Loom.Emit.MicroVerilog.Ast
import Loom.Core.Ts
import Loom.Core.Fun

/-!
# µVerilog semantics (L4, drafted at task 0.19)

A module denotes a synchronous transition system: state = register and
memory contents; one step = evaluate nets in order under the inputs,
then commit register next-values and memory writes. This is the semantics
the single trust axiom (`Axiom.lean`, Phase 2) asserts downstream tools
implement on the subset.

Draft: valuations are name-indexed with widths checked at lookup
(mismatch reads zero); the emission theorem's fine print will replace the
default-zero discipline with well-formedness preconditions discharged by
the emitter.
-/

namespace Loom.Emit.MicroVerilog

/-- A valuation: names to (width-tagged) values. -/
def Env := String → (w : Nat) → BitVec w

def Env.empty : Env := fun _ w => 0#w

def Env.set (ρ : Env) (name : String) {w : Nat} (v : BitVec w) : Env :=
  fun n w' => if n = name then (if h : w = w' then h ▸ v else 0#w') else ρ n w'

/-- Evaluate an expression under a valuation. Total. -/
def Expr.eval (ρ : Env) : {w : Nat} → Expr w → BitVec w
  | _, .lit v => v
  | w, .var n => ρ n w
  | _, .and a b => a.eval ρ &&& b.eval ρ
  | _, .or a b => a.eval ρ ||| b.eval ρ
  | _, .xor a b => a.eval ρ ^^^ b.eval ρ
  | _, .not a => ~~~(a.eval ρ)
  | _, .add a b => a.eval ρ + b.eval ρ
  | _, .sub a b => a.eval ρ - b.eval ρ
  | _, .eq a b => if a.eval ρ = b.eval ρ then 1#1 else 0#1
  | _, .lt a b => if (a.eval ρ).ult (b.eval ρ) then 1#1 else 0#1
  | _, .mux c t f => if c.eval ρ = 1#1 then t.eval ρ else f.eval ρ
  | _, .slice a lo width => (a.eval ρ).extractLsb' lo width
  | _, .zext a w' => (a.eval ρ).setWidth w'
  | _, .concat a b => (b.eval ρ) ++ (a.eval ρ)

/-- Module state: register valuation plus memory contents. -/
structure St (m : Module) where
  regs : Env
  mems : String → Nat → (w : Nat) → BitVec w   -- mem name → address → value

/-- Extend a valuation with the nets, in declaration order. -/
def elabNets (m : Module) (ρ : Env) : Env :=
  (m.nets.foldl (init := ρ) fun ρ a => ρ.set a.lhs.name (a.rhs.eval ρ))

/-- Read nets for memories' async read ports. -/
def withMemReads (m : Module) (σ : St m) (ρ : Env) : Env :=
  m.mems.foldl (init := ρ) fun ρ mem =>
    ρ.set mem.rdNet (σ.mems mem.name ((mem.rdAddr.eval ρ).toNat) mem.dataWidth)

/-- One clock cycle under input valuation `inp`. Nets are elaborated twice
around memory reads (draft simplification: read addresses may not depend
on memory read data — single-level memory pipelining, which is all the
emitter produces). -/
def cycle (m : Module) (inp : Env) (σ : St m) : St m :=
  let ρ0 : Env := fun n w => if m.inputs.any (fun s => s.name = n) then inp n w else σ.regs n w
  let ρ1 := elabNets m ρ0
  let ρ := elabNets m (withMemReads m σ ρ1)
  { regs := m.regs.foldl (init := σ.regs) fun env r =>
      env.set r.reg.name (r.next.eval ρ)
    mems := m.mems.foldl (init := σ.mems) fun f mem =>
      if mem.wrEnable.eval ρ = 1#1 then
        fun n a w =>
          if n = mem.name ∧ a = (mem.wrAddr.eval ρ).toNat ∧ w = mem.dataWidth
          then (mem.wrData.eval ρ).setWidth w
          else f n a w
      else f }

/-- The reset state. -/
def resetSt (m : Module) : St m :=
  { regs := m.regs.foldl (init := Env.empty) fun env r => env.set r.reg.name r.init
    mems := fun _ _ w => 0#w }

/-- A module as a transition system over a fixed input stream policy is
Phase-2 work; the closed (no-input) denotation suffices for the draft. -/
def toTSys (m : Module) : Loom.TSys :=
  Loom.TSys.ofFun (St m) (fun σ => σ = resetSt m) (cycle m Env.empty)

end Loom.Emit.MicroVerilog
