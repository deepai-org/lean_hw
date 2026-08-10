-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Frame
import Loom.Hw.Notation

/-!
# Small, stable hardware proof tactics

`cycle_support` rewrites a register or memory projection of `Design.cycle` to
the footprint-derived list of rules that can write that coordinate. It does
not unfold the other rules, so proof cost follows the property's writer cone.
Typed projection lemmas give `simp` a stable endpoint after that rewrite
without exposing environment-update implementation details.
-/

namespace Loom.Hw

/-! ## Stable simplification surface

These lemmas expose the observable result of typed reads and writes without
requiring a client proof to unfold `Design.cycle`, `RegEnv.set`, or
`MemEnv.set`. They are intentionally about one projected coordinate: after
`cycle_support` removes unrelated rules, this is the normal proof endpoint.
-/

@[simp] theorem Reg.eval_rd {w : Nat} (r : Reg w) (σ : St) :
    r.rd.eval σ = σ.regs r.name w := rfl

@[simp] theorem Reg.run_set_self {w : Nat} (r : Reg w) (v : Expr w)
    (σ acc : St) :
    ((r.set v).run σ acc).regs r.name w = v.eval σ := by
  simp [Reg.set, Act.run, RegEnv.set]

@[simp] theorem Reg.run_set_other {w w' : Nat} (r : Reg w) (v : Expr w)
    (σ acc : St) (r' : Reg w') (h : r'.name ≠ r.name) :
    ((r.set v).run σ acc).regs r'.name w' = acc.regs r'.name w' := by
  simp [Reg.set, Act.run, RegEnv.set, h]

@[simp] theorem Mem.eval_rd {aw dw : Nat} (m : Mem aw dw) (addr : Expr aw)
    (σ : St) :
    (m.rd addr).eval σ = σ.mems m.name (addr.eval σ).toNat dw := rfl

@[simp] theorem Mem.run_write_self {aw dw : Nat} (m : Mem aw dw) (port : Nat)
    (addr : Expr aw) (data : Expr dw) (σ acc : St) :
    ((m.write port addr data).run σ acc).mems
      m.name (addr.eval σ).toNat dw = data.eval σ := by
  simp [Mem.write, Act.run, MemEnv.set]

/-- Project the first cycle-register or cycle-memory occurrence in the goal
onto its computed writer support. -/
macro "cycle_support" : tactic =>
  `(tactic|
    first
    | rw [Loom.Hw.Design.cycle_regs_eq_support]
    | rw [Loom.Hw.Design.cycle_mems_eq_support])

end Loom.Hw
