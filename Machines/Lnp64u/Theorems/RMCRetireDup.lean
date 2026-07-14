-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireMove

/-!
# R-MC retirement: `cap_dup` support (NEXTSTEPS tier 2, stage D1)

Free-slot/free-cell priority-encoder bridges: the circuits' foldr-mux
trees against the spec's lowest-index `find?`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## Generic foldr-mux vs `find?` -/

private theorem fold_mux_of_find_some {n w : Nat} (σ : Loom.Hw.St)
    (okE : Fin n → Expr 1) (valE : Fin n → Expr w) (dflt : Expr w)
    (p : Fin n → Bool)
    (hok : ∀ t, ((okE t).eval σ = 1#1) ↔ p t = true) :
    ∀ (L : List (Fin n)) (s : Fin n), L.find? p = some s →
      ((L.foldr (fun t acc => Expr.mux (okE t) (valE t) acc) dflt).eval σ
        = (valE s).eval σ) := by
  intro L
  induction L with
  | nil => intro s hf; exact absurd hf (by simp)
  | cons t L ih =>
      intro s hf
      by_cases hp : p t = true
      · rw [List.find?_cons_of_pos hp] at hf
        injection hf with hf
        subst hf
        show (if (okE t).eval σ = 1#1 then (valE t).eval σ else _) = _
        rw [if_pos (hok t |>.mpr hp)]
      · rw [List.find?_cons_of_neg (by simpa using hp)] at hf
        show (if (okE t).eval σ = 1#1 then (valE t).eval σ else _) = _
        rw [if_neg (fun hc => hp ((hok t).mp hc))]
        exact ih s hf

private theorem fold_mux_of_find_none {n w : Nat} (σ : Loom.Hw.St)
    (okE : Fin n → Expr 1) (valE : Fin n → Expr w) (dflt : Expr w)
    (p : Fin n → Bool)
    (hok : ∀ t, ((okE t).eval σ = 1#1) ↔ p t = true) :
    ∀ L : List (Fin n), L.find? p = none →
      ((L.foldr (fun t acc => Expr.mux (okE t) (valE t) acc) dflt).eval σ
        = dflt.eval σ) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons t L ih =>
      intro hf
      have hnp : ¬ p t = true := by
        have := List.find?_eq_none.mp hf t (List.mem_cons_self ..)
        simpa using this
      have hf' : L.find? p = none := by
        rw [List.find?_cons_of_neg (by simpa using hnp)] at hf
        exact hf
      show (if (okE t).eval σ = 1#1 then (valE t).eval σ else _) = _
      rw [if_neg (fun hc => hnp ((hok t).mp hc))]
      exact ih hf'

/-! ## The free-slot encoder -/

/-- Per-slot freeness test against the abstraction. -/
theorem freeSlotOk_eval (σ : Loom.Hw.St) (E : DomainId) (s : Slot) :
    ((Hw.freeSlotOk E s).eval σ = 1#1)
      ↔ (((((Hw.abs σ).doms E).caps s).isNone
          && (((Hw.abs σ).doms E).slotGen s != genRetired)) = true) := by
  show ((~~~(σ.regs (Hw.dcapV E s) 1) &&&
    ~~~(if σ.regs (Hw.dgen E s) 8 = (255 : BitVec 8)
      then (1#1 : BitVec 1) else 0#1)) = 1#1) ↔ _
  rw [show (((Hw.abs σ).doms E).caps s).isNone
      = !(decide (σ.regs (Hw.dcapV E s) 1 = 1)) from by
    show (if σ.regs (Hw.dcapV E s) 1 = 1 then some _ else none).isNone = _
    by_cases hv : σ.regs (Hw.dcapV E s) 1 = 1
    · rw [if_pos hv, decide_eq_true hv]; rfl
    · rw [if_neg hv, decide_eq_false hv]; rfl]
  rw [show (((Hw.abs σ).doms E).slotGen s != genRetired)
      = !(decide (σ.regs (Hw.dgen E s) 8 = (255 : BitVec 8))) from by
    show (σ.regs (Hw.dgen E s) 8 != (255 : BitVec 8)) = _
    rfl]
  by_cases hv : σ.regs (Hw.dcapV E s) 1 = 1#1
  · by_cases hg : σ.regs (Hw.dgen E s) 8 = (255 : BitVec 8)
    · rw [decide_eq_true (show (σ.regs (Hw.dcapV E s) 1 = 1) from hv),
        decide_eq_true hg, if_pos hg, hv]
      decide
    · rw [decide_eq_true (show (σ.regs (Hw.dcapV E s) 1 = 1) from hv),
        decide_eq_false hg, if_neg hg, hv]
      decide
  · by_cases hg : σ.regs (Hw.dgen E s) 8 = (255 : BitVec 8)
    · rw [decide_eq_false (show ¬(σ.regs (Hw.dcapV E s) 1 = 1) from hv),
        decide_eq_true hg, if_pos hg, bv1_ne_one.mp hv]
      decide
    · rw [decide_eq_false (show ¬(σ.regs (Hw.dcapV E s) 1 = 1) from hv),
        decide_eq_false hg, if_neg hg, bv1_ne_one.mp hv]
      decide

end Machines.Lnp64u.Theorems.RMC
