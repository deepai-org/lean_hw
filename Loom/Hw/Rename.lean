-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Syntax

/-!
# Signal traversals for the compose layer (D16 candidate)

Two pure structural traversals over `Expr`/`Act`, the raw material for the
`Design` combinators in `Loom/Hw/Compose.lean`:

* `mapSignals f` renames every signal name (`.reg`, `.memRead` mem, and on
  the `Act` side the `.write`/`.memWrite` targets) through `f`. This is how
  `Design.prefixed` instantiates a module under a namespace.
* `substReg n w e` replaces reads of register/input `n` at width `w` by the
  expression `e`. A read of `n` at a *different* width is left untouched
  (WF rules the mixed-width case out). On the `Act` side write targets are
  NOT substituted — inputs (the only things `connect` substitutes) are never
  written, so the substitution only rewrites read positions inside the
  written *value* and the guards/addresses.

Both are ordinary total structural recursions; adding them changes no
existing definition. Intended lemma shapes are noted in the docstrings.
-/

namespace Loom.Hw

/-! ## `Expr.mapSignals` -/

/-- Rename every signal name occurring in an expression through `f`
(register reads and memory-read mem names). Structural, width-preserving.

Intended lemma: for `f` injective on the design's names,
`(e.mapSignals f).eval (σ ∘ f) = e.eval σ` — evaluation commutes with a
renaming of the state. -/
def Expr.mapSignals (f : String → String) : {w : Nat} → Expr w → Expr w
  | _, .lit v          => .lit v
  | _, .reg w n        => .reg w (f n)
  | _, .memRead dw m a  => .memRead dw (f m) (a.mapSignals f)
  | _, .and a b        => .and (a.mapSignals f) (b.mapSignals f)
  | _, .or a b         => .or (a.mapSignals f) (b.mapSignals f)
  | _, .xor a b        => .xor (a.mapSignals f) (b.mapSignals f)
  | _, .not a          => .not (a.mapSignals f)
  | _, .add a b        => .add (a.mapSignals f) (b.mapSignals f)
  | _, .sub a b        => .sub (a.mapSignals f) (b.mapSignals f)
  | _, .mul a b        => .mul (a.mapSignals f) (b.mapSignals f)
  | _, .udiv a b       => .udiv (a.mapSignals f) (b.mapSignals f)
  | _, .urem a b       => .urem (a.mapSignals f) (b.mapSignals f)
  | _, .shl a b        => .shl (a.mapSignals f) (b.mapSignals f)
  | _, .shr a b        => .shr (a.mapSignals f) (b.mapSignals f)
  | _, .eq a b         => .eq (a.mapSignals f) (b.mapSignals f)
  | _, .ult a b        => .ult (a.mapSignals f) (b.mapSignals f)
  | _, .slt a b        => .slt (a.mapSignals f) (b.mapSignals f)
  | _, .mux c t g      => .mux (c.mapSignals f) (t.mapSignals f) (g.mapSignals f)
  | _, .slice a lo w   => .slice (a.mapSignals f) lo w
  | _, .zext a w'      => .zext (a.mapSignals f) w'
  | _, .sext a w'      => .sext (a.mapSignals f) w'

/-! ## `Expr.substReg` -/

/-- Replace reads of register/input `n` at width `w` by `e`. A `.reg`
matching the name at a *different* width is left as-is. Memory names are
untouched (only registers/inputs are substituted). Widths line up because
the replacement `e` is provided at the matched width `w` and the syntactic
occurrence is `Expr w`.

Intended lemma: `(e.substReg n w rep).eval σ = e.eval (σ[n@w := rep.eval σ])`
— substitution of an input read by a same-cycle wire equals poking the read
coordinate with the wire's value (the `connect` correctness step). -/
def Expr.substReg (n : String) (w : Nat) (rep : Expr w) :
    {w' : Nat} → Expr w' → Expr w'
  | _, .lit v          => .lit v
  | w', .reg _ m       =>
      if h : m = n ∧ w = w' then
        (by obtain ⟨_, hw⟩ := h; subst hw; exact rep)
      else .reg w' m
  | _, .memRead dw m a  => .memRead dw m (Expr.substReg n w rep a)
  | _, .and a b        => .and (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .or a b         => .or (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .xor a b        => .xor (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .not a          => .not (Expr.substReg n w rep a)
  | _, .add a b        => .add (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .sub a b        => .sub (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .mul a b        => .mul (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .udiv a b       => .udiv (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .urem a b       => .urem (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .shl a b        => .shl (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .shr a b        => .shr (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .eq a b         => .eq (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .ult a b        => .ult (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .slt a b        => .slt (Expr.substReg n w rep a) (Expr.substReg n w rep b)
  | _, .mux c t g      => .mux (Expr.substReg n w rep c) (Expr.substReg n w rep t) (Expr.substReg n w rep g)
  | _, .slice a lo w'' => .slice (Expr.substReg n w rep a) lo w''
  | _, .zext a w''     => .zext (Expr.substReg n w rep a) w''
  | _, .sext a w''     => .sext (Expr.substReg n w rep a) w''

/-! ## `Act.mapSignals` / `Act.substReg` -/

/-- Rename every signal name in an action — write/memWrite *targets* too
(a renamed module writes its renamed registers). -/
def Act.mapSignals (f : String → String) : Act → Act
  | .skip => .skip
  | .seq a b => .seq (a.mapSignals f) (b.mapSignals f)
  | .ite c t e => .ite (c.mapSignals f) (t.mapSignals f) (e.mapSignals f)
  | .write w r v => .write w (f r) (v.mapSignals f)
  | .memWrite aw dw m p a d =>
      .memWrite aw dw (f m) p (a.mapSignals f) (d.mapSignals f)

/-- Substitute an input read `n@w` by `rep` throughout an action. Write
*targets* are NOT rewritten (`connect` only substitutes inputs, which are
never written); only the guards, addresses and written values — the read
positions — are affected. -/
def Act.substReg (n : String) (w : Nat) (rep : Expr w) : Act → Act
  | .skip => .skip
  | .seq a b => .seq (Act.substReg n w rep a) (Act.substReg n w rep b)
  | .ite c t e => .ite (Expr.substReg n w rep c) (Act.substReg n w rep t) (Act.substReg n w rep e)
  | .write w' r v => .write w' r (Expr.substReg n w rep v)
  | .memWrite aw dw m p a d =>
      .memWrite aw dw m p (Expr.substReg n w rep a) (Expr.substReg n w rep d)

/-- Rename all signal names in a rule (name of the rule is left to the
caller — `Design.prefixed` prefixes rule names separately). -/
def Rule.mapSignals (f : String → String) (r : Rule) : Rule :=
  { r with body := r.body.mapSignals f }

end Loom.Hw
