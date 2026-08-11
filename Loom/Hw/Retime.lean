-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Notation

/-!
# Retiming: the registered-output split combinator (D17 candidate)

The genuinely-safe first retiming primitive (feedforward cut / registered-
output split), per `Loom/Hw/RETIME_SPEC.md`:

`retimeReg d r w` adds a fresh register `r__pre` (width `w`, same init as
`r`), redirects every rule write to `r` so it targets `r__pre`, and appends
a final copy-back rule `r <= r__pre`. Effect: the value stream on `r` is
delayed by exactly one cycle, and the combinational cone that used to feed
`r` is cut at the new register — the timing win when `r`'s next-expr is the
critical path and `r`'s readers tolerate one cycle of lag (observability
latches, read-back values, counters feeding slow consumers).

## Traversals

`Expr.readsReg` / `Act.readsReg` / `Design.readsReg` are the decidable side
condition: does any rule of `d` *read* `r`? For the write-only /
observability class (`readsReg d r = false`) the retime is a plain forward
simulation with no Burch–Dill flush needed (see `retimeReg_stutter`).

## Soundness

`retimeReg_stutter` (Layer 2 of the spec) is stated and — for the
`readsReg d r = false` class — **proved** below as a genuine
`StutterSimulation`, obtained from a strict `Simulation` (no stutter step is
actually needed in this class) via `Simulation.toStutter`. The abstraction
function reads `r__pre` as the spec's `r` and drops `r__pre`.
-/

namespace Loom.Hw

/-! ## The delayed-register name -/

/-- The fresh pre-register introduced for `r`. Chosen so the combinator is a
pure function of `r`; callers keep `r` free of a literal `"__pre"` suffix. -/
def preName (r : String) : String := r ++ "__pre"

/-! ## `Expr.readsReg` -/

/-- Does the expression read register/input `n` (at any width)? Memory-read
*mem* names are not register reads; the address sub-expression is searched.
The decidable half of the retime side condition. -/
def Expr.readsReg (n : String) : {w : Nat} → Expr w → Bool
  | _, .lit _          => false
  | _, .reg _ m        => m == n
  | _, .memRead _ _ a  => a.readsReg n
  | _, .and a b        => a.readsReg n || b.readsReg n
  | _, .or a b         => a.readsReg n || b.readsReg n
  | _, .xor a b        => a.readsReg n || b.readsReg n
  | _, .not a          => a.readsReg n
  | _, .add a b        => a.readsReg n || b.readsReg n
  | _, .sub a b        => a.readsReg n || b.readsReg n
  | _, .mul a b        => a.readsReg n || b.readsReg n
  | _, .udiv a b       => a.readsReg n || b.readsReg n
  | _, .urem a b       => a.readsReg n || b.readsReg n
  | _, .shl a b        => a.readsReg n || b.readsReg n
  | _, .shr a b        => a.readsReg n || b.readsReg n
  | _, .eq a b         => a.readsReg n || b.readsReg n
  | _, .ult a b        => a.readsReg n || b.readsReg n
  | _, .slt a b        => a.readsReg n || b.readsReg n
  | _, .mux c t f      => c.readsReg n || t.readsReg n || f.readsReg n
  | _, .slice a _ _    => a.readsReg n
  | _, .zext a _       => a.readsReg n
  | _, .sext a _       => a.readsReg n

/-- All register names an expression reads (the traversal underlying
`readsReg`; handy for diagnostics / batch checks). -/
def Expr.readsOf : {w : Nat} → Expr w → List String
  | _, .lit _          => []
  | _, .reg _ m        => [m]
  | _, .memRead _ _ a  => a.readsOf
  | _, .and a b        => a.readsOf ++ b.readsOf
  | _, .or a b         => a.readsOf ++ b.readsOf
  | _, .xor a b        => a.readsOf ++ b.readsOf
  | _, .not a          => a.readsOf
  | _, .add a b        => a.readsOf ++ b.readsOf
  | _, .sub a b        => a.readsOf ++ b.readsOf
  | _, .mul a b        => a.readsOf ++ b.readsOf
  | _, .udiv a b       => a.readsOf ++ b.readsOf
  | _, .urem a b       => a.readsOf ++ b.readsOf
  | _, .shl a b        => a.readsOf ++ b.readsOf
  | _, .shr a b        => a.readsOf ++ b.readsOf
  | _, .eq a b         => a.readsOf ++ b.readsOf
  | _, .ult a b        => a.readsOf ++ b.readsOf
  | _, .slt a b        => a.readsOf ++ b.readsOf
  | _, .mux c t f      => c.readsOf ++ t.readsOf ++ f.readsOf
  | _, .slice a _ _    => a.readsOf
  | _, .zext a _       => a.readsOf
  | _, .sext a _       => a.readsOf

/-! ## `Act.readsReg` -/

/-- Does the action read register/input `n`? Write *targets* are not reads
(only the value/guard/address sub-expressions are searched). -/
def Act.readsReg (n : String) : Act → Bool
  | .skip => false
  | .seq a b => a.readsReg n || b.readsReg n
  | .ite c t e => c.readsReg n || t.readsReg n || e.readsReg n
  | .write _ _ v => v.readsReg n
  | .memWrite _ _ _ _ a d => a.readsReg n || d.readsReg n

/-- Does any rule of the design read register `n`? The decidable side
condition of `retimeReg_stutter`. -/
def Design.readsReg (d : Design) (n : String) : Bool :=
  d.rules.any (fun rule => rule.body.readsReg n)

/-! ## `Act.writesReg` (freshness of `preName r`) -/

/-- Does the action write register `n`? (`memWrite` targets memories, not
registers, so it never writes a register.) -/
def Act.writesReg (n : String) : Act → Bool
  | .skip => false
  | .seq a b => a.writesReg n || b.writesReg n
  | .ite _ t e => t.writesReg n || e.writesReg n
  | .write _ t _ => t == n
  | .memWrite _ _ _ _ _ _ => false

/-- Does any rule of the design write register `n`? Used only to state the
freshness of `preName r` (implied by legality + `DesignWF`). -/
def Design.writesReg (d : Design) (n : String) : Bool :=
  d.rules.any (fun rule => rule.body.writesReg n)

/-! ## The combinator -/

/-- Redirect every write to register `r` (width `w`) so it targets
`preName r` instead. Reads are untouched (this class has none of `r`); mem
writes are untouched. -/
def Act.redirectWrite (r : String) : Act → Act
  | .skip => .skip
  | .seq a b => .seq (a.redirectWrite r) (b.redirectWrite r)
  | .ite c t e => .ite c (t.redirectWrite r) (e.redirectWrite r)
  | .write w' t v => .write w' (if t = r then preName r else t) v
  | .memWrite aw dw m p a d => .memWrite aw dw m p a d

/-- `preName r` is a genuinely fresh name: the `"__pre"` suffix makes it
longer than `r`, so it can never equal `r`. -/
theorem preName_ne (r : String) : preName r ≠ r := by
  intro h
  have : (preName r).length = r.length := by rw [h]
  simp [preName, String.length_append] at this
  exact absurd this (by decide)

/-- The registered-output split. Adds `preName r` (init = `r`'s init),
redirects every write of `r` to it, and appends the copy-back rule
`r <= r__pre`. If `r` is not a declared register of `d`, the combinator is
the identity on registers apart from the (dead) copy-back rule; callers use
`retimeRegOkB` to reject that case. -/
def retimeRegInit (d : Design) (r : String) (w : Nat) : BitVec w :=
  match d.regs.find? (·.name = r) with
  | some rd => if h : rd.width = w then h ▸ rd.init else 0#w
  | none => 0#w

def retimeReg (d : Design) (r : String) (w : Nat) : Design :=
  { d with
    regs := d.regs ++ [⟨preName r, w, retimeRegInit d r w⟩]
    rules := d.rules.map (fun rule => { rule with body := rule.body.redirectWrite r })
             ++ [⟨"__retime_" ++ r, .write w r (.reg w (preName r))⟩] }

/-- Decidable legality guard for `retimeReg d r w`: `r` is a declared
register of width `w`, `preName r` is not already taken, and no rule reads
`r` (the proved-sound class). -/
def retimeRegOkB (d : Design) (r : String) (w : Nat) : Bool :=
  (d.regs.any (fun rd => rd.name == r && rd.width == w)) &&
  (!(d.regs.any (fun rd => rd.name == preName r))) &&
  (!(d.inputs.any (fun i => i.name == preName r))) &&
  (!(d.mems.any (fun m => m.name == preName r))) &&
  (!(d.readsReg r))

/-- The accumulator relation threaded through a cycle: the impl accumulator
`acci` agrees with the spec accumulator `accs` away from `r`/`preName r`,
carries the spec's `r` value in its `preName r` coordinate, and shares
memory. This is exactly `retimeAbs r acci = accs` once `acci` never touches
`r` (which holds throughout a redirected cycle). We phrase it fieldwise to
make the `Act.run`/`foldl` inductions go through. -/
structure RetimeRel (r : String) (acci accs : St) : Prop where
  regs_other : ∀ (n : String) (w : Nat),
    n ≠ r → n ≠ preName r → acci.regs n w = accs.regs n w
  regs_pre : ∀ (w : Nat), acci.regs (preName r) w = accs.regs r w
  mems_eq : acci.mems = accs.mems

/-! ## Soundness for the write-only / observability class

`retimeReg_stutter`: when no rule of `d` reads `r`, the retimed design
forward-simulates `d` through the abstraction that reads `r__pre` as `r`.
No stutter step is actually needed here (it is a strict `Simulation`), but
the theorem is packaged as a `StutterSimulation` because that is the
timing-insensitive interface downstream refinements consume. -/

/-- The abstraction on states: read `preName r` as the spec's `r`, forget
(zero) the `preName r` coordinate itself — it is unobservable at the spec
level, so a canonical value makes the abstraction a genuine function into
spec states — and leave every other register (and all memory) alone.
Zeroing `preName r` is what makes the commuting square hold *at* the
`preName r` coordinate: `d.cycle` never touches it, so both sides read
`0`. -/
def retimeAbs (r : String) (σ : St) : St :=
  { σ with regs := fun n w =>
      if n = preName r then 0#w
      else if n = r then σ.regs (preName r) w
      else σ.regs n w }

/-- `readsReg = false` is exactly "evaluation ignores the `r` coordinate":
any expression that does not read `r` evaluates the same in `σ` and in
`retimeAbs r σ` (which differs from `σ` only at `r`). -/
theorem Expr.eval_retimeAbs (r : String) (σ : St) :
    ∀ {w : Nat} (e : Expr w), e.readsReg r = false → e.readsReg (preName r) = false →
      e.eval (retimeAbs r σ) = e.eval σ := by
  intro w e
  induction e with
  | lit v => intro _ _; rfl
  | reg w m =>
    intro h hp
    simp only [Expr.readsReg, beq_eq_false_iff_ne, ne_eq] at h hp
    show (retimeAbs r σ).regs m w = σ.regs m w
    simp only [retimeAbs]
    rw [if_neg hp, if_neg h]
  | memRead dw m a ih =>
    intro h hp
    simp only [Expr.readsReg] at h hp
    show (retimeAbs r σ).mems m (a.eval (retimeAbs r σ)).toNat dw
       = σ.mems m (a.eval σ).toNat dw
    rw [ih h hp]; rfl
  | and a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show _ &&& _ = _ &&& _; rw [iha h.1 hp.1, ihb h.2 hp.2]
  | or a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show _ ||| _ = _ ||| _; rw [iha h.1 hp.1, ihb h.2 hp.2]
  | xor a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show _ ^^^ _ = _ ^^^ _; rw [iha h.1 hp.1, ihb h.2 hp.2]
  | not a iha =>
    intro h hp; simp only [Expr.readsReg] at h hp
    show ~~~_ = ~~~_; rw [iha h hp]
  | add a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show _ + _ = _ + _; rw [iha h.1 hp.1, ihb h.2 hp.2]
  | sub a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show _ - _ = _ - _; rw [iha h.1 hp.1, ihb h.2 hp.2]
  | mul a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show _ * _ = _ * _; rw [iha h.1 hp.1, ihb h.2 hp.2]
  | udiv a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show _ / _ = _ / _; rw [iha h.1 hp.1, ihb h.2 hp.2]
  | urem a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show _ % _ = _ % _; rw [iha h.1 hp.1, ihb h.2 hp.2]
  | shl a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show a.eval (retimeAbs r σ) <<< (b.eval (retimeAbs r σ)).toNat
       = a.eval σ <<< (b.eval σ).toNat
    rw [iha h.1 hp.1, ihb h.2 hp.2]
  | shr a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show a.eval (retimeAbs r σ) >>> (b.eval (retimeAbs r σ)).toNat
       = a.eval σ >>> (b.eval σ).toNat
    rw [iha h.1 hp.1, ihb h.2 hp.2]
  | eq a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show (if a.eval (retimeAbs r σ) = b.eval (retimeAbs r σ) then _ else _)
       = (if a.eval σ = b.eval σ then _ else _)
    rw [iha h.1 hp.1, ihb h.2 hp.2]
  | ult a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show (if (a.eval (retimeAbs r σ)).ult (b.eval (retimeAbs r σ)) then _ else _)
       = (if (a.eval σ).ult (b.eval σ) then _ else _)
    rw [iha h.1 hp.1, ihb h.2 hp.2]
  | slt a b iha ihb =>
    intro h hp; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show (if (a.eval (retimeAbs r σ)).slt (b.eval (retimeAbs r σ)) then _ else _)
       = (if (a.eval σ).slt (b.eval σ) then _ else _)
    rw [iha h.1 hp.1, ihb h.2 hp.2]
  | mux c t f ihc iht ihf =>
    intro h hp
    simp only [Expr.readsReg, Bool.or_eq_false_iff] at h hp
    show (if c.eval (retimeAbs r σ) = 1#1 then t.eval (retimeAbs r σ) else f.eval (retimeAbs r σ))
       = (if c.eval σ = 1#1 then t.eval σ else f.eval σ)
    rw [ihc h.1.1 hp.1.1, iht h.1.2 hp.1.2, ihf h.2 hp.2]
  | slice a lo width iha =>
    intro h hp; simp only [Expr.readsReg] at h hp
    show (a.eval (retimeAbs r σ)).extractLsb' lo width
       = (a.eval σ).extractLsb' lo width
    rw [iha h hp]
  | zext a w' iha =>
    intro h hp; simp only [Expr.readsReg] at h hp
    show (a.eval (retimeAbs r σ)).setWidth w' = (a.eval σ).setWidth w'
    rw [iha h hp]
  | sext a w' iha =>
    intro h hp; simp only [Expr.readsReg] at h hp
    show (a.eval (retimeAbs r σ)).signExtend w' = (a.eval σ).signExtend w'
    rw [iha h hp]

/-! ### `RegEnv.set` read-back -/

/-- Reading a different name back from `RegEnv.set` sees through it. -/
theorem RegEnv.set_get_ne (ρ : RegEnv) (tgt : String) {wv : Nat} (v : BitVec wv)
    (n : String) (w : Nat) (h : n ≠ tgt) : (ρ.set tgt v) n w = ρ n w := by
  simp only [RegEnv.set, if_neg h]

/-- Reading the written name back at the written width from `RegEnv.set`
returns the written value. -/
theorem RegEnv.set_get_eq (ρ : RegEnv) (tgt : String) {wv : Nat} (v : BitVec wv) :
    (ρ.set tgt v) tgt wv = v := by
  show (if tgt = tgt then (if h : wv = wv then h ▸ v else ρ tgt wv) else ρ tgt wv) = v
  rw [if_pos rfl, dif_pos rfl]

/-- Reading the written name at a *different* width sees the old value.
Combined with `set_get_eq` this fully characterizes a same-name read. -/
theorem RegEnv.set_get_same (ρ : RegEnv) (tgt : String) {wv : Nat} (v : BitVec wv)
    (w : Nat) (hw : wv ≠ w) : (ρ.set tgt v) tgt w = ρ tgt w := by
  show (if tgt = tgt then (if h : wv = w then h ▸ v else ρ tgt w) else ρ tgt w) = ρ tgt w
  rw [if_pos rfl, dif_neg hw]

/-! ### Unwritten coordinates are preserved -/

/-- An action that does not write register `p` leaves the `p` coordinate of
the accumulator untouched (at every width). -/
theorem Act.run_regs_notWrite (σ : St) (p : String) :
    ∀ (a : Act), a.writesReg p = false → ∀ (acc : St) (w : Nat),
      (a.run σ acc).regs p w = acc.regs p w := by
  intro a
  induction a with
  | skip => intro _ acc w; rfl
  | seq a b iha ihb =>
    intro h acc w
    simp only [Act.writesReg, Bool.or_eq_false_iff] at h
    show (b.run σ (a.run σ acc)).regs p w = acc.regs p w
    rw [ihb h.2, iha h.1]
  | ite c t e iht ihe =>
    intro h acc w
    simp only [Act.writesReg, Bool.or_eq_false_iff] at h
    show (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).regs p w = acc.regs p w
    by_cases hc : c.eval σ = 1#1
    · rw [if_pos hc]; exact iht h.1 acc w
    · rw [if_neg hc]; exact ihe h.2 acc w
  | write wv tgt v =>
    intro h acc w
    simp only [Act.writesReg, beq_eq_false_iff_ne, ne_eq] at h
    show (acc.regs.set tgt (v.eval σ)) p w = acc.regs p w
    exact RegEnv.set_get_ne _ _ _ _ _ (Ne.symm h)
  | memWrite aw dw m pt ad dt => intro _ acc w; rfl

/-- Folding a rule list none of which writes `p` preserves the `p`
coordinate. -/
theorem foldl_regs_notWrite (σ : St) (p : String) (rules : List Rule)
    (h : ∀ rule ∈ rules, rule.body.writesReg p = false) (acc : St) (w : Nat) :
    (rules.foldl (fun a rule => rule.body.run σ a) acc).regs p w = acc.regs p w := by
  induction rules generalizing acc with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rw [ih (fun rule hm => h rule (List.mem_cons_of_mem _ hm))]
    exact head.body.run_regs_notWrite σ p (h head (List.mem_cons_self ..)) acc w

/-! ### The per-action square (redirected impl vs spec) -/

/-- Running a redirected action against the pre-cycle impl state `σ`
preserves `RetimeRel` with respect to running the original action against
the spec pre-cycle state `retimeAbs r σ`. Requires the action not to read
`r` (so evaluations agree) and not to write `preName r` (the redirect owns
that coordinate). -/
theorem RetimeRel.run_redirect (r : String) (σ : St)
    {a : Act} (hr : a.readsReg r = false) (hrp : a.readsReg (preName r) = false)
    (hpre : a.writesReg (preName r) = false)
    {acci accs : St} (rel : RetimeRel r acci accs) :
    RetimeRel r ((a.redirectWrite r).run σ acci) (a.run (retimeAbs r σ) accs) := by
  induction a generalizing acci accs with
  | skip => exact rel
  | seq a b iha ihb =>
    simp only [Act.readsReg, Bool.or_eq_false_iff] at hr hrp
    simp only [Act.writesReg, Bool.or_eq_false_iff] at hpre
    exact ihb hr.2 hrp.2 hpre.2 (iha hr.1 hrp.1 hpre.1 rel)
  | ite c t e iht ihe =>
    simp only [Act.readsReg, Bool.or_eq_false_iff] at hr hrp
    simp only [Act.writesReg, Bool.or_eq_false_iff] at hpre
    simp only [Act.redirectWrite, Act.run]
    rw [Expr.eval_retimeAbs r σ c hr.1.1 hrp.1.1]
    by_cases hc : c.eval σ = 1#1
    · rw [if_pos hc, if_pos hc]; exact iht hr.1.2 hrp.1.2 hpre.1 rel
    · rw [if_neg hc, if_neg hc]; exact ihe hr.2 hrp.2 hpre.2 rel
  | write wv tgt v =>
    simp only [Act.readsReg] at hr hrp
    simp only [Act.writesReg, beq_eq_false_iff_ne, ne_eq] at hpre
    -- impl writes `tgt' = (if tgt = r then preName r else tgt)`; spec writes `tgt`.
    have hval : v.eval (retimeAbs r σ) = v.eval σ := Expr.eval_retimeAbs r σ v hr hrp
    show RetimeRel r
      { acci with regs := acci.regs.set (if tgt = r then preName r else tgt) (v.eval σ) }
      { accs with regs := accs.regs.set tgt (v.eval (retimeAbs r σ)) }
    rw [hval]
    by_cases htr : tgt = r
    · -- write to r ↦ write to preName r
      subst htr
      rw [if_pos rfl]
      refine ⟨?_, ?_, rel.mems_eq⟩
      · intro n w hn hnp
        show (acci.regs.set (preName tgt) (v.eval σ)) n w
           = (accs.regs.set tgt (v.eval σ)) n w
        rw [RegEnv.set_get_ne _ _ _ _ _ hnp, RegEnv.set_get_ne _ _ _ _ _ hn]
        exact rel.regs_other n w hn hnp
      · intro w
        show (acci.regs.set (preName tgt) (v.eval σ)) (preName tgt) w
           = (accs.regs.set tgt (v.eval σ)) tgt w
        by_cases hw : wv = w
        · subst hw; rw [RegEnv.set_get_eq, RegEnv.set_get_eq]
        · rw [RegEnv.set_get_same _ _ _ _ hw, RegEnv.set_get_same _ _ _ _ hw]
          exact rel.regs_pre w
    · -- write to some tgt ≠ r; also tgt ≠ preName r (hpre)
      rw [if_neg htr]
      refine ⟨?_, ?_, rel.mems_eq⟩
      · intro n w hn hnp
        show (acci.regs.set tgt (v.eval σ)) n w
           = (accs.regs.set tgt (v.eval σ)) n w
        by_cases hnt : n = tgt
        · subst hnt
          by_cases hw : wv = w
          · subst hw; rw [RegEnv.set_get_eq, RegEnv.set_get_eq]
          · rw [RegEnv.set_get_same _ _ _ _ hw, RegEnv.set_get_same _ _ _ _ hw]
            exact rel.regs_other n w hn hnp
        · rw [RegEnv.set_get_ne _ _ _ _ _ hnt, RegEnv.set_get_ne _ _ _ _ _ hnt]
          exact rel.regs_other n w hn hnp
      · intro w
        show (acci.regs.set tgt (v.eval σ)) (preName r) w
           = (accs.regs.set tgt (v.eval σ)) r w
        rw [RegEnv.set_get_ne _ _ _ _ _ (Ne.symm hpre),
            RegEnv.set_get_ne _ _ _ _ _ (Ne.symm htr)]
        exact rel.regs_pre w
  | memWrite aw dw m p ad dt =>
    simp only [Act.readsReg, Bool.or_eq_false_iff] at hr hrp
    -- both sides write the same memory cell; regs untouched
    have haddr : ad.eval (retimeAbs r σ) = ad.eval σ :=
      Expr.eval_retimeAbs r σ ad hr.1 hrp.1
    have hdata : dt.eval (retimeAbs r σ) = dt.eval σ :=
      Expr.eval_retimeAbs r σ dt hr.2 hrp.2
    show RetimeRel r
      { acci with mems := acci.mems.set m (ad.eval σ).toNat (dt.eval σ) }
      { accs with mems := accs.mems.set m (ad.eval (retimeAbs r σ)).toNat (dt.eval (retimeAbs r σ)) }
    rw [haddr, hdata]
    refine ⟨rel.regs_other, rel.regs_pre, ?_⟩
    show acci.mems.set m (ad.eval σ).toNat (dt.eval σ)
       = accs.mems.set m (ad.eval σ).toNat (dt.eval σ)
    rw [rel.mems_eq]

/-! ### The initial relation and the fold -/

/-- The pre-cycle state relates to its abstraction: `retimeAbs` is exactly
the `RetimeRel` of `σ` with itself in the impl/spec sense. -/
theorem RetimeRel.init (r : String) (σ : St) : RetimeRel r σ (retimeAbs r σ) := by
  refine ⟨?_, ?_, rfl⟩
  · intro n w hn hnp
    show σ.regs n w =
      (if n = preName r then 0#w else if n = r then σ.regs (preName r) w else σ.regs n w)
    rw [if_neg hnp, if_neg hn]
  · intro w
    show σ.regs (preName r) w =
      (if r = preName r then 0#w else if r = r then σ.regs (preName r) w else σ.regs r w)
    rw [if_neg (Ne.symm (preName_ne r)), if_pos rfl]

/-- Folding the redirected rule list from `σ` preserves `RetimeRel` against
folding the original rule list from `retimeAbs r σ`, provided no rule reads
`r` or writes `preName r`. -/
theorem RetimeRel.fold_redirect (r : String) (σ : St)
    (rules : List Rule)
    (hr : ∀ rule ∈ rules, rule.body.readsReg r = false)
    (hrp : ∀ rule ∈ rules, rule.body.readsReg (preName r) = false)
    (hpre : ∀ rule ∈ rules, rule.body.writesReg (preName r) = false)
    {acci accs : St} (rel : RetimeRel r acci accs) :
    RetimeRel r
      ((rules.map (fun rule => { rule with body := rule.body.redirectWrite r })).foldl
        (fun acc rule => rule.body.run σ acc) acci)
      (rules.foldl (fun acc rule => rule.body.run (retimeAbs r σ) acc) accs) := by
  induction rules generalizing acci accs with
  | nil => exact rel
  | cons head tail ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · exact fun rule hm => hr rule (List.mem_cons_of_mem _ hm)
    · exact fun rule hm => hrp rule (List.mem_cons_of_mem _ hm)
    · exact fun rule hm => hpre rule (List.mem_cons_of_mem _ hm)
    · exact rel.run_redirect r σ
        (hr head (List.mem_cons_self ..)) (hrp head (List.mem_cons_self ..))
        (hpre head (List.mem_cons_self ..))

/-! ### Reset commutes with the abstraction -/

/-- A fold of `RegEnv.set`s over a reg-decl list none of which is named `nm`
leaves the `nm` coordinate at its initial value. -/
theorem foldl_reset_notMem (L : List RegDecl) (ρ0 : RegEnv) (nm : String) (w : Nat)
    (h : ∀ rd ∈ L, rd.name ≠ nm) :
    (L.foldl (fun ρ rd => ρ.set rd.name rd.init) ρ0) nm w = ρ0 nm w := by
  induction L generalizing ρ0 with
  | nil => rfl
  | cons rd rest ih =>
    rw [List.foldl_cons, ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    exact RegEnv.set_get_ne _ _ _ _ _ (Ne.symm (h rd (List.mem_cons_self ..)))

/-- Appending one fresh decl to a reset fold: reading the appended name at
its own width returns the appended init; reading any other name is unchanged
from the base fold. -/
theorem foldl_reset_append_pre (L : List RegDecl) (ρ0 : RegEnv)
    (rd : RegDecl) (nm : String) (w : Nat) :
    ((L ++ [rd]).foldl (fun ρ x => ρ.set x.name x.init) ρ0) nm w =
      if _ : nm = rd.name then
        (if hw : rd.width = w then hw ▸ rd.init else
          (L.foldl (fun ρ x => ρ.set x.name x.init) ρ0) nm w)
      else (L.foldl (fun ρ x => ρ.set x.name x.init) ρ0) nm w := by
  rw [List.foldl_append]
  show (RegEnv.set (L.foldl (fun ρ x => ρ.set x.name x.init) ρ0) rd.name rd.init) nm w = _
  by_cases hn : nm = rd.name
  · subst hn
    rw [dif_pos rfl]
    by_cases hw : rd.width = w
    · subst hw; rw [dif_pos rfl, RegEnv.set_get_eq]
    · rw [dif_neg hw, RegEnv.set_get_same _ _ _ _ hw]
  · rw [dif_neg hn, RegEnv.set_get_ne _ _ _ _ _ hn]

/-- In a list whose names are `Nodup`, two elements sharing a name are equal. -/
theorem regName_unique (L : List RegDecl) (hnd : (L.map (·.name)).Nodup)
    (a b : RegDecl) (ha : a ∈ L) (hb : b ∈ L) (hn : a.name = b.name) : a = b := by
  induction L with
  | nil => exact absurd ha List.not_mem_nil
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (hn ▸ List.mem_map_of_mem (f := (·.name)) hb') hnd.1
    · subst hb'; exact absurd (hn.symm ▸ List.mem_map_of_mem (f := (·.name)) ha') hnd.1
    · exact ih hnd.2 ha' hb'

/-- Fold-lookup under distinct register names: the reset fold returns a
declared register's own init at its own width. -/
theorem foldl_reset_get (L : List RegDecl) (ρ0 : RegEnv) (rd0 : RegDecl)
    (hin : rd0 ∈ L) (hnd : (L.map (·.name)).Nodup) :
    (L.foldl (fun ρ x => ρ.set x.name x.init) ρ0) rd0.name rd0.width = rd0.init := by
  induction L generalizing ρ0 with
  | nil => exact absurd hin List.not_mem_nil
  | cons rd rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hin with heq | hmem
    · subst heq
      rw [foldl_reset_notMem rest _ rd0.name rd0.width
          (fun x hx he => hnd.1 (he ▸ List.mem_map_of_mem hx))]
      exact RegEnv.set_get_eq _ _ _
    · exact ih _ hmem hnd.2

/-- If no decl in `L` is named `nm` at width `wr`, the reset fold leaves the
`(nm, wr)` coordinate at its base value. -/
theorem foldl_reset_noWidth (L : List RegDecl) (ρ0 : RegEnv) (nm : String) (wr : Nat)
    (h : ∀ rd ∈ L, rd.name = nm → rd.width ≠ wr) :
    (L.foldl (fun ρ x => ρ.set x.name x.init) ρ0) nm wr = ρ0 nm wr := by
  induction L generalizing ρ0 with
  | nil => rfl
  | cons rd rest ih =>
    rw [List.foldl_cons, ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    show (ρ0.set rd.name rd.init) nm wr = ρ0 nm wr
    by_cases hnm : rd.name = nm
    · subst hnm
      have hw : rd.width ≠ wr := h rd (List.mem_cons_self ..) rfl
      exact RegEnv.set_get_same _ _ _ _ hw
    · exact RegEnv.set_get_ne _ _ _ _ _ (Ne.symm hnm)

/-- `d.reset` at a name declared by no register is `0`. -/
theorem Design.reset_regs_notMem (d : Design) (nm : String) (w : Nat)
    (h : ∀ rd ∈ d.regs, rd.name ≠ nm) : d.reset.regs nm w = 0#w := by
  show (d.regs.foldl (fun (ρ : RegEnv) (x : RegDecl) => ρ.set x.name x.init)
    (fun _ w => 0#w)) nm w = 0#w
  rw [foldl_reset_notMem d.regs _ nm w h]

/-- `d.reset` at a declared name but the *wrong* width is `0`. -/
theorem Design.reset_regs_noWidth (d : Design) (nm : String) (wr : Nat)
    (h : ∀ rd ∈ d.regs, rd.name = nm → rd.width ≠ wr) : d.reset.regs nm wr = 0#wr := by
  show (d.regs.foldl (fun (ρ : RegEnv) (x : RegDecl) => ρ.set x.name x.init)
    (fun _ w => 0#w)) nm wr = 0#wr
  rw [foldl_reset_noWidth d.regs _ nm wr h]

/-! ### The cycle square and the simulation -/

/-- The retimed cycle, read through `retimeAbs`, is exactly the source cycle.
Hypotheses: no rule of `d` reads `r`, no rule writes `preName r` (freshness),
and `preName r ≠ r` (automatic). The copy-back rule folds `preName r` onto
`r`, so the abstraction recovers the spec state exactly. -/
theorem retimeReg_cycle (d : Design) (r : String) (w : Nat)
    (hread : d.readsReg r = false) (hreadp : d.readsReg (preName r) = false)
    (hwrite : d.writesReg (preName r) = false) (σ : St) :
    retimeAbs r ((retimeReg d r w).cycle σ) = d.cycle (retimeAbs r σ) := by
  -- unfold both cycles
  have hr : ∀ rule ∈ d.rules, rule.body.readsReg r = false := by
    intro rule hm
    have := (List.any_eq_false).mp hread rule hm
    simpa using this
  have hrp : ∀ rule ∈ d.rules, rule.body.readsReg (preName r) = false := by
    intro rule hm
    have := (List.any_eq_false).mp hreadp rule hm
    simpa using this
  have hp : ∀ rule ∈ d.rules, rule.body.writesReg (preName r) = false := by
    intro rule hm
    have := (List.any_eq_false).mp hwrite rule hm
    simpa using this
  -- the redirected fold result B and the spec fold result A are RetimeRel-related
  have key := RetimeRel.fold_redirect r σ d.rules hr hrp hp (RetimeRel.init r σ)
  -- name the two fold results B (impl, pre-copyback) and A (spec cycle)
  generalize hBdef :
    (d.rules.map (fun rule => { rule with body := rule.body.redirectWrite r })).foldl
      (fun acc rule => rule.body.run σ acc) σ = B at key
  generalize hAdef :
    d.rules.foldl (fun acc rule => rule.body.run (retimeAbs r σ) acc) (retimeAbs r σ) = A at key
  -- (retimeReg d r w).cycle σ  =  copyback.run σ B. NB the copy-back reads
  -- the *pre-cycle* `preName r` (D9), i.e. `σ.regs (preName r) w` — the
  -- one-cycle-old value. `retimeAbs` overwrites the `r` coordinate with the
  -- *new* `preName r` value (`B.regs (preName r)`), so this old value is
  -- discarded by the abstraction; the copy-back is a no-op under `abs`.
  have hcyc : (retimeReg d r w).cycle σ =
      { B with regs := B.regs.set r (σ.regs (preName r) w) } := by
    show (List.foldl (fun acc rule => rule.body.run σ acc) σ
      ((d.rules.map (fun rule => { rule with body := rule.body.redirectWrite r }))
        ++ [⟨"__retime_" ++ r, .write w r (.reg w (preName r))⟩])) = _
    rw [List.foldl_append, hBdef]
    show (⟨"__retime_" ++ r, Act.write w r (.reg w (preName r))⟩ : Rule).body.run σ B = _
    show { B with regs := B.regs.set r ((Expr.reg w (preName r)).eval σ) } = _
    rfl
  -- d.cycle (retimeAbs r σ) = A
  have hspec : d.cycle (retimeAbs r σ) = A := hAdef
  -- the spec fold leaves preName r at its abstracted (zero) value
  have hApre : ∀ wr, A.regs (preName r) wr = (retimeAbs r σ).regs (preName r) wr := by
    intro wr; rw [← hAdef]
    exact foldl_regs_notWrite (retimeAbs r σ) (preName r) d.rules hp (retimeAbs r σ) wr
  rw [hcyc, hspec]
  -- now: retimeAbs r { B with regs := B.regs.set r (B.regs (preName r) w) } = A
  apply St.mk.injEq _ _ _ _ |>.mpr
  refine ⟨?_, key.mems_eq⟩
  funext n wr
  show (if n = preName r then 0#wr
        else if n = r then (B.regs.set r (σ.regs (preName r) w)) (preName r) wr
        else (B.regs.set r (σ.regs (preName r) w)) n wr) = A.regs n wr
  by_cases hnp : n = preName r
  · -- abstraction zeroes preName r; A never touches it, and its input was 0
    subst hnp
    rw [if_pos rfl, hApre wr]
    show (0#wr : BitVec wr) =
      (if preName r = preName r then 0#wr
       else if preName r = r then σ.regs (preName r) wr else σ.regs (preName r) wr)
    rw [if_pos rfl]
  · rw [if_neg hnp]
    by_cases hnr : n = r
    · rw [if_pos hnr, hnr, RegEnv.set_get_ne _ _ _ _ _ (preName_ne r)]
      -- B.regs (preName r) wr = A.regs r wr : this is regs_pre
      exact key.regs_pre wr
    · rw [if_neg hnr, RegEnv.set_get_ne _ _ _ _ _ hnr]
      exact key.regs_other n wr hnr hnp

/-- The legality bundle for `retimeReg d r w` as `Prop`s (the `retimeRegOkB`
checks, plus register-name `Nodup` from `DesignWF`). These are exactly the
decidable side conditions the combinator ships with. -/
structure RetimeLegal (d : Design) (r : String) (w : Nat) : Prop where
  /-- `r` is a declared register of width `w`. -/
  decl : (⟨r, w, retimeRegInit d r w⟩ : RegDecl) ∈ d.regs
  /-- Register names are distinct (from `DesignWF.regNames`). -/
  nodup : (d.regs.map (·.name)).Nodup
  /-- `preName r` is fresh among the registers. -/
  fresh : ∀ rd ∈ d.regs, rd.name ≠ preName r
  /-- No rule reads `r`. -/
  noRead : d.readsReg r = false
  /-- No rule reads `preName r` (freshness — implied by `DesignWF`). -/
  noReadPre : d.readsReg (preName r) = false
  /-- No rule writes `preName r` (freshness — implied by `DesignWF`). -/
  noWritePre : d.writesReg (preName r) = false

/-- Reset commutes with the abstraction: the retimed reset, abstracted, is
the source reset. `preName r` resets to `r`'s init, which the abstraction
reads back onto `r`; the (unobservable) `preName r` coordinate is zeroed on
both sides. -/
theorem retimeReg_reset (d : Design) (r : String) (w : Nat)
    (leg : RetimeLegal d r w) :
    retimeAbs r (retimeReg d r w).reset = d.reset := by
  apply St.mk.injEq _ _ _ _ |>.mpr
  refine ⟨?_, rfl⟩
  funext n wr
  -- a generic read of the retimed reset at name `nm`, width `wv`; the base
  -- fold `d.regs.foldl set 0` is exactly `d.reset.regs`.
  have hget : ∀ (nm : String) (wv : Nat),
      (retimeReg d r w).reset.regs nm wv =
        if hn : nm = preName r then
          (if hw : w = wv then hw ▸ retimeRegInit d r w else d.reset.regs nm wv)
        else d.reset.regs nm wv := by
    intro nm wv
    exact foldl_reset_append_pre d.regs (fun _ w => 0#w)
      ⟨preName r, w, retimeRegInit d r w⟩ nm wv
  show (if n = preName r then 0#wr
        else if n = r then (retimeReg d r w).reset.regs (preName r) wr
        else (retimeReg d r w).reset.regs n wr) = d.reset.regs n wr
  by_cases hnp : n = preName r
  · subst hnp; rw [if_pos rfl]
    -- d.reset has no preName r ⇒ 0
    show (0#wr : BitVec wr) = d.reset.regs (preName r) wr
    rw [d.reset_regs_notMem (preName r) wr (fun rd hrd => leg.fresh rd hrd)]
  · rw [if_neg hnp]
    by_cases hnr : n = r
    · rw [if_pos hnr, hnr, hget (preName r) wr, dif_pos rfl]
      by_cases hw : w = wr
      · subst hw; rw [dif_pos rfl]
        -- retimeRegInit d r w = r's declared init = d.reset.regs r w
        exact (foldl_reset_get d.regs _ ⟨r, w, retimeRegInit d r w⟩ leg.decl leg.nodup).symm
      · rw [dif_neg hw]
        -- LHS: d.reset at preName r (fresh) = 0; RHS: d.reset at r width wr≠w = 0
        show d.reset.regs (preName r) wr = d.reset.regs r wr
        rw [d.reset_regs_notMem (preName r) wr (fun rd hrd => leg.fresh rd hrd)]
        have hnw : ∀ rd ∈ d.regs, rd.name = r → rd.width ≠ wr := by
          intro rd hrd hrn
          have huniq : rd = ⟨r, w, retimeRegInit d r w⟩ :=
            regName_unique d.regs leg.nodup rd ⟨r, w, retimeRegInit d r w⟩ hrd leg.decl
              (by rw [hrn])
          rw [huniq]; exact hw
        rw [d.reset_regs_noWidth r wr hnw]
    · -- n ≠ r, n ≠ preName r: retimed reset agrees with d.reset
      rw [if_neg hnr, hget n wr, dif_neg hnp]

/-! ### The forward simulation and the stuttering simulation -/

/-- The retimed design forward-simulates the source design through
`retimeAbs` (the write-only / observability class: no rule reads `r`). A
strict `Simulation` — the copy-back cut delays `r` by a cycle, but the
abstraction reads the delayed value back so every impl cycle maps to exactly
one spec cycle. -/
def retimeReg_simulation (d : Design) (r : String) (w : Nat)
    (leg : RetimeLegal d r w) :
    Loom.Simulation d.toTSys (retimeReg d r w).toTSys where
  abs := retimeAbs r
  init_ok := by
    intro s hs
    -- hs : s = (retimeReg d r w).reset ; goal : d.toTSys.init (retimeAbs r s)
    have : s = (retimeReg d r w).reset := hs
    subst this
    show retimeAbs r (retimeReg d r w).reset = d.reset
    exact retimeReg_reset d r w leg
  square := by
    intro s s' hstep
    -- hstep : (retimeReg d r w).cycle s = s' ; goal : d.cycle (abs s) = abs s'
    have : (retimeReg d r w).cycle s = s' := hstep
    show d.cycle (retimeAbs r s) = retimeAbs r s'
    rw [← this]
    exact (retimeReg_cycle d r w leg.noRead leg.noReadPre leg.noWritePre s).symm

/-- **The spec's Layer-2 soundness theorem** (`retimeReg_stutter`): for the
`readsReg d r = false` observability class, the registered-output split is a
`StutterSimulation` of the source design. Obtained from the strict forward
`Simulation` via `Simulation.toStutter`; no genuine stutter step is used
(the class needs no Burch–Dill flush), but the result lands on the
timing-insensitive interface so architectural invariants ("err never set",
one-hot-ness, conservation) transport automatically through
`StutterSimulation.invariant_pullback`. -/
def retimeReg_stutter (d : Design) (r : String) (w : Nat)
    (leg : RetimeLegal d r w) :
    Loom.StutterSimulation d.toTSys (retimeReg d r w).toTSys :=
  (retimeReg_simulation d r w leg).toStutter

/-! ## Ordered plans of selected cuts

`retimeReg` is one verified cut. A usable transform pass needs to select
several cuts and return one refinement witness for the whole result. The plan
below deliberately remains sequential: every cut is checked against the
design produced by the preceding cuts, so freshness and read-side legality
cannot be accidentally checked only against the original source.
-/

/-- One selected registered-output cut. -/
structure RetimeCut where
  name : String
  width : Nat
  deriving Repr, DecidableEq, Inhabited

namespace RetimeCut

/-- Construct a cut from a typed register handle, keeping its width out of the
caller's stringly configuration. -/
def ofReg {w : Nat} (reg : Reg w) : RetimeCut :=
  ⟨reg.name, w⟩

end RetimeCut

/-- Apply selected cuts in order. Later cuts see every register and copy rule
introduced by earlier cuts. -/
def retimePlan : Design → List RetimeCut → Design
  | design, [] => design
  | design, cut :: cuts =>
      retimePlan (retimeReg design cut.name cut.width) cuts

/-- Executable plan guard. As with `retimeRegOkB`, this is the diagnostic
mirror; theorem consumers carry the corresponding `RetimePlanLegal` witness. -/
def retimePlanOkB : Design → List RetimeCut → Bool
  | _, [] => true
  | design, cut :: cuts =>
      retimeRegOkB design cut.name cut.width &&
      retimePlanOkB (retimeReg design cut.name cut.width) cuts

/-- Legality is indexed by the intermediate design at every step. This rules
out a common batch-pass bug where all freshness checks are performed against
the initial design even though earlier transforms have already added names. -/
inductive RetimePlanLegal : (design : Design) → List RetimeCut → Type
  | nil (design : Design) : RetimePlanLegal design []
  | cons {design : Design} {cut : RetimeCut} {cuts : List RetimeCut}
      (head : RetimeLegal design cut.name cut.width)
      (tail : RetimePlanLegal
        (retimeReg design cut.name cut.width) cuts) :
      RetimePlanLegal design (cut :: cuts)

/-- State abstraction induced by a plan, in the reverse order of its concrete
passes, matching composition of their individual simulations. -/
def retimePlanAbs : List RetimeCut → St → St
  | [], state => state
  | cut :: cuts, state => retimeAbs cut.name (retimePlanAbs cuts state)

/-- One proof-carrying refinement for an arbitrary ordered plan of legal
cuts. Invariants transport through the returned simulation in one step. -/
def retimePlan_stutter (design : Design) :
    (cuts : List RetimeCut) → RetimePlanLegal design cuts →
      Loom.StutterSimulation design.toTSys (retimePlan design cuts).toTSys
  | [], .nil _ => Loom.StutterSimulation.refl design.toTSys
  | cut :: cuts, .cons head tail =>
      (retimeReg_stutter design cut.name cut.width head).comp
        (retimePlan_stutter (retimeReg design cut.name cut.width) cuts tail)

/-- The composed simulation exposes the canonical plan abstraction. -/
@[simp] theorem retimePlan_stutter_abs (design : Design)
    (cuts : List RetimeCut) (legal : RetimePlanLegal design cuts) (state : St) :
    (retimePlan_stutter design cuts legal).abs state = retimePlanAbs cuts state := by
  induction cuts generalizing design with
  | nil => cases legal; rfl
  | cons cut cuts ih =>
      cases legal with
      | cons head tail =>
          change retimeAbs cut.name
            ((retimePlan_stutter
              (retimeReg design cut.name cut.width) cuts tail).abs state) =
            retimeAbs cut.name (retimePlanAbs cuts state)
          rw [ih]

end Loom.Hw
