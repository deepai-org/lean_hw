-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Footprint
import Loom.Hw.ReadsOk

/-!
# Frame rules (PLATONIC W2)

`Footprint.lean` has the *write* side: an action that does not write `(rn, w)`
leaves that entry alone. That bounds what a rule can disturb.

Missing was the *read* side, which is the half that makes proof cost scale with
a property's dependency cone: **an expression cannot see state outside its own
footprint.** With both halves, a property about register `X` needs only the
rules that write `X`, evaluated against only the state those rules read — the
rest of the design is framed out instead of being carried through the proof.

The footprint is `Expr.readSites` from W1.1 (`ReadsOk.lean`), so the same
syntactic analysis that gates emission is the one the proofs quantify over;
there is no second notion of "what this expression depends on" to keep in sync.

Memories are approximated by *name and data width*, not by address: an
expression's address operand is dynamic, so `readSites` cannot name the cell.
`AgreeOn` therefore demands agreement at every address of a read memory. That
is sound and is what a syntactic footprint can honestly promise; a sharper
address-level footprint would need the address to be a proven-constant, which
is a separate (and much more specialised) analysis.
-/

namespace Loom.Hw

/-- Two states agree on a footprint: on the listed register entries, and at
*every* address of the listed memories (see the note above on why memories are
name-and-width rather than address-precise). -/
def St.AgreeOn (rs ms : List (String × Nat)) (σ τ : St) : Prop :=
  (∀ n w, (n, w) ∈ rs → σ.regs n w = τ.regs n w) ∧
  (∀ m w, (m, w) ∈ ms → ∀ a, σ.mems m a w = τ.mems m a w)

theorem St.AgreeOn.mono {rs ms rs' ms' : List (String × Nat)} {σ τ : St}
    (hr : ∀ x, x ∈ rs' → x ∈ rs) (hm : ∀ x, x ∈ ms' → x ∈ ms)
    (h : St.AgreeOn rs ms σ τ) : St.AgreeOn rs' ms' σ τ :=
  ⟨fun n w hn => h.1 n w (hr _ hn), fun m w hmw => h.2 m w (hm _ hmw)⟩

theorem St.AgreeOn.append_left {rs ms rs' ms' : List (String × Nat)} {σ τ : St}
    (h : St.AgreeOn (rs ++ rs') (ms ++ ms') σ τ) : St.AgreeOn rs ms σ τ :=
  h.mono (fun _ hx => List.mem_append.mpr (Or.inl hx))
         (fun _ hx => List.mem_append.mpr (Or.inl hx))

theorem St.AgreeOn.append_right {rs ms rs' ms' : List (String × Nat)} {σ τ : St}
    (h : St.AgreeOn (rs ++ rs') (ms ++ ms') σ τ) : St.AgreeOn rs' ms' σ τ :=
  h.mono (fun _ hx => List.mem_append.mpr (Or.inr hx))
         (fun _ hx => List.mem_append.mpr (Or.inr hx))

/-- **The frame rule for expressions.** An expression evaluates identically in
any two states that agree on its footprint. Everything outside `readSites` is
irrelevant to its value — which is exactly the licence to ignore the rest of
the design when proving a property about it. -/
theorem Expr.eval_congr_of_agree : ∀ {w : Nat} (e : Expr w) {σ τ : St},
    St.AgreeOn e.readSites.1 e.readSites.2 σ τ → e.eval σ = e.eval τ := by
  intro w e
  induction e with
  | lit v => intro _ _ _; rfl
  | reg w n => intro σ τ h; exact h.1 n w (by simp [Expr.readSites])
  | memRead dw m a ih =>
      intro σ τ h
      have hm : (m, dw) ∈ ((m, dw) :: a.readSites.2) := by simp
      have ha : St.AgreeOn a.readSites.1 a.readSites.2 σ τ :=
        ⟨fun n w hn => h.1 n w (by simpa [Expr.readSites] using hn),
         fun m' w' hm' => h.2 m' w' (by
           simp only [Expr.readSites]
           exact List.mem_cons_of_mem _ hm')⟩
      show σ.mems m (a.eval σ).toNat dw = τ.mems m (a.eval τ).toNat dw
      rw [ih ha]
      exact h.2 m dw (by simp [Expr.readSites]) _
  | not a ih => intro σ τ h; simp [Expr.eval, ih (by simp [Expr.readSites] at h ⊢; exact h)]
  | slice a lo width ih =>
      intro σ τ h; simp [Expr.eval, ih (by simpa [Expr.readSites] using h)]
  | zext a w' ih => intro σ τ h; simp [Expr.eval, ih (by simpa [Expr.readSites] using h)]
  | sext a w' ih => intro σ τ h; simp [Expr.eval, ih (by simpa [Expr.readSites] using h)]
  | mux c t f ihc iht ihf =>
      intro σ τ h
      simp only [Expr.readSites] at h
      -- footprint is c ++ t ++ f on both components
      -- `r ++ r' ++ r''` associates to the LEFT: `(c ++ t) ++ f`.
      have hct := h.append_left
      have hf : St.AgreeOn f.readSites.1 f.readSites.2 σ τ := h.append_right
      have hc : St.AgreeOn c.readSites.1 c.readSites.2 σ τ := hct.append_left
      have ht : St.AgreeOn t.readSites.1 t.readSites.2 σ τ := hct.append_right
      simp [Expr.eval, ihc hc, iht ht, ihf hf]
  | and a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | or a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | xor a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | add a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | sub a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | shl a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | shr a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | eq a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | ult a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | slt a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]

/-- **The frame rule for a cycle.** A register no rule of the design writes is
carried through `Design.cycle` unchanged.

This is the lift of `Act.run_regs_notin` from one action to a whole cycle, and
it is what lets a proof about one register ignore every rule that does not
mention it — the dependency-cone property W2 is after. -/
theorem Design.cycle_regs_notin (d : Design) (rn : String) (w : Nat)
    (h : ∀ r ∈ d.rules, (rn, w) ∉ r.body.regWrites) (σ : St) :
    (d.cycle σ).regs rn w = σ.regs rn w := by
  show (d.rules.foldl (fun acc r => r.body.run σ acc) σ).regs rn w = σ.regs rn w
  -- generalise the accumulator so the fold can be inducted on
  suffices H : ∀ (rs : List Rule) (acc : St),
      (∀ r ∈ rs, (rn, w) ∉ r.body.regWrites) →
      (rs.foldl (fun acc r => r.body.run σ acc) acc).regs rn w = acc.regs rn w by
    exact H d.rules σ h
  intro rs
  induction rs with
  | nil => intro acc _; rfl
  | cons r rest ih =>
      intro acc hmem
      have hr : (rn, w) ∉ r.body.regWrites := hmem r (List.mem_cons_self)
      have hrest : ∀ r' ∈ rest, (rn, w) ∉ r'.body.regWrites :=
        fun r' hr' => hmem r' (List.mem_cons_of_mem _ hr')
      show (rest.foldl (fun acc r => r.body.run σ acc) (r.body.run σ acc)).regs rn w
             = acc.regs rn w
      rw [ih _ hrest, Act.run_regs_notin rn w r.body hr]

/-- Likewise for memories: a memory no rule writes survives a cycle, at every
address and width. Stated pointwise to match `Act.run_mems_notin`. -/
theorem Design.cycle_mems_notin (d : Design) (mn : String)
    (h : ∀ r ∈ d.rules, mn ∉ r.body.memWrites) (σ : St) (ad w : Nat) :
    (d.cycle σ).mems mn ad w = σ.mems mn ad w := by
  show (d.rules.foldl (fun acc r => r.body.run σ acc) σ).mems mn ad w = σ.mems mn ad w
  suffices H : ∀ (rs : List Rule) (acc : St),
      (∀ r ∈ rs, mn ∉ r.body.memWrites) →
      (rs.foldl (fun acc r => r.body.run σ acc) acc).mems mn ad w = acc.mems mn ad w by
    exact H d.rules σ h
  intro rs
  induction rs with
  | nil => intro acc _; rfl
  | cons r rest ih =>
      intro acc hmem
      have hr : mn ∉ r.body.memWrites := hmem r (List.mem_cons_self)
      have hrest : ∀ r' ∈ rest, mn ∉ r'.body.memWrites :=
        fun r' hr' => hmem r' (List.mem_cons_of_mem _ hr')
      show (rest.foldl (fun acc r => r.body.run σ acc) (r.body.run σ acc)).mems mn ad w
             = acc.mems mn ad w
      rw [ih _ hrest, Act.run_mems_notin mn r.body hr]

/-! ## Discharging the side conditions by evaluation

A frame rule is only labour-saving if its hypothesis is cheaper to establish
than the property it frames. `∀ r ∈ d.rules, (rn, w) ∉ r.body.regWrites` is a
quantified statement over every rule of a design that, for `lnp64mini`, has
hundreds of them — proving it by hand would cost more than it saves.

These Boolean mirrors are computable, so the hypothesis is discharged by
`decide` (or `native_decide` on a large design) and the frame rule becomes a
one-liner. This is the "support inference" half of W2: the analysis runs, the
proof consumes its result. -/

/-- Computable: no rule of `d` writes register `(rn, w)`. -/
def Design.regUnwrittenB (d : Design) (rn : String) (w : Nat) : Bool :=
  d.rules.all fun r => !(r.body.regWrites.contains (rn, w))

/-- Computable: no rule of `d` writes memory `mn`. -/
def Design.memUnwrittenB (d : Design) (mn : String) : Bool :=
  d.rules.all fun r => !(r.body.memWrites.contains mn)

theorem Design.cycle_regs_of_unwrittenB {d : Design} {rn : String} {w : Nat}
    (h : d.regUnwrittenB rn w = true) (σ : St) :
    (d.cycle σ).regs rn w = σ.regs rn w := by
  refine d.cycle_regs_notin rn w (fun r hr hmem => ?_) σ
  have := (List.all_eq_true.mp h) r hr
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  exact this hmem

theorem Design.cycle_mems_of_unwrittenB {d : Design} {mn : String}
    (h : d.memUnwrittenB mn = true) (σ : St) (ad w : Nat) :
    (d.cycle σ).mems mn ad w = σ.mems mn ad w := by
  refine d.cycle_mems_notin mn (fun r hr hmem => ?_) σ ad w
  have := (List.all_eq_true.mp h) r hr
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  exact this hmem

/-! ## The rules firing on a design

A worked check that the API is usable as advertised: a two-register design
whose only rule bumps `a`. The frame rule then says `b` survives a cycle, and
the hypothesis is discharged by `decide` — no induction over the rule list at
the use site, which is the entire point.

`Expr.eval_congr_of_agree` is exercised on the other side: two states differing
*only* in `b` agree on the footprint of an expression that reads only `a`, so
the expression cannot tell them apart. -/

private def frameDemo : Design where
  name := "framedemo"
  regs := [{ name := "a", width := 8, init := 0 }, { name := "b", width := 8, init := 7 }]
  mems := []
  rules := [{ name := "bump_a", body := .write 8 "a" (.add (.reg 8 "a") (.lit 1#8)) }]
  inputs := []
  outputs := ["a", "b"]

-- The side condition is a computation, not a proof obligation.
example : frameDemo.regUnwrittenB "b" 8 = true := by decide

/-- `b` is framed out of the cycle: one `decide`, no reasoning about `bump_a`. -/
example (σ : St) : (frameDemo.cycle σ).regs "b" 8 = σ.regs "b" 8 :=
  frameDemo.cycle_regs_of_unwrittenB (by decide) σ

/-- And the design does not vacuously preserve everything: `a` *is* written, so
the checker refuses it. A frame rule that fired on every register would be
useless, so this is the half worth pinning down. -/
example : frameDemo.regUnwrittenB "a" 8 = false := by decide

/-- Read side: an expression over `a` alone cannot observe a change to `b`. -/
example (σ : St) (v : BitVec 8) :
    (Expr.add (.reg 8 "a") (.lit 3#8)).eval σ
      = (Expr.add (.reg 8 "a") (.lit 3#8)).eval { σ with regs := σ.regs.set "b" v } := by
  refine Expr.eval_congr_of_agree _ ⟨fun n w hn => ?_, fun m w hm => by simp [Expr.readSites] at hm⟩
  -- the footprint is exactly [("a", 8)], and `RegEnv.set "b"` leaves it alone
  simp only [Expr.readSites, List.append_nil, List.mem_singleton] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hn
  simp [RegEnv.set]

end Loom.Hw
