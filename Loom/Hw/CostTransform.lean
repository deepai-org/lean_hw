-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Cost
import Loom.Hw.Compose
import Loom.Hw.Trees

/-!
# W6, on real transformations — what the cost vector actually does

`Loom/Hw/Cost.lean` states the W6 claim ("a verified transformation does not
make the abstract cost vector worse") and proves the order is usable
(`Cost.le_refl`, `le_trans`, `add_le_add`). It proves nothing *about* a
transformation. This file connects the two ends for the transformations the
library actually ships: the compose layer (D16, `Loom/Hw/Compose.lean`) and
the balanced-tree builders (D18, `Loom/Hw/Trees.lean`).

## What is proved

* **Renaming is cost-neutral.** `prefixed_cost` — instantiating a design
  under a namespace leaves the whole vector unchanged. Three of the five
  dimensions (`stateBits`, `bitOps`, `maxFanout`) are unconditional; see the
  caveat below for the other two.
* **Parallel composition is additive.** `par_stateBits`, `par_bitOps`,
  `par_macroBits` are exact sums, and `par_cost_le` gives the whole vector
  as `Cost.le` against `Cost.add` — i.e. the hypothesis of `Cost.add_le_add`
  is now discharged by a real combinator rather than assumed. `softBits` is
  `≤` and not `=` there for a dull reason: it is a truncated `Nat`
  subtraction, and splitting one subtraction into two can only lose.
* **The balanced tree is never more area than the linear chain it
  replaces, and on a non-empty list is at least one operator cheaper.**
  `reduceTree_cost_le_foldr` and `reduceTree_cost_lt_foldr`, with the
  corollaries for `orTree`, `orTreeW` and `addTree`. D18 sells `reduceTree`
  as a *depth* fix; this says it is not paid for in area. The saved operator
  is the fold's final combine against the unit element `d`, which the tree
  never builds. (The bound is one-sided: no matching lower bound on the
  tree's cost is proved, so "at least", not "exactly".)

## What is NOT proved, and two things that are false

* **`priTree` is NOT area-neutral, and this file proves it is not.**
  `priTree_cost_gt` exhibits a two-entry list where the balanced priority
  select has strictly greater `Expr.cost` than the linear `priChain` it
  equals.
  The reason is structural, not an artefact of the example: `priPair`
  duplicates the left guard (`(.or gl gr, .mux gl vl vr)`), so every fusion
  pass copies guard cones. The balanced priority select buys depth with
  area. Nothing in D18 said otherwise; nothing had checked, either.
* **`par` is NOT `≤` on `maxFanout` for arbitrary designs**, and
  `par_maxFanout_gt` is the counterexample: two designs that both own a
  register named `x` compose to one whose `x` has twice the read sites,
  while `Cost.add` takes a `max`. That is exactly the aliasing `parOkB`
  exists to refuse, so `par_cost_le` takes the read-disjointness as an
  explicit hypothesis (`hab`, `hba`) rather than pretending it is free.
* **The two memory dimensions are conditional.** `macroBits`/`softBits` are
  the only entries that consult the target, through
  `MemTarget.familyOf t d md`, which reads the *whole design* (D19's
  `syncReadOkB` and the compiled write-port count). Renaming or composing a
  design therefore feeds a different design to the predictor, and the
  invariance of that predictor under an injective renaming — true, but a
  statement about `Compile.designTrace` and `Design.syncReadOkB`, not about
  cost — is taken as a hypothesis (`hfam`) here and is not proved anywhere
  in the repo. The memory-free corollaries (`prefixed_cost_of_no_mems`,
  `par_cost_le_of_no_mems`) are the unconditional part.
* **This is the abstract vector only.** No claim is made that the
  transformed design uses fewer LUTs, closes timing, or is smaller after
  synthesis — `Cost.lean`'s own honesty boundary applies unchanged. In
  particular the tree builders' *point* is depth, and depth is not one of
  the five dimensions: this file says the balanced form is not paid for in
  area, not that it is faster.
-/

namespace Loom.Hw

/-! ## List plumbing

Four `foldl`/`foldr` facts the cost folds need. All private: they are
scaffolding, not results. -/

private theorem foldl_congr_mem {α β : Type} {l : List α} {f g : β → α → β}
    (h : ∀ a ∈ l, ∀ b, f b a = g b a) :
    ∀ b, l.foldl f b = l.foldl g b := by
  induction l with
  | nil => intro b; rfl
  | cons a t ih =>
    intro b
    simp only [List.foldl_cons]
    rw [h a (by simp) b]
    exact ih (fun x hx c => h x (by simp [hx]) c) _

/-- An additively-accumulating `foldl` is its start plus its content. -/
private theorem foldl_add_start {α : Type} (h : α → Nat) :
    ∀ (l : List α) (k : Nat),
      l.foldl (fun acc a => acc + h a) k = k + l.foldl (fun acc a => acc + h a) 0 := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons a t ih =>
    intro k
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (k + h a), ih (h a)]
    omega

/-- …hence it distributes over `++`. -/
private theorem foldl_add_append {α : Type} (h : α → Nat) (l1 l2 : List α) :
    (l1 ++ l2).foldl (fun acc a => acc + h a) 0
      = l1.foldl (fun acc a => acc + h a) 0 + l2.foldl (fun acc a => acc + h a) 0 := by
  rw [List.foldl_append, foldl_add_start h l2]

/-- Elements contributing nothing leave the accumulator alone. -/
private theorem foldl_add_zero {α : Type} (h : α → Nat) {l : List α}
    (hz : ∀ a ∈ l, h a = 0) :
    ∀ k, l.foldl (fun acc a => acc + h a) k = k := by
  induction l with
  | nil => intro k; rfl
  | cons a t ih =>
    intro k
    simp only [List.foldl_cons, hz a (by simp), Nat.add_zero]
    exact ih (fun x hx => hz x (by simp [hx])) k

/-- The conditionally-accumulating memory fold has the same shape. -/
private theorem foldl_ite_add (P : MemDecl → Bool) :
    ∀ (l : List MemDecl) (k : Nat),
      l.foldl (fun acc m =>
          if P m then acc + m.dataWidth * 2 ^ m.addrWidth else acc) k
        = k + l.foldl (fun acc m =>
            if P m then acc + m.dataWidth * 2 ^ m.addrWidth else acc) 0 := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons a t ih =>
    intro k
    by_cases h : P a = true
    · simp only [List.foldl_cons, h, if_true, Nat.zero_add]
      rw [ih (k + a.dataWidth * 2 ^ a.addrWidth), ih (a.dataWidth * 2 ^ a.addrWidth)]
      omega
    · simp only [List.foldl_cons, h, if_false, Nat.zero_add, Bool.false_eq_true]
      exact ih k

/-- A `max`-accumulating `foldl` is the max of its start and its content. -/
private theorem foldl_max_start {α : Type} (h : α → Nat) :
    ∀ (l : List α) (k : Nat),
      l.foldl (fun acc a => max acc (h a)) k
        = max k (l.foldl (fun acc a => max acc (h a)) 0) := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons a t ih =>
    intro k
    simp only [List.foldl_cons, Nat.zero_max]
    rw [ih (max k (h a)), ih (h a)]
    omega

private theorem foldl_max_append {α : Type} (h : α → Nat) (l1 l2 : List α) :
    (l1 ++ l2).foldl (fun acc a => max acc (h a)) 0
      = max (l1.foldl (fun acc a => max acc (h a)) 0)
            (l2.foldl (fun acc a => max acc (h a)) 0) := by
  rw [List.foldl_append, foldl_max_start h l2]

/-! ## Reading the cost vector without unfolding the transformation

`Design.cost` is a `let`-heavy definition and the combinators are structure
literals; unfolding both at once rewrites the design *inside*
`MemTarget.familyOf` and loses the hypotheses. These `rfl` lemmas expose one
dimension at a time instead. -/

private theorem cost_stateBits (d : Design) (t : MemTarget) :
    (d.cost t).stateBits
      = d.regs.foldl (fun acc r => acc + r.width) 0
        + d.mems.foldl (fun acc m => acc + m.dataWidth * 2 ^ m.addrWidth) 0 := rfl

private theorem cost_bitOps (d : Design) (t : MemTarget) :
    (d.cost t).bitOps = d.rules.foldl (fun acc r => acc + r.body.cost) 0 := rfl

private theorem cost_macroBits (d : Design) (t : MemTarget) :
    (d.cost t).macroBits
      = d.mems.foldl (fun acc m =>
          if t.familyOf d m == MemFamily.bram then
            acc + m.dataWidth * 2 ^ m.addrWidth else acc) 0 := rfl

private theorem cost_softBits (d : Design) (t : MemTarget) :
    (d.cost t).softBits
      = d.mems.foldl (fun acc m => acc + m.dataWidth * 2 ^ m.addrWidth) 0
        - (d.cost t).macroBits := rfl

private theorem cost_maxFanout (d : Design) (t : MemTarget) :
    (d.cost t).maxFanout
      = d.regs.foldl (fun acc r =>
          max acc (d.rules.foldl (fun a rl => a + rl.body.regReads r.name) 0)) 0 := rfl

private theorem cost_eq {c1 c2 : Cost}
    (h1 : c1.stateBits = c2.stateBits) (h2 : c1.bitOps = c2.bitOps)
    (h3 : c1.macroBits = c2.macroBits) (h4 : c1.softBits = c2.softBits)
    (h5 : c1.maxFanout = c2.maxFanout) : c1 = c2 := by
  cases c1; cases c2; simp_all

private theorem prefixed_mems (p : String) (d : Design) :
    (d.prefixed p).mems = d.mems.map (fun m => { m with name := p ++ m.name }) := rfl

private theorem par_mems (a b : Design) : (a.par b).mems = a.mems ++ b.mems := rfl

/-! ## Renaming does not move any operator

`Expr.mapSignals`/`Act.mapSignals` change names and nothing else, so the
combinational weight is literally the same tree. -/

theorem Expr.cost_mapSignals (f : String → String) :
    ∀ {w : Nat} (e : Expr w), (e.mapSignals f).cost = e.cost := by
  intro w e
  induction e with
  | lit v => rfl
  | reg w n => rfl
  | _ => simp [Expr.mapSignals, Expr.cost, *]

theorem Act.cost_mapSignals (f : String → String) :
    ∀ a : Act, (a.mapSignals f).cost = a.cost := by
  intro a
  induction a with
  | skip => rfl
  | _ => simp [Act.mapSignals, Act.cost, Expr.cost_mapSignals, *]

/-- Read *sites* survive an injective renaming one-for-one: the register a
site reads is renamed with the register it names. -/
theorem Expr.regReads_mapSignals {f : String → String}
    (hf : ∀ x y, f x = f y → x = y) (n : String) :
    ∀ {w : Nat} (e : Expr w), (e.mapSignals f).regReads (f n) = e.regReads n := by
  intro w e
  induction e with
  | lit v => rfl
  | reg w m =>
    by_cases h : m = n
    · simp [Expr.mapSignals, Expr.regReads, h]
    · have : ¬ f m = f n := fun hh => h (hf _ _ hh)
      simp [Expr.mapSignals, Expr.regReads, h, this]
  | _ => simp [Expr.mapSignals, Expr.regReads, *]

theorem Act.regReads_mapSignals {f : String → String}
    (hf : ∀ x y, f x = f y → x = y) (n : String) :
    ∀ a : Act, (a.mapSignals f).regReads (f n) = a.regReads n := by
  intro a
  induction a with
  | skip => rfl
  | _ => simp [Act.mapSignals, Act.regReads, Expr.regReads_mapSignals hf, *]

/-- Prefixing a string is injective — the fact that makes `prefixed` a
renaming rather than a merge. -/
theorem prefix_injective (p : String) : ∀ x y : String, p ++ x = p ++ y → x = y := by
  intro x y h
  have h2 := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h2
  exact String.ext (List.append_cancel_left h2)

/-! ## `Design.prefixed` — instantiation is cost-neutral -/

theorem prefixed_stateBits (p : String) (d : Design) (t : MemTarget) :
    ((d.prefixed p).cost t).stateBits = (d.cost t).stateBits := by
  simp [Design.cost, Design.prefixed, List.foldl_map]

theorem prefixed_bitOps (p : String) (d : Design) (t : MemTarget) :
    ((d.prefixed p).cost t).bitOps = (d.cost t).bitOps := by
  simp [Design.cost, Design.prefixed, List.foldl_map, Act.cost_mapSignals]

theorem prefixed_maxFanout (p : String) (d : Design) (t : MemTarget) :
    ((d.prefixed p).cost t).maxFanout = (d.cost t).maxFanout := by
  have hinner : ∀ r : RegDecl,
      (d.rules.foldl (fun a rl =>
          a + (rl.body.mapSignals (p ++ ·)).regReads (p ++ r.name)) 0)
        = d.rules.foldl (fun a rl => a + rl.body.regReads r.name) 0 := by
    intro r
    exact foldl_congr_mem
      (fun rl _ b => by
        rw [Act.regReads_mapSignals (prefix_injective p) r.name rl.body]) 0
  simp only [Design.cost, Design.prefixed, List.foldl_map]
  exact foldl_congr_mem (fun r _ b => by rw [hinner r]) 0

/-- **Renaming is cost-neutral**: instantiating `d` under the namespace `p`
leaves every dimension of the abstract cost vector unchanged.

`hfam` is the target-prediction hypothesis the module docstring names: the
realization class `t` predicts for a memory must not depend on the prefix.
It is true (the prediction reads write-port traces and D19 read sites, all
of which are matched by name and so are renamed with the memory) but it is
a statement about `Compile.designTrace`/`Design.syncReadOkB`, and it is not
proved in this repo — so it is a hypothesis here, not an assumption hidden
inside a proof. -/
theorem prefixed_cost (p : String) (d : Design) (t : MemTarget)
    (hfam : ∀ md ∈ d.mems,
      t.familyOf (d.prefixed p) { md with name := p ++ md.name }
        = t.familyOf d md) :
    (d.prefixed p).cost t = d.cost t := by
  have hmacro :
      ((d.prefixed p).cost t).macroBits = (d.cost t).macroBits := by
    rw [cost_macroBits, cost_macroBits, prefixed_mems]
    simp only [List.foldl_map]
    exact foldl_congr_mem (fun md hmd b => by rw [hfam md hmd]) 0
  have hsoft : ((d.prefixed p).cost t).softBits = (d.cost t).softBits := by
    rw [cost_softBits, cost_softBits, hmacro, prefixed_mems]
    simp only [List.foldl_map]
  exact cost_eq (prefixed_stateBits p d t) (prefixed_bitOps p d t) hmacro hsoft
    (prefixed_maxFanout p d t)

/-- The unconditional corollary: a design with no memories has no
target-dependent dimension, so `prefixed` is cost-neutral outright. -/
theorem prefixed_cost_of_no_mems (p : String) (d : Design) (t : MemTarget)
    (h : d.mems = []) : (d.prefixed p).cost t = d.cost t :=
  prefixed_cost p d t (by simp [h])

/-! ## `Design.par` — composition is additive -/

theorem par_stateBits (a b : Design) (t : MemTarget) :
    ((a.par b).cost t).stateBits = (a.cost t).stateBits + (b.cost t).stateBits := by
  simp only [Design.cost, Design.par]
  rw [foldl_add_append (fun r : RegDecl => r.width),
    foldl_add_append (fun m : MemDecl => m.dataWidth * 2 ^ m.addrWidth)]
  omega

theorem par_bitOps (a b : Design) (t : MemTarget) :
    ((a.par b).cost t).bitOps = (a.cost t).bitOps + (b.cost t).bitOps := by
  simp only [Design.cost, Design.par]
  rw [foldl_add_append (fun rl : Rule => rl.body.cost)]

/-- The memory dimensions need the same prediction hypothesis `prefixed`
does, for the same reason: `familyOf` reads the whole (now composite)
design. -/
theorem par_macroBits (a b : Design) (t : MemTarget)
    (hfa : ∀ md ∈ a.mems, t.familyOf (a.par b) md = t.familyOf a md)
    (hfb : ∀ md ∈ b.mems, t.familyOf (a.par b) md = t.familyOf b md) :
    ((a.par b).cost t).macroBits
      = (a.cost t).macroBits + (b.cost t).macroBits := by
  rw [cost_macroBits, cost_macroBits, cost_macroBits, par_mems, List.foldl_append]
  rw [foldl_congr_mem (l := a.mems)
      (f := fun acc (m : MemDecl) =>
        if t.familyOf (a.par b) m == MemFamily.bram then
          acc + m.dataWidth * 2 ^ m.addrWidth else acc)
      (g := fun acc (m : MemDecl) =>
        if t.familyOf a m == MemFamily.bram then
          acc + m.dataWidth * 2 ^ m.addrWidth else acc)
      (fun md hmd c => by simp only [hfa md hmd]) 0]
  rw [foldl_congr_mem (l := b.mems)
      (f := fun acc (m : MemDecl) =>
        if t.familyOf (a.par b) m == MemFamily.bram then
          acc + m.dataWidth * 2 ^ m.addrWidth else acc)
      (g := fun acc (m : MemDecl) =>
        if t.familyOf b m == MemFamily.bram then
          acc + m.dataWidth * 2 ^ m.addrWidth else acc)
      (fun md hmd c => by simp only [hfb md hmd])]
  exact foldl_ite_add (fun m => t.familyOf b m == MemFamily.bram) b.mems _

/-- **Composition is monotone against `Cost.add`.**

The two `hf*` hypotheses are the target-prediction invariance discussed in
the module docstring. `hab`/`hba` say the parts do not read each other's
registers — the aliasing `Design.parOkB` refuses; without them the
`maxFanout` component is genuinely false (`par_maxFanout_gt`). -/
theorem par_cost_le (a b : Design) (t : MemTarget)
    (hfa : ∀ md ∈ a.mems, t.familyOf (a.par b) md = t.familyOf a md)
    (hfb : ∀ md ∈ b.mems, t.familyOf (a.par b) md = t.familyOf b md)
    (hab : ∀ r ∈ a.regs, ∀ rl ∈ b.rules, rl.body.regReads r.name = 0)
    (hba : ∀ r ∈ b.regs, ∀ rl ∈ a.rules, rl.body.regReads r.name = 0) :
    (a.par b).cost t ≤ a.cost t + b.cost t := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_of_eq (par_stateBits a b t)
  · exact Nat.le_of_eq (par_bitOps a b t)
  · exact Nat.le_of_eq (par_macroBits a b t hfa hfb)
  · -- softBits: `memBits - macroBits`, and Nat subtraction only helps the sum
    have hm := par_macroBits a b t hfa hfb
    have hmem : (a.par b).mems.foldl (fun acc m => acc + m.dataWidth * 2 ^ m.addrWidth) 0
        = a.mems.foldl (fun acc m => acc + m.dataWidth * 2 ^ m.addrWidth) 0
          + b.mems.foldl (fun acc m => acc + m.dataWidth * 2 ^ m.addrWidth) 0 := by
      rw [par_mems]
      exact foldl_add_append _ _ _
    show ((a.par b).cost t).softBits ≤ (a.cost t).softBits + (b.cost t).softBits
    rw [cost_softBits, cost_softBits, cost_softBits, hmem, hm]
    omega
  · -- maxFanout: each part's registers are read only by that part's rules
    show ((a.par b).cost t).maxFanout ≤ max (a.cost t).maxFanout (b.cost t).maxFanout
    simp only [Design.cost, Design.par]
    have hA : ∀ r ∈ a.regs, ∀ k : Nat,
        (a.rules ++ b.rules).foldl (fun acc rl => acc + rl.body.regReads r.name) k
          = a.rules.foldl (fun acc rl => acc + rl.body.regReads r.name) k := by
      intro r hr k
      rw [List.foldl_append]
      exact foldl_add_zero (fun rl : Rule => rl.body.regReads r.name)
        (fun rl hrl => hab r hr rl hrl) _
    have hB : ∀ r ∈ b.regs, ∀ k : Nat,
        (a.rules ++ b.rules).foldl (fun acc rl => acc + rl.body.regReads r.name) k
          = b.rules.foldl (fun acc rl => acc + rl.body.regReads r.name) k := by
      intro r hr k
      rw [List.foldl_append,
        foldl_add_zero (fun rl : Rule => rl.body.regReads r.name)
          (fun rl hrl => hba r hr rl hrl) k]
    rw [foldl_max_append (fun r : RegDecl =>
      (a.rules ++ b.rules).foldl (fun acc rl => acc + rl.body.regReads r.name) 0)]
    have ea := foldl_congr_mem (l := a.regs)
      (f := fun acc (r : RegDecl) => max acc
        ((a.rules ++ b.rules).foldl (fun x rl => x + rl.body.regReads r.name) 0))
      (g := fun acc (r : RegDecl) => max acc
        (a.rules.foldl (fun x rl => x + rl.body.regReads r.name) 0))
      (fun r hr c => by simp only [hA r hr]) 0
    have eb := foldl_congr_mem (l := b.regs)
      (f := fun acc (r : RegDecl) => max acc
        ((a.rules ++ b.rules).foldl (fun x rl => x + rl.body.regReads r.name) 0))
      (g := fun acc (r : RegDecl) => max acc
        (b.rules.foldl (fun x rl => x + rl.body.regReads r.name) 0))
      (fun r hr c => by simp only [hB r hr]) 0
    rw [ea, eb]
    exact Nat.le_refl _

/-- The memory-free corollary, with no prediction hypothesis left. -/
theorem par_cost_le_of_no_mems (a b : Design) (t : MemTarget)
    (ha : a.mems = []) (hb : b.mems = [])
    (hab : ∀ r ∈ a.regs, ∀ rl ∈ b.rules, rl.body.regReads r.name = 0)
    (hba : ∀ r ∈ b.regs, ∀ rl ∈ a.rules, rl.body.regReads r.name = 0) :
    (a.par b).cost t ≤ a.cost t + b.cost t :=
  par_cost_le a b t (by simp [ha]) (by simp [hb]) hab hba

/-! ### …but not without disjointness

Two designs that each own a register called `x` compose to a design whose
`x` is read twice, while `Cost.add` takes a `max` of the two parts' fanout.
This is the aliasing `Design.parOkB` exists to refuse, and it is why
`par_cost_le` asks for `hab`/`hba` instead of quietly assuming them. -/

/-- One register `x`, one rule reading it once. -/
private def fanD : Design where
  name := "fan"
  regs := [{ name := "x", width := 1, init := 0 }]
  mems := []
  rules := [{ name := "r", body := .write 1 "x" (.reg 1 "x") }]
  outputs := ["x"]

theorem par_maxFanout_gt :
    ((fanD.par fanD).cost MemTarget.xc7).maxFanout
      > (fanD.cost MemTarget.xc7 + fanD.cost MemTarget.xc7).maxFanout := by
  decide

theorem par_cost_not_le :
    ¬ ((fanD.par fanD).cost MemTarget.xc7
        ≤ fanD.cost MemTarget.xc7 + fanD.cost MemTarget.xc7) := by
  intro h
  obtain ⟨-, -, -, -, hfan⟩ := h
  exact absurd hfan (by decide)

/-! ## The balanced tree builders (D18)

`reduceTree f d xs` and `xs.foldr f d` compute the same value
(`Trees.reduceTree_eval`). This section says what they cost: the tree is
never dearer, and on a non-empty list is at least one operator cheaper,
because the linear fold ends with a combine against the unit element `d`
and the tree never builds it. -/

/-- Total cost of the leaves. -/
def costSum {w : Nat} (xs : List (Expr w)) : Nat :=
  xs.foldr (fun e acc => e.cost + acc) 0

/-- The linear chain, exactly: leaves, plus one `k`-weight operator per
element, plus the default. -/
theorem foldr_cost {w k : Nat} (f : Expr w → Expr w → Expr w) (d : Expr w)
    (hf : ∀ a b, (f a b).cost = k + a.cost + b.cost) :
    ∀ xs : List (Expr w),
      (xs.foldr f d).cost = costSum xs + k * xs.length + d.cost := by
  intro xs
  induction xs with
  | nil => simp [costSum]
  | cons a t ih =>
    simp only [List.foldr_cons, hf, ih, costSum, List.foldr_cons, List.length_cons]
    rw [Nat.mul_succ]
    omega

private theorem pairFold_length {w : Nat} (f : Expr w → Expr w → Expr w) :
    ∀ xs : List (Expr w), (pairFold f xs).length = (xs.length + 1) / 2 := by
  intro xs
  induction xs using pairFold.induct with
  | case1 a b t ih =>
    simp only [pairFold, List.length_cons] at *
    omega
  | case2 l h =>
    cases l with
    | nil => simp [pairFold]
    | cons a t =>
      cases t with
      | nil => simp [pairFold]
      | cons b t' => exact absurd rfl (h a b t')

/-- One fusion pass adds one operator per fused pair, and nothing else. -/
private theorem pairFold_cost {w k : Nat} (f : Expr w → Expr w → Expr w)
    (hf : ∀ a b, (f a b).cost = k + a.cost + b.cost) :
    ∀ xs : List (Expr w),
      costSum (pairFold f xs) = costSum xs + k * (xs.length / 2) := by
  intro xs
  induction xs using pairFold.induct with
  | case1 a b t ih =>
    simp only [pairFold, costSum, List.foldr_cons, List.length_cons] at *
    rw [hf, ih]
    have hd : (t.length + 1 + 1) / 2 = t.length / 2 + 1 := by omega
    rw [hd, Nat.mul_add, Nat.mul_one]
    omega
  | case2 l h =>
    cases l with
    | nil => simp [pairFold, costSum]
    | cons a t =>
      cases t with
      | nil => simp [pairFold, costSum]
      | cons b t' => exact absurd rfl (h a b t')

private theorem reduceTreeAux_cost {w k : Nat} (f : Expr w → Expr w → Expr w)
    (d : Expr w) (hf : ∀ a b, (f a b).cost = k + a.cost + b.cost) :
    ∀ (n : Nat) (xs : List (Expr w)), xs.length ≤ n + 1 →
      (reduceTreeAux f d n xs).cost ≤ costSum xs + k * (xs.length - 1) + d.cost := by
  intro n
  induction n with
  | zero =>
    intro xs hlen
    match xs with
    | [] => simp [reduceTreeAux, costSum]
    | [x] => simp [reduceTreeAux, costSum]
    | a :: b :: t => simp only [List.length_cons] at hlen; omega
  | succ n ih =>
    intro xs hlen
    match xs with
    | [] => simp [reduceTreeAux, costSum]
    | [x] => simp [reduceTreeAux, costSum]
    | a :: b :: t =>
      have hlen' : (pairFold f (a :: b :: t)).length ≤ n + 1 := by
        rw [pairFold_length f]
        simp only [List.length_cons] at hlen ⊢
        omega
      have hrec := ih (pairFold f (a :: b :: t)) hlen'
      rw [pairFold_cost f hf, pairFold_length f] at hrec
      simp only [reduceTreeAux]
      refine Nat.le_trans hrec ?_
      simp only [List.length_cons] at *
      have hsplit : k * ((t.length + 1 + 1) / 2)
          + k * ((t.length + 1 + 1 + 1) / 2 - 1)
          = k * (t.length + 1 + 1 - 1) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega

/-- **The balanced reduction never costs more than the linear fold.** -/
theorem reduceTree_cost_le_foldr {w k : Nat} (f : Expr w → Expr w → Expr w)
    (d : Expr w) (hf : ∀ a b, (f a b).cost = k + a.cost + b.cost)
    (xs : List (Expr w)) :
    (reduceTree f d xs).cost ≤ (xs.foldr f d).cost := by
  have h := reduceTreeAux_cost f d hf xs.length xs (Nat.le_succ _)
  rw [foldr_cost f d hf]
  refine Nat.le_trans h ?_
  have : k * (xs.length - 1) ≤ k * xs.length :=
    Nat.mul_le_mul_left k (Nat.sub_le _ _)
  omega

/-- …and on a non-empty list it costs at least one operator *less*: the
linear fold's final combine against the unit `d`, which the tree omits. -/
theorem reduceTree_cost_lt_foldr {w k : Nat} (f : Expr w → Expr w → Expr w)
    (d : Expr w) (hf : ∀ a b, (f a b).cost = k + a.cost + b.cost)
    (xs : List (Expr w)) (hne : xs ≠ []) :
    (reduceTree f d xs).cost + k ≤ (xs.foldr f d).cost := by
  have h := reduceTreeAux_cost f d hf xs.length xs (Nat.le_succ _)
  have hred : (reduceTree f d xs).cost = (reduceTreeAux f d xs.length xs).cost := rfl
  rw [foldr_cost f d hf, hred]
  have hlen : 1 ≤ xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => simp
  have hk : k * (xs.length - 1) + k = k * xs.length := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  omega

theorem orTreeW_cost_le {w : Nat} (xs : List (Expr w)) :
    (orTreeW xs).cost ≤ (xs.foldr Expr.or (Expr.lit (BitVec.ofNat w 0))).cost :=
  reduceTree_cost_le_foldr (k := w) Expr.or _ (fun _ _ => rfl) xs

theorem orTree_cost_le (xs : List (Expr 1)) :
    (orTree xs).cost ≤ (xs.foldr Expr.or (Expr.lit 0)).cost :=
  reduceTree_cost_le_foldr (k := 1) Expr.or _ (fun _ _ => rfl) xs

theorem addTree_cost_le {w : Nat} (xs : List (Expr w)) :
    (addTree xs).cost ≤ (xs.foldr Expr.add (Expr.lit (BitVec.ofNat w 0))).cost :=
  reduceTree_cost_le_foldr (k := w) Expr.add _ (fun _ _ => rfl) xs

/-- The strict form for the OR tree: `w` bits of work cheaper. -/
theorem orTreeW_cost_lt {w : Nat} (xs : List (Expr w)) (hne : xs ≠ []) :
    (orTreeW xs).cost + w
      ≤ (xs.foldr Expr.or (Expr.lit (BitVec.ofNat w 0))).cost :=
  reduceTree_cost_lt_foldr (k := w) Expr.or _ (fun _ _ => rfl) xs hne

theorem addTree_cost_lt {w : Nat} (xs : List (Expr w)) (hne : xs ≠ []) :
    (addTree xs).cost + w
      ≤ (xs.foldr Expr.add (Expr.lit (BitVec.ofNat w 0))).cost :=
  reduceTree_cost_lt_foldr (k := w) Expr.add _ (fun _ _ => rfl) xs hne

/-! ### `priTree` is the exception

`priPair` emits `(.or gl gr, .mux gl vl vr)`: the left guard appears twice.
Every fusion pass therefore *copies* guard cones, and the balanced priority
select costs strictly more than the linear chain it equals. Two entries with
zero-cost guards already show it — one extra `.or` at width 1. -/

theorem priTree_cost_gt :
    (priChain [((Expr.reg 1 "g1"), (Expr.reg 8 "v1")),
               ((Expr.reg 1 "g2"), (Expr.reg 8 "v2"))] (Expr.lit 0)).cost
      < (priTree [((Expr.reg 1 "g1"), (Expr.reg 8 "v1")),
                  ((Expr.reg 1 "g2"), (Expr.reg 8 "v2"))] (Expr.lit 0)).cost := by
  decide

end Loom.Hw
