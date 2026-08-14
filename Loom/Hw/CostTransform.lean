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

**This file was rewritten when `Expr.cost` stopped being a tree cost.** The
old metric billed a shared subexpression once per syntactic occurrence,
while the emitter gives it one wire; `Loom/Hw/Cost.lean` documents the
measurement that showed the sign of a real transformation coming out
backwards. `Expr.cost` now counts hash-consed nodes. Some theorems below
survived unchanged, some needed a hypothesis they never needed before, and
some are now **false** — each is labelled.

## What is proved

* **Renaming is cost-neutral — now only for an *injective* renaming.**
  `prefixed_cost` still holds, because prefixing is injective
  (`prefix_injective`), but the underlying `Expr.cost_mapSignals` /
  `Act.cost_mapSignals` now *require* injectivity and are false without it:
  a renaming that merges two names merges their nodes, and a hash-consed
  cost legitimately drops. The proof route is new — `Expr.hc_mapSignals`
  shows the whole intern table is carried along by the renaming — and the
  old one-line induction is gone.
* **Parallel composition is still exactly additive on `bitOps`**
  (`par_bitOps`), and `par_cost_le` is unchanged. This is not an accident:
  `Design.cost` deduplicates *within a rule body* and then sums over rules,
  precisely so that appending rule lists stays additive. Cross-rule sharing
  is real in the emitter and is deliberately not modelled; `Cost.lean` says
  so and names the direction of the residual error.
* **The hash-consed cost is never worse than the old tree cost**
  (`Expr.cost_le_treeCost`, `Act.cost_le_treeCost`), so every theorem that
  used to be stated about the tree recursion survives as an upper bound.
  Those theorems are all still here, renamed to `…treeCost…`
  (`reduceTree_treeCost_le_foldr`, `orTreeW_treeCost_lt`, …) with their
  proofs unchanged, since the tree recursion is what makes the exact
  arithmetic of `pairFold` provable.

## What is now FALSE, and stated as such

* **`reduceTree_cost_le_foldr` is false under the DAG cost.**
  `reduceTree_cost_not_le_foldr` is the counterexample: three leaves over
  `Expr.or`, where the third leaf is *literally the linear chain's own
  suffix*. The chain's combines then collapse into that leaf (3 OR nodes)
  while the balanced tree still builds 4. The old proof went through a
  term-count identity (`treeCostSum xs + k·(n-1)`) that is only valid when
  no node is shared, so it survives on `treeCost` and dies on `cost`. The
  corollaries `orTree_cost_le`, `orTreeW_cost_lt`, `addTree_cost_lt` die
  with it and are gone; their `treeCost` versions remain. On leaves that do
  *not* alias (`orTree_cost_lt_example`) the balanced tree is still
  strictly cheaper, which is the case D18 actually builds.
* **`par` is NOT `≤` on `maxFanout` for arbitrary designs**, unchanged:
  `par_maxFanout_gt` / `par_cost_not_le` are the same counterexample as
  before, and are why `par_cost_le` takes read-disjointness as a hypothesis.
* **The two memory dimensions are conditional**, unchanged.
  `macroBits`/`softBits` are the only entries that consult the target,
  through `MemTarget.classOf t d md`, which reads the *whole design*.
  Renaming or composing feeds a different design to the predictor, and the
  invariance of that predictor under an injective renaming is taken as a
  hypothesis (`hfam`) rather than proved. The memory-free corollaries
  (`prefixed_cost_of_no_mems`, `par_cost_le_of_no_mems`) are the
  unconditional part.

## `priTree`: the counterexample survived, its explanation did not

`priTree_cost_gt` still holds and is still proved by `decide`, but the old
reading of it was wrong. It used to be blamed on `priPair` duplicating the
left guard (`(.or gl gr, .mux gl vl vr)`) so that "every fusion pass copies
guard cones". Under the hash-consed cost the duplicated guard collapses to
one wire and costs nothing extra — exactly the point of the rewrite. What
is left is real and much smaller: the balanced form emits `n-1` extra
width-1 `or` nodes that the linear chain never builds, so it is dearer by
`n-1` bits and by nothing else, *whatever the guards cost*.

`sel_cost_dag` / `sel_cost_tree` pin that down on a four-way select with a
non-trivial shared guard cone: the balanced form costs `+3` (= `n-1`) under
the new metric and `+36` under the old one. At `n = 32` with the same guard
shape the numbers are 4 321 vs 4 352 (`+31`, 0.7%) against 4 352 vs 5 072
(`+720`, 17%) — the model no longer claims the balanced priority select is
materially worse. It also does not claim it is better: the 357 LUT win
synthesis reports on `s_ex_body` comes from yosys's own optimisation of the
mux cone, not from node count, and `Cost.lean`'s honesty boundary about
synthesis and P&R applies unchanged.

## This is the abstract vector only

No claim is made that a transformed design uses fewer LUTs or closes
timing. In particular the tree builders' *point* is depth, and depth is not
one of the five dimensions.
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
`MemTarget.classOf` and loses the hypotheses. These `rfl` lemmas expose one
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
          if t.classOf d m == MemClass.macro then
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

`Expr.mapSignals`/`Act.mapSignals` change names and nothing else. For the
*tree* recursion that is the whole story — same tree, same weights. For the
hash-consed cost it is not: node identity is partly a name, so the intern
table has to be carried along by the renaming, and the renaming has to be
injective or the table gets *smaller*. Both facts are proved below. -/

@[simp] theorem Expr.mulOperandWidth_mapSignals (f : String → String) :
    ∀ {w : Nat} (e : Expr w), (e.mapSignals f).mulOperandWidth = e.mulOperandWidth := by
  intro w e
  induction e <;> simp [Expr.mapSignals, Expr.mulOperandWidth, *]

theorem Expr.treeCost_mapSignals (f : String → String) :
    ∀ {w : Nat} (e : Expr w), (e.mapSignals f).treeCost = e.treeCost := by
  intro w e
  induction e with
  | lit v => rfl
  | reg w n => rfl
  | _ => simp [Expr.mapSignals, Expr.treeCost, *]

theorem Act.treeCost_mapSignals (f : String → String) :
    ∀ a : Act, (a.mapSignals f).treeCost = a.treeCost := by
  intro a
  induction a with
  | skip => rfl
  | _ => simp [Act.mapSignals, Act.treeCost, Expr.treeCost_mapSignals, *]

/-! ### The intern table under a renaming

A renaming acts on `ENode` by renaming the two name-carrying constructors
and nothing else; indices are untouched, because a renaming cannot change
*which* subcircuits are equal — provided it is injective. -/

/-- A renaming, transported to emitted nodes. -/
def ENode.rename (f : String → String) : ENode → ENode
  | .sig n => .sig (f n)
  | .mem dw m a => .mem dw (f m) a
  | n => n

/-- Weights do not depend on names. -/
theorem ENode.weight_rename (f : String → String) (n : ENode) :
    (n.rename f).weight = n.weight := by
  cases n <;> rfl

/-- **Injectivity is the hypothesis this whole section needs**: a renaming
that merges two names merges their nodes, and the cost drops. -/
theorem ENode.rename_inj {f : String → String} (hf : ∀ x y, f x = f y → x = y) :
    ∀ n m : ENode, n.rename f = m.rename f → n = m := by
  intro n m h
  cases n <;> cases m <;> simp_all [ENode.rename] <;>
    first
      | exact hf _ _ h
      | exact hf _ _ h.2.1

theorem ENode.find?_map_rename {f : String → String} (hf : ∀ x y, f x = f y → x = y)
    (n : ENode) : ∀ (tbl : List ENode) (i : Nat),
      (n.rename f).find? (tbl.map (ENode.rename f)) i = n.find? tbl i := by
  intro tbl
  induction tbl with
  | nil => intro i; rfl
  | cons m t ih =>
    intro i
    by_cases h : m = n
    · subst h; simp [ENode.find?]
    · have hne : ¬ (m.rename f = n.rename f) := fun hh => h (ENode.rename_inj hf _ _ hh)
      simp [ENode.find?, h, hne, ih]

theorem ENode.intern_map_rename {f : String → String} (hf : ∀ x y, f x = f y → x = y)
    (n : ENode) (tbl : List ENode) :
    (n.rename f).intern (tbl.map (ENode.rename f))
      = ((n.intern tbl).1, ((n.intern tbl).2).map (ENode.rename f)) := by
  simp only [ENode.intern, ENode.find?_map_rename hf]
  cases n.find? tbl 0 with
  | none => simp
  | some i => simp

/-- The same, for the nodes a renaming leaves alone (everything but
`sig`/`mem`). -/
theorem ENode.intern_map_rename_pure {f : String → String} (hf : ∀ x y, f x = f y → x = y)
    {n : ENode} (hn : n.rename f = n) (tbl : List ENode) :
    n.intern (tbl.map (ENode.rename f))
      = ((n.intern tbl).1, ((n.intern tbl).2).map (ENode.rename f)) := by
  have h : n.intern (tbl.map (ENode.rename f))
      = (n.rename f).intern (tbl.map (ENode.rename f)) := by rw [hn]
  rw [h, ENode.intern_map_rename hf n tbl]

/-- **A renaming carries the whole intern table**: interning a renamed
expression into a renamed table gives the same index and the renamed table.
This is what replaces the old one-line `cost_mapSignals` induction. -/
theorem Expr.hc_mapSignals {f : String → String} (hf : ∀ x y, f x = f y → x = y) :
    ∀ {w : Nat} (e : Expr w) (tbl : List ENode),
      (e.mapSignals f).hc (tbl.map (ENode.rename f))
        = ((e.hc tbl).1, ((e.hc tbl).2).map (ENode.rename f)) := by
  intro w e
  induction e <;> intro tbl <;>
    simp only [Expr.mapSignals, Expr.hc, Expr.mulOperandWidth_mapSignals, *] <;>
    ((try split) <;> (try split) <;>
      first
        | (refine ENode.intern_map_rename_pure hf ?_ _; rfl)
        | exact ENode.intern_map_rename hf (.sig _) _
        | exact ENode.intern_map_rename hf (.mem _ _ _) _)

private theorem nodesWeight_map_rename (f : String → String) :
    ∀ (l : List ENode) (k : Nat),
      (l.map (ENode.rename f)).foldl (fun acc n => acc + n.weight) k
        = l.foldl (fun acc n => acc + n.weight) k := by
  intro l
  induction l with
  | nil => intro k; rfl
  | cons a t ih => intro k; simp [ENode.weight_rename, ih]

/-- **An injective renaming is cost-neutral.** Injectivity is not
decoration: `fun _ => "x"` collapses every read to one node. -/
theorem Expr.cost_mapSignals {f : String → String} (hf : ∀ x y, f x = f y → x = y)
    {w : Nat} (e : Expr w) : (e.mapSignals f).cost = e.cost := by
  have h := Expr.hc_mapSignals hf e []
  simp only [List.map_nil] at h
  simp only [Expr.cost, h, nodesWeight, nodesWeight_map_rename]

theorem Act.hc_mapSignals {f : String → String} (hf : ∀ x y, f x = f y → x = y) :
    ∀ (a : Act) (tbl : List ENode),
      (a.mapSignals f).hc (tbl.map (ENode.rename f)) = (a.hc tbl).map (ENode.rename f) := by
  intro a
  induction a with
  | skip => intro tbl; rfl
  | seq x y ihx ihy => intro tbl; simp only [Act.mapSignals, Act.hc, ihx, ihy]
  | ite c x y ihx ihy =>
      intro tbl
      simp only [Act.mapSignals, Act.hc, Expr.hc_mapSignals hf, ihx, ihy]
  | write w r v => intro tbl; simp only [Act.mapSignals, Act.hc, Expr.hc_mapSignals hf]
  | writeSlice w r lo fw h v =>
      intro tbl; simp only [Act.mapSignals, Act.hc, Expr.hc_mapSignals hf]
  | memWrite aw dw m p a d =>
      intro tbl; simp only [Act.mapSignals, Act.hc, Expr.hc_mapSignals hf]

theorem Act.cost_mapSignals {f : String → String} (hf : ∀ x y, f x = f y → x = y)
    (a : Act) : (a.mapSignals f).cost = a.cost := by
  have h := Act.hc_mapSignals hf a []
  simp only [List.map_nil] at h
  simp only [Act.cost, h, nodesWeight, nodesWeight_map_rename]

/-! ### The hash-consed cost is bounded by the tree cost

Deduplication can only remove table entries, so every `treeCost` bound
proved below is also a `cost` bound. This is what keeps the D18 tree
arithmetic useful after the metric changed. -/

private theorem nodesWeight_append (l1 l2 : List ENode) :
    nodesWeight (l1 ++ l2) = nodesWeight l1 + nodesWeight l2 := by
  simp only [nodesWeight, List.foldl_append]
  exact foldl_add_start ENode.weight l2 _

theorem nodesWeight_intern_le (n : ENode) (tbl : List ENode) :
    nodesWeight (n.intern tbl).2 ≤ nodesWeight tbl + n.weight := by
  simp only [ENode.intern]
  cases n.find? tbl 0 with
  | some i => simp
  | none => simp [nodesWeight]

theorem Expr.hc_weight_le : ∀ {w : Nat} (e : Expr w) (tbl : List ENode),
    nodesWeight (e.hc tbl).2 ≤ nodesWeight tbl + e.treeCost := by
  intro w e
  induction e with
  | lit v =>
      intro tbl
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | reg w n =>
      intro tbl
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | memRead dw m a ih =>
      intro tbl
      have h1 := ih tbl
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | and a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | or a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | xor a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | add a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | sub a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | mul a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | udiv a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | urem a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | shl a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | shr a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | eq a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | ult a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | slt a b iha ihb =>
      intro tbl
      have h1 := iha tbl; have h2 := ihb (a.hc tbl).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | not a ih =>
      intro tbl
      have h1 := ih tbl
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | mux c x y ihc ihx ihy =>
      intro tbl
      have h1 := ihc tbl
      have h2 := ihx (c.hc tbl).2
      have h3 := ihy (x.hc (c.hc tbl).2).2
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | slice a lo wd ih =>
      intro tbl
      have h1 := ih tbl
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | zext a w' ih =>
      intro tbl
      have h1 := ih tbl
      simp only [Expr.hc, Expr.treeCost]
      refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
      simp only [ENode.weight]
      omega
  | sext a w' ih =>
      intro tbl
      have h1 := ih tbl
      simp only [Expr.hc, Expr.treeCost]
      split
      · refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
        simp only [ENode.weight]; omega
      · split
        · refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
          simp only [ENode.weight]; omega
        · refine Nat.le_trans (nodesWeight_intern_le _ _) ?_
          simp only [ENode.weight]; omega

theorem Expr.cost_le_treeCost {w : Nat} (e : Expr w) : e.cost ≤ e.treeCost := by
  have h := Expr.hc_weight_le e []
  simpa [Expr.cost, nodesWeight] using h

theorem Act.hc_weight_le : ∀ (a : Act) (tbl : List ENode),
    nodesWeight (a.hc tbl) ≤ nodesWeight tbl + a.treeCost := by
  intro a
  induction a with
  | skip => intro tbl; simp [Act.hc, Act.treeCost]
  | seq x y ihx ihy =>
      intro tbl
      have h1 := ihx tbl; have h2 := ihy (x.hc tbl)
      simp only [Act.hc, Act.treeCost] at *; omega
  | ite c x y ihx ihy =>
      intro tbl
      have h0 := Expr.hc_weight_le c tbl
      have h1 := ihx (Expr.hc c tbl).2
      have h2 := ihy (x.hc (Expr.hc c tbl).2)
      simp only [Act.hc, Act.treeCost] at *; omega
  | write w r v =>
      intro tbl
      have h := Expr.hc_weight_le v tbl
      simp only [Act.hc, Act.treeCost] at *; omega
  | writeSlice w r lo fw hb v =>
      intro tbl
      have h := Expr.hc_weight_le v tbl
      simp only [Act.hc, Act.treeCost] at *; omega
  | memWrite aw dw m p a d =>
      intro tbl
      have h1 := Expr.hc_weight_le a tbl
      have h2 := Expr.hc_weight_le d (Expr.hc a tbl).2
      simp only [Act.hc, Act.treeCost] at *; omega

theorem Act.cost_le_treeCost (a : Act) : a.cost ≤ a.treeCost := by
  have h := Act.hc_weight_le a []
  simpa [Act.cost, nodesWeight] using h

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
  simp [Design.cost, Design.prefixed, List.foldl_map,
    Act.cost_mapSignals (prefix_injective p)]

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
      t.classOf (d.prefixed p) { md with name := p ++ md.name }
        = t.classOf d md) :
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
does, for the same reason: `classOf` reads the whole (now composite)
design. -/
theorem par_macroBits (a b : Design) (t : MemTarget)
    (hfa : ∀ md ∈ a.mems, t.classOf (a.par b) md = t.classOf a md)
    (hfb : ∀ md ∈ b.mems, t.classOf (a.par b) md = t.classOf b md) :
    ((a.par b).cost t).macroBits
      = (a.cost t).macroBits + (b.cost t).macroBits := by
  rw [cost_macroBits, cost_macroBits, cost_macroBits, par_mems, List.foldl_append]
  rw [foldl_congr_mem (l := a.mems)
      (f := fun acc (m : MemDecl) =>
        if t.classOf (a.par b) m == MemClass.macro then
          acc + m.dataWidth * 2 ^ m.addrWidth else acc)
      (g := fun acc (m : MemDecl) =>
        if t.classOf a m == MemClass.macro then
          acc + m.dataWidth * 2 ^ m.addrWidth else acc)
      (fun md hmd c => by simp only [hfa md hmd]) 0]
  rw [foldl_congr_mem (l := b.mems)
      (f := fun acc (m : MemDecl) =>
        if t.classOf (a.par b) m == MemClass.macro then
          acc + m.dataWidth * 2 ^ m.addrWidth else acc)
      (g := fun acc (m : MemDecl) =>
        if t.classOf b m == MemClass.macro then
          acc + m.dataWidth * 2 ^ m.addrWidth else acc)
      (fun md hmd c => by simp only [hfb md hmd])]
  exact foldl_ite_add (fun m => t.classOf b m == MemClass.macro) b.mems _

/-- **Composition is monotone against `Cost.add`.**

The two `hf*` hypotheses are the target-prediction invariance discussed in
the module docstring. `hab`/`hba` say the parts do not read each other's
registers — the aliasing `Design.parOkB` refuses; without them the
`maxFanout` component is genuinely false (`par_maxFanout_gt`). -/
theorem par_cost_le (a b : Design) (t : MemTarget)
    (hfa : ∀ md ∈ a.mems, t.classOf (a.par b) md = t.classOf a md)
    (hfb : ∀ md ∈ b.mems, t.classOf (a.par b) md = t.classOf b md)
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

/-- Arbitrary technology-neutral profile used only to evaluate a memory-free
counterexample; none of its target fields can affect the result. -/
private def fanTarget : MemTarget where
  name := "logical"
  macroName := "macro"
  softName := "soft memory"
  maxMacroWritePorts := 0
  macroMinDataBits := 0
  macroMinDepth := 0
  macroInitDeliverable := false
  softInitDeliverable := false

theorem par_maxFanout_gt :
    ((fanD.par fanD).cost fanTarget).maxFanout
      > (fanD.cost fanTarget + fanD.cost fanTarget).maxFanout := by
  decide

theorem par_cost_not_le :
    ¬ ((fanD.par fanD).cost fanTarget
        ≤ fanD.cost fanTarget + fanD.cost fanTarget) := by
  intro h
  obtain ⟨-, -, -, -, hfan⟩ := h
  exact absurd hfan (by decide)

/-! ## The balanced tree builders (D18)

`reduceTree f d xs` and `xs.foldr f d` compute the same value
(`Trees.reduceTree_eval`). This section says what they cost.

**All of it is stated on `Expr.treeCost`, not `Expr.cost`**, and that is
the honest scope. The proofs work by an exact term count — "leaves, plus
one `k`-weight operator per element" — which is a true statement about a
tree and a false one about a DAG, where two of those operators can be the
same wire. `Expr.cost_le_treeCost` turns every bound here into an upper
bound on the emitted node weight, which is all a `treeCost` statement is
now entitled to claim. `reduceTree_cost_not_le_foldr` below shows the
`Expr.cost` version is not merely unproved but false. -/

/-- Total tree cost of the leaves. -/
def treeCostSum {w : Nat} (xs : List (Expr w)) : Nat :=
  xs.foldr (fun e acc => e.treeCost + acc) 0

/-- The linear chain, exactly: leaves, plus one `k`-weight operator per
element, plus the default. -/
theorem foldr_treeCost {w k : Nat} (f : Expr w → Expr w → Expr w) (d : Expr w)
    (hf : ∀ a b, (f a b).treeCost = k + a.treeCost + b.treeCost) :
    ∀ xs : List (Expr w),
      (xs.foldr f d).treeCost = treeCostSum xs + k * xs.length + d.treeCost := by
  intro xs
  induction xs with
  | nil => simp [treeCostSum]
  | cons a t ih =>
    simp only [List.foldr_cons, hf, ih, treeCostSum, List.foldr_cons, List.length_cons]
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
private theorem pairFold_treeCost {w k : Nat} (f : Expr w → Expr w → Expr w)
    (hf : ∀ a b, (f a b).treeCost = k + a.treeCost + b.treeCost) :
    ∀ xs : List (Expr w),
      treeCostSum (pairFold f xs) = treeCostSum xs + k * (xs.length / 2) := by
  intro xs
  induction xs using pairFold.induct with
  | case1 a b t ih =>
    simp only [pairFold, treeCostSum, List.foldr_cons, List.length_cons] at *
    rw [hf, ih]
    have hd : (t.length + 1 + 1) / 2 = t.length / 2 + 1 := by omega
    rw [hd, Nat.mul_add, Nat.mul_one]
    omega
  | case2 l h =>
    cases l with
    | nil => simp [pairFold, treeCostSum]
    | cons a t =>
      cases t with
      | nil => simp [pairFold, treeCostSum]
      | cons b t' => exact absurd rfl (h a b t')

private theorem reduceTreeAux_treeCost {w k : Nat} (f : Expr w → Expr w → Expr w)
    (d : Expr w) (hf : ∀ a b, (f a b).treeCost = k + a.treeCost + b.treeCost) :
    ∀ (n : Nat) (xs : List (Expr w)), xs.length ≤ n + 1 →
      (reduceTreeAux f d n xs).treeCost
        ≤ treeCostSum xs + k * (xs.length - 1) + d.treeCost := by
  intro n
  induction n with
  | zero =>
    intro xs hlen
    match xs with
    | [] => simp [reduceTreeAux, treeCostSum]
    | [x] => simp [reduceTreeAux, treeCostSum]
    | a :: b :: t => simp only [List.length_cons] at hlen; omega
  | succ n ih =>
    intro xs hlen
    match xs with
    | [] => simp [reduceTreeAux, treeCostSum]
    | [x] => simp [reduceTreeAux, treeCostSum]
    | a :: b :: t =>
      have hlen' : (pairFold f (a :: b :: t)).length ≤ n + 1 := by
        rw [pairFold_length f]
        simp only [List.length_cons] at hlen ⊢
        omega
      have hrec := ih (pairFold f (a :: b :: t)) hlen'
      rw [pairFold_treeCost f hf, pairFold_length f] at hrec
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

/-- **The balanced reduction never costs more than the linear fold — in the
tree metric.** -/
theorem reduceTree_treeCost_le_foldr {w k : Nat} (f : Expr w → Expr w → Expr w)
    (d : Expr w) (hf : ∀ a b, (f a b).treeCost = k + a.treeCost + b.treeCost)
    (xs : List (Expr w)) :
    (reduceTree f d xs).treeCost ≤ (xs.foldr f d).treeCost := by
  have h := reduceTreeAux_treeCost f d hf xs.length xs (Nat.le_succ _)
  rw [foldr_treeCost f d hf]
  refine Nat.le_trans h ?_
  have : k * (xs.length - 1) ≤ k * xs.length :=
    Nat.mul_le_mul_left k (Nat.sub_le _ _)
  omega

/-- …and on a non-empty list it costs at least one operator *less*: the
linear fold's final combine against the unit `d`, which the tree omits. -/
theorem reduceTree_treeCost_lt_foldr {w k : Nat} (f : Expr w → Expr w → Expr w)
    (d : Expr w) (hf : ∀ a b, (f a b).treeCost = k + a.treeCost + b.treeCost)
    (xs : List (Expr w)) (hne : xs ≠ []) :
    (reduceTree f d xs).treeCost + k ≤ (xs.foldr f d).treeCost := by
  have h := reduceTreeAux_treeCost f d hf xs.length xs (Nat.le_succ _)
  have hred : (reduceTree f d xs).treeCost = (reduceTreeAux f d xs.length xs).treeCost := rfl
  rw [foldr_treeCost f d hf, hred]
  have hlen : 1 ≤ xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => simp
  have hk : k * (xs.length - 1) + k = k * xs.length := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  omega

theorem orTreeW_treeCost_le {w : Nat} (xs : List (Expr w)) :
    (orTreeW xs).treeCost ≤ (xs.foldr Expr.or (Expr.lit (BitVec.ofNat w 0))).treeCost :=
  reduceTree_treeCost_le_foldr (k := w) Expr.or _ (fun _ _ => rfl) xs

theorem orTree_treeCost_le (xs : List (Expr 1)) :
    (orTree xs).treeCost ≤ (xs.foldr Expr.or (Expr.lit 0)).treeCost :=
  reduceTree_treeCost_le_foldr (k := 1) Expr.or _ (fun _ _ => rfl) xs

theorem addTree_treeCost_le {w : Nat} (xs : List (Expr w)) :
    (addTree xs).treeCost ≤ (xs.foldr Expr.add (Expr.lit (BitVec.ofNat w 0))).treeCost :=
  reduceTree_treeCost_le_foldr (k := w) Expr.add _ (fun _ _ => rfl) xs

/-- The strict form for the OR tree: `w` bits of work cheaper. -/
theorem orTreeW_treeCost_lt {w : Nat} (xs : List (Expr w)) (hne : xs ≠ []) :
    (orTreeW xs).treeCost + w
      ≤ (xs.foldr Expr.or (Expr.lit (BitVec.ofNat w 0))).treeCost :=
  reduceTree_treeCost_lt_foldr (k := w) Expr.or _ (fun _ _ => rfl) xs hne

theorem addTree_treeCost_lt {w : Nat} (xs : List (Expr w)) (hne : xs ≠ []) :
    (addTree xs).treeCost + w
      ≤ (xs.foldr Expr.add (Expr.lit (BitVec.ofNat w 0))).treeCost :=
  reduceTree_treeCost_lt_foldr (k := w) Expr.add _ (fun _ _ => rfl) xs hne

/-- The bridge: the emitted (hash-consed) weight of a balanced reduction is
bounded by the *tree* weight of the linear chain it replaces. This is the
strongest thing the section above can say about `Expr.cost`, and it is
strictly weaker than the theorem that used to be here. -/
theorem reduceTree_cost_le_foldr_treeCost {w k : Nat} (f : Expr w → Expr w → Expr w)
    (d : Expr w) (hf : ∀ a b, (f a b).treeCost = k + a.treeCost + b.treeCost)
    (xs : List (Expr w)) :
    (reduceTree f d xs).cost ≤ (xs.foldr f d).treeCost :=
  Nat.le_trans (Expr.cost_le_treeCost _) (reduceTree_treeCost_le_foldr f d hf xs)

/-! ### …and why there is no `reduceTree_cost_le_foldr`

The tree-metric proof counts one operator per list element. Under the
hash-consed cost the linear chain's operators need not be distinct *from
the leaves*: a leaf can be, structurally, one of the chain's own suffixes,
and then the chain's combines are free while the balanced tree still builds
its own. Three leaves are enough.

`ceX` is exactly `foldr Expr.or (lit 0) [ceB, ceC]`, so the chain
`or ceX (or ceB (or ceC 0))` is `or ceX ceX` and interns to three OR nodes;
the balanced tree `or (or ceX ceB) ceC` interns to four. -/

private def ceB : Expr 1 := .reg 1 "b"
private def ceC : Expr 1 := .reg 1 "c"
private def ceX : Expr 1 := .or ceB (.or ceC (.lit 0))
private def ceL : List (Expr 1) := [ceX, ceB, ceC]

/-- **`reduceTree` is NOT `≤` the linear fold under the hash-consed cost.**
The `treeCost` statement (`reduceTree_treeCost_le_foldr`) is unaffected;
what dies is the claim about what gets emitted. -/
theorem reduceTree_cost_not_le_foldr :
    ¬ ((reduceTree Expr.or (Expr.lit 0) ceL).cost
        ≤ (ceL.foldr Expr.or (Expr.lit 0)).cost) := by decide

/-- The positive case, and the one D18 actually builds: on leaves that do
not alias each other, the balanced tree is still strictly cheaper — the
chain pays one extra combine against the unit element. -/
private def dsL : List (Expr 1) :=
  [.reg 1 "p", .reg 1 "q", .reg 1 "r", .reg 1 "s"]

theorem orTree_cost_lt_example :
    (reduceTree Expr.or (Expr.lit 0) dsL).cost
      < (dsL.foldr Expr.or (Expr.lit 0)).cost := by decide

/-! ### `priTree`: still dearer, for a much smaller reason

`priPair` emits `(.or gl gr, .mux gl vl vr)`, so the left guard appears
twice in the *term*. Under the old tree cost that meant every fusion pass
copied a whole guard cone, and the balanced priority select looked
catastrophically expensive — the measurement in `Cost.lean` (+154 679
abstract bitOps against a real 357 LUT *saving*) is that error.

Under the hash-consed cost the duplicated guard is one wire and costs
nothing. What remains is that the balanced form emits `n-1` extra width-1
`or` nodes, so it is dearer by `n-1` bits and by nothing else, however
expensive the guards are. Two entries with atomic guards still show it —
one extra `.or` at width 1, `16 < 17` — so the counterexample survives, but
it is now a statement about `n-1` bits rather than about guard cones. -/

theorem priTree_cost_gt :
    (priChain [((Expr.reg 1 "g1"), (Expr.reg 8 "v1")),
               ((Expr.reg 1 "g2"), (Expr.reg 8 "v2"))] (Expr.lit 0)).cost
      < (priTree [((Expr.reg 1 "g1"), (Expr.reg 8 "v1")),
                  ((Expr.reg 1 "g2"), (Expr.reg 8 "v2"))] (Expr.lit 0)).cost := by
  decide

/-! And the point of the whole rewrite, on a select whose guards are *not*
free: a four-way select on `(opc == i) & ~stall`, sharing the `opc` read
and the `~stall` cone. -/

private def gsel (i : Nat) : Expr 1 :=
  .and (.eq (.reg 6 "opc") (.lit (BitVec.ofNat 6 i))) (.not (.reg 1 "stall"))

private def selL : List (Expr 1 × Expr 64) :=
  [(gsel 0, .reg 64 "v0"), (gsel 1, .reg 64 "v1"),
   (gsel 2, .reg 64 "v2"), (gsel 3, .reg 64 "v3")]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Under the hash-consed cost the balanced select costs exactly `n-1`
more: 285 against 288, the three extra 1-bit ORs and nothing else. -/
theorem sel_cost_dag :
    (priTree selL (.reg 64 "d")).cost = (priChain selL (.reg 64 "d")).cost + 3 := by
  decide

/-- Under the old tree cost the same pair differed by 36 — twelve times as
much — because each of the four guard cones was billed twice. That factor
is what made the model call a 357 LUT saving a large regression. -/
theorem sel_cost_tree :
    (priTree selL (.reg 64 "d")).treeCost
      = (priChain selL (.reg 64 "d")).treeCost + 36 := by
  decide

end Loom.Hw
