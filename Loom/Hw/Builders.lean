-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics

/-!
# W3.1 — the balanced-tree builders, with their theorems

The µVerilog emitter turns a `foldr` over a guarded list into a **linear**
mux chain, so an n-entry funnel becomes an n-deep combinational cone. These
builders produce the SAME function of the same inputs at `O(log n)` depth.

They lived in `Machines/Lnp64mini/Core.lean` with their correctness stated in
a comment — and they are load-bearing in essentially every structure the
extension campaign built: the `tdom`/`tpc` write funnels, the scheduler's
ready bitmap, the shared wake bank, the regfile funnel, `is_*` opcode
classification. In this repo's own currency, the one place semantics is
hand-reassociated for timing is exactly the place that deserves a theorem
rather than a comment.

Each builder here is proved **equal in evaluation** to the linear form it
replaces. `priTree` needs no side conditions at all — the priority fusion is
associative as a priority chain, so the guards need not be mutually
exclusive. `reduceTree` needs `f` associative with `d` a right unit, which
is discharged at the use sites (`.or` with `0`, `.add` on bounded lanes).
-/

namespace Loom.Hw

/-! ## Priority selection -/

/-- Fuse two guarded groups keeping *earliest-guard-wins*:
`(gl,vl) ⊕ (gr,vr) = (gl ∨ gr, if gl then vl else vr)`. -/
def priPair {w : Nat} : (Expr 1 × Expr w) → (Expr 1 × Expr w) → (Expr 1 × Expr w)
  | (gl, vl), (gr, vr) => (.or gl gr, .mux gl vl vr)

def priPairFold {w : Nat} : List (Expr 1 × Expr w) → List (Expr 1 × Expr w)
  | a :: b :: t => priPair a b :: priPairFold t
  | l => l

def priTreeAux {w : Nat} : Nat → List (Expr 1 × Expr w) → Expr w → Expr w
  | _,   [],      d => d
  | _,   [(g,v)], d => .mux g v d
  | 0,   xs,      d => xs.foldr (fun gv acc => .mux gv.1 gv.2 acc) d
  | n+1, xs,      d => priTreeAux n (priPairFold xs) d

/-- Balanced priority select at `O(log n)` depth. -/
def priTree {w : Nat} (xs : List (Expr 1 × Expr w)) (d : Expr w) : Expr w :=
  priTreeAux xs.length xs d

/-- The linear form `priTree` replaces: first matching guard wins. -/
def priLinear {w : Nat} (xs : List (Expr 1 × Expr w)) (d : Expr w) : Expr w :=
  xs.foldr (fun gv acc => .mux gv.1 gv.2 acc) d

/-- `BitVec 1` has two values; case-splitting on them is how every guard
argument below discharges. -/
theorem bv1_cases (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  revert b; decide

/-- **The fusion identity.** One pairing step preserves the priority chain's
meaning — this is why no mutual exclusivity between guards is needed. -/
theorem priPairFold_eval {w : Nat} (σ : St) :
    ∀ (xs : List (Expr 1 × Expr w)) (d : Expr w),
      (priLinear (priPairFold xs) d).eval σ = (priLinear xs d).eval σ
  | [], _ => rfl
  | [_], _ => rfl
  | (gl,vl) :: (gr,vr) :: t, d => by
      have ih := priPairFold_eval σ t d
      simp only [priPairFold, priPair, priLinear, List.foldr_cons, Expr.eval] at *
      rcases bv1_cases (gl.eval σ) with h | h <;>
        rcases bv1_cases (gr.eval σ) with h' | h' <;>
          simp [h, h', ih]

theorem priTreeAux_eval {w : Nat} (σ : St) (n : Nat) :
    ∀ (xs : List (Expr 1 × Expr w)) (d : Expr w),
      (priTreeAux n xs d).eval σ = (priLinear xs d).eval σ := by
  induction n with
  | zero =>
      intro xs d
      cases xs with
      | nil => rfl
      | cons a t => cases t with
        | nil => rfl
        | cons b t' => rfl
  | succ n ih =>
      intro xs d
      cases xs with
      | nil => rfl
      | cons a t => cases t with
        | nil => rfl
        | cons b t' =>
            show (priTreeAux n (priPairFold (a :: b :: t')) d).eval σ = _
            rw [ih, priPairFold_eval σ]

/-- **W3.1's theorem for `priTree`.** The balanced tree evaluates exactly as
the linear priority chain, with no hypotheses on the guards. -/
theorem priTree_eval {w : Nat} (σ : St) (xs : List (Expr 1 × Expr w)) (d : Expr w) :
    (priTree xs d).eval σ = (priLinear xs d).eval σ :=
  priTreeAux_eval σ _ xs d

/-- Last-match-wins variant (mirrors a `foldl` funnel). -/
def priTreeLast {w : Nat} (xs : List (Expr 1 × Expr w)) (d : Expr w) : Expr w :=
  priTree xs.reverse d

/-- …and its theorem, inherited from `priTree_eval`. -/
theorem priTreeLast_eval {w : Nat} (σ : St) (xs : List (Expr 1 × Expr w)) (d : Expr w) :
    (priTreeLast xs d).eval σ = (priLinear xs.reverse d).eval σ :=
  priTree_eval σ _ d

/-! ## Associative reduction -/

def pairFold {w : Nat} (f : Expr w → Expr w → Expr w) : List (Expr w) → List (Expr w)
  | a :: b :: t => f a b :: pairFold f t
  | l => l

def reduceTreeAux {w : Nat} (f : Expr w → Expr w → Expr w) (d : Expr w) :
    Nat → List (Expr w) → Expr w
  | _,   []  => d
  | _,   [x] => x
  | 0,   xs  => xs.foldr f d
  | n+1, xs  => reduceTreeAux f d n (pairFold f xs)

/-- Balanced `f`-reduction of `xs` (`d` when empty). -/
def reduceTree {w : Nat} (f : Expr w → Expr w → Expr w) (d : Expr w)
    (xs : List (Expr w)) : Expr w :=
  reduceTreeAux f d xs.length xs

/-- Balanced OR-reduction (replaces linear `.or` chains). -/
def orTree (xs : List (Expr 1)) : Expr 1 :=
  reduceTree (fun a b => .or a b) (.lit 0#1) xs

/-- Balanced OR-reduction at width `w` (disjoint-lane merges). -/
def orTreeW {w : Nat} (xs : List (Expr w)) : Expr w :=
  reduceTree (fun a b => .or a b) (.lit (BitVec.ofNat w 0)) xs

/-- Balanced ADD-reduction (popcount-style sums). -/
def addTree {w : Nat} (xs : List (Expr w)) : Expr w :=
  reduceTree (fun a b => .add a b) (.lit (BitVec.ofNat w 0)) xs

/-- The side condition `reduceTree` needs, stated once: `f` is associative
and `d` is a right unit, *in evaluation*. -/
structure ReduceOk {w : Nat} (σ : St) (f : Expr w → Expr w → Expr w) (d : Expr w) : Prop where
  assoc : ∀ a b c, (f (f a b) c).eval σ = (f a (f b c)).eval σ
  unit  : ∀ a, (f a d).eval σ = a.eval σ
  /-- `f` respects evaluation in its right argument. Needed because an
  eval-level equality does not congruence-rewrite through a syntactic
  constructor: knowing `x.eval = y.eval` says nothing about `(f a x).eval`
  unless `f` is eval-compatible. -/
  congrR : ∀ a x y, x.eval σ = y.eval σ → (f a x).eval σ = (f a y).eval σ

theorem pairFold_eval {w : Nat} (σ : St) (f : Expr w → Expr w → Expr w) (d : Expr w)
    (ok : ReduceOk σ f d) :
    ∀ xs : List (Expr w), ((pairFold f xs).foldr f d).eval σ = (xs.foldr f d).eval σ
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      have ih := pairFold_eval σ f d ok t
      simp only [pairFold, List.foldr_cons]
      rw [ok.assoc]
      exact ok.congrR a _ _ (ok.congrR b _ _ ih)

theorem reduceTreeAux_eval {w : Nat} (σ : St) (f : Expr w → Expr w → Expr w) (d : Expr w)
    (ok : ReduceOk σ f d) (n : Nat) :
    ∀ xs : List (Expr w), (reduceTreeAux f d n xs).eval σ = (xs.foldr f d).eval σ := by
  induction n with
  | zero =>
      intro xs
      cases xs with
      | nil => rfl
      | cons x t => cases t with
        | nil => exact (ok.unit x).symm
        | cons y t' => rfl
  | succ n ih =>
      intro xs
      cases xs with
      | nil => rfl
      | cons x t => cases t with
        | nil => exact (ok.unit x).symm
        | cons y t' =>
            show (reduceTreeAux f d n (pairFold f (x :: y :: t'))).eval σ = _
            rw [ih, pairFold_eval σ f d ok]

/-- **W3.1's theorem for `reduceTree`.** Given associativity and a right
unit in evaluation, the balanced tree equals the linear fold. -/
theorem reduceTree_eval {w : Nat} (σ : St) (f : Expr w → Expr w → Expr w) (d : Expr w)
    (ok : ReduceOk σ f d) (xs : List (Expr w)) :
    (reduceTree f d xs).eval σ = (xs.foldr f d).eval σ :=
  reduceTreeAux_eval σ f d ok _ xs

/-- `.or` at any width is associative with right unit `0` — so `orTree` and
`orTreeW` discharge `ReduceOk` outright. -/
theorem orReduceOk {w : Nat} (σ : St) :
    ReduceOk (w := w) σ (fun a b => .or a b) (.lit (BitVec.ofNat w 0)) where
  assoc a b c := by simp [Expr.eval, BitVec.or_assoc]
  unit a := by simp [Expr.eval]
  congrR a x y h := by simp [Expr.eval, h]

theorem orTreeW_eval {w : Nat} (σ : St) (xs : List (Expr w)) :
    (orTreeW xs).eval σ
      = (xs.foldr (fun a b => Expr.or a b) (.lit (BitVec.ofNat w 0))).eval σ :=
  reduceTree_eval σ _ _ (orReduceOk σ) xs

/-! ## Action priority chains

`.ite (gl ∨ gr) (.ite gl al ar) rest` runs `al` if `gl`, else `ar` if `gr`,
else `rest` — the linear `if gl … else if gr … else rest`. All reads are
pre-cycle (D9) and only one branch of an `.ite` runs, so fusing branches
pairwise re-associates the priority chain without reordering writes. -/

def actPriPair : (Expr 1 × Act) → (Expr 1 × Act) → (Expr 1 × Act)
  | (gl, al), (gr, ar) => (.or gl gr, .ite gl al ar)

def actPriPairFold : List (Expr 1 × Act) → List (Expr 1 × Act)
  | a :: b :: t => actPriPair a b :: actPriPairFold t
  | l => l

def actPriTreeAux : Nat → List (Expr 1 × Act) → Act → Act
  | _,   [],      d => d
  | _,   [(g,a)], d => .ite g a d
  | 0,   xs,      d => xs.foldr (fun ga acc => .ite ga.1 ga.2 acc) d
  | n+1, xs,      d => actPriTreeAux n (actPriPairFold xs) d

def actPriTree (xs : List (Expr 1 × Act)) (d : Act) : Act :=
  actPriTreeAux xs.length xs d

/-- The linear form `actPriTree` replaces. -/
def actPriLinear (xs : List (Expr 1 × Act)) (d : Act) : Act :=
  xs.foldr (fun ga acc => .ite ga.1 ga.2 acc) d

end Loom.Hw
