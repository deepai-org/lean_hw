-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics

/-!
# Balanced-tree builders (timing; semantics-preserving)

The Verilog emitter turns a `foldr`/`foldl` over a list of guarded values
into a *linear* mux/or/add chain, so a 64-entry fold becomes a 64-level
combinational cone.  The builders here produce the SAME function of the
same inputs at `O(log n)` depth.

These were written inline in `Machines/Lnp64mini/Core.lean`; this module is
the machine-independent extraction, **with the evaluation lemmas the
original never had**:

* `reduceTree_eval` — a balanced `f`-reduction equals the linear `foldr`
  whenever `f`'s denotation is associative with `d` as a right unit;
  specialised to the two operators actually used (`orTree_eval`,
  `addTree_eval`, `orTreeW_eval`);
* `priTree_eval` — the balanced priority select equals the linear
  first-match-wins mux chain, with **no** mutual-exclusivity assumption on
  the guards;
* `actPriTree_run` — likewise for `Act` else-if chains.

Everything is proved (no `sorry`, no new axioms).
-/

namespace Loom.Hw

/-! ## Associative reduction -/

/-- One balanced-reduction pass: fuse adjacent elements with `f`. -/
def pairFold {w : Nat} (f : Expr w → Expr w → Expr w) : List (Expr w) → List (Expr w)
  | a :: b :: t => f a b :: pairFold f t
  | l => l

def reduceTreeAux {w : Nat} (f : Expr w → Expr w → Expr w) (d : Expr w) :
    Nat → List (Expr w) → Expr w
  | _,   []  => d
  | _,   [x] => x
  | 0,   xs  => xs.foldr f d          -- fuel guard; never taken (fuel = length)
  | n+1, xs  => reduceTreeAux f d n (pairFold f xs)

/-- Balanced `f`-reduction of `xs` (`d` when empty). -/
def reduceTree {w : Nat} (f : Expr w → Expr w → Expr w) (d : Expr w)
    (xs : List (Expr w)) : Expr w :=
  reduceTreeAux f d xs.length xs

/-- Balanced OR-reduction at width 1. -/
def orTree (xs : List (Expr 1)) : Expr 1 := reduceTree .or (.lit 0) xs

/-- Balanced OR-reduction at width `w` (disjoint-lane merges). -/
def orTreeW {w : Nat} (xs : List (Expr w)) : Expr w :=
  reduceTree .or (.lit (BitVec.ofNat w 0)) xs

/-- Balanced ADD-reduction (popcount-style sums). -/
def addTree {w : Nat} (xs : List (Expr w)) : Expr w :=
  reduceTree .add (.lit (BitVec.ofNat w 0)) xs

/-! ### Correctness of the balanced reduction -/

/-- The denotation of the linear `foldr` the tree is supposed to equal. -/
def foldEval {w : Nat} (σ : St) (g : BitVec w → BitVec w → BitVec w)
    (z : BitVec w) (xs : List (Expr w)) : BitVec w :=
  xs.foldr (fun e acc => g (e.eval σ) acc) z

theorem foldr_eval {w : Nat} (σ : St) (f : Expr w → Expr w → Expr w)
    (g : BitVec w → BitVec w → BitVec w) (d : Expr w)
    (hf : ∀ a b, (f a b).eval σ = g (a.eval σ) (b.eval σ)) :
    ∀ xs : List (Expr w), (xs.foldr f d).eval σ = foldEval σ g (d.eval σ) xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a t ih => simp only [List.foldr_cons, hf, ih, foldEval]

theorem pairFold_eval {w : Nat} (σ : St) (f : Expr w → Expr w → Expr w)
    (g : BitVec w → BitVec w → BitVec w) (z : BitVec w)
    (hf : ∀ a b, (f a b).eval σ = g (a.eval σ) (b.eval σ))
    (hassoc : ∀ a b c, g (g a b) c = g a (g b c)) :
    ∀ xs : List (Expr w), foldEval σ g z (pairFold f xs) = foldEval σ g z xs := by
  intro xs
  induction xs using pairFold.induct with
  | case1 a b t ih =>
    simp only [pairFold, foldEval, List.foldr_cons] at *
    rw [hf, ih, hassoc]
  | case2 l h =>
    cases l with
    | nil => rfl
    | cons a t =>
      cases t with
      | nil => rfl
      | cons b t' => exact absurd rfl (h a b t')

theorem reduceTreeAux_eval {w : Nat} (σ : St) (f : Expr w → Expr w → Expr w)
    (g : BitVec w → BitVec w → BitVec w) (d : Expr w)
    (hf : ∀ a b, (f a b).eval σ = g (a.eval σ) (b.eval σ))
    (hassoc : ∀ a b c, g (g a b) c = g a (g b c))
    (hunit : ∀ a, g a (d.eval σ) = a) :
    ∀ (n : Nat) (xs : List (Expr w)),
      (reduceTreeAux f d n xs).eval σ = foldEval σ g (d.eval σ) xs := by
  intro n
  induction n with
  | zero =>
    intro xs
    match xs with
    | [] => rfl
    | [x] => simpa [reduceTreeAux, foldEval] using (hunit (x.eval σ)).symm
    | a :: b :: t =>
      simpa [reduceTreeAux] using foldr_eval σ f g d hf (a :: b :: t)
  | succ n ih =>
    intro xs
    match xs with
    | [] => rfl
    | [x] => simpa [reduceTreeAux, foldEval] using (hunit (x.eval σ)).symm
    | a :: b :: t =>
      simp only [reduceTreeAux]
      rw [ih, pairFold_eval σ f g (d.eval σ) hf hassoc]

/-- **The balanced reduction computes the linear fold.** -/
theorem reduceTree_eval {w : Nat} (σ : St) (f : Expr w → Expr w → Expr w)
    (g : BitVec w → BitVec w → BitVec w) (d : Expr w)
    (hf : ∀ a b, (f a b).eval σ = g (a.eval σ) (b.eval σ))
    (hassoc : ∀ a b c, g (g a b) c = g a (g b c))
    (hunit : ∀ a, g a (d.eval σ) = a) (xs : List (Expr w)) :
    (reduceTree f d xs).eval σ = (xs.foldr f d).eval σ := by
  rw [reduceTree, reduceTreeAux_eval σ f g d hf hassoc hunit,
    foldr_eval σ f g d hf]

theorem orTreeW_eval {w : Nat} (σ : St) (xs : List (Expr w)) :
    (orTreeW xs).eval σ
      = (xs.foldr Expr.or (Expr.lit (BitVec.ofNat w 0))).eval σ :=
  reduceTree_eval σ Expr.or (· ||| ·) (Expr.lit (BitVec.ofNat w 0))
    (fun _ _ => rfl) (fun a b c => BitVec.or_assoc a b c)
    (fun a => by simp [Expr.eval]) xs

theorem orTree_eval (σ : St) (xs : List (Expr 1)) :
    (orTree xs).eval σ = (xs.foldr Expr.or (Expr.lit 0)).eval σ :=
  reduceTree_eval σ Expr.or (· ||| ·) (Expr.lit 0)
    (fun _ _ => rfl) (fun a b c => BitVec.or_assoc a b c)
    (fun a => by simp [Expr.eval]) xs

theorem addTree_eval {w : Nat} (σ : St) (xs : List (Expr w)) :
    (addTree xs).eval σ
      = (xs.foldr Expr.add (Expr.lit (BitVec.ofNat w 0))).eval σ :=
  reduceTree_eval σ Expr.add (· + ·) (Expr.lit (BitVec.ofNat w 0))
    (fun _ _ => rfl) (fun a b c => BitVec.add_assoc a b c)
    (fun a => by simp [Expr.eval]) xs

/-! ## Priority select -/

/-- Fuse two guarded groups into one, keeping *earliest-guard-wins*. -/
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

/-- Balanced priority select: exactly
`xs.foldr (fun (g,v) acc => .mux g v acc) d` at `O(log n)` depth. -/
def priTree {w : Nat} (xs : List (Expr 1 × Expr w)) (d : Expr w) : Expr w :=
  priTreeAux xs.length xs d

/-- Last-match-wins variant (mirrors a `foldl` funnel). -/
def priTreeLast {w : Nat} (xs : List (Expr 1 × Expr w)) (d : Expr w) : Expr w :=
  priTree xs.reverse d

/-- The linear chain `priTree` is supposed to equal. -/
def priChain {w : Nat} (xs : List (Expr 1 × Expr w)) (d : Expr w) : Expr w :=
  xs.foldr (fun gv acc => .mux gv.1 gv.2 acc) d

/-! ### Correctness of the balanced priority select -/

theorem bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have h : x.toNat < 2 := by simpa using x.isLt
  have h2 : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases h2 with h0 | h1
  · exact Or.inl (BitVec.toNat_inj.mp (by simp [h0]))
  · exact Or.inr (BitVec.toNat_inj.mp (by simp [h1]))

theorem priPairFold_eval {w : Nat} (σ : St) (d : Expr w) :
    ∀ xs : List (Expr 1 × Expr w),
      (priChain (priPairFold xs) d).eval σ = (priChain xs d).eval σ := by
  intro xs
  induction xs using priPairFold.induct with
  | case1 a b t ih =>
    obtain ⟨gl, vl⟩ := a
    obtain ⟨gr, vr⟩ := b
    simp only [priPairFold, priPair, priChain, List.foldr_cons, Expr.eval] at *
    rcases bv1_cases (gl.eval σ) with h | h <;> simp only [h] <;>
      rcases bv1_cases (gr.eval σ) with h' | h' <;> simp only [h'] <;>
      simp [ih]
  | case2 l h =>
    cases l with
    | nil => rfl
    | cons a t =>
      cases t with
      | nil => rfl
      | cons b t' => exact absurd rfl (h a b t')

theorem priTreeAux_eval {w : Nat} (σ : St) (d : Expr w) :
    ∀ (n : Nat) (xs : List (Expr 1 × Expr w)),
      (priTreeAux n xs d).eval σ = (priChain xs d).eval σ := by
  intro n
  induction n with
  | zero =>
    intro xs
    match xs with
    | [] => rfl
    | [(g,v)] => rfl
    | a :: b :: t => rfl
  | succ n ih =>
    intro xs
    match xs with
    | [] => rfl
    | [(g,v)] => rfl
    | a :: b :: t =>
      simp only [priTreeAux]
      rw [ih, priPairFold_eval]

/-- **The balanced priority select computes the linear mux chain.**  No
mutual exclusivity between the guards is required. -/
theorem priTree_eval {w : Nat} (σ : St) (xs : List (Expr 1 × Expr w))
    (d : Expr w) : (priTree xs d).eval σ = (priChain xs d).eval σ :=
  priTreeAux_eval σ d xs.length xs

theorem priTreeLast_eval {w : Nat} (σ : St) (xs : List (Expr 1 × Expr w))
    (d : Expr w) : (priTreeLast xs d).eval σ = (priChain xs.reverse d).eval σ :=
  priTree_eval σ xs.reverse d

/-! ## The same trick for `Act` else-if chains -/

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

/-- Balanced else-if chain. -/
def actPriTree (xs : List (Expr 1 × Act)) (d : Act) : Act :=
  actPriTreeAux xs.length xs d

/-- The linear chain `actPriTree` is supposed to equal. -/
def actChain (xs : List (Expr 1 × Act)) (d : Act) : Act :=
  xs.foldr (fun ga acc => .ite ga.1 ga.2 acc) d

/-- Right-nested sequence of a list of actions. -/
def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

theorem actPriPairFold_run (σ : St) (d : Act) :
    ∀ (xs : List (Expr 1 × Act)) (acc : St),
      (actChain (actPriPairFold xs) d).run σ acc = (actChain xs d).run σ acc := by
  intro xs
  induction xs using actPriPairFold.induct with
  | case1 a b t ih =>
    obtain ⟨gl, al⟩ := a
    obtain ⟨gr, ar⟩ := b
    intro acc
    simp only [actPriPairFold, actPriPair, actChain, List.foldr_cons, Act.run,
      Expr.eval] at *
    rcases bv1_cases (gl.eval σ) with h | h <;> simp only [h] <;>
      rcases bv1_cases (gr.eval σ) with h' | h' <;> simp only [h'] <;>
      simp [ih]
  | case2 l h =>
    intro acc
    cases l with
    | nil => rfl
    | cons a t =>
      cases t with
      | nil => rfl
      | cons b t' => exact absurd rfl (h a b t')

theorem actPriTreeAux_run (σ : St) (d : Act) :
    ∀ (n : Nat) (xs : List (Expr 1 × Act)) (acc : St),
      (actPriTreeAux n xs d).run σ acc = (actChain xs d).run σ acc := by
  intro n
  induction n with
  | zero =>
    intro xs acc
    match xs with
    | [] => rfl
    | [(g,a)] => rfl
    | a :: b :: t => rfl
  | succ n ih =>
    intro xs acc
    match xs with
    | [] => rfl
    | [(g,a)] => rfl
    | a :: b :: t =>
      simp only [actPriTreeAux]
      rw [ih, actPriPairFold_run]

/-- **The balanced else-if chain runs exactly like the linear one.** -/
theorem actPriTree_run (σ : St) (xs : List (Expr 1 × Act)) (d : Act) (acc : St) :
    (actPriTree xs d).run σ acc = (actChain xs d).run σ acc :=
  actPriTreeAux_run σ d xs.length xs acc

/-! ## Generic dynamic (index-computed) access over a name builder -/

/-- `nameOf idx <= v idx` for the one `idx` the runtime index selects: a
guarded write per family member, in index order (last write wins, but the
guards are mutually exclusive so at most one fires). -/
def dynWrite {iw w : Nat} (n : Nat) (idx : Expr iw) (nameOf : Nat → String)
    (v : Nat → Expr w) : Act :=
  actSeq ((List.range n).map (fun i =>
    .ite (.eq idx (.lit (BitVec.ofNat iw i))) (.write w (nameOf i) (v i)) .skip))

/-- The balanced dynamic read `val[idx]` (`dflt` when `idx` is out of the
family). -/
def dynRead {iw w : Nat} (n : Nat) (idx : Expr iw) (val : Nat → Expr w)
    (dflt : Expr w) : Expr w :=
  priTree ((List.range n).map
    (fun i => ((Expr.eq idx (.lit (BitVec.ofNat iw i)) : Expr 1), val i))) dflt

end Loom.Hw
