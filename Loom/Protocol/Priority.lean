-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

/-!
# Priority orders as data (D36)

Two mechanized engines state the same kind of obligation about their check:

* `Machines/Epoch/Protocol.lean` T-E4 — §3's "failure precedence is
  structural, then poison, then freshness, then rights";
* `Machines/CapWalk/Protocol.lean` T-C2 — §2.2's "checks occur in that
  order".

and both discharge it the same way, twice, by hand: six or seven
`X_before_Y` lemmas at arbitrary width, plus one exhaustive `decide` at the
model's bounds against a *separately written* priority function (2^10 views
for T-E4, 2048 for T-C2).

This file makes the priority order a **first-class object** instead of
prose duplicated across a nest of `if`s and a second nest of `if`s. A
`Priority` is a list of `(guard, outcome)` clauses plus a fallback; the
ordering lemmas are derived from the list at arbitrary width
(`Agrees.fires`), and the exhaustive check is the same `Agrees` statement
at a small width, where the kernel can just enumerate it.

## The two obligations, and how they differ

`Agrees f P` says the engine's hand-written total function `f` **is** the
order `P`. An engine gets it either way round:

* by proof, at arbitrary width — then every `X_before_Y` lemma follows from
  `Agrees.fires` with no further case analysis;
* by `decide`, at the model's bounds — the independent cross-check that the
  hand-written nest of `if`s and the clause list denote the same order,
  which is exactly what T-E4/T-C2's exhaustive theorems buy.

Both are kept, because they are different evidence: one is a proof, the
other is an enumeration against an independently written artifact.

**Note on `decide`.** The view type of a real check is a record of small
`BitVec`s and `Bool`s. Mathlib's derived `Fintype` instance does not reduce
in the kernel (it is built with `Eq.mpr`), so the enumeration is done the
way the frozen engines do it — destructure the view and `revert` its
fields, leaving a curried `∀` over `BitVec`/`Bool` whose core instances do
reduce. No `native_decide` anywhere.
-/

namespace Loom

/-- One clause of a priority order: the guard that selects it, and the
outcome it commits to when it is the **first** guard to fire. The outcome
may still depend on the view — §2.2's empty-slot clause is
`if cep = qep then badref else stale`, one clause with a view-dependent
result. -/
structure Clause (V O : Type) where
  /-- The guard. -/
  guard : V → Bool
  /-- The outcome, when this clause is the first whose guard fires. -/
  out : V → O

/-- A priority order: clauses in order of precedence, plus the outcome for
a view that trips no guard. -/
structure Priority (V O : Type) where
  /-- The clauses, highest precedence first. -/
  clauses : List (Clause V O)
  /-- The fall-through outcome. -/
  fallback : V → O

namespace Priority

variable {V O : Type}

/-- First-match evaluation of a clause list. -/
def evalList (cs : List (Clause V O)) (fb : V → O) (v : V) : O :=
  match cs with
  | [] => fb v
  | c :: rest => if c.guard v then c.out v else evalList rest fb v

/-- The total outcome function a priority order denotes. -/
def eval (P : Priority V O) (v : V) : O := evalList P.clauses P.fallback v

@[simp] theorem evalList_nil {fb : V → O} {v : V} : evalList [] fb v = fb v := rfl

@[simp] theorem evalList_cons_pos {c : Clause V O} {cs : List (Clause V O)}
    {fb : V → O} {v : V} (h : c.guard v = true) :
    evalList (c :: cs) fb v = c.out v := by simp [evalList, h]

@[simp] theorem evalList_cons_neg {c : Clause V O} {cs : List (Clause V O)}
    {fb : V → O} {v : V} (h : c.guard v = false) :
    evalList (c :: cs) fb v = evalList cs fb v := by simp [evalList, h]

/-- **The ordering rule.** The first clause whose guard fires decides the
outcome — whatever any later clause would have said. Splitting the clause
list as `pre ++ c :: post` and requiring only that `pre`'s guards are false
is the `X_before_Y` shape: `post` never appears in the statement, which is
precisely the claim that `c` outranks everything after it. -/
theorem eval_of_first {P : Priority V O} {pre post : List (Clause V O)}
    {c : Clause V O} {v : V} (hsplit : P.clauses = pre ++ c :: post)
    (hpre : ∀ d ∈ pre, d.guard v = false) (hc : c.guard v = true) :
    P.eval v = c.out v := by
  rw [eval, hsplit]
  clear hsplit
  induction pre with
  | nil => simpa using evalList_cons_pos (cs := post) (fb := P.fallback) hc
  | cons d ds ih =>
      rw [List.cons_append,
        evalList_cons_neg (hpre d List.mem_cons_self)]
      exact ih (fun x hx => hpre x (List.mem_cons_of_mem _ hx))

theorem evalList_of_none {fb : V → O} {v : V} : ∀ (cs : List (Clause V O)),
    (∀ c ∈ cs, c.guard v = false) → evalList cs fb v = fb v
  | [], _ => rfl
  | c :: cs, h => by
      rw [evalList_cons_neg (h c List.mem_cons_self)]
      exact evalList_of_none cs (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The fall-through rule: a view that trips no guard gets the default. -/
theorem eval_of_none {P : Priority V O} {v : V}
    (h : ∀ c ∈ P.clauses, c.guard v = false) : P.eval v = P.fallback v :=
  evalList_of_none P.clauses h

/-- **The obligation**: this total outcome function *is* this priority
order. Proved at arbitrary width, or decided at the model's bounds. -/
def Agrees (f : V → O) (P : Priority V O) : Prop := ∀ v, f v = P.eval v

namespace Agrees

variable {f : V → O} {P : Priority V O}

theorem eq (h : Agrees f P) (v : V) : f v = P.eval v := h v

/-- **The per-clause lemma generator.** Everything the two engines write by
hand as `X_before_Y` is this, applied to a split of the clause list: given
that the higher-precedence guards are false and this one fires, the
hand-written function returns this clause's outcome — regardless of every
lower-precedence guard. -/
theorem fires (h : Agrees f P) {pre post : List (Clause V O)} {c : Clause V O}
    {v : V} (hsplit : P.clauses = pre ++ c :: post)
    (hpre : ∀ d ∈ pre, d.guard v = false) (hc : c.guard v = true) :
    f v = c.out v := by rw [h v]; exact eval_of_first hsplit hpre hc

/-- The fall-through half: all guards false gives the default outcome. -/
theorem falls (h : Agrees f P) {v : V}
    (hall : ∀ c ∈ P.clauses, c.guard v = false) : f v = P.fallback v := by
  rw [h v]; exact eval_of_none hall

end Agrees
end Priority
end Loom
