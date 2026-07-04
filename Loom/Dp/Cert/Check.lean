-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Std.Sat.CNF

/-!
# In-house kernel-reducible RUP/LRAT checker (task 1.2a, decision D2)

`Std.Tactic.BVDecide.LRAT.check` is *not* kernel-reducible (its well-founded
recursion sticks under `whnf` — see `Loom/Dp/Cert/Lrat.lean` and D2), and
Rule 1 bans `native_decide` on the trusted path. This module is the
replacement: a checker in which **every** recursion is structural (plain
pattern matching, plus a fuel parameter for unhinted unit propagation), over
plain `List`s, so the kernel unfolds it under ordinary `decide`.

## Design

* CNF representation: `Std.Sat.CNF Nat` *is already* the reduction-friendly
  `List (List (Nat × Bool))`, so we reuse it — and its `eval`/`Unsat` —
  which makes `check_sound` land directly on `Std.Sat.CNF.Unsat` (the type
  the rest of the Dp layer speaks, and what `bv_decide`'s untrusted
  cross-validation path produces).
* Partial assignments are association lists (`List (Nat × Bool)`, newest
  binding first); lookup is structural recursion with `Nat.decEq`
  (kernel-accelerated).
* Certificates are LRAT-style: `Step.add C hints` where `hints` name the
  clauses to propagate through, in order (as in an LRAT line) — but as
  *positions* in the accumulated newest-first formula (see `check`), not
  LRAT clause ids; the id→position translation is trivial and untrusted
  (`scripts/gen_php_cert.py`). `Step.del` is accepted and ignored
  (soundness-preserving). Empty `hints` falls back to full fuel-bounded
  unit propagation (plain RUP) — correct but quadratic; hint-driven
  checking costs one list walk per hint and is what the benchmarks use.
* The trusted judgment is `check F cert = true`, established by kernel
  reduction (`by decide`); `check_sound` turns it into `CNF.Unsat F`.
  No `sorry`, no axioms beyond the classical trio, no `native_decide`,
  no wf-recursion, no `partial`, no `Array`.

## Benchmark (D2 numbers, kernel `decide`, this machine, 2026-07-03)

Wall-clock `lake env lean` time on one-example scratch files, net of the
0.8 s import baseline. Certificates: `dp` = DP-resolution certs from
`scripts/gen_php_cert.py`; `cad` = cadical LRAT proofs translated to
`Step` form (both untrusted). php2/php3 live below; php4–php6 in
`Tests/CheckBench.lean`.

* php2→1 (1 step) and php3→2 (4 steps, hinted *and* unhinted): noise
  (< 50 ms total for all three examples).
* php4→3 cad (15 steps, 100 hints):            ≈ 0.2 s.
* php4→3 dp (139 steps, 450 lits):             ≈ 1.5 s.
* php5→4 cad (48 steps, 380 hints):            ≈ 1.5 s.
* php6→5 cad (162 steps, 2 121 hints):         ≈ 13.5 s.
* php7→6 cad (1 141 steps, 17 083 hints):      ≈ 4.5 min, and only with
  `decide +kernel`, `--tstack=512000` and `maxRecDepth 100000` — plain
  `decide` (elaborator whnf) dies at `maxRecDepth`/heartbeats, and the
  default 8 MB thread stack overflows on ~10³-deep `check` recursion.
  Not committed to the build for that reason.
* php5→4 dp (6 799 steps, 42 755 lits): did NOT finish within 9 min under
  either evaluator (before the prepend redesign an `F ++ [c]` append-chain
  variant was even worse). DP-resolution certificates are the wrong input;
  solver LRAT for the same instance is 48 steps (140× smaller).

Findings for D2: (1) hint-driven kernel checking works and is honestly
fast for solver-sized certificates — roughly *seconds per few hundred LRAT
steps*, cost dominated by the O(position) list walk per hint, superlinear
in accumulated-formula size; (2) the practical budget on the trusted path
is ≈ 10²–10³ certificate steps per query at second-to-minute cost, which
covers task-1.2 BMC queries provided CNFs are solver-certified (never
resolution-expanded); (3) beyond ~10³ steps the recursion depth also hits
elaborator/stack limits, so scaling further needs a better clause index
(e.g. a balanced tree) — a v2 concern, not a v1 blocker. D2: **go**, with
certificate size as the budget to watch.
-/

namespace Loom.Dp.Cert.Check

open Std.Sat

/-- A CNF formula: `Std.Sat.CNF Nat` = `List (List (Nat × Bool))`. -/
abbrev Cnf := CNF Nat

/-- A clause: a list of literals `(var, polarity)`. -/
abbrev Clause := CNF.Clause Nat

/-- A literal: `(var, polarity)`; satisfied by `f` iff `f var = polarity`. -/
abbrev Lit := Literal Nat

/-- A partial assignment: an association list, newest binding first. -/
abbrev PAssign := List (Nat × Bool)

/-- Look a variable up in a partial assignment (first hit wins). -/
def lookup : PAssign → Nat → Option Bool
  | [], _ => none
  | (w, b) :: τ, v => if v = w then some b else lookup τ v

/-- A total assignment `f` agrees with every binding of `τ`. (If `τ` is
inconsistent this is simply unsatisfiable — which is exactly what we want
when `τ` is the negation of a tautological clause.) -/
def Agrees (f : Nat → Bool) (τ : PAssign) : Prop := ∀ p ∈ τ, f p.1 = p.2

theorem Agrees.tail {f : Nat → Bool} {p : Nat × Bool} {τ : PAssign}
    (ha : Agrees f (p :: τ)) : Agrees f τ :=
  fun q hq => ha q (List.mem_cons_of_mem _ hq)

theorem Agrees.lookup_eq {f : Nat → Bool} {τ : PAssign} {v : Nat} {b : Bool}
    (ha : Agrees f τ) (h : lookup τ v = some b) : f v = b := by
  induction τ with
  | nil => simp [lookup] at h
  | cons p τ ih =>
    obtain ⟨w, b'⟩ := p
    simp only [lookup] at h
    split at h
    · rename_i hw
      injection h with hb
      have hm := ha (w, b') List.mem_cons_self
      rw [hw, hm]
      exact hb
    · exact ih ha.tail h

/-- Result of reducing one clause under a partial assignment. -/
inductive RRes where
  /-- Every literal is false under the assignment. -/
  | conflict
  /-- Every literal is false under the assignment or equal to `l`,
  and `l` is unassigned. -/
  | unit (l : Lit)
  /-- The clause is satisfied, or has ≥ 2 distinct unassigned literals. -/
  | stuck
deriving DecidableEq

/-- Combine the head literal `l` (unassigned under `τ`) with the reduction
result of the rest of the clause. -/
def bump (r : RRes) (l : Lit) : RRes :=
  match r with
  | .conflict => .unit l
  | .unit l' => if l' = l then .unit l' else .stuck
  | .stuck => .stuck

/-- Reduce a clause under `τ`: detect conflict / unit (structural). -/
def reduce (τ : PAssign) : Clause → RRes
  | [] => .conflict
  | (v, b) :: c =>
    match lookup τ v with
    | some b' => if b' = b then .stuck else reduce τ c
    | none => bump (reduce τ c) (v, b)

theorem bump_ne_conflict (r : RRes) (l : Lit) : bump r l ≠ .conflict := by
  cases r <;> simp [bump]
  split <;> simp

theorem bump_eq_unit {r : RRes} {l l' : Lit} (h : bump r l = .unit l') :
    l' = l ∧ (r = .conflict ∨ r = .unit l) := by
  cases r <;> simp only [bump] at h
  · exact ⟨(RRes.unit.inj h).symm, Or.inl rfl⟩
  · split at h
    · rename_i heq
      exact ⟨(RRes.unit.inj h) ▸ heq, Or.inr (heq ▸ rfl)⟩
    · cases h
  · cases h

theorem eval_false_of_reduce_conflict {τ : PAssign} {c : Clause}
    (h : reduce τ c = .conflict) {f : Nat → Bool} (ha : Agrees f τ) :
    c.eval f = false := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    obtain ⟨v, b⟩ := l
    simp only [reduce] at h
    split at h
    · rename_i b' hl
      split at h
      · cases h
      · rename_i hne
        have hv : f v = b' := ha.lookup_eq hl
        have hb : (f v == b) = false := by
          rw [hv]; exact beq_eq_false_iff_ne.mpr hne
        simp [CNF.Clause.eval_cons, hb, ih h]
    · exact absurd h (bump_ne_conflict _ _)

theorem lit_sat_of_reduce_unit {τ : PAssign} {c : Clause} {l : Lit}
    (h : reduce τ c = .unit l) {f : Nat → Bool} (ha : Agrees f τ)
    (he : c.eval f = true) : f l.1 = l.2 := by
  induction c with
  | nil => cases h
  | cons p c ih =>
    obtain ⟨v, b⟩ := p
    simp only [reduce] at h
    rw [CNF.Clause.eval_cons, Bool.or_eq_true] at he
    split at h
    · rename_i b' hl
      split at h
      · cases h
      · rename_i hne
        rcases he with he | he
        · have hv : f v = b' := ha.lookup_eq hl
          rw [hv] at he
          exact absurd (eq_of_beq he) hne
        · exact ih h he
    · obtain ⟨hl', hr⟩ := bump_eq_unit h
      subst hl'
      rcases he with he | he
      · simpa using he
      · rcases hr with hr | hr
        · rw [eval_false_of_reduce_conflict hr ha] at he; cases he
        · exact ih hr he

/-- Extract "every clause of a true CNF is true". -/
theorem clause_eval_of_cnf_eval {f : Nat → Bool} {F : Cnf}
    (hF : CNF.eval f F = true) {c : Clause} (hc : c ∈ F) : c.eval f = true :=
  List.all_eq_true.mp hF c hc

/-! ## Hint-driven RUP (the fast path: LRAT hints) -/

/-- Run an LRAT hint list: each hint indexes a clause of `F` that must be
unit (extending `τ`) or in conflict (closing the check). Structural in the
hint list. -/
def runHints (F : Cnf) (τ : PAssign) : List Nat → Bool
  | [] => false
  | i :: is =>
    match F[i]? with
    | none => false
    | some c =>
      match reduce τ c with
      | .conflict => true
      | .unit (v, b) => runHints F ((v, b) :: τ) is
      | .stuck => false

theorem runHints_sound {F : Cnf} {hs : List Nat} {τ : PAssign}
    (h : runHints F τ hs = true) {f : Nat → Bool}
    (hF : CNF.eval f F = true) (ha : Agrees f τ) : False := by
  induction hs generalizing τ with
  | nil => cases h
  | cons i is ih =>
    simp only [runHints] at h
    split at h
    · cases h
    · rename_i c hg
      have hc : c.eval f = true :=
        clause_eval_of_cnf_eval hF (List.mem_of_getElem? hg)
      split at h
      · rename_i hr
        rw [eval_false_of_reduce_conflict hr ha] at hc
        cases hc
      · rename_i v b hr
        have hv : f v = b := lit_sat_of_reduce_unit hr ha hc
        exact ih h fun p hp => by
          rcases List.mem_cons.mp hp with hp | hp
          · subst hp; exact hv
          · exact ha p hp
      · cases h

/-! ## Unhinted RUP (fuel-bounded full unit propagation; slow path) -/

/-- Result of scanning a formula for one propagation step. -/
inductive FRes where
  | conflict
  | unit (l : Lit)
  | idle

/-- Scan `F` for a conflict (preferred) or a unit clause under `τ`. -/
def findStep (τ : PAssign) : Cnf → FRes
  | [] => .idle
  | c :: F =>
    match reduce τ c with
    | .conflict => .conflict
    | .unit l =>
      match findStep τ F with
      | .conflict => .conflict
      | _ => .unit l
    | .stuck => findStep τ F

theorem findStep_conflict {τ : PAssign} {F : Cnf}
    (h : findStep τ F = .conflict) : ∃ c ∈ F, reduce τ c = .conflict := by
  induction F with
  | nil => cases h
  | cons c F ih =>
    simp only [findStep] at h
    split at h
    · rename_i hr
      exact ⟨c, List.mem_cons_self, hr⟩
    · split at h
      · rename_i hf
        obtain ⟨d, hd, hrd⟩ := ih hf
        exact ⟨d, List.mem_cons_of_mem _ hd, hrd⟩
      · cases h
    · obtain ⟨d, hd, hrd⟩ := ih h
      exact ⟨d, List.mem_cons_of_mem _ hd, hrd⟩

theorem findStep_unit {τ : PAssign} {F : Cnf} {l : Lit}
    (h : findStep τ F = .unit l) : ∃ c ∈ F, reduce τ c = .unit l := by
  induction F with
  | nil => cases h
  | cons c F ih =>
    simp only [findStep] at h
    split at h
    · cases h
    · rename_i l' hr
      split at h
      · cases h
      · cases h
        exact ⟨c, List.mem_cons_self, hr⟩
    · obtain ⟨d, hd, hrd⟩ := ih h
      exact ⟨d, List.mem_cons_of_mem _ hd, hrd⟩

/-- Fuel-bounded unit propagation to conflict (structural in the fuel). -/
def propagate (F : Cnf) (τ : PAssign) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    match findStep τ F with
    | .conflict => true
    | .unit (v, b) => propagate F ((v, b) :: τ) fuel
    | .idle => false

theorem propagate_sound {F : Cnf} {fuel : Nat} {τ : PAssign}
    (h : propagate F τ fuel = true) {f : Nat → Bool}
    (hF : CNF.eval f F = true) (ha : Agrees f τ) : False := by
  induction fuel generalizing τ with
  | zero => cases h
  | succ fuel ih =>
    simp only [propagate] at h
    split at h
    · rename_i hs
      obtain ⟨c, hc, hrc⟩ := findStep_conflict hs
      have := clause_eval_of_cnf_eval hF hc
      rw [eval_false_of_reduce_conflict hrc ha] at this
      cases this
    · rename_i v b hs
      obtain ⟨c, hc, hrc⟩ := findStep_unit hs
      have hv : f v = b :=
        lit_sat_of_reduce_unit hrc ha (clause_eval_of_cnf_eval hF hc)
      exact ih h fun p hp => by
        rcases List.mem_cons.mp hp with hp | hp
        · subst hp; exact hv
        · exact ha p hp
    · cases h

/-- Enough fuel to assign every literal of `F` once, plus the final scan. -/
def fuelFor (F : Cnf) : Nat := F.foldr (fun c n => c.length + n) 0 + 1

/-! ## RUP steps and the checker -/

/-- The partial assignment asserting the negation of a clause. -/
def negate (c : Clause) : PAssign := c.map fun (v, b) => (v, !b)

theorem agrees_negate {c : Clause} {f : Nat → Bool}
    (h : c.eval f = false) : Agrees f (negate c) := by
  induction c with
  | nil => intro p hp; cases hp
  | cons l c ih =>
    obtain ⟨v, b⟩ := l
    rw [CNF.Clause.eval_cons, Bool.or_eq_false_iff] at h
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst hp
      revert h; cases hf : f v <;> cases b <;> simp
    · exact ih h.2 p hp

/-- Check that `c` has the RUP property w.r.t. `F`: assuming `¬c`, unit
propagation reaches a conflict. With `hints`, propagation is driven by the
LRAT hint list (linear); without, by a full fuel-bounded search. -/
def checkRup (F : Cnf) (c : Clause) (hints : List Nat) : Bool :=
  match hints with
  | [] => propagate F (negate c) (fuelFor F)
  | _ :: _ => runHints F (negate c) hints

/-- A RUP-checked clause is semantically implied. -/
theorem clause_implied_of_checkRup {F : Cnf} {c : Clause} {hs : List Nat}
    (h : checkRup F c hs = true) {f : Nat → Bool}
    (hF : CNF.eval f F = true) : c.eval f = true := by
  cases he : c.eval f
  · exfalso
    have ha := agrees_negate he
    unfold checkRup at h
    match hs, h with
    | [], h => exact propagate_sound h hF ha
    | _ :: _, h => exact runHints_sound h hF ha
  · rfl

/-- One certificate step: add a RUP clause (with optional LRAT hints; `[]`
means unhinted search), or delete clauses — deletions are ignored, which is
soundness-preserving. -/
inductive Step where
  | add (clause : Clause) (hints : List Nat)
  | del (ids : List Nat)
deriving DecidableEq

/-- Check a certificate against `F`: every added clause must be RUP w.r.t.
the accumulated formula, and the certificate must reach the empty clause.

Learned clauses are *prepended* (`c :: F`, an O(1) extension the kernel
never has to re-force, unlike an `F ++ [c]` append chain), so hint indices
refer to the accumulated formula with the **most recently added clause
first** and the original clauses of `F` last, i.e. after `k` additions the
original clause `F[i]` sits at hint position `k + i` and the `j`-th learned
clause (0-based) at position `k - 1 - j`. -/
def check (F : Cnf) : List Step → Bool
  | [] => false
  | .del _ :: rest => check F rest
  | .add c hints :: rest =>
    if checkRup F c hints then
      match c with
      | [] => true
      | _ :: _ => check (c :: F) rest
    else false

/-- **Soundness**: a checked certificate establishes `Std.Sat.CNF.Unsat`.
This theorem plus kernel reduction of `check` is the whole trust story. -/
theorem check_sound {F : Cnf} {cert : List Step}
    (h : check F cert = true) : CNF.Unsat F := by
  induction cert generalizing F with
  | nil => cases h
  | cons s rest ih =>
    match s with
    | .del _ => exact ih h
    | .add c hints =>
      simp only [check] at h
      split at h
      case isFalse => cases h
      case isTrue hr =>
        match c, h with
        | [], _ =>
          intro f
          cases hF : CNF.eval f F
          · rfl
          · have := clause_implied_of_checkRup hr hF
            simp [CNF.Clause.eval] at this
        | c₀ :: c', h =>
          intro f
          cases hF : CNF.eval f F
          · rfl
          · have hu := ih h f
            rw [CNF.eval_cons, hF] at hu
            simp [clause_implied_of_checkRup hr hF] at hu

/-! ## Pigeonhole smoke tests (kernel `decide`; larger sizes in
`Tests/CheckBench.lean`, generator in `Tools/CertGen.lean`) -/

/-- php2→1: pigeons 1,2 into hole 1 (vars `x_p` = "pigeon p in hole 1"). -/
def php2 : Cnf := [[(1, true)], [(2, true)], [(1, false), (2, false)]]

def php2Cert : List Step := [.add [] [0, 1, 2]]

example : check php2 php2Cert = true := by decide

/-- php3→2: vars `x_{p,h}` numbered `x11=1, x12=2, x21=3, x22=4, x31=5,
x32=6`. Clauses 0–2: each pigeon somewhere; 3–8: no hole holds two. -/
def php3 : Cnf :=
  [[(1, true), (2, true)], [(3, true), (4, true)], [(5, true), (6, true)],
   [(1, false), (3, false)], [(1, false), (5, false)], [(3, false), (5, false)],
   [(2, false), (4, false)], [(2, false), (6, false)], [(4, false), (6, false)]]

/-- Handwritten hinted RUP derivation: `¬x11∨¬x22`, `¬x11`, `¬x21`, `⊥`. -/
def php3Cert : List Step :=
  [.add [(1, false), (4, false)] [3, 4, 2, 8],
   .add [(1, false)] [4, 5, 0, 2],
   .add [(3, false)] [0, 2, 7, 4, 9],
   .add [] [1, 0, 3, 4, 9]]

example : check php3 php3Cert = true := by decide

/-- The unhinted (plain RUP) path also closes php3 on the same clause list,
at the cost of a full scan per propagation. -/
def php3CertNoHints : List Step :=
  [.add [(1, false), (4, false)] [],
   .add [(1, false)] [],
   .add [(3, false)] [],
   .add [] []]

example : check php3 php3CertNoHints = true := by decide

end Loom.Dp.Cert.Check
