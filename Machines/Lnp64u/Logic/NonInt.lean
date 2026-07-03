import Machines.Lnp64u.Logic.GateStep
import Machines.Lnp64u.Logic.DFrame
import Machines.Lnp64u.Logic.DRel
import Machines.Lnp64u.Logic.Inflight
import Machines.Lnp64u.Logic.Authority
import Machines.Lnp64u.Logic.Hostage
import Machines.Lnp64u.Theorems.Inv
import Mathlib.Data.List.Basic

/-!
# Noninterference vocabulary and engine lemmas (T5 support)

Definitions and lemmas for T5 (`Theorems/T5.lean`). This file records the
*adjudicated* form of the theorem's vocabulary; the original statement was
falsified twice — see the adjudication notes below.

## Adjudication 1: the original T5 statement was FALSE (scheduling/grants)

The original statement hypothesized only `Isolated` (no gate caps held by
`d`, no gate whose callee is `d`, root-range disjointness) and `AgreeOn`
(equal `d`-config, equal ROM under `d`'s roots). That leaves the *other*
domains' configurations completely free, and the following two-manifest
counterexample refutes it:

* `m₁`: `d` has the top priority; every other domain has an empty region
  map (`initRegions = fun _ => none`), so each fetch-faults the first time
  it is scheduled and halts. `d`'s ROM is an infinite loop that changes
  `pc` every retirement (any loop does). `d`'s destuttered trajectory
  gains at least one element per retirement of `d`: unbounded in `n`.
* `m₂`: identical `d`-config and `d`-ROM (so `AgreeOn` holds), but a hog
  domain `H` with priority above `d`'s and `budgetQ = periodP` (legal:
  `Manifest.WF.budget_le` only requires `Q ≤ P`). `H` runs a tight loop.
  The scheduler (`schedule`) picks the highest-priority running domain
  whose payer's budget is positive, and even an `H` too poor for its next
  instruction *stalls the core* (`corePhase` returns `σ` unchanged rather
  than falling through to the next domain). With `Q = P`, `H`'s budget is
  refilled every period and upfront charging can never exhaust it below 1
  at an issue opportunity, so `d` is never scheduled: `d` never retires,
  its compared fields (`regs`/`pc`/`run`/`cause`) never change, and its
  destuttered trajectory has length 1 forever.

Hence the theorem now hypothesizes `TopPriority` for both manifests, and
`Isolated` gains clauses closing the *grant-in* channel (`mem_grant`
installs capabilities into the target's table without consent, perturbing
the target's later `cap_dup` handle values) and the *globally-sensitive
instruction* channel (`d`'s own `mem_grant`/`move` read foreign table
state / machine-global Mover state into `d`'s `rd`):

* `slots_full` — `d`'s slot table boots full, so every grant into `d`
  fails with `-ESLOTOCCUPIED` at the granter;
* `code_local` — no word of `d`'s code decodes to `cap_drop` (17),
  `cap_revoke` (18), `mem_grant` (19), or `move` (24).

## Adjudication 2 (this pass): two further proof-forced repairs

**2a. The observation had to become a projection.** The first repair kept
`destutter : List DomainState → List DomainState` (deduplicating by the
compared fields) and demanded a *list prefix* — i.e. full `DomainState`
equality of the kept representatives. But the kept elements carry `budget`,
and the two runs' budgets provably drift: refill happens at *absolute*
cycles (`σ.cycle % periodP = 0`, and `σ.cycle` advances identically in both
runs) while spending happens at *drifted* issue cycles (the other domains'
in-flight instructions delay `d` differently in the two manifests). Whether
a refill lands between `d`'s j-th and (j+1)-th retirement is therefore
run-dependent, so the pre-event `budget` values differ and no prefix of
full `DomainState`s exists. The observation is now an explicit projection
`Obs` (`regs`/`pc`/`run`/`cause`) and `destutter`/`trajectory` work on
`List Obs`. This is the honest statement: budget and capability
bookkeeping are timing/authority state, not architectural observation.

**2b. `Isolated` needs W^X *across* `d`'s roots (`wx_disjoint`).** The
machine enforces W^X per capability, but nothing stops a manifest giving
`d` two *overlapping* roots, one writable and one executable. `d` could
then rewrite its own code region and execute words that are not in the
ROM — in particular `move` (reads the machine-global Mover busy state
into `rd`) or `mem_grant` (reads the target's table state) — reopening
the global channels `code_local` closed, because `code_local` constrains
only the *ROM*. `wx_disjoint` requires `d`'s writable roots to be
range-disjoint from its executable roots, which makes "memory under
`d`'s executable roots equals the ROM" (`Insulated.code_intact`) an
invariant, so every word `d` ever fetches is a ROM word.

## The residual argument (why the strengthened statement is true)

With `TopPriority`, `schedule_top` gives: whenever the core is idle and
`d` is running with positive budget, `d` is issued. Other domains'
in-flight instructions still *delay* `d` (issue cycles drift between the
two runs) and `d`'s budget *values* differ transiently, but budget is
never architecturally observable, so the drift is pure stutter: `d`'s
k-th observation change computes the same `Obs` in both runs (the
`Coupled` invariant below), and `d` is never starved (each in-flight
instruction finishes, each period refills `d` to `budgetQ`, and `d`'s
issue costs are ≤ `budgetQ` whenever they were ever payable), so run 2
eventually realizes every observation change of run 1's `n`-cycle prefix.
Destuttering erases the drift and yields the prefix.

The proof is assembled in `Theorems/T5.lean` from four engine lemmas
(stated at the bottom of this file, in the `Wip` namespace while their
sweeps are completed):

* `insulated_step` — the per-run invariant `Insulated` is inductive;
* `frame_step` — on a cycle that neither retires `d`'s instruction nor
  issues for `d`, `d`'s architectural slice and the memory under `d`'s
  roots are untouched (`DFrozen`);
* `retire_step_lockstep` — when both runs retire the same latched word
  for `d` from `Coupled` states, the post-states are `Coupled`;
* `progress` — from any quiescent state with `d` running, run 2 reaches
  an issue instant for `d` (with any required budget ≤ `budgetQ`
  available) through a `d`-frozen window.
-/

namespace Machines.Lnp64u.NonInt

open Machines.Lnp64u Loom

/-! ## Manifest-level hypotheses -/

/-- Domain `d` has the strictly highest scheduling priority. Together with
`schedule_top` this removes scheduling interference: `d` is issued at every
idle cycle at which it is eligible. -/
def TopPriority (m : Manifest) (d : DomainId) : Prop :=
  ∀ d', d' ≠ d → (m.doms d').priority < (m.doms d).priority

/-- Address `a` lies under one of `d`'s root memory capabilities: the
memory `d` can ever access (its authority closure stays inside this set —
T2's confinement — since grants into `d` are excluded by `Isolated`). -/
def UnderRoots (m : Manifest) (d : DomainId) (a : Addr) : Prop :=
  ∃ s b l p, (m.doms d).initCaps s = some (.mem b l p) ∧
    b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + l.toNat

/-- Address `a` lies under an *executable* root of `d`: everywhere `d` can
ever fetch from. -/
def UnderXRoots (m : Manifest) (d : DomainId) (a : Addr) : Prop :=
  ∃ s b l p, (m.doms d).initCaps s = some (.mem b l p) ∧ p.x = true ∧
    b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + l.toNat

theorem UnderXRoots.underRoots {m : Manifest} {d : DomainId} {a : Addr}
    (h : UnderXRoots m d a) : UnderRoots m d a := by
  obtain ⟨s, b, l, p, h1, _, h3, h4⟩ := h
  exact ⟨s, b, l, p, h1, h3, h4⟩

theorem underRoots_congr {m₁ m₂ : Manifest} {d : DomainId}
    (h : m₁.doms d = m₂.doms d) (a : Addr) :
    UnderRoots m₁ d a ↔ UnderRoots m₂ d a := by
  unfold UnderRoots; rw [h]

/-- Domain `d` is authority-isolated in manifest `m`. Clauses 1–3 are the
original path-freedom conditions; the rest were forced by adjudication
(see the module docstring). -/
structure Isolated (m : Manifest) (d : DomainId) : Prop where
  /-- `d` holds no gate capabilities (it can call nobody). -/
  no_gates_held : ∀ s g, (m.doms d).initCaps s ≠ some (.gate g)
  /-- No gate's callee is `d` (nobody can activate `d`). -/
  no_gates_in : ∀ g, (m.gates g).callee ≠ d
  /-- `d`'s root ranges overlap no other domain's root ranges. -/
  roots_disjoint : ∀ d' s s' b l p b' l' p', d' ≠ d →
    (m.doms d).initCaps s = some (.mem b l p) →
    (m.doms d').initCaps s' = some (.mem b' l' p') →
    b.toNat + l.toNat ≤ b'.toNat ∨ b'.toNat + l'.toNat ≤ b.toNat
  /-- `d`'s slot table boots full, so `mem_grant` into `d` always fails at
  the granter with `-ESLOTOCCUPIED` (as long as `d` never frees a slot —
  `code_local`). This is the honest price of µ's grant-without-consent
  design: isolation requires a full table. -/
  slots_full : ∀ s, (m.doms d).initCaps s ≠ none
  /-- No word of `d`'s code decodes to a slot-freeing or globally-sensitive
  op: `cap_drop` (17) and `cap_revoke` (18) would reopen the grant-in
  channel by freeing a slot; `mem_grant` (19) by `d` reads the *target's*
  table state into `d`'s `rd`; `move` (24) reads the machine-global Mover
  busy/idle state into `d`'s `rd`. -/
  code_local : ∀ a, UnderRoots m d a →
    ∀ i, Loom.Isa.decode isa (m.rom a) = some i →
      i.opcode ≠ 17 ∧ i.opcode ≠ 18 ∧ i.opcode ≠ 19 ∧ i.opcode ≠ 24
  /-- W^X across `d`'s roots (adjudication 2b): `d`'s writable roots are
  range-disjoint from its executable roots, so `d` cannot rewrite its own
  code and smuggle in the opcodes `code_local` excludes. -/
  wx_disjoint : ∀ s s' b l p b' l' p',
    (m.doms d).initCaps s = some (.mem b l p) →
    (m.doms d).initCaps s' = some (.mem b' l' p') →
    p.w = true → p'.x = true →
    b.toNat + l.toNat ≤ b'.toNat ∨ b'.toNat + l'.toNat ≤ b.toNat

/-- Two manifests agree on everything `d` can see: `d`'s configuration and
the ROM under `d`'s root ranges. -/
def AgreeOn (m₁ m₂ : Manifest) (d : DomainId) : Prop :=
  m₁.doms d = m₂.doms d ∧
  (∀ a, UnderRoots m₁ d a → m₁.rom a = m₂.rom a)

/-! ## Observation and destuttering (adjudication 2a) -/

/-- The architectural observation of one domain: registers, program
counter, run state, cause. Budget, capability tables, and region registers
are deliberately *not* observed — timing and authority bookkeeping are
where the two runs are allowed to drift. -/
structure Obs where
  regs : RegId → Loom.Word32
  pc : Addr
  run : RunState
  cause : Loom.Word32

theorem Obs.ext_iff (x y : Obs) :
    x = y ↔ x.regs = y.regs ∧ x.pc = y.pc ∧ x.run = y.run ∧ x.cause = y.cause := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3, h4⟩; cases x; cases y; simp_all

instance : DecidableEq Obs := fun x y =>
  decidable_of_iff _ (Obs.ext_iff x y).symm

/-- Project a domain state to its observation. -/
def obsOf (ds : DomainState) : Obs :=
  { regs := ds.regs, pc := ds.pc, run := ds.run, cause := ds.cause }

/-- Remove consecutive duplicates. -/
def destutter : List Obs → List Obs
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if x = y then destutter (y :: rest) else x :: destutter (y :: rest)

/-- `d`'s observed trajectory over `n` cycles. -/
def trajectory (m : Manifest) (d : DomainId) (n : Nat) : List Obs :=
  (List.range n).map fun i => obsOf ((stepN m i m.initState).doms d)

/-! ### Destutter combinatorics -/

theorem destutter_snoc_stutter :
    ∀ (l : List Obs) (x : Obs), l.getLast? = some x →
      destutter (l ++ [x]) = destutter l
  | [], x, h => by simp at h
  | [a], x, h => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      show destutter [a, a] = destutter [a]
      show (if a = a then destutter [a] else a :: destutter [a]) = destutter [a]
      rw [if_pos rfl]
  | a :: b :: t, x, h => by
      have hlast : (b :: t).getLast? = some x := by
        rw [← h, List.getLast?_cons_cons]
      have ih : destutter (b :: (t ++ [x])) = destutter (b :: t) := by
        rw [← List.cons_append]
        exact destutter_snoc_stutter (b :: t) x hlast
      show destutter (a :: b :: (t ++ [x])) = destutter (a :: b :: t)
      show (if a = b then destutter (b :: (t ++ [x]))
            else a :: destutter (b :: (t ++ [x]))) =
           (if a = b then destutter (b :: t) else a :: destutter (b :: t))
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab]
        exact ih
      · rw [if_neg hab, if_neg hab, ih]

theorem destutter_snoc_new :
    ∀ (l : List Obs) (x y : Obs), l.getLast? = some x → x ≠ y →
      destutter (l ++ [y]) = destutter l ++ [y]
  | [], x, y, h, _ => by simp at h
  | [a], x, y, h, hxy => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      show destutter [a, y] = destutter [a] ++ [y]
      show (if a = y then destutter [y] else a :: destutter [y]) = destutter [a] ++ [y]
      rw [if_neg hxy]
      rfl
  | a :: b :: t, x, y, h, hxy => by
      have hlast : (b :: t).getLast? = some x := by
        rw [← h, List.getLast?_cons_cons]
      have ih : destutter (b :: (t ++ [y])) = destutter (b :: t) ++ [y] := by
        rw [← List.cons_append]
        exact destutter_snoc_new (b :: t) x y hlast hxy
      show destutter (a :: b :: (t ++ [y])) = destutter (a :: b :: t) ++ [y]
      show (if a = b then destutter (b :: (t ++ [y]))
            else a :: destutter (b :: (t ++ [y]))) =
           (if a = b then destutter (b :: t) else a :: destutter (b :: t)) ++ [y]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab]
        exact ih
      · rw [if_neg hab, if_neg hab, ih]
        rfl

/-- Appending one element to two lists with equal destutters and equal last
elements keeps the destutters equal (uniform in whether the new element
stutters). -/
theorem destutter_snoc_congr {l₁ l₂ : List Obs} {x : Obs} (y : Obs)
    (heq : destutter l₁ = destutter l₂)
    (h₁ : l₁.getLast? = some x) (h₂ : l₂.getLast? = some x) :
    destutter (l₁ ++ [y]) = destutter (l₂ ++ [y]) := by
  by_cases hxy : x = y
  · subst hxy
    rw [destutter_snoc_stutter l₁ x h₁, destutter_snoc_stutter l₂ x h₂, heq]
  · rw [destutter_snoc_new l₁ x y h₁ hxy, destutter_snoc_new l₂ x y h₂ hxy, heq]

/-- Appending a run of stutters changes nothing. -/
theorem destutter_append_replicate (l : List Obs) (x : Obs) (j : Nat)
    (h : l.getLast? = some x) :
    destutter (l ++ List.replicate j x) = destutter l := by
  induction j generalizing l with
  | zero => simp
  | succ n ih =>
      have : l ++ List.replicate (n + 1) x = (l ++ [x]) ++ List.replicate n x := by
        rw [List.replicate_succ, List.append_assoc]
        rfl
      rw [this, ih (l ++ [x]) (by simp), destutter_snoc_stutter l x h]

theorem getLast?_append_replicate {α : Type} (l : List α) (x : α) (j : Nat)
    (h : l.getLast? = some x) :
    (l ++ List.replicate j x).getLast? = some x := by
  cases j with
  | zero => simpa using h
  | succ n =>
      have : l ++ List.replicate (n + 1) x = (l ++ List.replicate n x) ++ [x] := by
        rw [List.replicate_succ', ← List.append_assoc]
      rw [this]
      exact List.getLast?_concat

/-! ### Trajectory algebra -/

theorem trajectory_succ (m : Manifest) (d : DomainId) (n : Nat) :
    trajectory m d (n + 1) =
      trajectory m d n ++ [obsOf ((stepN m n m.initState).doms d)] := by
  unfold trajectory
  rw [List.range_succ, List.map_append]
  rfl

theorem trajectory_one (m : Manifest) (d : DomainId) :
    trajectory m d 1 = [obsOf (m.initState.doms d)] := by
  show [obsOf ((stepN m 0 m.initState).doms d)] = [obsOf (m.initState.doms d)]
  rfl

theorem trajectory_getLast (m : Manifest) (d : DomainId) (n : Nat) :
    (trajectory m d (n + 1)).getLast? =
      some (obsOf ((stepN m n m.initState).doms d)) := by
  rw [trajectory_succ]
  exact List.getLast?_concat

/-- Splitting a trajectory at cycle `a`. -/
theorem trajectory_add (m : Manifest) (d : DomainId) (a : Nat) :
    ∀ b, trajectory m d (a + b) =
      trajectory m d a ++
        (List.range b).map (fun i => obsOf ((stepN m (a + i) m.initState).doms d))
  | 0 => by simp [trajectory]
  | b + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 from rfl, trajectory_succ,
        trajectory_add m d a b, List.range_succ, List.map_append,
        List.append_assoc]
      rfl

/-! ## Scheduling: top priority wins -/

/-- The scheduler's fold function (as written inline in `schedule`). -/
private abbrev schedFold (m : Manifest) : Option DomainId → DomainId → Option DomainId :=
  fun best d =>
    match best with
    | none => some d
    | some b => if (m.doms b).priority < (m.doms d).priority then some d else some b

private theorem foldl_sched_keep (m : Manifest) (d : DomainId) :
    ∀ l : List DomainId,
      (∀ x ∈ l, ¬ (m.doms d).priority < (m.doms x).priority) →
      l.foldl (schedFold m) (some d) = some d
  | [], _ => rfl
  | x :: l, h => by
      rw [List.foldl_cons]
      show l.foldl (schedFold m)
        (if (m.doms d).priority < (m.doms x).priority then some x else some d) = some d
      rw [if_neg (h x (List.mem_cons_self ..))]
      exact foldl_sched_keep m d l fun y hy => h y (List.mem_cons_of_mem x hy)

private theorem foldl_sched_top (m : Manifest) (d : DomainId)
    (hpri : ∀ x, x ≠ d → (m.doms x).priority < (m.doms d).priority) :
    ∀ (l : List DomainId) (acc : Option DomainId),
      d ∈ l →
      (acc = none ∨ ∃ a, acc = some a ∧
        (a = d ∨ (m.doms a).priority < (m.doms d).priority)) →
      l.foldl (schedFold m) acc = some d := by
  have hnotlt : ∀ x, ¬ (m.doms d).priority < (m.doms x).priority := by
    intro x hlt
    by_cases hx : x = d
    · exact absurd hlt (hx ▸ Nat.lt_irrefl _)
    · exact absurd hlt (Nat.lt_asymm (hpri x hx))
  intro l
  induction l with
  | nil => intro acc hmem _; cases hmem
  | cons x l ih =>
      intro acc hmem hacc
      rw [List.foldl_cons]
      by_cases hx : x = d
      · -- the accumulator becomes `some d`; the rest cannot displace it
        subst hx
        have hstep : schedFold m acc x = some x := by
          rcases hacc with h | ⟨a, ha, hcase⟩
          · rw [h]
          · rw [ha]
            rcases hcase with h | h
            · subst h; show (if _ < _ then _ else _) = _
              rw [if_neg (Nat.lt_irrefl _)]
            · show (if _ < _ then _ else _) = _
              rw [if_pos h]
        rw [hstep]
        exact foldl_sched_keep m x l fun y hy => hnotlt y
      · -- x is not d: the accumulator invariant is preserved
        have hd : d ∈ l := by
          cases hmem with
          | head => exact absurd rfl hx
          | tail _ h => exact h
        refine ih _ hd ?_
        right
        rcases hacc with h | ⟨a, ha, hcase⟩
        · exact ⟨x, by rw [h], Or.inr (hpri x hx)⟩
        · rw [ha]
          show ∃ b, (if (m.doms a).priority < (m.doms x).priority
              then some x else some a) = some b ∧ _
          by_cases hlt : (m.doms a).priority < (m.doms x).priority
          · exact ⟨x, by rw [if_pos hlt], Or.inr (hpri x hx)⟩
          · exact ⟨a, by rw [if_neg hlt], hcase⟩

/-- **Top priority wins.** If `d` is running with a solvent payer and has
strictly the highest priority, the scheduler picks `d`. This is the lemma
that removes *scheduling* interference from the T5 coupling: whenever the
core is idle, `d`'s eligibility alone decides whether `d` issues. -/
theorem schedule_top (m : Manifest) (d : DomainId)
    (hpri : TopPriority m d) (σ : MachineState)
    (hrun : (σ.doms d).run = .running)
    (hbud : 0 < (σ.doms (σ.payer d)).budget) :
    schedule m σ = some d := by
  apply foldl_sched_top m d hpri
  · exact List.mem_filter.mpr ⟨List.mem_finRange d, by simp [hrun, hbud]⟩
  · exact Or.inl rfl

/-- A domain serving no gate pays for itself. For an isolated `d` (never a
callee, holds no gate capabilities) this holds at every reachable state,
so `d`'s eligibility is `run = .running ∧ 0 < budget` of `d` itself. -/
theorem payer_eq_self (σ : MachineState) (d : DomainId)
    (h : (σ.doms d).serving = none) : σ.payer d = d := by
  show σ.chainOrigin maxChainDepth d = d
  show σ.chainOrigin 4 d = d
  unfold MachineState.chainOrigin
  rw [h]

/-! ## Phase-level frame lemmas

`step` is refill → core → mover → cycle bump. The coupling's cycle-level
case analysis needs to know that the refill and mover phases never touch
the fields `Coupled` compares: refill changes only budgets, the mover
changes only memory and its own job record. -/

/-- The refill phase changes at most a domain's budget. -/
theorem refillPhase_doms (m : Manifest) (σ : MachineState) (e : DomainId) :
    (refillPhase m σ).doms e = σ.doms e ∨
    (refillPhase m σ).doms e = { σ.doms e with budget := (m.doms e).budgetQ } := by
  unfold refillPhase
  by_cases h0 : σ.cycle = 0
  · exact Or.inl (by rw [if_pos h0])
  · rw [if_neg h0]
    by_cases hp : σ.cycle % (m.doms e).periodP = 0
    · exact Or.inr (by simp [hp])
    · exact Or.inl (by simp [hp])

/-- The refill phase touches nothing but the domain table. -/
theorem refillPhase_frame (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).mem = σ.mem ∧ (refillPhase m σ).inflight = σ.inflight ∧
    (refillPhase m σ).mover = σ.mover ∧ (refillPhase m σ).gates = σ.gates ∧
    (refillPhase m σ).cycle = σ.cycle := by
  unfold refillPhase
  by_cases h0 : σ.cycle = 0
  · rw [if_pos h0]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg h0]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Refill keeps a bounded budget bounded (it only ever resets to `Q`). -/
theorem refillPhase_budget_le (m : Manifest) (σ : MachineState) (d : DomainId)
    (h : (σ.doms d).budget ≤ (m.doms d).budgetQ) :
    ((refillPhase m σ).doms d).budget ≤ (m.doms d).budgetQ := by
  rcases refillPhase_doms m σ d with hr | hr <;> rw [hr]
  exact h

/-- The mover phase touches nothing but memory and the job record: every
domain's state, the in-flight instruction, the gates, and the cycle
counter pass through unchanged. -/
theorem moverPhase_frame (σ : MachineState) :
    (moverPhase σ).doms = σ.doms ∧ (moverPhase σ).inflight = σ.inflight ∧
    (moverPhase σ).gates = σ.gates ∧ (moverPhase σ).cycle = σ.cycle := by
  unfold moverPhase moverStatus MachineState.write
  cases σ.mover with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some job => dsimp only; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Refill leaves fetch alone (it touches only budgets). -/
theorem refillPhase_fetch (m : Manifest) (σ : MachineState) (d : DomainId) :
    fetch (refillPhase m σ) d = fetch σ d := by
  unfold fetch MachineState.domCovers MachineState.read
  rw [refillPhase_regions, refillPhase_pc, (refillPhase_frame m σ).1]

/-! ## Instruction costs are positive -/

theorem cost_pos : ∀ c : WcetClass, 0 < c.cost := by
  intro c; cases c <;> decide

/-! ## The d-slice frame and the two-run coupling -/

/-- Nothing of `d`'s architectural slice moved between `σ` and `σ'`, and
memory under `d`'s roots is untouched. (`budget` is deliberately absent —
refill touches it on every period boundary.) -/
structure DFrozen (m : Manifest) (d : DomainId) (σ σ' : MachineState) : Prop where
  regs : (σ'.doms d).regs = (σ.doms d).regs
  pc : (σ'.doms d).pc = (σ.doms d).pc
  run : (σ'.doms d).run = (σ.doms d).run
  cause : (σ'.doms d).cause = (σ.doms d).cause
  serving : (σ'.doms d).serving = (σ.doms d).serving
  caps : (σ'.doms d).caps = (σ.doms d).caps
  slotGen : (σ'.doms d).slotGen = (σ.doms d).slotGen
  lineage : (σ'.doms d).lineage = (σ.doms d).lineage
  regions : (σ'.doms d).regions = (σ.doms d).regions
  mem : ∀ a, UnderRoots m d a → σ'.mem a = σ.mem a

theorem DFrozen.refl (m : Manifest) (d : DomainId) (σ : MachineState) :
    DFrozen m d σ σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem DFrozen.trans {m : Manifest} {d : DomainId} {σ σ₁ σ₂ : MachineState}
    (h1 : DFrozen m d σ σ₁) (h2 : DFrozen m d σ₁ σ₂) : DFrozen m d σ σ₂ :=
  ⟨h2.regs.trans h1.regs, h2.pc.trans h1.pc, h2.run.trans h1.run,
   h2.cause.trans h1.cause, h2.serving.trans h1.serving, h2.caps.trans h1.caps,
   h2.slotGen.trans h1.slotGen, h2.lineage.trans h1.lineage,
   h2.regions.trans h1.regions,
   fun a ha => (h2.mem a ha).trans (h1.mem a ha)⟩

theorem DFrozen.obs_eq {m : Manifest} {d : DomainId} {σ σ' : MachineState}
    (h : DFrozen m d σ σ') : obsOf (σ'.doms d) = obsOf (σ.doms d) := by
  unfold obsOf; rw [h.regs, h.pc, h.run, h.cause]

/-- The two-run coupling on `d`'s dynamic architectural slice, asserted at
*aligned* instants (equal counts of `d`-observation changes, not equal
cycle numbers — issue cycles drift because the other domains' in-flight
instructions occupy the core for run-dependent stretches).

What is deliberately **excluded**, and why it is sound to exclude it:

* `budget` — refill happens at absolute cycles, spending at drifted issue
  cycles, so the two budgets differ transiently. No instruction reads the
  budget, so the difference only affects *when* `d` issues, never *what*
  the issued instruction computes; the liveness side (`progress`) covers
  the "when".
* `caps`/`slotGen`/`lineage` — for an insulated `d` these are *constant*
  (equal to boot in both runs, `Insulated.boot_*` + `AgreeOn`), so they
  need no coupling clause.
* everything about the other domains, the gates, memory outside `d`'s
  roots, `σ.cycle`, `σ.mover`, and the in-flight latch — timing and
  foreign state, unread by `d`'s slice. -/
structure Coupled (m : Manifest) (d : DomainId) (σ₁ σ₂ : MachineState) : Prop where
  regs : (σ₁.doms d).regs = (σ₂.doms d).regs
  pc : (σ₁.doms d).pc = (σ₂.doms d).pc
  run : (σ₁.doms d).run = (σ₂.doms d).run
  cause : (σ₁.doms d).cause = (σ₂.doms d).cause
  regions : (σ₁.doms d).regions = (σ₂.doms d).regions
  /-- Memory under `d`'s roots is equal: only `d` writes there. -/
  mem : ∀ a, UnderRoots m d a → σ₁.mem a = σ₂.mem a

theorem Coupled.obs_eq {m : Manifest} {d : DomainId} {σ₁ σ₂ : MachineState}
    (h : Coupled m d σ₁ σ₂) : obsOf (σ₁.doms d) = obsOf (σ₂.doms d) := by
  unfold obsOf; rw [h.regs, h.pc, h.run, h.cause]

/-- Transport a coupling across a frozen stretch of run 1. -/
theorem Coupled.frozen_left {m : Manifest} {d : DomainId} {σ₁ σ₁' σ₂ : MachineState}
    (h : Coupled m d σ₁ σ₂) (hf : DFrozen m d σ₁ σ₁') : Coupled m d σ₁' σ₂ :=
  ⟨hf.regs.trans h.regs, hf.pc.trans h.pc, hf.run.trans h.run,
   hf.cause.trans h.cause, hf.regions.trans h.regions,
   fun a ha => (hf.mem a ha).trans (h.mem a ha)⟩

/-- Transport a coupling across a frozen stretch of run 2 (whose frame is
stated against `m₂`'s roots — equal to `m₁`'s under agreement). -/
theorem Coupled.frozen_right {m₁ m₂ : Manifest} {d : DomainId}
    {σ₁ σ₂ σ₂' : MachineState} (h : Coupled m₁ d σ₁ σ₂)
    (hf : DFrozen m₂ d σ₂ σ₂') (hdom : m₁.doms d = m₂.doms d) :
    Coupled m₁ d σ₁ σ₂' :=
  ⟨h.regs.trans hf.regs.symm, h.pc.trans hf.pc.symm, h.run.trans hf.run.symm,
   h.cause.trans hf.cause.symm, h.regions.trans hf.regions.symm,
   fun a ha =>
     (h.mem a ha).trans (hf.mem a ((underRoots_congr hdom a).mp ha)).symm⟩

/-! ## The per-run insulation invariant -/

/-- `d` is not in flight. -/
def Quiet (d : DomainId) (σ : MachineState) : Prop :=
  ∀ fl, σ.inflight = some fl → fl.dom ≠ d

/-- `d` is mid-flight, and the latched word is re-derivable from `d`'s
(frozen) slice: it is what `d` fetches at its current `pc`, it decodes,
and its cost is within `d`'s per-period budget (it was once payable). The
run-1 arm of the T5 simulation invariant between issue and retirement. -/
def Midflight (m : Manifest) (d : DomainId) (σ : MachineState) : Prop :=
  ∃ fl instr, σ.inflight = some fl ∧ fl.dom = d ∧
    fetch σ d = some fl.word ∧
    Loom.Isa.decode isa fl.word = some instr ∧
    fl.cyclesLeft ≤ instr.cost.cost ∧
    instr.cost.cost ≤ (m.doms d).budgetQ

/-- The single-run inductive invariant of an isolated, insulated domain:
`d`'s capability bookkeeping is frozen at boot (its slot table is full and
nothing it may execute can free a slot or install an entry), it never
serves or blocks on a gate, its region registers cache only its own boot
roots, no foreign capability reaches under its roots, the Mover never
carries its authority, and the memory under its executable roots is still
the ROM (`wx_disjoint`). -/
structure Insulated (m : Manifest) (d : DomainId) (σ : MachineState) : Prop where
  wf : Wf σ
  acyclic : Acyclic σ
  /-- `d`'s capability table is its boot table, forever. -/
  boot_caps : (σ.doms d).caps =
    fun s => ((m.doms d).initCaps s).map (fun k => { kind := k, lineage := none })
  boot_slotGen : (σ.doms d).slotGen = fun _ => genFirst
  boot_lineage : (σ.doms d).lineage = fun _ => none
  serving_none : (σ.doms d).serving = none
  not_blocked : ∀ g, (σ.doms d).run ≠ .blocked g
  /-- Machine-wide: every region register is backed by a capability of its
  own domain (regions are only ever installed by `map`, which caches the
  executing domain's own capability). -/
  regions_own : ∀ e r rg, (σ.doms e).regions r = some rg → rg.backing.dom = e
  /-- No foreign capability's range reaches under `d`'s roots. -/
  foreign_off : ∀ e, e ≠ d → ∀ s entry b l p, (σ.doms e).caps s = some entry →
    entry.kind = .mem b l p → ∀ a : Addr, b.toNat ≤ a.toNat →
    a.toNat < b.toNat + l.toNat → ¬ UnderRoots m d a
  /-- The Mover never runs `d`'s job (`d`'s code has no `move`). -/
  mover_foreign : ∀ job, σ.mover = some job → job.owner ≠ d
  /-- Gate configurations are boot-static. -/
  gates_static : ∀ g, (σ.gates g).config = m.gates g
  budget_le : (σ.doms d).budget ≤ (m.doms d).budgetQ
  maxDon_eq : (σ.doms d).maxDonation = (m.doms d).maxDonation
  /-- Memory under `d`'s executable roots is still the ROM. -/
  code_intact : ∀ a, UnderXRoots m d a → σ.mem a = m.rom a
  /-- Latch provenance (proof-forced, 2026-07-03): whenever `d`'s
  instruction is in flight, the latched word is what `d` fetches at its
  (frozen) `pc` — hence a ROM word under an executable root, so its decoded
  opcode is one `code_local` constrains. Without this clause
  `insulated_step` is *false*: `Insulated` said nothing about the latch, so
  a rogue in-flight `mem_grant`/`cap_drop` word retiring for `d` could
  break the boot pinning. The clause is self-propagating: the issue path
  latches exactly the fetched word and freezes `d`'s fetch inputs. -/
  latch_rom : ∀ fl, σ.inflight = some fl → fl.dom = d → fetch σ d = some fl.word

/-- Boot states are insulated. -/
theorem insulated_init (m : Manifest) (d : DomainId) (hm : m.WF)
    (hiso : Isolated m d) : Insulated m d m.initState := by
  refine ⟨Machines.Lnp64u.Theorems.Inv.init_wf m hm, init_acyclic m,
    rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, Nat.le_refl _, rfl, fun _ _ => rfl,
    fun fl h _ => absurd h (by simp [Manifest.initState])⟩
  · intro g h
    simp only [Manifest.initState, Manifest.bootDom] at h
    exact absurd h (by simp)
  · intro e r rg hrg
    simp only [Manifest.initState, Manifest.bootDom] at hrg
    rcases hcfg : (m.doms e).initRegions r with _ | s
    · simp only [hcfg] at hrg; cases hrg
    · simp only [hcfg] at hrg
      rcases hcap : (m.doms e).initCaps s with _ | k
      · simp only [hcap] at hrg; cases hrg
      · simp only [hcap] at hrg
        cases k with
        | mem b l p =>
            simp only [Option.some.injEq] at hrg
            rw [← hrg]
        | gate g => simp at hrg
  · intro e hne s entry b l p hcap hkind a hba hab hur
    obtain ⟨sd, bd, ld, pd, hd, hda, had⟩ := hur
    simp only [Manifest.initState, Manifest.bootDom, Option.map_eq_some_iff] at hcap
    obtain ⟨k, hk, hke⟩ := hcap
    have hkind' : k = .mem b l p := by rw [← hkind, ← hke]
    rw [hkind'] at hk
    rcases hiso.roots_disjoint e sd s bd ld pd b l p hne hd hk with hle | hle <;> omega
  · intro job h; exact absurd h (by simp [Manifest.initState])
  · intro g; rfl

/-- `Insulated` pins `d`'s whole capability bookkeeping to boot, so two
insulated runs of agreeing manifests have equal `d`-tables. -/
theorem Insulated.caps_eq {m₁ m₂ : Manifest} {d : DomainId}
    {σ₁ σ₂ : MachineState} (h₁ : Insulated m₁ d σ₁) (h₂ : Insulated m₂ d σ₂)
    (hdom : m₁.doms d = m₂.doms d) :
    (σ₁.doms d).caps = (σ₂.doms d).caps ∧
    (σ₁.doms d).slotGen = (σ₂.doms d).slotGen ∧
    (σ₁.doms d).lineage = (σ₂.doms d).lineage := by
  refine ⟨?_, h₁.boot_slotGen.trans h₂.boot_slotGen.symm,
    h₁.boot_lineage.trans h₂.boot_lineage.symm⟩
  rw [h₁.boot_caps, h₂.boot_caps, hdom]

/-- Boot states are coupled whenever the manifests agree on `d`. -/
theorem coupled_init (m₁ m₂ : Manifest) (d : DomainId)
    (hag : AgreeOn m₁ m₂ d) :
    Coupled m₁ d m₁.initState m₂.initState := by
  obtain ⟨hdom, hrom⟩ := hag
  have hboot : m₁.initState.doms d = m₂.initState.doms d := by
    show Manifest.bootDom d (m₁.doms d) = Manifest.bootDom d (m₂.doms d)
    rw [hdom]
  exact
    { regs := by rw [hboot], pc := by rw [hboot], run := by rw [hboot]
      cause := by rw [hboot], regions := by rw [hboot]
      mem := fun a ha => hrom a ha }

/-! ## Authority geometry: who can touch memory under `d`'s roots -/

/-- A region register of `d` caches (a fragment of) one of `d`'s roots:
its range is inside the root's range and its permissions are below the
root's. The bridge from `fetch`/`load`/`store` checks to root geometry. -/
theorem region_of_insulated {m : Manifest} {d : DomainId} {σ : MachineState}
    (hins : Insulated m d σ) {r : RegionId} {rg : Region}
    (hrg : (σ.doms d).regions r = some rg) :
    ∃ b l p, (m.doms d).initCaps rg.backing.slot = some (.mem b l p) ∧
      b.toNat ≤ rg.base.toNat ∧
      rg.base.toNat + rg.len.toNat ≤ b.toNat + l.toNat ∧
      rg.perms.le p = true := by
  have hown : rg.backing.dom = d := hins.regions_own d r rg hrg
  obtain ⟨e, hlive, hle⟩ := hins.wf.region_backed d r rg hrg
  rw [hown] at hlive
  -- the live entry is a boot entry
  have hcaps : (σ.doms d).caps rg.backing.slot = some e := caps_of_liveCap hlive
  have hboot := hins.boot_caps
  have : (fun s => ((m.doms d).initCaps s).map
      (fun k => ({ kind := k, lineage := none } : CapEntry))) rg.backing.slot = some e := by
    rw [← hboot]; exact hcaps
  simp only [Option.map_eq_some_iff] at this
  obtain ⟨k, hk, hke⟩ := this
  have hek : e.kind = k := by rw [← hke]
  cases k with
  | gate g =>
      rw [hek] at hle
      cases hle
  | mem b l p =>
      rw [hek] at hle
      obtain ⟨hb, hbl, hp⟩ := hle
      exact ⟨b, l, p, hk, hb, hbl, hp⟩

/-- Whatever `d`'s regions cover lies under `d`'s roots (with matching
permission classes): coverage with an `x`-need lands under `x`-roots. -/
theorem domCovers_underRoots {m : Manifest} {d : DomainId} {σ : MachineState}
    (hins : Insulated m d σ) {a : Addr} {need : Perms}
    (hcov : σ.domCovers d a need = true) :
    UnderRoots m d a ∧ (need.x = true → UnderXRoots m d a) := by
  unfold MachineState.domCovers at hcov
  rw [decide_eq_true_iff] at hcov
  obtain ⟨r, rg, hrg, hc⟩ := hcov
  unfold Region.covers at hc
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc
  obtain ⟨⟨hlo, hhi⟩, hperm⟩ := hc
  obtain ⟨b, l, p, hk, hb, hbl, hp⟩ := region_of_insulated hins hrg
  refine ⟨⟨_, b, l, p, hk, by omega, by omega⟩, fun hx => ?_⟩
  have hpx : p.x = true := by
    -- need ≤ rg.perms ≤ p, and need.x
    unfold Perms.le at hperm hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hperm hp
    rcases hperm.2 with h | h
    · rw [hx] at h; cases h
    · rcases hp.2 with h' | h'
      · rw [h] at h'; cases h'
      · exact h'
  exact ⟨_, b, l, p, hk, hpx, by omega, by omega⟩

/-- A successful fetch of an insulated domain reads a ROM word under an
executable root — hence one `code_local` constrains. -/
theorem fetch_of_insulated {m : Manifest} {d : DomainId} {σ : MachineState}
    (hins : Insulated m d σ) {w : Loom.Word32} (hf : fetch σ d = some w) :
    UnderXRoots m d ((σ.doms d).pc) ∧ w = m.rom ((σ.doms d).pc) := by
  unfold fetch at hf
  split at hf
  · rename_i hcov
    have hux := (domCovers_underRoots hins hcov).2 rfl
    refine ⟨hux, ?_⟩
    have : σ.read (σ.doms d).pc = w := by injection hf
    rw [← this]
    exact hins.code_intact _ hux
  · exact absurd hf (by simp)

/-- Fetch is a function of the frozen `d`-slice. -/
theorem fetch_frozen {m : Manifest} {d : DomainId} {σ σ' : MachineState}
    (hins : Insulated m d σ) (hf : DFrozen m d σ σ') :
    fetch σ' d = fetch σ d := by
  unfold fetch
  have hcov : ∀ need, σ'.domCovers d ((σ'.doms d).pc) need =
      σ.domCovers d ((σ.doms d).pc) need := by
    intro need
    unfold MachineState.domCovers
    rw [hf.regions, hf.pc]
  by_cases hc : σ.domCovers d ((σ.doms d).pc) { r := false, w := false, x := true }
  · have hc' : σ'.domCovers d ((σ'.doms d).pc)
        { r := false, w := false, x := true } = true := by rw [hcov]; exact hc
    rw [if_pos hc, if_pos hc']
    have hux := (domCovers_underRoots hins hc).2 rfl
    show some (σ'.mem ((σ'.doms d).pc)) = some (σ.mem ((σ.doms d).pc))
    rw [hf.pc, hf.mem _ hux.underRoots]
  · have hc' : ¬ σ'.domCovers d ((σ'.doms d).pc)
        { r := false, w := false, x := true } = true := by rw [hcov]; exact hc
    rw [if_neg hc, if_neg hc']

/-- Fetch is a function of the coupled `d`-slice: the two runs fetch the
same word (or both fail). -/
theorem fetch_coupled {m₁ : Manifest} {d : DomainId} {σ₁ σ₂ : MachineState}
    (hins₁ : Insulated m₁ d σ₁) (hcpl : Coupled m₁ d σ₁ σ₂) :
    fetch σ₁ d = fetch σ₂ d := by
  unfold fetch
  have hcov : ∀ need, σ₁.domCovers d ((σ₁.doms d).pc) need =
      σ₂.domCovers d ((σ₂.doms d).pc) need := by
    intro need
    unfold MachineState.domCovers
    rw [hcpl.regions, hcpl.pc]
  by_cases hc : σ₁.domCovers d ((σ₁.doms d).pc) { r := false, w := false, x := true }
  · have hc₂ : σ₂.domCovers d ((σ₂.doms d).pc)
        { r := false, w := false, x := true } = true := by rw [← hcov]; exact hc
    rw [if_pos hc, if_pos hc₂]
    have hux := (domCovers_underRoots hins₁ hc).2 rfl
    show some (σ₁.mem ((σ₁.doms d).pc)) = some (σ₂.mem ((σ₂.doms d).pc))
    rw [hcpl.mem _ hux.underRoots, hcpl.pc]
  · have hc₂ : ¬ σ₂.domCovers d ((σ₂.doms d).pc)
        { r := false, w := false, x := true } = true := by rw [← hcov]; exact hc
    rw [if_neg hc, if_neg hc₂]

/-! ## Foreign accesses never reach under `d`'s roots

The three memory channels of a cycle that are *not* `d`'s own instruction —
foreign stores, the Mover's data words, and the Mover status writes — all
go through either `domCovers` of a foreign domain or `moverCheck` of a
foreign capability. Both are excluded from `d`'s roots by
`regions_own`/`foreign_off`. Stated with component hypotheses (all about
`doms`/`mover` only) so they transport across the decorations of a cycle. -/

/-- A covered access by `e ≠ d` misses `d`'s roots: `e`'s region registers
cache `e`'s own capabilities, which are excluded by `foreign_off`. -/
theorem covers_not_underRoots {m : Manifest} {d : DomainId} {σ : MachineState}
    (hrb : ∀ e r rg, (σ.doms e).regions r = some rg →
      ∃ entry, ((σ.doms rg.backing.dom).liveCap rg.backing.slot rg.backing.gen)
          = some entry ∧
        (CapKind.mem rg.base rg.len rg.perms).le entry.kind)
    (hro : ∀ e r rg, (σ.doms e).regions r = some rg → rg.backing.dom = e)
    (hfo : ∀ e, e ≠ d → ∀ s entry b l p, (σ.doms e).caps s = some entry →
      entry.kind = .mem b l p → ∀ a : Addr, b.toNat ≤ a.toNat →
      a.toNat < b.toNat + l.toNat → ¬ UnderRoots m d a)
    {e : DomainId} {a : Addr} {need : Perms} (hne : e ≠ d)
    (hcov : σ.domCovers e a need = true) : ¬ UnderRoots m d a := by
  unfold MachineState.domCovers at hcov
  rw [decide_eq_true_iff] at hcov
  obtain ⟨r, rg, hrg, hc⟩ := hcov
  unfold Region.covers at hc
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc
  obtain ⟨⟨hlo, hhi⟩, _⟩ := hc
  have hown : rg.backing.dom = e := hro e r rg hrg
  obtain ⟨entry, hlive, hle⟩ := hrb e r rg hrg
  rw [hown] at hlive
  have hcaps : (σ.doms e).caps rg.backing.slot = some entry := caps_of_liveCap hlive
  cases hk : entry.kind with
  | gate g => rw [hk] at hle; cases hle
  | mem b l p =>
      rw [hk] at hle
      obtain ⟨hb, hbl, _⟩ := hle
      exact hfo e hne rg.backing.slot entry b l p hcaps hk a (by omega) (by omega)

/-- A Mover per-word check through a capability of `e ≠ d` misses `d`'s
roots. -/
theorem moverCheck_not_underRoots {m : Manifest} {d : DomainId} {σ : MachineState}
    (hfo : ∀ e, e ≠ d → ∀ s entry b l p, (σ.doms e).caps s = some entry →
      entry.kind = .mem b l p → ∀ a : Addr, b.toNat ≤ a.toNat →
      a.toNat < b.toNat + l.toNat → ¬ UnderRoots m d a)
    {r : CapRef} (hne : r.dom ≠ d) {a : Addr} {need : Perms}
    (hc : moverCheck σ r a need = true) : ¬ UnderRoots m d a := by
  unfold moverCheck at hc
  cases hl : (σ.doms r.dom).liveCap r.slot r.gen with
  | none => simp [hl] at hc
  | some e =>
      simp only [hl] at hc
      have hcaps := caps_of_liveCap hl
      cases hk : e.kind with
      | gate g => rw [hk] at hc; simp [CapKind.covers] at hc
      | mem b l p =>
          rw [hk] at hc
          unfold CapKind.covers at hc
          simp only [Bool.and_eq_true, decide_eq_true_iff] at hc
          exact hfo r.dom hne r.slot e b l p hcaps hk a hc.1.1 hc.1.2

/-- The Mover status write never lands under `d`'s roots when the job's
owner is not `d`. -/
theorem moverStatus_mem_frame {m : Manifest} {d : DomainId} {σ : MachineState}
    (hrb : ∀ e r rg, (σ.doms e).regions r = some rg →
      ∃ entry, ((σ.doms rg.backing.dom).liveCap rg.backing.slot rg.backing.gen)
          = some entry ∧
        (CapKind.mem rg.base rg.len rg.perms).le entry.kind)
    (hro : ∀ e r rg, (σ.doms e).regions r = some rg → rg.backing.dom = e)
    (hfo : ∀ e, e ≠ d → ∀ s entry b l p, (σ.doms e).caps s = some entry →
      entry.kind = .mem b l p → ∀ a : Addr, b.toNat ≤ a.toNat →
      a.toNat < b.toNat + l.toNat → ¬ UnderRoots m d a)
    {job : MoverJob} (howner : job.owner ≠ d) (v : Loom.Word32)
    (a : Addr) (ha : UnderRoots m d a) :
    (moverStatus σ job v).mem a = σ.mem a := by
  unfold moverStatus
  by_cases hcov : σ.domCovers job.owner job.statusAddr
      { r := false, w := true, x := false } = true
  · rw [if_pos hcov]
    have hns := covers_not_underRoots hrb hro hfo howner hcov
    show Loom.Fun.update σ.mem job.statusAddr v a = σ.mem a
    exact Loom.Fun.update_ne _ _ _ _ (fun h => hns (h ▸ ha))
  · rw [if_neg hcov]

/-- **The Mover phase leaves memory under `d`'s roots untouched** when its
job (if any) is foreign. -/
theorem moverPhase_mem_frame {m : Manifest} {d : DomainId} {σ : MachineState}
    (hrb : ∀ e r rg, (σ.doms e).regions r = some rg →
      ∃ entry, ((σ.doms rg.backing.dom).liveCap rg.backing.slot rg.backing.gen)
          = some entry ∧
        (CapKind.mem rg.base rg.len rg.perms).le entry.kind)
    (hro : ∀ e r rg, (σ.doms e).regions r = some rg → rg.backing.dom = e)
    (hfo : ∀ e, e ≠ d → ∀ s entry b l p, (σ.doms e).caps s = some entry →
      entry.kind = .mem b l p → ∀ a : Addr, b.toNat ≤ a.toNat →
      a.toNat < b.toNat + l.toNat → ¬ UnderRoots m d a)
    (hmf : ∀ job, σ.mover = some job → job.owner ≠ d)
    (hmw : ∀ job, σ.mover = some job → job.dst.dom = job.owner)
    (a : Addr) (ha : UnderRoots m d a) : (moverPhase σ).mem a = σ.mem a := by
  unfold moverPhase
  cases hj : σ.mover with
  | none => rfl
  | some job =>
      have howner := hmf job hj
      have hdst := hmw job hj
      dsimp only
      by_cases hrem : job.remaining = 0
      · rw [if_pos hrem]
        exact moverStatus_mem_frame (σ := { σ with mover := none })
          hrb hro hfo howner 1 a ha
      · rw [if_neg hrem]
        by_cases hchk : (moverCheck σ job.src job.srcCur
              { r := true, w := false, x := false } &&
            moverCheck σ job.dst job.dstCur
              { r := false, w := true, x := false }) = true
        · rw [if_pos hchk]
          simp only [Bool.and_eq_true] at hchk
          have hnd : ¬ UnderRoots m d job.dstCur :=
            moverCheck_not_underRoots hfo (hdst ▸ howner) hchk.2
          have hwr : (σ.write job.dstCur (σ.read job.srcCur)).mem a = σ.mem a := by
            show Loom.Fun.update σ.mem job.dstCur _ a = σ.mem a
            exact Loom.Fun.update_ne _ _ _ _ (fun h => hnd (h ▸ ha))
          set σ' := σ.write job.dstCur (σ.read job.srcCur) with hσ'
          by_cases hrem' : job.remaining - 1 = 0
          · rw [if_pos hrem']
            refine Eq.trans ?_ hwr
            exact moverStatus_mem_frame (σ := { σ' with mover := none })
              hrb hro hfo howner 1 a ha
          · rw [if_neg hrem']
            exact hwr
        · rw [if_neg hchk]
          exact moverStatus_mem_frame (σ := { σ with mover := none })
            hrb hro hfo howner _ a ha

/-! ## The halt observation (issue-time faults) -/

/-- `step m σ` halted `d` with fault `f` and touched nothing else of `d`'s
slice (nor the memory under `d`'s roots). -/
structure DHalt (m : Manifest) (d : DomainId) (σ σ' : MachineState)
    (f : Fault) : Prop where
  regs : (σ'.doms d).regs = (σ.doms d).regs
  pc : (σ'.doms d).pc = (σ.doms d).pc
  run : (σ'.doms d).run = .halted
  cause : (σ'.doms d).cause = BitVec.ofNat 32 f.code
  serving : (σ'.doms d).serving = none
  caps : (σ'.doms d).caps = (σ.doms d).caps
  slotGen : (σ'.doms d).slotGen = (σ.doms d).slotGen
  lineage : (σ'.doms d).lineage = (σ.doms d).lineage
  regions : (σ'.doms d).regions = (σ.doms d).regions
  mem : ∀ a, UnderRoots m d a → σ'.mem a = σ.mem a
  inflight : σ'.inflight = none

/-- Two matching halts from coupled states leave coupled states. -/
theorem coupled_of_dhalt {m₁ m₂ : Manifest} {d : DomainId}
    {σ₁ σ₂ σ₁' σ₂' : MachineState} {f : Fault}
    (hcpl : Coupled m₁ d σ₁ σ₂) (hdom : m₁.doms d = m₂.doms d)
    (h₁ : DHalt m₁ d σ₁ σ₁' f) (h₂ : DHalt m₂ d σ₂ σ₂' f) :
    Coupled m₁ d σ₁' σ₂' :=
  { regs := by rw [h₁.regs, h₂.regs, hcpl.regs]
    pc := by rw [h₁.pc, h₂.pc, hcpl.pc]
    run := by rw [h₁.run, h₂.run]
    cause := by rw [h₁.cause, h₂.cause]
    regions := by rw [h₁.regions, h₂.regions, hcpl.regions]
    mem := fun a ha => by
      rw [h₁.mem a ha, h₂.mem a ((underRoots_congr hdom a).mp ha)]
      exact hcpl.mem a ha }

/-! ## The core phase latches only the running domain -/

/-- Every in-flight record produced by the core phase belongs either to the
domain already in flight (countdown) or, on an idle core, to the scheduled
domain (issue). The clean characterization `step_quiet` needs. -/
theorem corePhase_inflight_dom (m : Manifest) (σ : MachineState) (fl : InFlight)
    (h : (corePhase m σ).inflight = some fl) :
    (∃ fl0, σ.inflight = some fl0 ∧ fl.dom = fl0.dom) ∨
    (σ.inflight = none ∧ schedule m σ = some fl.dom) := by
  have hhalt : ∀ (d' : DomainId) (f : Fault),
      (haltWith σ d' f).inflight = σ.inflight := fun d' f => by
    rw [haltWith, haltDom_inflight]
  unfold corePhase at h
  rcases hi : σ.inflight with _ | fl0
  · -- idle core
    simp only [hi] at h
    refine Or.inr ⟨rfl, ?_⟩
    rcases hs : schedule m σ with _ | d'
    · simp only [hs] at h; rw [hi] at h; exact absurd h (by simp)
    · simp only [hs] at h
      rcases hf : fetch σ d' with _ | w
      · simp only [hf] at h; rw [hhalt, hi] at h; exact absurd h (by simp)
      · simp only [hf] at h
        rcases hd : Loom.Isa.decode isa w with _ | instr
        · simp only [hd] at h; rw [hhalt, hi] at h; exact absurd h (by simp)
        · simp only [hd] at h
          by_cases hb : instr.cost.cost ≤ (σ.doms (σ.payer d')).budget
          · rw [if_pos hb] at h
            rcases hserv : (σ.doms d').serving with _ | g
            · simp only [hserv] at h
              have h2 : some (⟨d', w, instr.cost.cost⟩ : InFlight) = some fl := h
              injection h2 with h2; rw [← h2]
            · simp only [hserv] at h
              rcases hact : (σ.gates g).act with _ | a
              · simp only [hact] at h; rw [hhalt, hi] at h; exact absurd h (by simp)
              · simp only [hact] at h
                by_cases hdon : instr.cost.cost ≤ a.donated
                · rw [if_pos hdon] at h
                  have h2 : some (⟨d', w, instr.cost.cost⟩ : InFlight) = some fl := h
                  injection h2 with h2; rw [← h2]
                · rw [if_neg hdon] at h; rw [hhalt, hi] at h; exact absurd h (by simp)
          · rw [if_neg hb] at h; rw [hi] at h; exact absurd h (by simp)
  · -- some fl0 in flight
    simp only [hi] at h
    by_cases hc : fl0.cyclesLeft ≤ 1
    · rw [if_pos hc, Machines.Lnp64u.Wip.retire_inflight] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      refine Or.inl ⟨fl0, rfl, ?_⟩
      have h2 : some (⟨fl0.dom, fl0.word, fl0.cyclesLeft - 1⟩ : InFlight) = some fl := h
      injection h2 with h2; rw [← h2]

/-! ## Bridge to the `DFrame` sweep -/

/-- An insulated state satisfies the sweep context. -/
theorem dctx_of_insulated {m : Manifest} {d : DomainId} {σ : MachineState}
    (hiso : Isolated m d) (hins : Insulated m d σ) :
    DFrame.DCtx d (UnderRoots m d) σ where
  dfull := fun s hc => by
    have := congrFun hins.boot_caps s
    rw [hc] at this
    cases hi : (m.doms d).initCaps s with
    | none => exact hiso.slots_full s hi
    | some k => rw [hi] at this; cases this
  dlin := fun l => congrFun hins.boot_lineage l
  dent := fun s e h => by
    have := congrFun hins.boot_caps s
    rw [h] at this
    cases hi : (m.doms d).initCaps s with
    | none => rw [hi] at this; cases this
    | some k =>
        rw [hi] at this
        injection this with this
        rw [this]
  dgates := fun s e g h hk => by
    have := congrFun hins.boot_caps s
    rw [h] at this
    cases hi : (m.doms d).initCaps s with
    | none => rw [hi] at this; cases this
    | some k =>
        rw [hi] at this
        injection this with this
        have hkk : k = .gate g := by
          have := congrArg CapEntry.kind this
          simp only [hk] at this
          exact this.symm
        exact hiso.no_gates_held s g (hkk ▸ hi)
  dserv := hins.serving_none
  dnoblk := hins.not_blocked
  dreg := fun r rg hrg => by
    have hown := hins.regions_own d r rg hrg
    obtain ⟨entry, hlive, -⟩ := hins.wf.region_backed d r rg hrg
    rw [hown] at hlive
    exact ⟨hown, by rw [hlive]; rfl⟩
  ro := hins.regions_own
  fo := hins.foreign_off
  covOff := fun e he a need hcov =>
    covers_not_underRoots hins.wf.region_backed hins.regions_own hins.foreign_off
      he hcov
  movOff := hins.mover_foreign
  ncallee := fun g => by rw [hins.gates_static g]; exact hiso.no_gates_in g
  acaller := fun g a ha hc => by
    have hblk := (hins.wf.gate_serving g a ha).2.1
    rw [hc] at hblk
    exact hins.not_blocked g hblk

/-- The sweep context survives the refill phase (budgets only). -/
theorem dctx_refill {m : Manifest} {d : DomainId} {σ : MachineState}
    (hctx : DFrame.DCtx d (UnderRoots m d) σ) :
    DFrame.DCtx d (UnderRoots m d) (refillPhase m σ) where
  dfull := fun s => by rw [refillPhase_caps]; exact hctx.dfull s
  dlin := fun l => by rw [refillPhase_lineage]; exact hctx.dlin l
  dent := fun s e h => hctx.dent s e (by rw [← refillPhase_caps m σ d]; exact h)
  dgates := fun s e g h => hctx.dgates s e g (by rw [← refillPhase_caps m σ d]; exact h)
  dserv := by rw [refillPhase_serving]; exact hctx.dserv
  dnoblk := fun g => by rw [refillPhase_run]; exact hctx.dnoblk g
  dreg := fun r rg hrg => by
    rw [refillPhase_regions] at hrg
    obtain ⟨hown, hlive⟩ := hctx.dreg r rg hrg
    refine ⟨hown, ?_⟩
    rw [liveCap_congr_of_eq _ _ (refillPhase_caps m σ d) (refillPhase_slotGen m σ d)]
    exact hlive
  ro := fun e r rg h => hctx.ro e r rg (by rw [← refillPhase_regions m σ e]; exact h)
  fo := fun e he s entry b l p hc =>
    hctx.fo e he s entry b l p (by rw [← refillPhase_caps m σ e]; exact hc)
  covOff := fun e he a need hcov => by
    refine hctx.covOff e he a need ?_
    unfold MachineState.domCovers at hcov ⊢
    rw [decide_eq_true_iff] at hcov ⊢
    obtain ⟨r, rg, hrg, hc⟩ := hcov
    rw [refillPhase_regions] at hrg
    exact ⟨r, rg, hrg, hc⟩
  movOff := fun job hj => hctx.movOff job (by rw [← refillPhase_mover m σ]; exact hj)
  ncallee := fun g => by rw [refillPhase_gates]; exact hctx.ncallee g
  acaller := fun g a ha => hctx.acaller g a (by rw [← refillPhase_gates m σ]; exact ha)

/-- Refill never touches `maxDonation`. -/
theorem refillPhase_maxDon (m : Manifest) (σ : MachineState) (d : DomainId) :
    ((refillPhase m σ).doms d).maxDonation = (σ.doms d).maxDonation := by
  rcases refillPhase_doms m σ d with h | h <;> rw [h]

/-- A writable coverage of `d` never lands under `d`'s executable roots
(`wx_disjoint`): `d` cannot rewrite its own code. -/
theorem covers_w_not_underXRoots {m : Manifest} {d : DomainId} {σ : MachineState}
    (hiso : Isolated m d) (hins : Insulated m d σ) :
    ∀ a, σ.domCovers d a { r := false, w := true, x := false } = true →
      ¬ UnderXRoots m d a := by
  intro a hcov hX
  unfold MachineState.domCovers at hcov
  rw [decide_eq_true_iff] at hcov
  obtain ⟨r, rg, hrg, hc⟩ := hcov
  unfold Region.covers at hc
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc
  obtain ⟨⟨hlo, hhi⟩, hperm⟩ := hc
  obtain ⟨b, l, p, hk, hb, hbl, hp⟩ := region_of_insulated hins hrg
  have hw : rg.perms.w = true := by
    by_contra hn
    have hz : rg.perms.w = false := by revert hn; cases rg.perms.w <;> simp
    unfold Perms.le at hperm
    rw [hz] at hperm
    simp at hperm
  have hpw : p.w = true := by
    by_contra hn
    have hz : p.w = false := by revert hn; cases p.w <;> simp
    unfold Perms.le at hp
    rw [hz, hw] at hp
    simp at hp
  obtain ⟨s', b', l', p', hk', hx', hb', hbl'⟩ := hX
  rcases hiso.wx_disjoint _ s' b l p b' l' p' hk hk' hpw hx' with hle | hle <;> omega

/-- The refill phase leaves coverage alone. -/
theorem refillPhase_covers (m : Manifest) (σ : MachineState) (e : DomainId)
    (a : Addr) (need : Perms) :
    (refillPhase m σ).domCovers e a need = σ.domCovers e a need := by
  unfold MachineState.domCovers
  rw [refillPhase_regions]

/-! ## The engine lemmas

The four cycle-level engines the T5 assembly consumes — all discharged
(2026-07-03) on the sweep infrastructure of `Logic/DFrame.lean` (the unary
d-frame sweep: `DCtx`/`DKeep`/`DCycle` for foreign cycles, `DSelf` for
`d`'s own `code_local`-constrained retirement) and `Logic/DRel.lean` (the
two-run relational sweep `RC`/`RLe` behind the lockstep):

1. `insulated_step` — invariant preservation: foreign cycles via
   `DFrame.corePhase_dcycle`, `d`'s own retirement via
   `DFrame.retire_dself` (ROM pinning + `code_local` exclude the four
   global opcodes), `d`'s issue instants by direct `corePhase` shapes;
   `Wf`/`Acyclic` via `step_wfa`.
2. `frame_step` — the d-slice frame over a non-`d` cycle
   (`corePhase_dcycle` + the Mover memory frame).
3. `retire_step_lockstep` — the relational sweep `DRel.retire_rel`: the
   same ROM word retires from `RC`-coupled slices to `RC`-coupled slices.
4. `progress` — scheduling liveness: `frame_step`/`stall_step` walk,
   `refill_within_period` funds `d`, `TopPriority` (`schedule_top`) hands
   `d` the first idle instant, and the in-flight countdown bounds the wait.

They remain in `Wip` purely to avoid churning the `T5.lean` consumers'
names; all are `sorry`-free.
-/

namespace Wip

/-- **Engine 2: the d-slice frame.** A cycle that does not retire `d`'s
in-flight instruction and does not issue for `d` leaves `d`'s slice and
the memory under `d`'s roots untouched. -/
theorem frame_step_full (m : Manifest) (d : DomainId) (σ : MachineState)
    (hm : m.WF) (hiso : Isolated m d) (hins : Insulated m d σ)
    (hnr : ∀ fl, σ.inflight = some fl → fl.dom = d → 1 < fl.cyclesLeft)
    (hni : σ.inflight = none → schedule m (refillPhase m σ) ≠ some d) :
    DFrozen m d σ (step m σ) ∧
    (step m σ).doms d = (refillPhase m σ).doms d := by
  have hctx := dctx_of_insulated hiso hins
  have hctxρ : DFrame.DCtx d (UnderRoots m d) (refillPhase m σ) := dctx_refill hctx
  have hwfρ : Wf (refillPhase m σ) := refillPhase_preserves_wf m σ hins.wf
  have hexecA : ExecPreservesWfA :=
    execPreservesWfA_of_system Machines.Lnp64u.Isa.Wip.system_preserves_wfa
  have hwfκ : Wf (corePhase m (refillPhase m σ)) :=
    (corePhase_preserves_wfa hexecA m hm _ hwfρ (acyclic_refillPhase m σ hins.acyclic)).1
  have hcy : DFrame.DCycle d (UnderRoots m d) (refillPhase m σ)
      (corePhase m (refillPhase m σ)) := by
    refine DFrame.corePhase_dcycle m _ hctxρ ?_ ?_
    · intro fl hfl hfd
      rw [refillPhase_inflight] at hfl
      exact hnr fl hfl hfd
    · intro h
      rw [refillPhase_inflight] at h
      exact hni h
  have hmemμ : ∀ a, UnderRoots m d a →
      (moverPhase (corePhase m (refillPhase m σ))).mem a
        = (corePhase m (refillPhase m σ)).mem a := by
    intro a ha
    refine moverPhase_mem_frame hwfκ.region_backed hcy.ro hcy.fo ?_ ?_ a ha
    · intro job hj
      rcases hcy.mover job hj with hj' | hj'
      · rw [refillPhase_mover] at hj'
        exact hins.mover_foreign job hj'
      · exact hj'
    · intro job hj
      exact (hwfκ.mover_wf job hj).2.1
  have hdd : (step m σ).doms d = (refillPhase m σ).doms d := by
    rw [step_doms]
    exact hcy.ddoms
  have hmem : ∀ a, UnderRoots m d a → (step m σ).mem a = σ.mem a := by
    intro a ha
    have h1 : (step m σ).mem a
        = (moverPhase (corePhase m (refillPhase m σ))).mem a := rfl
    rw [h1, hmemμ a ha, hcy.mem a ha]
    exact congrFun (refillPhase_frame m σ).1 a
  exact
    ⟨{ regs := by rw [hdd, refillPhase_regs]
       pc := by rw [hdd, refillPhase_pc]
       run := by rw [hdd, refillPhase_run]
       cause := by rw [hdd, refillPhase_cause]
       serving := by rw [hdd, refillPhase_serving]
       caps := by rw [hdd, refillPhase_caps]
       slotGen := by rw [hdd, refillPhase_slotGen]
       lineage := by rw [hdd, refillPhase_lineage]
       regions := by rw [hdd, refillPhase_regions]
       mem := hmem }, hdd⟩

/-- **Engine 2: the d-slice frame.** A cycle that does not retire `d`'s
in-flight instruction and does not issue for `d` leaves `d`'s slice and
the memory under `d`'s roots untouched. -/
theorem frame_step (m : Manifest) (d : DomainId) (σ : MachineState)
    (hm : m.WF) (hiso : Isolated m d) (hins : Insulated m d σ)
    (hnr : ∀ fl, σ.inflight = some fl → fl.dom = d → 1 < fl.cyclesLeft)
    (hni : σ.inflight = none → schedule m (refillPhase m σ) ≠ some d) :
    DFrozen m d σ (step m σ) :=
  (frame_step_full m d σ hm hiso hins hnr hni).1

/-- **Engine 1: the insulation invariant is inductive.** -/
theorem insulated_step (m : Manifest) (d : DomainId) (σ : MachineState)
    (hm : m.WF) (hiso : Isolated m d) (hins : Insulated m d σ) :
    Insulated m d (step m σ) := by
  have hexecA := execPreservesWfA_of_system Machines.Lnp64u.Isa.Wip.system_preserves_wfa
  obtain ⟨hwf', hac'⟩ := step_wfa hexecA m hm σ hins.wf hins.acyclic
  have hctx := dctx_of_insulated hiso hins
  have hctxρ := dctx_refill (m := m) hctx
  have hwfρ : Wf (refillPhase m σ) := refillPhase_preserves_wf m σ hins.wf
  have hwfκ : Wf (corePhase m (refillPhase m σ)) :=
    (corePhase_preserves_wfa hexecA m hm _ hwfρ (acyclic_refillPhase m σ hins.acyclic)).1
  set ρ := refillPhase m σ with hρdef
  set κ := corePhase m ρ with hκdef
  have hdoms : (step m σ).doms = κ.doms := step_doms m σ
  have hgatesS : (step m σ).gates = κ.gates := moverPhase_gates κ
  have hinfS : (step m σ).inflight = κ.inflight := moverPhase_inflight κ
  have hservρ : (ρ.doms d).serving = none := hctxρ.dserv
  have hmemρ : ∀ a, ρ.mem a = σ.mem a := fun a => congrFun (refillPhase_frame m σ).1 a
  -- the common assembly from κ-level facts
  have assemble :
      (κ.doms d).caps = (σ.doms d).caps →
      (κ.doms d).slotGen = (σ.doms d).slotGen →
      (κ.doms d).lineage = (σ.doms d).lineage →
      (κ.doms d).serving = none →
      (∀ g, (κ.doms d).run ≠ .blocked g) →
      (∀ e r rg, (κ.doms e).regions r = some rg → rg.backing.dom = e) →
      (∀ e, e ≠ d → ∀ s entry b l p, (κ.doms e).caps s = some entry →
        entry.kind = .mem b l p → ∀ a : Addr, b.toNat ≤ a.toNat →
        a.toNat < b.toNat + l.toNat → ¬ UnderRoots m d a) →
      (∀ job, κ.mover = some job → job.owner ≠ d) →
      (∀ g, (κ.gates g).config = (σ.gates g).config) →
      (κ.doms d).budget ≤ (m.doms d).budgetQ →
      (κ.doms d).maxDonation = (m.doms d).maxDonation →
      (∀ a, UnderXRoots m d a → κ.mem a = σ.mem a) →
      ((∀ a, UnderRoots m d a → (step m σ).mem a = κ.mem a) →
        ∀ fl, κ.inflight = some fl → fl.dom = d →
          fetch (step m σ) d = some fl.word) →
      Insulated m d (step m σ) := by
    intro hcaps hgen hlin hserv hnb hro hfo hmov hgcfg hbud hmdon hmemX hlatch
    have hmemR : ∀ a, UnderRoots m d a → (step m σ).mem a = κ.mem a := by
      intro a ha
      exact moverPhase_mem_frame hwfκ.region_backed hro hfo hmov
        (fun job hj => (hwfκ.mover_wf job hj).2.1) a ha
    refine ⟨hwf', hac', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [congrFun hdoms d, hcaps]; exact hins.boot_caps
    · rw [congrFun hdoms d, hgen]; exact hins.boot_slotGen
    · rw [congrFun hdoms d, hlin]; exact hins.boot_lineage
    · rw [congrFun hdoms d]; exact hserv
    · intro g; rw [congrFun hdoms d]; exact hnb g
    · intro e r rg h
      rw [congrFun hdoms e] at h
      exact hro e r rg h
    · intro e he s entry b l p hc hk
      rw [congrFun hdoms e] at hc
      exact hfo e he s entry b l p hc hk
    · intro job hj
      have hj' : (moverPhase κ).mover = some job := hj
      rcases moverPhase_mover κ with hnone | ⟨job0, job', hj0, hjeq, howner, -, -⟩
      · rw [hnone] at hj'; cases hj'
      · rw [hjeq] at hj'
        injection hj' with hj'
        rw [← hj', howner]
        exact hmov job0 hj0
    · intro g
      have h1 : ((step m σ).gates g).config = ((κ.gates g)).config := by rw [hgatesS]
      rw [h1, hgcfg g]
      exact hins.gates_static g
    · rw [congrFun hdoms d]; exact hbud
    · rw [congrFun hdoms d]; exact hmdon
    · intro a hX
      rw [hmemR a hX.underRoots, hmemX a hX]
      exact hins.code_intact a hX
    · intro fl hfl hfd
      rw [hinfS] at hfl
      exact hlatch hmemR fl hfl hfd
  rcases hinf : σ.inflight with _ | fl
  · -- idle core
    have hρinf : ρ.inflight = none := by rw [hρdef, refillPhase_inflight]; exact hinf
    by_cases hsd : schedule m ρ = some d
    · -- CASE C: issue instant for d
      have hpay : ρ.payer d = d := payer_eq_self ρ d hservρ
      have hfρ : fetch ρ d = fetch σ d := by rw [hρdef]; exact refillPhase_fetch m σ d
      -- a sub-assembly for the two issue-halt shapes and the stall
      have haltcase : ∀ f : Fault, corePhase m ρ = haltWith ρ d f →
          Insulated m d (step m σ) := by
        intro f hcore
        have hbase : κ = ρ.haltBase d (BitVec.ofNat 32 f.code) := by
          rw [hκdef, hcore]
          exact haltDom_base ρ d _ hservρ
        have hdd : ∀ pr : DomainState → Prop,
            pr (ρ.haltBase d (BitVec.ofNat 32 f.code) |>.doms d) → pr (κ.doms d) := by
          intro pr h
          rw [hbase]
          exact h
        refine assemble ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hbase, haltBase_caps, hρdef, refillPhase_caps]
        · rw [hbase, haltBase_slotGen, hρdef, refillPhase_slotGen]
        · rw [hbase, haltBase_lineage, hρdef, refillPhase_lineage]
        · rw [hbase, haltBase_serving, if_pos rfl]
        · intro g
          rw [hbase, haltBase_run, if_pos rfl]
          simp
        · intro e r rg h
          rw [hbase, haltBase_regions] at h
          exact hctxρ.ro e r rg h
        · intro e he s entry b l p hc hk
          rw [hbase, haltBase_caps] at hc
          exact hctxρ.fo e he s entry b l p hc hk
        · intro job hj
          rw [hbase, haltBase_mover] at hj
          exact hctxρ.movOff job hj
        · intro g
          rw [hbase]
          show ((ρ.haltBase d _).gates g).config = _
          rw [haltBase_gates, hρdef, refillPhase_gates]
        · have : (κ.doms d).budget = (ρ.doms d).budget := by
            rw [hbase]
            unfold MachineState.haltBase
            rw [setDom_doms_same]
          rw [this]
          exact refillPhase_budget_le m σ d hins.budget_le
        · have : (κ.doms d).maxDonation = (ρ.doms d).maxDonation := by
            rw [hbase]
            unfold MachineState.haltBase
            rw [setDom_doms_same]
          rw [this, hρdef, refillPhase_maxDon]
          exact hins.maxDon_eq
        · intro a hX
          rw [hbase]
          show (ρ.haltBase d _).mem a = σ.mem a
          exact hmemρ a
        · intro _ fl hfl
          rw [hbase, haltBase_inflight, hρinf] at hfl
          cases hfl
      cases hf : fetch σ d with
      | none =>
          refine haltcase .memoryAuthority ?_
          have hfρ' : fetch ρ d = none := by rw [hfρ]; exact hf
          unfold corePhase
          simp only [hρinf, hsd, hfρ']
      | some w =>
          have hfρ' : fetch ρ d = some w := by rw [hfρ]; exact hf
          cases hd : Loom.Isa.decode isa w with
          | none =>
              refine haltcase .illegalInstruction ?_
              unfold corePhase
              simp only [hρinf, hsd, hfρ', hd]
          | some instr =>
              by_cases hbud : instr.cost.cost ≤ (ρ.doms d).budget
              · -- latch
                have hbud' : instr.cost.cost ≤ (ρ.doms (ρ.payer d)).budget := by
                  rw [hpay]; exact hbud
                have hcore : κ =
                    { ρ.setDom (ρ.payer d)
                        (fun ds => { ds with budget := ds.budget - instr.cost.cost })
                      with inflight := some ⟨d, w, instr.cost.cost⟩ } := by
                  rw [hκdef]
                  unfold corePhase
                  simp only [hρinf, hsd, hfρ', hd, hservρ]
                  rw [if_pos hbud']
                rw [hpay] at hcore
                have hκd : κ.doms d =
                    { ρ.doms d with budget := (ρ.doms d).budget - instr.cost.cost } := by
                  rw [hcore]
                  exact setDom_doms_same ρ d
                    (fun ds => { ds with budget := ds.budget - instr.cost.cost })
                have hκe : ∀ e, e ≠ d → κ.doms e = ρ.doms e := by
                  intro e he
                  rw [hcore]
                  exact setDom_doms_ne ρ d
                    (fun ds => { ds with budget := ds.budget - instr.cost.cost }) e he
                refine assemble ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                · rw [hκd, hρdef, refillPhase_caps]
                · rw [hκd, hρdef, refillPhase_slotGen]
                · rw [hκd, hρdef, refillPhase_lineage]
                · rw [hκd]; exact hservρ
                · intro g
                  rw [hκd]
                  show (ρ.doms d).run ≠ .blocked g
                  exact hctxρ.dnoblk g
                · intro e r rg h
                  by_cases he : e = d
                  · subst he
                    rw [hκd] at h
                    exact hctxρ.ro e r rg h
                  · rw [hκe e he] at h
                    exact hctxρ.ro e r rg h
                · intro e he s entry b l p hc hk
                  rw [hκe e he] at hc
                  exact hctxρ.fo e he s entry b l p hc hk
                · intro job hj
                  rw [hcore] at hj
                  exact hctxρ.movOff job hj
                · intro g
                  have h1 : (κ.gates g).config = (ρ.gates g).config := by
                    rw [hcore]
                    rfl
                  rw [h1, hρdef, refillPhase_gates]
                · rw [hκd]
                  show (ρ.doms d).budget - instr.cost.cost ≤ (m.doms d).budgetQ
                  have := refillPhase_budget_le m σ d hins.budget_le
                  rw [← hρdef] at this
                  omega
                · rw [hκd]
                  show (ρ.doms d).maxDonation = _
                  rw [hρdef, refillPhase_maxDon]
                  exact hins.maxDon_eq
                · intro a hX
                  rw [hcore]
                  show ρ.mem a = σ.mem a
                  exact hmemρ a
                · intro hmemR fl hfl hfd
                  rw [hcore] at hfl
                  have hfl' : some (⟨d, w, instr.cost.cost⟩ : InFlight) = some fl := hfl
                  injection hfl' with hfl'
                  rw [← hfl']
                  show fetch (step m σ) d = some w
                  have hfz : DFrozen m d σ (step m σ) := by
                    have hd1 : (step m σ).doms d = κ.doms d := congrFun hdoms d
                    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · rw [hd1, hκd]
                      show (ρ.doms d).regs = _
                      rw [hρdef, refillPhase_regs]
                    · rw [hd1, hκd]
                      show (ρ.doms d).pc = _
                      rw [hρdef, refillPhase_pc]
                    · rw [hd1, hκd]
                      show (ρ.doms d).run = _
                      rw [hρdef, refillPhase_run]
                    · rw [hd1, hκd]
                      show (ρ.doms d).cause = _
                      rw [hρdef, refillPhase_cause]
                    · rw [hd1, hκd]
                      show (ρ.doms d).serving = _
                      rw [hρdef, refillPhase_serving]
                    · rw [hd1, hκd]
                      show (ρ.doms d).caps = _
                      rw [hρdef, refillPhase_caps]
                    · rw [hd1, hκd]
                      show (ρ.doms d).slotGen = _
                      rw [hρdef, refillPhase_slotGen]
                    · rw [hd1, hκd]
                      show (ρ.doms d).lineage = _
                      rw [hρdef, refillPhase_lineage]
                    · rw [hd1, hκd]
                      show (ρ.doms d).regions = _
                      rw [hρdef, refillPhase_regions]
                    · intro a ha
                      rw [hmemR a ha, hcore]
                      show ρ.mem a = σ.mem a
                      exact hmemρ a
                  rw [fetch_frozen hins hfz]
                  exact hf
              · -- stall
                have hcore : κ = ρ :=
                  corePhase_stall m ρ d w instr hρinf hsd hfρ' hd
                    (by rw [hpay]; exact hbud)
                refine assemble ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                · rw [hcore, hρdef, refillPhase_caps]
                · rw [hcore, hρdef, refillPhase_slotGen]
                · rw [hcore, hρdef, refillPhase_lineage]
                · rw [hcore]; exact hservρ
                · intro g; rw [hcore]; exact hctxρ.dnoblk g
                · intro e r rg h; rw [hcore] at h; exact hctxρ.ro e r rg h
                · intro e he s entry b l p hc hk
                  rw [hcore] at hc
                  exact hctxρ.fo e he s entry b l p hc hk
                · intro job hj; rw [hcore] at hj; exact hctxρ.movOff job hj
                · intro g; rw [hcore, hρdef, refillPhase_gates]
                · rw [hcore]
                  exact refillPhase_budget_le m σ d hins.budget_le
                · rw [hcore, hρdef, refillPhase_maxDon]; exact hins.maxDon_eq
                · intro a _; rw [hcore]; exact hmemρ a
                · intro _ fl hfl
                  rw [hcore, hρinf] at hfl
                  cases hfl
    · -- CASE A3: idle, no d-issue
      have hfz := frame_step m d σ hm hiso hins
        (fun fl' hfl' _ => by rw [hinf] at hfl'; cases hfl')
        (fun _ => by rw [← hρdef]; exact hsd)
      have hcy : DFrame.DCycle d (UnderRoots m d) ρ κ := by
        rw [hκdef]
        refine DFrame.corePhase_dcycle m ρ hctxρ ?_ ?_
        · intro fl' hfl' _
          rw [hρinf] at hfl'
          cases hfl'
        · intro _
          exact hsd
      refine assemble ?_ ?_ ?_ ?_ ?_ hcy.ro hcy.fo ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hcy.ddoms, hρdef, refillPhase_caps]
      · rw [hcy.ddoms, hρdef, refillPhase_slotGen]
      · rw [hcy.ddoms, hρdef, refillPhase_lineage]
      · rw [hcy.ddoms]; exact hservρ
      · intro g; rw [hcy.ddoms]; exact hctxρ.dnoblk g
      · intro job hj
        rcases hcy.mover job hj with hj' | hj'
        · rw [hρdef, refillPhase_mover] at hj'
          exact hins.mover_foreign job hj'
        · exact hj'
      · intro g
        rw [hcy.gcfg g, hρdef, refillPhase_gates]
      · rw [hcy.ddoms]
        exact refillPhase_budget_le m σ d hins.budget_le
      · rw [hcy.ddoms, hρdef, refillPhase_maxDon]; exact hins.maxDon_eq
      · intro a hX
        rw [hcy.mem a hX.underRoots]
        exact hmemρ a
      · intro _ fl' hfl' hfd'
        rcases corePhase_inflight_dom m ρ fl' (by rw [← hκdef]; exact hfl') with
          ⟨fl0, hfl0, -⟩ | ⟨-, hs⟩
        · rw [hρinf] at hfl0; cases hfl0
        · rw [hfd'] at hs
          exact absurd hs hsd
  · -- an instruction is in flight
    have hρinf : ρ.inflight = some fl := by rw [hρdef, refillPhase_inflight]; exact hinf
    by_cases hcl : fl.cyclesLeft ≤ 1
    · by_cases hfld : fl.dom = d
      · -- CASE B: d retires its latched (ROM-pinned) word
        have hword : fetch σ d = some fl.word := hins.latch_rom fl hinf hfld
        obtain ⟨hux, hwrom⟩ := fetch_of_insulated hins hword
        have hop : ∀ instr, Loom.Isa.decode isa fl.word = some instr →
            instr.opcode ≠ 17 ∧ instr.opcode ≠ 18 ∧ instr.opcode ≠ 19 ∧
            instr.opcode ≠ 24 := by
          intro instr hdec
          refine hiso.code_local _ hux.underRoots instr ?_
          rw [← hwrom]
          exact hdec
        have hcore : κ = retire { ρ with inflight := none } d fl.word := by
          rw [hκdef]
          unfold corePhase
          simp only [hρinf]
          rw [if_pos hcl, hfld]
        have hDS : DFrame.DSelf d (UnderXRoots m d) { ρ with inflight := none } κ := by
          rw [hcore]
          refine DFrame.retire_dself _ fl.word ?_ ?_ ?_ ?_ hop
          · exact hctxρ.dfull
          · exact hctxρ.dgates
          · exact hctxρ.dserv
          · intro a hcov
            refine covers_w_not_underXRoots hiso hins a ?_
            rw [← refillPhase_covers m σ d a]
            exact hcov
        refine assemble ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [show ((κ.doms d).caps = (ρ.doms d).caps) from hDS.caps,
            hρdef, refillPhase_caps]
        · rw [show ((κ.doms d).slotGen = (ρ.doms d).slotGen) from hDS.slotGen,
            hρdef, refillPhase_slotGen]
        · rw [show ((κ.doms d).lineage = (ρ.doms d).lineage) from hDS.lineage,
            hρdef, refillPhase_lineage]
        · rw [show ((κ.doms d).serving = (ρ.doms d).serving) from hDS.serving]
          exact hservρ
        · intro g hblk
          exact hctxρ.dnoblk g (hDS.nb g hblk)
        · intro e r rg h
          by_cases he : e = d
          · subst he
            rcases hDS.regsown r rg h with h' | h'
            · exact h'
            · exact hctxρ.ro e r rg h'
          · rw [show (κ.doms e = ρ.doms e) from hDS.odoms e he] at h
            exact hctxρ.ro e r rg h
        · intro e he s entry b l p hc hk
          rw [show (κ.doms e = ρ.doms e) from hDS.odoms e he] at hc
          exact hctxρ.fo e he s entry b l p hc hk
        · intro job hj
          exact hctxρ.movOff job (hDS.mover job hj)
        · intro g
          rw [show ((κ.gates g).config = (ρ.gates g).config) from hDS.gcfg g,
            hρdef, refillPhase_gates]
        · have hb := hDS.bud
          have := refillPhase_budget_le m σ d hins.budget_le
          rw [← hρdef] at this
          show (κ.doms d).budget ≤ _
          have hb' : (κ.doms d).budget ≤ (ρ.doms d).budget := hb
          omega
        · rw [show ((κ.doms d).maxDonation = (ρ.doms d).maxDonation) from hDS.mdon,
            hρdef, refillPhase_maxDon]
          exact hins.maxDon_eq
        · intro a hX
          rw [show (κ.mem a = ρ.mem a) from hDS.memX a hX]
          exact hmemρ a
        · intro _ fl' hfl' _
          rw [hcore, Machines.Lnp64u.Wip.retire_inflight] at hfl'
          cases hfl'
      · -- CASE A1: a foreign instruction retires
        have hfz := frame_step m d σ hm hiso hins
          (fun fl' hfl' hfd' => by
            rw [hinf] at hfl'
            injection hfl' with hfl'
            rw [← hfl'] at hfd'
            exact absurd hfd' hfld)
          (fun h => by rw [hinf] at h; cases h)
        have hcy : DFrame.DCycle d (UnderRoots m d) ρ κ := by
          rw [hκdef]
          refine DFrame.corePhase_dcycle m ρ hctxρ ?_ ?_
          · intro fl' hfl' hfd'
            rw [hρinf] at hfl'
            injection hfl' with hfl'
            rw [← hfl'] at hfd'
            exact absurd hfd' hfld
          · intro h
            rw [hρinf] at h
            cases h
        have hκinf : κ.inflight = none := by
          rw [hκdef]
          unfold corePhase
          simp only [hρinf]
          rw [if_pos hcl, Machines.Lnp64u.Wip.retire_inflight]
        refine assemble ?_ ?_ ?_ ?_ ?_ hcy.ro hcy.fo ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hcy.ddoms, hρdef, refillPhase_caps]
        · rw [hcy.ddoms, hρdef, refillPhase_slotGen]
        · rw [hcy.ddoms, hρdef, refillPhase_lineage]
        · rw [hcy.ddoms]; exact hservρ
        · intro g; rw [hcy.ddoms]; exact hctxρ.dnoblk g
        · intro job hj
          rcases hcy.mover job hj with hj' | hj'
          · rw [hρdef, refillPhase_mover] at hj'
            exact hins.mover_foreign job hj'
          · exact hj'
        · intro g
          rw [hcy.gcfg g, hρdef, refillPhase_gates]
        · rw [hcy.ddoms]
          exact refillPhase_budget_le m σ d hins.budget_le
        · rw [hcy.ddoms, hρdef, refillPhase_maxDon]; exact hins.maxDon_eq
        · intro a hX
          rw [hcy.mem a hX.underRoots]
          exact hmemρ a
        · intro _ fl' hfl' _
          rw [hκinf] at hfl'
          cases hfl'
    · -- CASE A2: countdown
      have hfz := frame_step m d σ hm hiso hins
        (fun fl' hfl' _ => by
          rw [hinf] at hfl'
          injection hfl' with hfl'
          rw [← hfl']
          omega)
        (fun h => by rw [hinf] at h; cases h)
      have hcy : DFrame.DCycle d (UnderRoots m d) ρ κ := by
        rw [hκdef]
        refine DFrame.corePhase_dcycle m ρ hctxρ ?_ ?_
        · intro fl' hfl' _
          rw [hρinf] at hfl'
          injection hfl' with hfl'
          rw [← hfl']
          omega
        · intro h
          rw [hρinf] at h
          cases h
      have hκinf : κ.inflight = some { fl with cyclesLeft := fl.cyclesLeft - 1 } := by
        rw [hκdef]
        unfold corePhase
        simp only [hρinf]
        rw [if_neg hcl]
      refine assemble ?_ ?_ ?_ ?_ ?_ hcy.ro hcy.fo ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hcy.ddoms, hρdef, refillPhase_caps]
      · rw [hcy.ddoms, hρdef, refillPhase_slotGen]
      · rw [hcy.ddoms, hρdef, refillPhase_lineage]
      · rw [hcy.ddoms]; exact hservρ
      · intro g; rw [hcy.ddoms]; exact hctxρ.dnoblk g
      · intro job hj
        rcases hcy.mover job hj with hj' | hj'
        · rw [hρdef, refillPhase_mover] at hj'
          exact hins.mover_foreign job hj'
        · exact hj'
      · intro g
        rw [hcy.gcfg g, hρdef, refillPhase_gates]
      · rw [hcy.ddoms]
        exact refillPhase_budget_le m σ d hins.budget_le
      · rw [hcy.ddoms, hρdef, refillPhase_maxDon]; exact hins.maxDon_eq
      · intro a hX
        rw [hcy.mem a hX.underRoots]
        exact hmemρ a
      · intro _ fl' hfl' hfd'
        rw [hκinf] at hfl'
        injection hfl' with hfl'
        have hword : fetch σ d = some fl.word := by
          refine hins.latch_rom fl hinf ?_
          rw [← hfl'] at hfd'
          exact hfd'
        rw [← hfl']
        show fetch (step m σ) d = some fl.word
        rw [fetch_frozen hins hfz]
        exact hword

/-- Insulation along a run. -/
theorem insulated_stepN (m : Manifest) (d : DomainId)
    (hm : m.WF) (hiso : Isolated m d) :
    ∀ (n : Nat) (σ : MachineState), Insulated m d σ →
      Insulated m d (stepN m n σ)
  | 0, σ, h => h
  | n + 1, σ, h =>
      insulated_stepN m d hm hiso n (step m σ) (insulated_step m d σ hm hiso h)


/-- **Quiet preservation** over a cycle that does not issue for `d`. -/
theorem step_quiet (m : Manifest) (d : DomainId) (σ : MachineState)
    (hq : Quiet d σ)
    (hni : σ.inflight = none → schedule m (refillPhase m σ) ≠ some d) :
    Quiet d (step m σ) := by
  intro fl hfl
  rw [Machines.Lnp64u.Wip.step_inflight_reduce] at hfl
  set ρ := refillPhase m σ with hρ
  have hρinf : ρ.inflight = σ.inflight := refillPhase_inflight m σ
  rcases corePhase_inflight_dom m ρ fl hfl with ⟨fl0, hfl0, hdd⟩ | ⟨h0, hs⟩
  · rw [hρinf] at hfl0
    rw [hdd]
    exact hq fl0 hfl0
  · -- issue on an idle core: fl.dom is the scheduled domain
    rw [hρinf] at h0
    intro hcontra
    exact hni h0 (hcontra ▸ hs)


/-- **Engine 3: retirement lockstep.** Both runs retire the same latched
word for `d` from coupled, insulated states: the post-states are coupled.
(The fetch provenance hypothesis pins the word to `d`'s ROM, so the
decoded opcode is one the relational sweep covers.) -/
theorem retire_step_lockstep (m₁ m₂ : Manifest) (d : DomainId)
    (σ₁ σ₂ : MachineState)
    (hm₁ : m₁.WF) (hm₂ : m₂.WF)
    (hiso₁ : Isolated m₁ d) (hiso₂ : Isolated m₂ d)
    (hag : AgreeOn m₁ m₂ d)
    (hins₁ : Insulated m₁ d σ₁) (hins₂ : Insulated m₂ d σ₂)
    (hcpl : Coupled m₁ d σ₁ σ₂)
    (w : Loom.Word32) (c₁ c₂ : Nat) (hc₁ : c₁ ≤ 1) (hc₂ : c₂ ≤ 1)
    (hf₁ : σ₁.inflight = some ⟨d, w, c₁⟩) (hf₂ : σ₂.inflight = some ⟨d, w, c₂⟩)
    (hfetch : fetch σ₁ d = some w) :
    Coupled m₁ d (step m₁ σ₁) (step m₂ σ₂) := by
  have hdom : m₁.doms d = m₂.doms d := hag.1
  have hctx₁ := dctx_of_insulated hiso₁ hins₁
  have hctxρ₁ := dctx_refill (m := m₁) hctx₁
  have hctx₂ := dctx_of_insulated hiso₂ hins₂
  have hctxρ₂ := dctx_refill (m := m₂) hctx₂
  have hexecA : ExecPreservesWfA :=
    execPreservesWfA_of_system Machines.Lnp64u.Isa.Wip.system_preserves_wfa
  have hwfρ₁ : Wf (refillPhase m₁ σ₁) := refillPhase_preserves_wf m₁ σ₁ hins₁.wf
  have hwfρ₂ : Wf (refillPhase m₂ σ₂) := refillPhase_preserves_wf m₂ σ₂ hins₂.wf
  have hwfκ₁ : Wf (corePhase m₁ (refillPhase m₁ σ₁)) :=
    (corePhase_preserves_wfa hexecA m₁ hm₁ _ hwfρ₁ (acyclic_refillPhase m₁ σ₁ hins₁.acyclic)).1
  have hwfκ₂ : Wf (corePhase m₂ (refillPhase m₂ σ₂)) :=
    (corePhase_preserves_wfa hexecA m₂ hm₂ _ hwfρ₂ (acyclic_refillPhase m₂ σ₂ hins₂.acyclic)).1
  -- 1. both cores retire the latched word
  have hρinf₁ : (refillPhase m₁ σ₁).inflight = some ⟨d, w, c₁⟩ := by
    rw [refillPhase_inflight]; exact hf₁
  have hρinf₂ : (refillPhase m₂ σ₂).inflight = some ⟨d, w, c₂⟩ := by
    rw [refillPhase_inflight]; exact hf₂
  have hcore₁ : corePhase m₁ (refillPhase m₁ σ₁)
      = retire { refillPhase m₁ σ₁ with inflight := none } d w := by
    unfold corePhase
    simp only [hρinf₁]
    rw [if_pos hc₁]
  have hcore₂ : corePhase m₂ (refillPhase m₂ σ₂)
      = retire { refillPhase m₂ σ₂ with inflight := none } d w := by
    unfold corePhase
    simp only [hρinf₂]
    rw [if_pos hc₂]
  -- 2. the ROM pins the opcode
  obtain ⟨hux, hwrom⟩ := fetch_of_insulated hins₁ hfetch
  have hop : ∀ instr, Loom.Isa.decode isa w = some instr →
      instr.opcode ≠ 17 ∧ instr.opcode ≠ 18 ∧ instr.opcode ≠ 19 ∧
      instr.opcode ≠ 24 := by
    intro instr hdec
    refine hiso₁.code_local _ hux.underRoots instr ?_
    rw [← hwrom]
    exact hdec
  -- 3. the relational coupling at the pre-retire states
  have hrcρ : DRel.RC d (UnderRoots m₁ d)
      { refillPhase m₁ σ₁ with inflight := none }
      { refillPhase m₂ σ₂ with inflight := none } := by
    have hcaps12 : ((refillPhase m₁ σ₁).doms d).caps
        = ((refillPhase m₂ σ₂).doms d).caps := by
      rw [refillPhase_caps, refillPhase_caps]
      exact (Insulated.caps_eq hins₁ hins₂ hdom).1
    have hgen12 : ((refillPhase m₁ σ₁).doms d).slotGen
        = ((refillPhase m₂ σ₂).doms d).slotGen := by
      rw [refillPhase_slotGen, refillPhase_slotGen]
      exact (Insulated.caps_eq hins₁ hins₂ hdom).2.1
    exact
      { regs := by rw [refillPhase_regs, refillPhase_regs]; exact hcpl.regs
        pc := by rw [refillPhase_pc, refillPhase_pc]; exact hcpl.pc
        run := by rw [refillPhase_run, refillPhase_run]; exact hcpl.run
        cause := by rw [refillPhase_cause, refillPhase_cause]; exact hcpl.cause
        regions := by rw [refillPhase_regions, refillPhase_regions]; exact hcpl.regions
        caps := hcaps12
        gen := hgen12
        serv1 := hctxρ₁.dserv
        serv2 := hctxρ₂.dserv
        full1 := hctxρ₁.dfull
        nog1 := hctxρ₁.dgates
        capsR := by
          intro s e b l p hc hk a h1 h2
          have hcσ : (σ₁.doms d).caps s = some e := by
            rw [← refillPhase_caps m₁ σ₁ d]
            exact hc
          have hboot := congrFun hins₁.boot_caps s
          rw [hcσ] at hboot
          cases hi : (m₁.doms d).initCaps s with
          | none => rw [hi] at hboot; cases hboot
          | some k =>
              rw [hi] at hboot
              injection hboot with hboot
              have hkk : k = .mem b l p := by
                have := congrArg CapEntry.kind hboot
                simp only [hk] at this
                exact this.symm
              exact ⟨s, b, l, p, hkk ▸ hi, h1, h2⟩
        memR := fun a ha => by
          show (refillPhase m₁ σ₁).mem a = (refillPhase m₂ σ₂).mem a
          rw [congrFun (refillPhase_frame m₁ σ₁).1 a,
            congrFun (refillPhase_frame m₂ σ₂).1 a]
          exact hcpl.mem a ha
        covR := fun a need hcov => by
          have hcov' : σ₁.domCovers d a need = true := by
            rw [← refillPhase_covers m₁ σ₁ d a need]
            exact hcov
          exact (domCovers_underRoots hins₁ hcov').1 }
  have hrcκ : DRel.RC d (UnderRoots m₁ d) (corePhase m₁ (refillPhase m₁ σ₁))
      (corePhase m₂ (refillPhase m₂ σ₂)) := by
    rw [hcore₁, hcore₂]
    exact DRel.retire_rel _ _ w hrcρ hop
  -- 4. the self-frame gives the mover-phase facts on each side
  have hDS₁ : DFrame.DSelf d (UnderXRoots m₁ d) { refillPhase m₁ σ₁ with inflight := none }
      (corePhase m₁ (refillPhase m₁ σ₁)) := by
    rw [hcore₁]
    refine DFrame.retire_dself _ w hctxρ₁.dfull hctxρ₁.dgates hctxρ₁.dserv ?_ hop
    intro a hcov
    refine covers_w_not_underXRoots hiso₁ hins₁ a ?_
    rw [← refillPhase_covers m₁ σ₁ d a]
    exact hcov
  have hDS₂ : DFrame.DSelf d (UnderXRoots m₂ d) { refillPhase m₂ σ₂ with inflight := none }
      (corePhase m₂ (refillPhase m₂ σ₂)) := by
    rw [hcore₂]
    refine DFrame.retire_dself _ w hctxρ₂.dfull hctxρ₂.dgates hctxρ₂.dserv ?_ hop
    intro a hcov
    refine covers_w_not_underXRoots hiso₂ hins₂ a ?_
    rw [← refillPhase_covers m₂ σ₂ d a]
    exact hcov
  -- 5. mover-phase memory frames
  have hmemS : ∀ (m : Manifest) (σ : MachineState)
      (hctxρ : DFrame.DCtx d (UnderRoots m d) (refillPhase m σ))
      (hins : Insulated m d σ)
      (hDS : DFrame.DSelf d (UnderXRoots m d) { refillPhase m σ with inflight := none }
        (corePhase m (refillPhase m σ)))
      (hwfκ : Wf (corePhase m (refillPhase m σ))),
      ∀ a, UnderRoots m d a →
        (step m σ).mem a = (corePhase m (refillPhase m σ)).mem a := by
    intro m σ hctxρ hins hDS hwfκ a ha
    refine moverPhase_mem_frame hwfκ.region_backed ?_ ?_ ?_
      (fun job hj => (hwfκ.mover_wf job hj).2.1) a ha
    · intro e r rg h
      by_cases he : e = d
      · subst he
        rcases hDS.regsown r rg h with h' | h'
        · exact h'
        · exact hctxρ.ro e r rg h'
      · rw [show ((corePhase m (refillPhase m σ)).doms e = (refillPhase m σ).doms e)
          from hDS.odoms e he] at h
        exact hctxρ.ro e r rg h
    · intro e he s entry b l p hc hk
      rw [show ((corePhase m (refillPhase m σ)).doms e = (refillPhase m σ).doms e)
        from hDS.odoms e he] at hc
      exact hctxρ.fo e he s entry b l p hc hk
    · intro job hj
      exact hctxρ.movOff job (hDS.mover job hj)
  have hmem₁ := hmemS m₁ σ₁ hctxρ₁ hins₁ hDS₁ hwfκ₁
  have hmem₂ := hmemS m₂ σ₂ hctxρ₂ hins₂ hDS₂ hwfκ₂
  -- 6. assemble the post coupling
  exact
    { regs := by
        rw [congrFun (step_doms m₁ σ₁) d, congrFun (step_doms m₂ σ₂) d]
        exact hrcκ.regs
      pc := by
        rw [congrFun (step_doms m₁ σ₁) d, congrFun (step_doms m₂ σ₂) d]
        exact hrcκ.pc
      run := by
        rw [congrFun (step_doms m₁ σ₁) d, congrFun (step_doms m₂ σ₂) d]
        exact hrcκ.run
      cause := by
        rw [congrFun (step_doms m₁ σ₁) d, congrFun (step_doms m₂ σ₂) d]
        exact hrcκ.cause
      regions := by
        rw [congrFun (step_doms m₁ σ₁) d, congrFun (step_doms m₂ σ₂) d]
        exact hrcκ.regions
      mem := fun a ha => by
        rw [hmem₁ a ha, hmem₂ a ((underRoots_congr hdom a).mp ha)]
        exact hrcκ.memR a ha }


/-! ## Engine 4 support: the frozen-quiet walk -/

/-- The full frame of a stalled issue instant for `d`: the core stalls, so
the whole cycle is refill + Mover only. -/
private theorem stall_step (m : Manifest) (d : DomainId) (σ : MachineState)
    (hm : m.WF) (hiso : Isolated m d) (hins : Insulated m d σ)
    (hinf : σ.inflight = none)
    (hsched : schedule m (refillPhase m σ) = some d)
    (w : Loom.Word32) (instr : Loom.Isa.InstrDecl sig Semantics WcetClass)
    (hf : fetch σ d = some w) (hd : Loom.Isa.decode isa w = some instr)
    (hbud : ¬ instr.cost.cost ≤ ((refillPhase m σ).doms d).budget) :
    DFrozen m d σ (step m σ) ∧
    (step m σ).doms d = (refillPhase m σ).doms d ∧
    (step m σ).inflight = none := by
  have hctx := dctx_of_insulated hiso hins
  have hctxρ : DFrame.DCtx d (UnderRoots m d) (refillPhase m σ) := dctx_refill hctx
  have hwfρ : Wf (refillPhase m σ) := refillPhase_preserves_wf m σ hins.wf
  have hρinf : (refillPhase m σ).inflight = none := by
    rw [refillPhase_inflight]; exact hinf
  have hservρ : ((refillPhase m σ).doms d).serving = none := hctxρ.dserv
  have hpay : (refillPhase m σ).payer d = d := payer_eq_self _ d hservρ
  have hfρ : fetch (refillPhase m σ) d = some w := by
    rw [refillPhase_fetch]; exact hf
  have hcore : corePhase m (refillPhase m σ) = refillPhase m σ :=
    corePhase_stall m _ d w instr hρinf hsched hfρ hd (by rw [hpay]; exact hbud)
  have hdd : (step m σ).doms d = (refillPhase m σ).doms d := by
    rw [step_doms, hcore]
  have hmem : ∀ a, UnderRoots m d a → (step m σ).mem a = σ.mem a := by
    intro a ha
    have h1 : (step m σ).mem a = (moverPhase (corePhase m (refillPhase m σ))).mem a := rfl
    rw [h1, hcore,
      moverPhase_mem_frame hwfρ.region_backed hctxρ.ro hctxρ.fo hctxρ.movOff
        (fun job hj => (hwfρ.mover_wf job hj).2.1) a ha]
    exact congrFun (refillPhase_frame m σ).1 a
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem⟩, hdd, ?_⟩
  · rw [hdd, refillPhase_regs]
  · rw [hdd, refillPhase_pc]
  · rw [hdd, refillPhase_run]
  · rw [hdd, refillPhase_cause]
  · rw [hdd, refillPhase_serving]
  · rw [hdd, refillPhase_caps]
  · rw [hdd, refillPhase_slotGen]
  · rw [hdd, refillPhase_lineage]
  · rw [hdd, refillPhase_regions]
  · show (moverPhase (corePhase m (refillPhase m σ))).inflight = none
    rw [moverPhase_inflight, hcore]
    exact hρinf

/-- Refill only ever tops the budget up to `Q`. -/
private theorem refill_budget_ge (m : Manifest) (σ : MachineState) (d : DomainId)
    (c : Nat) (hb : c ≤ (σ.doms d).budget) (hcQ : c ≤ (m.doms d).budgetQ) :
    c ≤ ((refillPhase m σ).doms d).budget := by
  rcases refillPhase_doms m σ d with h | h <;> rw [h]
  · exact hb
  · exact hcQ

/-- One step of the catch-up walk: a cycle that is not a funded issue
instant for `d` keeps `d` frozen and quiescent (and only refill touches
`d`'s budget). -/
private theorem progress_extend (m : Manifest) (d : DomainId) (τ : MachineState)
    (hm : m.WF) (hiso : Isolated m d) (hins : Insulated m d τ) (hq : Quiet d τ)
    (c : Nat) (hc0 : 0 < c)
    (hcost : c = 1 ∨ ∃ w instr, fetch τ d = some w ∧
      Loom.Isa.decode isa w = some instr ∧ instr.cost.cost = c)
    (hnotdone : ¬ (τ.inflight = none ∧ schedule m (refillPhase m τ) = some d ∧
        c ≤ ((refillPhase m τ).doms d).budget)) :
    DFrozen m d τ (step m τ) ∧ (step m τ).doms d = (refillPhase m τ).doms d ∧
    Quiet d (step m τ) := by
  rcases hinfτ : τ.inflight with _ | fl
  · by_cases hsd : schedule m (refillPhase m τ) = some d
    · -- an unfunded issue instant: the machine stalls
      have hbud : ¬ c ≤ ((refillPhase m τ).doms d).budget := by
        intro hc
        exact hnotdone ⟨hinfτ, hsd, hc⟩
      rcases hcost with hc1 | ⟨w, instr, hf, hd, hcc⟩
      · -- c = 1: schedulability already implies a positive budget
        exfalso
        subst hc1
        have helig := schedule_eligible m (refillPhase m τ) d hsd
        obtain ⟨-, hbpos⟩ := helig
        have hpay : (refillPhase m τ).payer d = d :=
          payer_eq_self _ d (by rw [refillPhase_serving]; exact hins.serving_none)
        rw [hpay] at hbpos
        exact hbud hbpos
      · obtain ⟨hfz, hdd, hinf'⟩ := stall_step m d τ hm hiso hins hinfτ hsd w instr hf hd
          (by rw [hcc]; exact hbud)
        exact ⟨hfz, hdd, fun fl' hfl' => by rw [hinf'] at hfl'; cases hfl'⟩
    · obtain ⟨hfz, hdd⟩ := frame_step_full m d τ hm hiso hins
        (fun fl' hfl' _ => by rw [hinfτ] at hfl'; cases hfl')
        (fun _ => hsd)
      refine ⟨hfz, hdd, ?_⟩
      exact step_quiet m d τ hq
        (fun _ => hsd)
  · have hfld : fl.dom ≠ d := hq fl hinfτ
    obtain ⟨hfz, hdd⟩ := frame_step_full m d τ hm hiso hins
      (fun fl' hfl' hfd' => by
        rw [hinfτ] at hfl'
        injection hfl' with hfl'
        rw [← hfl'] at hfd'
        exact absurd hfd' hfld)
      (fun h => by rw [hinfτ] at h; cases h)
    refine ⟨hfz, hdd, ?_⟩
    refine step_quiet m d τ hq ?_
    intro h
    rw [hinfτ] at h
    cases h

/-- **Engine 4: progress.** From a quiescent insulated state with `d`
running, some cycle `j` later the machine is at an issue instant for `d`
with any required budget `c ≤ budgetQ` available, and `d`'s slice was
frozen (and quiescent) throughout the wait.

The `hcost` hypothesis is proof-forced (2026-07-03): without it the
statement is *false* for a `c` exceeding the cost of the instruction `d`
actually fetches — at the first idle instant with `0 < budget < c` the
machine would *issue* `d`'s (cheaper) instruction rather than stall, so no
`d`-frozen window reaches a `c`-funded instant. The consumers use exactly
the two sound instantiations: `c = 1` (the halting catch-up — eligibility
alone) and `c` = the cost of the word `d`'s frozen fetch yields (the
retirement catch-up), under which every underfunded idle instant provably
stalls. -/
theorem progress (m : Manifest) (d : DomainId) (σ : MachineState)
    (hm : m.WF) (hpri : TopPriority m d) (hiso : Isolated m d)
    (hins : Insulated m d σ) (hq : Quiet d σ)
    (hrun : (σ.doms d).run = .running)
    (c : Nat) (hc0 : 0 < c) (hcQ : c ≤ (m.doms d).budgetQ)
    (hcost : c = 1 ∨ ∃ w instr, fetch σ d = some w ∧
      Loom.Isa.decode isa w = some instr ∧ instr.cost.cost = c) :
    ∃ j, (∀ i, i ≤ j → DFrozen m d σ (stepN m i σ) ∧ Quiet d (stepN m i σ)) ∧
      (stepN m j σ).inflight = none ∧
      schedule m (refillPhase m (stepN m j σ)) = some d ∧
      c ≤ ((refillPhase m (stepN m j σ)).doms d).budget := by
  -- vocabulary
  set W : Nat → Prop := fun n => ∀ i, i ≤ n →
    DFrozen m d σ (stepN m i σ) ∧ Quiet d (stepN m i σ) with hW
  set D : Nat → Prop := fun j => (stepN m j σ).inflight = none ∧
    schedule m (refillPhase m (stepN m j σ)) = some d ∧
    c ≤ ((refillPhase m (stepN m j σ)).doms d).budget with hD
  suffices h : ∃ j, W j ∧ D j by
    obtain ⟨j, hw, hd⟩ := h
    exact ⟨j, hw, hd.1, hd.2.1, hd.2.2⟩
  have hinsN : ∀ n, Insulated m d (stepN m n σ) :=
    fun n => insulated_stepN m d hm hiso n σ hins
  have hcostN : ∀ n, W n → (c = 1 ∨ ∃ w instr, fetch (stepN m n σ) d = some w ∧
      Loom.Isa.decode isa w = some instr ∧ instr.cost.cost = c) := by
    intro n hw
    rcases hcost with h1 | ⟨w, instr, hf, hd, hcc⟩
    · exact Or.inl h1
    · refine Or.inr ⟨w, instr, ?_, hd, hcc⟩
      rw [fetch_frozen hins (hw n (Nat.le_refl n)).1]
      exact hf
  -- one-step extension of a not-yet-done window
  have extend : ∀ n, W n → ¬ D n → W (n + 1) ∧
      ((stepN m (n + 1) σ).doms d = (refillPhase m (stepN m n σ)).doms d) := by
    intro n hw hnd
    obtain ⟨hfz, hdd, hq'⟩ := progress_extend m d (stepN m n σ) hm hiso (hinsN n)
      (hw n (Nat.le_refl n)).2 c hc0 (hcostN n hw) hnd
    have hsucc : stepN m (n + 1) σ = step m (stepN m n σ) :=
      Machines.Lnp64u.Wip.stepN_succ m n σ
    refine ⟨?_, by rw [hsucc]; exact hdd⟩
    intro i hi
    by_cases hin : i ≤ n
    · exact hw i hin
    · have : i = n + 1 := by omega
      subst this
      rw [hsucc]
      exact ⟨(hw n (Nat.le_refl n)).1.trans hfz, hq'⟩
  -- an idle instant with a funded refilled budget is done
  have done_of_idle : ∀ j, W j → c ≤ ((refillPhase m (stepN m j σ)).doms d).budget →
      (stepN m j σ).inflight = none → D j := by
    intro j hw hb hidle
    refine ⟨hidle, ?_, hb⟩
    refine schedule_top m d hpri _ ?_ ?_
    · rw [refillPhase_run, (hw j (Nat.le_refl j)).1.run]
      exact hrun
    · have hpay : (refillPhase m (stepN m j σ)).payer d = d := by
        refine payer_eq_self _ d ?_
        rw [refillPhase_serving]
        exact (hinsN j).serving_none
      rw [hpay]
      omega
  -- the budget floor propagates across not-done steps
  have floor_step : ∀ n, W n → ¬ D n →
      c ≤ ((refillPhase m (stepN m n σ)).doms d).budget →
      c ≤ ((refillPhase m (stepN m (n + 1) σ)).doms d).budget := by
    intro n hw hnd hb
    obtain ⟨-, hdd⟩ := extend n hw hnd
    refine refill_budget_ge m _ d c ?_ hcQ
    rw [hdd]
    exact hb
  -- stage 2: drain the in-flight instruction after the refill instant
  have drain : ∀ (t : Nat) (n : Nat), W n →
      c ≤ ((refillPhase m (stepN m n σ)).doms d).budget →
      (∀ fl, (stepN m n σ).inflight = some fl → fl.cyclesLeft ≤ t) →
      ∃ j, W j ∧ D j := by
    intro t
    induction t with
    | zero =>
        intro n hw hb hbound
        rcases hinfn : (stepN m n σ).inflight with _ | fl
        · exact ⟨n, hw, done_of_idle n hw hb hinfn⟩
        · -- cyclesLeft ≤ 0 retires this cycle
          have hnd : ¬ D n := by
            intro hdn
            rw [hdn.1] at hinfn
            cases hinfn
          obtain ⟨hw', hdd⟩ := extend n hw hnd
          have hb' := floor_step n hw hnd hb
          have hretire : (step m (stepN m n σ)).inflight = none :=
            Machines.Lnp64u.Wip.step_inflight_retire m _ fl hinfn
              (Nat.le_trans (hbound fl hinfn) (Nat.zero_le 1))
          have hidle : (stepN m (n + 1) σ).inflight = none := by
            rw [Machines.Lnp64u.Wip.stepN_succ]
            exact hretire
          exact ⟨n + 1, hw', done_of_idle (n + 1) hw' hb' hidle⟩
    | succ t ih =>
        intro n hw hb hbound
        rcases hinfn : (stepN m n σ).inflight with _ | fl
        · exact ⟨n, hw, done_of_idle n hw hb hinfn⟩
        · have hnd : ¬ D n := by
            intro hdn
            rw [hdn.1] at hinfn
            cases hinfn
          obtain ⟨hw', hdd⟩ := extend n hw hnd
          have hb' := floor_step n hw hnd hb
          by_cases hcl : fl.cyclesLeft ≤ 1
          · have hidle : (stepN m (n + 1) σ).inflight = none := by
              rw [Machines.Lnp64u.Wip.stepN_succ]
              exact Machines.Lnp64u.Wip.step_inflight_retire m _ fl hinfn hcl
            exact ⟨n + 1, hw', done_of_idle (n + 1) hw' hb' hidle⟩
          · have hcount : (stepN m (n + 1) σ).inflight =
                some { fl with cyclesLeft := fl.cyclesLeft - 1 } := by
              rw [Machines.Lnp64u.Wip.stepN_succ]
              exact Machines.Lnp64u.Wip.step_inflight_countdown m _ fl hinfn (by omega)
            refine ih (n + 1) hw' hb' ?_
            intro fl' hfl'
            rw [hcount] at hfl'
            injection hfl' with hfl'
            rw [← hfl']
            have := hbound fl hinfn
            show fl.cyclesLeft - 1 ≤ t
            omega
  -- stage 1: reach the refill instant (or finish early)
  obtain ⟨k, hkle, hbQ⟩ := refill_within_period m hm σ d
  have stage1 : ∀ n, (∃ j, W j ∧ D j) ∨ W n := by
    intro n
    induction n with
    | zero =>
        refine Or.inr ?_
        intro i hi
        have : i = 0 := Nat.le_zero.mp hi
        subst this
        exact ⟨DFrozen.refl m d σ, hq⟩
    | succ n ih =>
        rcases ih with hdone | hw
        · exact Or.inl hdone
        · by_cases hdn : D n
          · exact Or.inl ⟨n, hw, hdn⟩
          · exact Or.inr (extend n hw hdn).1
  rcases stage1 k with hdone | hwk
  · exact hdone
  · have hbk : c ≤ ((refillPhase m (stepN m k σ)).doms d).budget := by
      rw [hbQ]
      exact hcQ
    rcases hinfk : (stepN m k σ).inflight with _ | fl
    · exact ⟨k, hwk, done_of_idle k hwk hbk hinfk⟩
    · exact drain fl.cyclesLeft k hwk hbk
        (fun fl' hfl' => by
          rw [hinfk] at hfl'
          injection hfl' with hfl'
          rw [← hfl'])


private theorem haltBase_cause' (σ : MachineState) (d : DomainId) (c : Loom.Word32)
    (d' : DomainId) :
    ((σ.haltBase d c).doms d').cause = if d' = d then c else (σ.doms d').cause := by
  unfold MachineState.haltBase MachineState.setDom
  by_cases hd : d' = d
  · subst hd; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd, hd]

/-- **The issue-cycle case split** for `d` at an idle core: fetch fault,
decode fault, stall, or latch — with the d-slice frame in every case. -/
theorem issue_step (m : Manifest) (d : DomainId) (σ : MachineState)
    (hm : m.WF) (hiso : Isolated m d) (hins : Insulated m d σ)
    (hinf : σ.inflight = none)
    (hsched : schedule m (refillPhase m σ) = some d) :
    (fetch σ d = none ∧ DHalt m d σ (step m σ) Fault.memoryAuthority) ∨
    (∃ w, fetch σ d = some w ∧ Loom.Isa.decode isa w = none ∧
       DHalt m d σ (step m σ) Fault.illegalInstruction) ∨
    (∃ w instr, fetch σ d = some w ∧ Loom.Isa.decode isa w = some instr ∧
       ((refillPhase m σ).doms d).budget < instr.cost.cost ∧
       DFrozen m d σ (step m σ) ∧ (step m σ).inflight = none) ∨
    (∃ w instr, fetch σ d = some w ∧ Loom.Isa.decode isa w = some instr ∧
       instr.cost.cost ≤ ((refillPhase m σ).doms d).budget ∧
       DFrozen m d σ (step m σ) ∧
       (step m σ).inflight = some ⟨d, w, instr.cost.cost⟩) := by
  have hwfρ : Wf (refillPhase m σ) := refillPhase_preserves_wf m σ hins.wf
  set ρ := refillPhase m σ with hρdef
  have hρinf : ρ.inflight = none := by
    rw [hρdef, refillPhase_inflight]; exact hinf
  have hservρ : (ρ.doms d).serving = none := by
    rw [hρdef, refillPhase_serving]; exact hins.serving_none
  have hfρ : fetch ρ d = fetch σ d := by rw [hρdef]; exact refillPhase_fetch m σ d
  have hrunρ : (ρ.doms d).run = .running := schedule_running m ρ d hsched
  have hroρ : ∀ e r rg, (ρ.doms e).regions r = some rg → rg.backing.dom = e := by
    intro e r rg hrg
    rw [hρdef, refillPhase_regions] at hrg
    exact hins.regions_own e r rg hrg
  have hfoρ : ∀ e, e ≠ d → ∀ s entry b l p, (ρ.doms e).caps s = some entry →
      entry.kind = .mem b l p → ∀ a : Addr, b.toNat ≤ a.toNat →
      a.toNat < b.toNat + l.toNat → ¬ UnderRoots m d a := by
    intro e hne s entry b l p hcap hk a h1 h2
    rw [hρdef, refillPhase_caps] at hcap
    exact hins.foreign_off e hne s entry b l p hcap hk a h1 h2
  have hmfρ : ∀ job, ρ.mover = some job → job.owner ≠ d := by
    intro job hj
    rw [hρdef, refillPhase_mover] at hj
    exact hins.mover_foreign job hj
  have hmwρ : ∀ job, ρ.mover = some job → job.dst.dom = job.owner := by
    intro job hj; exact (hwfρ.mover_wf job hj).2.1
  have hmemρ : ∀ a, ρ.mem a = σ.mem a := by
    intro a; rw [hρdef]; exact congrFun (refillPhase_frame m σ).1 a
  -- the fault-halt package: `corePhase` halted `d` at issue
  have halt_pack : ∀ f : Fault, corePhase m ρ = haltWith ρ d f →
      DHalt m d σ (step m σ) f := by
    intro f hcore
    have hbase : corePhase m ρ = ρ.haltBase d (BitVec.ofNat 32 f.code) := by
      rw [hcore]
      show ρ.haltDom d (BitVec.ofNat 32 f.code) = _
      exact haltDom_base ρ d _ hservρ
    set τ := ρ.haltBase d (BitVec.ofNat 32 f.code) with hτdef
    have hwfτ : Wf τ := haltBase_preserves_wf ρ d _ hwfρ hrunρ hservρ hρinf
    have hdoms : (step m σ).doms = τ.doms := by
      rw [step_doms, ← hρdef, hbase]
    have hdomsd : (step m σ).doms d = τ.doms d := congrFun hdoms d
    have hmem : ∀ a, UnderRoots m d a → (step m σ).mem a = σ.mem a := by
      intro a ha
      have h1 : (step m σ).mem a = (moverPhase τ).mem a := by
        show (moverPhase (corePhase m (refillPhase m σ))).mem a = _
        rw [← hρdef, hbase]
      rw [h1]
      have h2 : (moverPhase τ).mem a = τ.mem a := by
        refine moverPhase_mem_frame ?_ ?_ ?_ ?_ ?_ a ha
        · exact hwfτ.region_backed
        · intro e r rg hrg
          rw [hτdef, haltBase_regions] at hrg
          exact hroρ e r rg hrg
        · intro e hne s entry b l p hcap hk a' h1' h2'
          rw [hτdef, haltBase_caps] at hcap
          exact hfoρ e hne s entry b l p hcap hk a' h1' h2'
        · intro job hj
          rw [hτdef, haltBase_mover] at hj
          exact hmfρ job hj
        · intro job hj
          rw [hτdef, haltBase_mover] at hj
          exact hmwρ job hj
      rw [h2]
      have h3 : τ.mem a = ρ.mem a := by rw [hτdef]; rfl
      rw [h3, hmemρ a]
    have hinfS : (step m σ).inflight = none := by
      show (moverPhase (corePhase m (refillPhase m σ))).inflight = none
      rw [moverPhase_inflight, ← hρdef, hbase, hτdef, haltBase_inflight]
      exact hρinf
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem, hinfS⟩
    · rw [hdomsd, hτdef, haltBase_regs, hρdef, refillPhase_regs]
    · rw [hdomsd, hτdef, haltBase_pc, hρdef, refillPhase_pc]
    · rw [hdomsd, hτdef, haltBase_run, if_pos rfl]
    · rw [hdomsd, hτdef, haltBase_cause', if_pos rfl]
    · rw [hdomsd, hτdef, haltBase_serving, if_pos rfl]
    · rw [hdomsd, hτdef, haltBase_caps, hρdef, refillPhase_caps]
    · rw [hdomsd, hτdef, haltBase_slotGen, hρdef, refillPhase_slotGen]
    · rw [hdomsd, hτdef, haltBase_lineage, hρdef, refillPhase_lineage]
    · rw [hdomsd, hτdef, haltBase_regions, hρdef, refillPhase_regions]
  cases hf : fetch σ d with
  | none =>
      refine Or.inl ⟨rfl, halt_pack .memoryAuthority ?_⟩
      have hfρ' : fetch ρ d = none := by rw [hfρ]; exact hf
      unfold corePhase
      simp only [hρinf, hsched, hfρ']
  | some w =>
      have hfρ' : fetch ρ d = some w := by rw [hfρ]; exact hf
      cases hd : Loom.Isa.decode isa w with
      | none =>
          refine Or.inr (Or.inl ⟨w, rfl, hd, halt_pack .illegalInstruction ?_⟩)
          unfold corePhase
          simp only [hρinf, hsched, hfρ', hd]
      | some instr =>
          have hpay : ρ.payer d = d := payer_eq_self ρ d hservρ
          by_cases hbud : instr.cost.cost ≤ (ρ.doms d).budget
          · -- latch
            have hbud' : instr.cost.cost ≤ (ρ.doms (ρ.payer d)).budget := by
              rw [hpay]; exact hbud
            have hcore : corePhase m ρ =
                { ρ.setDom (ρ.payer d)
                    (fun ds => { ds with budget := ds.budget - instr.cost.cost })
                  with inflight := some ⟨d, w, instr.cost.cost⟩ } := by
              unfold corePhase
              simp only [hρinf, hsched, hfρ', hd, hservρ]
              rw [if_pos hbud']
            rw [hpay] at hcore
            set σL := ρ.setDom d
              (fun ds => { ds with budget := ds.budget - instr.cost.cost }) with hσL
            obtain ⟨hLcaps, hLlin, hLgen, hLreg, hLrun, hLserv, hLgates, hLmover⟩ :=
              setBudget_proj ρ d (fun ds => ds.budget - instr.cost.cost)
            have hLall : ∀ e, ((σL.doms e).regs = (ρ.doms e).regs) ∧
                ((σL.doms e).pc = (ρ.doms e).pc) ∧
                ((σL.doms e).cause = (ρ.doms e).cause) := by
              intro e
              rw [hσL]
              unfold MachineState.setDom
              by_cases he : e = d
              · subst he; simp [Loom.Fun.update_same]
              · simp [Loom.Fun.update_ne _ _ _ _ he]
            have hLlive : ∀ e s g, ((σL.doms e).liveCap s g) = ((ρ.doms e).liveCap s g) := by
              intro e s g
              unfold DomainState.liveCap
              rw [hLcaps, hLgen]
            have hdoms : (step m σ).doms = σL.doms := by
              rw [step_doms, ← hρdef, hcore]
            have hdomsd : (step m σ).doms d = σL.doms d := congrFun hdoms d
            have hmem : ∀ a, UnderRoots m d a → (step m σ).mem a = σ.mem a := by
              intro a ha
              have h1 : (step m σ).mem a =
                  (moverPhase ({ σL with inflight := some ⟨d, w, instr.cost.cost⟩ }
                    : MachineState)).mem a := by
                show (moverPhase (corePhase m (refillPhase m σ))).mem a = _
                rw [← hρdef, hcore]
              rw [h1]
              have h2 : (moverPhase ({ σL with inflight := some ⟨d, w, instr.cost.cost⟩ }
                  : MachineState)).mem a = σL.mem a := by
                refine moverPhase_mem_frame ?_ ?_ ?_ ?_ ?_ a ha
                · intro e r rg hrg
                  have hrg' : (σL.doms e).regions r = some rg := hrg
                  rw [hLreg] at hrg'
                  obtain ⟨entry, hlive, hle⟩ := hwfρ.region_backed e r rg hrg'
                  refine ⟨entry, ?_, hle⟩
                  show (σL.doms rg.backing.dom).liveCap rg.backing.slot rg.backing.gen
                    = some entry
                  rw [hLlive]
                  exact hlive
                · intro e r rg hrg
                  have hrg' : (σL.doms e).regions r = some rg := hrg
                  rw [hLreg] at hrg'
                  exact hroρ e r rg hrg'
                · intro e hne s entry b l p hcap hk a' h1' h2'
                  have hcap' : (σL.doms e).caps s = some entry := hcap
                  rw [hLcaps] at hcap'
                  exact hfoρ e hne s entry b l p hcap' hk a' h1' h2'
                · intro job hj
                  have hj' : σL.mover = some job := hj
                  rw [hLmover] at hj'
                  exact hmfρ job hj'
                · intro job hj
                  have hj' : σL.mover = some job := hj
                  rw [hLmover] at hj'
                  exact hmwρ job hj'
              rw [h2]
              have h3 : σL.mem a = ρ.mem a := by rw [hσL]; rfl
              rw [h3, hmemρ a]
            have hinfS : (step m σ).inflight = some ⟨d, w, instr.cost.cost⟩ := by
              show (moverPhase (corePhase m (refillPhase m σ))).inflight = _
              rw [moverPhase_inflight, ← hρdef, hcore]
            refine Or.inr (Or.inr (Or.inr ⟨w, instr, rfl, hd, hbud, ?_, hinfS⟩))
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem⟩
            · rw [hdomsd, (hLall d).1, hρdef, refillPhase_regs]
            · rw [hdomsd, (hLall d).2.1, hρdef, refillPhase_pc]
            · rw [hdomsd, hLrun d, hρdef, refillPhase_run]
            · rw [hdomsd, (hLall d).2.2, hρdef, refillPhase_cause]
            · rw [hdomsd, hLserv d, hρdef, refillPhase_serving]
            · rw [hdomsd, hLcaps d, hρdef, refillPhase_caps]
            · rw [hdomsd, hLgen d, hρdef, refillPhase_slotGen]
            · rw [hdomsd, hLlin d, hρdef, refillPhase_lineage]
            · rw [hdomsd, hLreg d, hρdef, refillPhase_regions]
          · -- stall
            have hcore : corePhase m ρ = ρ :=
              corePhase_stall m ρ d w instr hρinf hsched hfρ' hd
                (by rw [hpay]; exact hbud)
            have hdoms : (step m σ).doms = ρ.doms := by
              rw [step_doms, ← hρdef, hcore]
            have hdomsd : (step m σ).doms d = ρ.doms d := congrFun hdoms d
            have hmem : ∀ a, UnderRoots m d a → (step m σ).mem a = σ.mem a := by
              intro a ha
              have h1 : (step m σ).mem a = (moverPhase ρ).mem a := by
                show (moverPhase (corePhase m (refillPhase m σ))).mem a = _
                rw [← hρdef, hcore]
              rw [h1, moverPhase_mem_frame hwfρ.region_backed hroρ hfoρ hmfρ hmwρ a ha,
                hmemρ a]
            have hinfS : (step m σ).inflight = none := by
              show (moverPhase (corePhase m (refillPhase m σ))).inflight = none
              rw [moverPhase_inflight, ← hρdef, hcore]
              exact hρinf
            refine Or.inr (Or.inr (Or.inl ⟨w, instr, rfl, hd, Nat.lt_of_not_le hbud,
              ?_, hinfS⟩))
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem⟩
            · rw [hdomsd, hρdef, refillPhase_regs]
            · rw [hdomsd, hρdef, refillPhase_pc]
            · rw [hdomsd, hρdef, refillPhase_run]
            · rw [hdomsd, hρdef, refillPhase_cause]
            · rw [hdomsd, hρdef, refillPhase_serving]
            · rw [hdomsd, hρdef, refillPhase_caps]
            · rw [hdomsd, hρdef, refillPhase_slotGen]
            · rw [hdomsd, hρdef, refillPhase_lineage]
            · rw [hdomsd, hρdef, refillPhase_regions]



end Wip

end Machines.Lnp64u.NonInt
