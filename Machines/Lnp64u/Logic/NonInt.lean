import Machines.Lnp64u.Logic.Wf
import Mathlib.Data.List.Basic

/-!
# Noninterference vocabulary and scheduling lemmas (T5 support)

Definitions and sorry-free lemmas for T5 (`Theorems/T5.lean`). This file
records the *adjudicated* form of the theorem's vocabulary; the original
statement was falsifiable — see the adjudication note below.

## Adjudication: the original T5 statement was FALSE

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
  its compared fields (`regs`/`pc`/`run`/`cause`) never change (refill
  touches only `budget`, which `destutter` ignores), and its destuttered
  trajectory has length 1 forever.

For `n` large enough that `destutter (trajectory m₁ d n)` has length ≥ 2,
no `k` makes it a prefix of the length-≤ 1 list `destutter (trajectory m₂
d k)`. Hence the statement was false; the theorem now additionally
hypothesizes `TopPriority` for both manifests, and `Isolated` gains the
clauses below.

## Why `Isolated` needed strengthening beyond priority

Even with `d` at top priority in both manifests, other domains still get
core cycles (whenever `d`'s budget is exhausted or `d` is in flight), and
the machine has cross-domain channels that reach `d` *without* `d`'s
authority ranges overlapping anyone's:

1. **Grants in.** `mem_grant` installs a capability into the *target*
   domain's lowest free slot and consumes one of the target's lineage
   cells (`allocDerived (descDom dw) …`), requiring no consent from the
   target. A foreign capability parked in `d`'s table never changes `d`'s
   compared fields directly, but it perturbs `d`'s *own* subsequent
   `cap_dup` results: the chosen free slot (hence the handle word written
   to `rd`) and the lineage quota (hence `-ENOLINEAGE`) both depend on
   table occupancy. Since the granter's behavior is unconstrained and
   differs between manifests, this leaks into `d`'s register trajectory.
   Closed by `slots_full`: `d`'s slot table boots full, so `freeSlot d =
   none` and every grant into `d` fails with `-ESLOTOCCUPIED` at the
   granter — *provided `d` never frees a slot*, which `code_local` below
   guarantees (no `cap_drop`/`cap_revoke` in `d`'s code).

2. **`d`'s own globally-sensitive instructions.** Even with no foreign
   state in `d`'s tables, three of `d`'s own operations read shared or
   foreign state into `d`'s registers:
   * `mem_grant` *out of* `d` returns the target-relative handle (the
     target's free slot and generation) or `-ESLOTOCCUPIED`/`-ENOLINEAGE`
     depending on the *target's* table — unconstrained across manifests.
   * `move` returns `-EMOVERBUSY` whenever the single machine-wide Mover
     is running *anyone's* job.
   * `cap_drop`/`cap_revoke` free `d`'s slots, reopening channel 1.
   Closed by `code_local`: no word of `d`'s ROM (under `d`'s roots, which
   is everywhere `d` can ever fetch, by authority confinement) decodes to
   `cap_drop` (17), `cap_revoke` (18), `mem_grant` (19), or `move` (24).
   Everything else `d` can execute — ALU/branch ops, `lw`/`sw` in its own
   disjoint ranges, `cap_dup`, `map`/`unmap`, `yield`, `halt`, and the
   (deterministically failing, since `d` holds no gate capabilities)
   `gate_call`/`gate_return` — reads and writes only `d`'s slice plus
   memory under `d`'s own authority.

## The residual argument (why the strengthened statement is true)

With `TopPriority`, `schedule_top` below gives: whenever the core is idle
and `d` is running with positive budget, `d` is issued. Other domains'
in-flight instructions still *delay* `d` (issue cycles drift between the
two runs) and `d`'s budget *values* differ transiently (refill happens at
absolute cycles, spending happens at drifted issue cycles), but budget is
never architecturally observable (no instruction reads it), so the drift
is pure stutter: `d`'s *k*-th retirement computes the same architectural
`d`-state in both runs (coupling `Coupled` below), and `d` is never
starved (each in-flight instruction finishes, each period refills `d` to
`budgetQ`), so run 2 eventually makes as many `d`-retirements as run 1's
`n`-cycle prefix contains. Destuttering erases the drift and yields the
prefix relation.
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

/-- Domain `d` is authority-isolated in manifest `m`. Clauses 1–3 are the
original path-freedom conditions; clauses 4–5 were forced by adjudication
(see the module docstring): they close the grant-in channel and forbid
`d`'s own globally-sensitive instructions. -/
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
  table state into `d`'s `rd`; `move` reads the machine-global Mover
  busy/idle state into `d`'s `rd`. -/
  code_local : ∀ a, UnderRoots m d a →
    ∀ i, Loom.Isa.decode isa (m.rom a) = some i →
      i.opcode ≠ 17 ∧ i.opcode ≠ 18 ∧ i.opcode ≠ 19 ∧ i.opcode ≠ 24

/-- Two manifests agree on everything `d` can see: `d`'s configuration and
the ROM under `d`'s root ranges. -/
def AgreeOn (m₁ m₂ : Manifest) (d : DomainId) : Prop :=
  m₁.doms d = m₂.doms d ∧
  (∀ a, UnderRoots m₁ d a → m₁.rom a = m₂.rom a)

/-! ## Observation and destuttering -/

/-- The observation equivalence `destutter` collapses under: equal compared
fields (registers, PC, run state, cause). Budget, capability tables, and
region registers are deliberately *not* observed — timing and authority
bookkeeping are where the two runs are allowed to drift. -/
def ObsEq (x y : DomainState) : Prop :=
  x.regs = y.regs ∧ x.pc = y.pc ∧ x.run = y.run ∧ x.cause = y.cause

instance (x y : DomainState) : Decidable (ObsEq x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem ObsEq.refl (x : DomainState) : ObsEq x x := ⟨rfl, rfl, rfl, rfl⟩

/-- Remove consecutive `ObsEq`-duplicates (keeping the last of each run). -/
def destutter : List DomainState → List DomainState
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if ObsEq x y then destutter (y :: rest) else x :: destutter (y :: rest)

/-- `d`'s architectural trajectory over `n` cycles. -/
def trajectory (m : Manifest) (d : DomainId) (n : Nat) : List DomainState :=
  (List.range n).map fun i => (stepN m i m.initState).doms d

/-- A constant trajectory destutters to a single point. -/
theorem destutter_replicate (x : DomainState) :
    ∀ n, destutter (List.replicate (n + 1) x) = [x]
  | 0 => rfl
  | n + 1 => by
      show destutter (x :: x :: List.replicate n x) = [x]
      rw [destutter, if_pos (ObsEq.refl x)]
      exact destutter_replicate x n

/-- Destuttering a pointwise-`ObsEq`… more useful here: prepending an
`ObsEq`-equal head does not change the destuttered list. -/
theorem destutter_cons_obsEq (x y : DomainState) (l : List DomainState)
    (h : ObsEq x y) : destutter (x :: y :: l) = destutter (y :: l) := by
  rw [destutter, if_pos h]

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

/-! ## The two-run coupling invariant -/

/-- The coupling between the two runs, asserted at *aligned* instants
(equal counts of `d`-retirements, not equal cycle numbers — issue cycles
drift because the other domains' in-flight instructions occupy the core
for run-dependent stretches).

What is deliberately **excluded**, and why it is sound to exclude it:

* `budget` of `d` — refill happens at absolute cycles (`σ.cycle %
  periodP`), spending at drifted issue cycles, so the two budgets differ
  transiently. No instruction reads the budget (only `yield` writes it,
  to the constant 0), so the difference is unobservable; it affects only
  *when* `d` issues, never *what* the issued instruction computes. It
  does force the coupling to carry a liveness side-argument (`d` is
  refilled every period and wins every idle cycle, so it is never starved)
  rather than a budget equality.
* everything about the other domains, the gates, and memory outside `d`'s
  roots — unconstrained by hypothesis, unread by `d` (`code_local` +
  root disjointness + authority confinement).
* `σ.cycle`, `σ.mover`, and non-`d` in-flight state — pure timing. -/
structure Coupled (m : Manifest) (d : DomainId) (σ₁ σ₂ : MachineState) : Prop where
  regs : (σ₁.doms d).regs = (σ₂.doms d).regs
  pc : (σ₁.doms d).pc = (σ₂.doms d).pc
  run : (σ₁.doms d).run = (σ₂.doms d).run
  cause : (σ₁.doms d).cause = (σ₂.doms d).cause
  /-- Isolation keeps `d` out of gate service in both runs. -/
  serving : (σ₁.doms d).serving = none ∧ (σ₂.doms d).serving = none
  /-- Full authority-bookkeeping equality: `d`'s own cap ops (`cap_dup`,
  `map`, `unmap`) read and write these, and no foreign grant ever lands
  (`slots_full` + `code_local`), so they evolve in lockstep. -/
  caps : (σ₁.doms d).caps = (σ₂.doms d).caps
  slotGen : (σ₁.doms d).slotGen = (σ₂.doms d).slotGen
  lineage : (σ₁.doms d).lineage = (σ₂.doms d).lineage
  regions : (σ₁.doms d).regions = (σ₂.doms d).regions
  /-- Memory under `d`'s roots is equal: only `d` writes there (roots
  disjoint + confinement + Mover jobs re-check the issuer's own caps). -/
  mem : ∀ a, UnderRoots m d a → σ₁.mem a = σ₂.mem a
  /-- `d`'s in-flight status is aligned: at aligned instants either `d` is
  in flight in both runs with the same latched word and countdown, or in
  neither. (Non-`d` in-flight records are unconstrained.) -/
  inflight : ∀ fl, fl.dom = d →
    (σ₁.inflight = some fl ↔ σ₂.inflight = some fl)

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
      cause := by rw [hboot], serving := ⟨rfl, rfl⟩
      caps := by rw [hboot], slotGen := by rw [hboot], lineage := by rw [hboot]
      regions := by rw [hboot]
      mem := fun a ha => hrom a ha
      inflight := fun _ _ => Iff.rfl }

end Machines.Lnp64u.NonInt
