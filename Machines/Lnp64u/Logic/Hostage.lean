import Machines.Lnp64u.Logic.Budget
import Machines.Lnp64u.Logic.GateStep
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# T6 support: hyperperiod, donation ceiling, unwind and scheduler lemmas

The per-cycle ingredients of the `no_hostage` liveness proof (T6). All
lemmas here are sorry-free; the assembly into the full resume bound lives
in `Theorems/T6.lean`.

Contents:
* `hyperL` / `maxDonationBound` / `budgetMass` / `maxCostBound` — the
  manifest-computable quantities the (repaired) `resumeBound` is built
  from, with positivity/divisibility/ceiling lemmas.
* `stepN_add` — window splitting for the counting argument.
* Unwind lemmas — a serving domain that halts (fault, `halt`, or donation
  exhaustion) *unconditionally* frees its gate and resumes the caller:
  the mechanism that makes every "callee makes progress" cycle also a
  progress cycle for the blocked caller.
* Scheduler lemmas — the scheduler is total on eligible domains, monotone
  in priority, and (with `Manifest.WF.prio_inj`) picks exactly the
  top-priority eligible domain. This is what rules out "stall with the
  chain head runnable": if the serving-chain head is eligible and nothing
  of higher priority is, it *is* issued.
* `corePhase_issue_serving` / `corePhase_stall` — the progress dichotomy
  at an issue cycle of a serving domain: either the activation's `donated`
  strictly decreases (and the instruction is in flight), or the donation
  is exhausted and the forced unwind fires this very cycle.
* `StallsAt` and `corePhase_cases` — the exhaustive whole-cycle
  classification of the core (burn / retire / idle / fault-halt / stall /
  issue), with the payer-charge equation on the issue arm: the case split
  every cycle of the T6 counting argument goes through.
* `massExcept` — the total budget outside a distinguished domain (the T6
  potential's main term), with its per-arm evolution lemmas: monotone
  under `corePhase`, exact `-cost` decrement on a foreign issue, and
  `≤ +Q`-per-boundary growth under `refillPhase`.
-/

namespace Machines.Lnp64u

open Loom

/-! ## Manifest-level quantities -/

/-- The hyperperiod: `lcm` of all domain periods. One refill of every
domain happens inside any window of `hyperL` cycles. -/
def hyperL (m : Manifest) : Nat :=
  (List.finRange numDomains).foldl (fun acc d => Nat.lcm acc (m.doms d).periodP) 1

/-- Machine-wide donation ceiling: every gate activation's `donated` field
is initialized from *some* domain's `maxDonation` (the caller's at that
chain level), so this bounds the donation of every activation on any
serving chain. -/
def maxDonationBound (m : Manifest) : Nat :=
  (List.finRange numDomains).foldl (fun acc d => max acc (m.doms d).maxDonation) 0

private theorem foldl_lcm_pos (f : DomainId → Nat) :
    ∀ (l : List DomainId) (acc : Nat), 0 < acc → (∀ d ∈ l, 0 < f d) →
      0 < l.foldl (fun a d => Nat.lcm a (f d)) acc := by
  intro l
  induction l with
  | nil => intro acc hacc _; exact hacc
  | cons x xs ih =>
      intro acc hacc h
      exact ih _ (Nat.lcm_pos hacc (h x (by simp)))
        (fun d hd => h d (List.mem_cons_of_mem _ hd))

private theorem acc_dvd_foldl_lcm (f : DomainId → Nat) :
    ∀ (l : List DomainId) (acc : Nat),
      acc ∣ l.foldl (fun a d => Nat.lcm a (f d)) acc := by
  intro l
  induction l with
  | nil => intro acc; exact Nat.dvd_refl acc
  | cons x xs ih =>
      intro acc
      exact Nat.dvd_trans (Nat.dvd_lcm_left _ _) (ih (Nat.lcm acc (f x)))

private theorem mem_dvd_foldl_lcm (f : DomainId → Nat) :
    ∀ (l : List DomainId) (acc : Nat) (d : DomainId), d ∈ l →
      f d ∣ l.foldl (fun a d => Nat.lcm a (f d)) acc := by
  intro l
  induction l with
  | nil => intro _ _ h; cases h
  | cons x xs ih =>
      intro acc d h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.dvd_trans (Nat.dvd_lcm_right _ _) (acc_dvd_foldl_lcm f xs _)
      · exact ih _ d h'

/-- The hyperperiod is positive (periods are positive by manifest WF). -/
theorem hyperL_pos (m : Manifest) (hwf : m.WF) : 0 < hyperL m := by
  unfold hyperL
  exact foldl_lcm_pos _ _ 1 Nat.one_pos (fun d _ => hwf.period_pos d)

/-- Every period divides the hyperperiod: each domain is refilled exactly
`hyperL m / periodP` times per hyperperiod window. -/
theorem periodP_dvd_hyperL (m : Manifest) (d : DomainId) :
    (m.doms d).periodP ∣ hyperL m := by
  unfold hyperL
  exact mem_dvd_foldl_lcm _ _ 1 d (List.mem_finRange d)

private theorem le_foldl_max (f : DomainId → Nat) :
    ∀ (l : List DomainId) (acc : Nat),
      acc ≤ l.foldl (fun a d => max a (f d)) acc ∧
      ∀ d ∈ l, f d ≤ l.foldl (fun a d => max a (f d)) acc := by
  intro l
  induction l with
  | nil => intro acc; exact ⟨Nat.le_refl _, fun _ h => absurd h (List.not_mem_nil)⟩
  | cons x xs ih =>
      intro acc
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) (ih (max acc (f x))).1, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | h'
      · exact Nat.le_trans (Nat.le_max_right _ _) (ih (max acc (f d))).1
      · exact (ih (max acc (f x))).2 d h'

/-- Every domain's donation bound is below the machine-wide ceiling. -/
theorem maxDonation_le_bound (m : Manifest) (d : DomainId) :
    (m.doms d).maxDonation ≤ maxDonationBound m := by
  unfold maxDonationBound
  exact (le_foldl_max (fun d' => (m.doms d').maxDonation) _ 0).2 d
    (List.mem_finRange d)

/-- Every period is at most the hyperperiod (it divides it). -/
theorem periodP_le_hyperL (m : Manifest) (hwf : m.WF) (d : DomainId) :
    (m.doms d).periodP ≤ hyperL m :=
  Nat.le_of_dvd (hyperL_pos m hwf) (periodP_dvd_hyperL m d)

/-- The machine-wide instruction-cost ceiling (`cap_revoke`'s 24 cycles):
an in-flight instruction occupies the core for at most `maxCostBound + 1`
cycles (issue through retirement). -/
def maxCostBound : Nat := 24

theorem cost_le_maxCostBound (c : WcetClass) : c.cost ≤ maxCostBound := by
  cases c <;> decide

/-- Every instruction costs at least one cycle: an issue always charges the
payer — the fact that makes charged cycles countable against budgets. -/
theorem cost_pos (c : WcetClass) : 0 < c.cost := by
  cases c <;> decide

/-- Total manifest budget mass `Σ_e Q_e`: the ceiling on what refills can
hand out per hyperperiod-boundary sweep, hence on the interference the T6
potential must absorb. -/
def budgetMass (m : Manifest) : Nat :=
  ((List.finRange numDomains).map (fun e => (m.doms e).budgetQ)).sum

/-! ## Window splitting -/

theorem stepN_add (m : Manifest) :
    ∀ (a b : Nat) (σ : MachineState),
      stepN m (a + b) σ = stepN m b (stepN m a σ)
  | 0, b, σ => by rw [Nat.zero_add]; rfl
  | a + 1, b, σ => by
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h]
      show stepN m (a + b) (step m σ) = stepN m b (stepN m a (step m σ))
      exact stepN_add m a b (step m σ)

/-- Reachability is closed under `stepN`: the T6 windows stay inside the
reachable set, so `Wf`, `Acyclic`, and `StallFree` apply at every cycle. -/
theorem stepN_reachable (m : Manifest) (σ : MachineState)
    (hreach : (machine m).Reachable σ) :
    ∀ n, (machine m).Reachable (stepN m n σ) := by
  intro n
  induction n generalizing σ with
  | zero => exact hreach
  | succ k ih => exact ih (step m σ) (Loom.TSys.Reachable.step hreach rfl)

/-- A non-serving domain pays for itself — contrapositively, any domain
whose payer is the blocked caller's chain origin (other than the origin
itself) is *serving*, i.e. sits on the origin's chain: the fact that
makes `massExcept σ origin` chargeable only by foreign issues. -/
theorem payer_ne_of_serving_none (σ : MachineState) (e x : DomainId)
    (hne : e ≠ x) (hserv : (σ.doms e).serving = none) : σ.payer e ≠ x := by
  show σ.chainOrigin maxChainDepth e ≠ x
  unfold MachineState.chainOrigin
  rw [hserv]
  exact hne

/-! ## Unwind lemmas: a halting callee frees its caller *this cycle* -/

/-- `unwindGate` resumes the caller unconditionally. -/
theorem unwindGate_caller_running (σ : MachineState) (g : GateId)
    (cl : DomainId) (rd : RegId) :
    ((σ.unwindGate g cl rd).doms cl).run = .running := by
  unfold MachineState.unwindGate MachineState.setDom
  simp only [Loom.Fun.update_same]
  unfold DomainState.setReg
  split <;> rfl

/-- `unwindGate` frees the gate record. -/
theorem unwindGate_gate_free (σ : MachineState) (g : GateId)
    (cl : DomainId) (rd : RegId) :
    ((σ.unwindGate g cl rd).gates g).act = none := by
  unfold MachineState.unwindGate MachineState.setDom
  simp [Loom.Fun.update_same]

/-- A serving domain that halts (for any cause: fault at issue or retire,
voluntary `halt`, donation exhaustion) resumes its blocked caller in the
same cycle — the T6 forced-unwind mechanism, as a plain projection. -/
theorem haltDom_caller_running (σ : MachineState) (c : DomainId)
    (cause : Loom.Word32) (g : GateId) (a : Activation)
    (hserv : (σ.doms c).serving = some g) (hact : (σ.gates g).act = some a) :
    ((σ.haltDom c cause).doms a.caller).run = .running := by
  unfold MachineState.haltDom
  simp only [hserv]
  have hact' : ((σ.haltBase c cause).gates g).act = some a := hact
  simp only [hact]
  exact unwindGate_caller_running _ g a.caller a.callerRd

/-- The halting callee's gate is freed in the same cycle. -/
theorem haltDom_gate_free (σ : MachineState) (c : DomainId)
    (cause : Loom.Word32) (g : GateId) (a : Activation)
    (hserv : (σ.doms c).serving = some g) (hact : (σ.gates g).act = some a) :
    ((σ.haltDom c cause).gates g).act = none := by
  unfold MachineState.haltDom
  simp only [hserv, hact]
  exact unwindGate_gate_free _ g a.caller a.callerRd

/-! ## Scheduler lemmas -/

/-- Domain `d` is eligible for scheduling in `σ`: running, and its payer
has budget. Exactly the `schedule` filter predicate, propositionally. -/
def Eligible (σ : MachineState) (d : DomainId) : Prop :=
  (σ.doms d).run = .running ∧ 0 < (σ.doms (σ.payer d)).budget

/-- The `schedule` fold step. -/
private def schedStep (m : Manifest) : Option DomainId → DomainId → Option DomainId :=
  fun best d =>
    match best with
    | none => some d
    | some b => if (m.doms b).priority < (m.doms d).priority then some d else some b

private theorem schedule_eq_foldl (m : Manifest) (σ : MachineState) :
    schedule m σ =
      ((List.finRange numDomains).filter fun d =>
        decide ((σ.doms d).run = .running) &&
        decide (0 < (σ.doms (σ.payer d)).budget)).foldl (schedStep m) none := rfl

private theorem foldl_schedStep_isSome (m : Manifest) :
    ∀ (l : List DomainId) (b : DomainId),
      (l.foldl (schedStep m) (some b)).isSome := by
  intro l
  induction l with
  | nil => intro b; rfl
  | cons x xs ih =>
      intro b
      rw [List.foldl_cons]
      show (xs.foldl (schedStep m)
        (if (m.doms b).priority < (m.doms x).priority then some x else some b)).isSome
      split <;> exact ih _

private theorem foldl_schedStep_ge (m : Manifest) :
    ∀ (l : List DomainId) (init : Option DomainId) (r : DomainId),
      l.foldl (schedStep m) init = some r →
      (∀ d ∈ l, (m.doms d).priority ≤ (m.doms r).priority) ∧
      (∀ b, init = some b → (m.doms b).priority ≤ (m.doms r).priority) := by
  intro l
  induction l with
  | nil =>
      intro init r h
      exact ⟨fun _ hd => absurd hd (List.not_mem_nil),
             fun b hb => by rw [hb] at h; cases h; exact Nat.le_refl _⟩
  | cons x xs ih =>
      intro init r h
      rw [List.foldl_cons] at h
      obtain ⟨hxs, hinit'⟩ := ih (schedStep m init x) r h
      have hx : (m.doms x).priority ≤ (m.doms r).priority := by
        cases init with
        | none => exact hinit' x rfl
        | some b =>
            unfold schedStep at hinit'
            by_cases hlt : (m.doms b).priority < (m.doms x).priority
            · exact hinit' x (by simp [hlt])
            · exact Nat.le_trans (Nat.le_of_not_lt hlt) (hinit' b (by simp [hlt]))
      refine ⟨fun d hd => ?_, fun b hb => ?_⟩
      · rcases List.mem_cons.mp hd with rfl | h'
        · exact hx
        · exact hxs d h'
      · subst hb
        unfold schedStep at hinit'
        by_cases hlt : (m.doms b).priority < (m.doms x).priority
        · exact Nat.le_trans (Nat.le_of_lt hlt) (hinit' x (by simp [hlt]))
        · exact hinit' b (by simp [hlt])

private theorem foldl_schedStep_mem (m : Manifest) :
    ∀ (l : List DomainId) (init : Option DomainId) (r : DomainId),
      l.foldl (schedStep m) init = some r → init = some r ∨ r ∈ l := by
  intro l
  induction l with
  | nil => intro init r h; exact .inl h
  | cons x xs ih =>
      intro init r h
      rw [List.foldl_cons] at h
      rcases ih (schedStep m init x) r h with h' | h'
      · cases init with
        | none =>
            cases h'
            exact .inr (by simp)
        | some b =>
            unfold schedStep at h'
            by_cases hlt : (m.doms b).priority < (m.doms x).priority
            · simp only [if_pos hlt] at h'
              cases h'
              exact .inr (by simp)
            · simp only [if_neg hlt] at h'
              exact .inl h'
      · exact .inr (List.mem_cons_of_mem _ h')

private theorem mem_schedule_filter (σ : MachineState) (d : DomainId)
    (h : Eligible σ d) :
    d ∈ (List.finRange numDomains).filter fun d' =>
      decide ((σ.doms d').run = .running) &&
      decide (0 < (σ.doms (σ.payer d')).budget) :=
  List.mem_filter.mpr ⟨List.mem_finRange d, by simp [h.1, h.2]⟩

/-- **Scheduler totality on eligibles.** If any domain is eligible, the
scheduler picks someone — the core is never idle while the serving-chain
head is runnable and funded. -/
theorem schedule_isSome_of_eligible (m : Manifest) (σ : MachineState)
    (d : DomainId) (h : Eligible σ d) : (schedule m σ).isSome := by
  rw [schedule_eq_foldl]
  have hmem := mem_schedule_filter σ d h
  revert hmem
  cases hL : (List.finRange numDomains).filter fun d' =>
      decide ((σ.doms d').run = .running) &&
      decide (0 < (σ.doms (σ.payer d')).budget) with
  | nil => intro hmem; exact absurd hmem (List.not_mem_nil)
  | cons x xs =>
      intro _
      rw [List.foldl_cons]
      show (xs.foldl (schedStep m) (schedStep m none x)).isSome
      exact foldl_schedStep_isSome m xs x

/-- **Scheduler priority monotonicity.** The scheduled domain has
priority at least that of every eligible domain. -/
theorem schedule_priority_le (m : Manifest) (σ : MachineState)
    (d b : DomainId) (h : Eligible σ d) (hs : schedule m σ = some b) :
    (m.doms d).priority ≤ (m.doms b).priority := by
  rw [schedule_eq_foldl] at hs
  exact (foldl_schedStep_ge m _ none b hs).1 d (mem_schedule_filter σ d h)

/-- The scheduled domain is itself eligible (strengthens
`PhaseLemmas.schedule_running` with the payer-budget fact). -/
theorem schedule_eligible (m : Manifest) (σ : MachineState) (b : DomainId)
    (hs : schedule m σ = some b) : Eligible σ b := by
  rw [schedule_eq_foldl] at hs
  rcases foldl_schedStep_mem m _ none b hs with h | h
  · cases h
  · have := (List.mem_filter.mp h).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, this.2⟩

/-- **The top-priority eligible domain is scheduled.** With distinct
priorities (manifest WF), an eligible domain that dominates every other
eligible domain's priority is exactly the scheduler's pick. This is the
lemma that kills "stall with the chain head runnable": interference can
only come from *strictly higher-priority* eligible domains. -/
theorem schedule_eq_of_top (m : Manifest) (hwf : m.WF) (σ : MachineState)
    (d : DomainId) (h : Eligible σ d)
    (htop : ∀ d', Eligible σ d' → (m.doms d').priority ≤ (m.doms d).priority) :
    schedule m σ = some d := by
  have hsome := schedule_isSome_of_eligible m σ d h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  have h1 := schedule_priority_le m σ d b h hb
  have h2 := htop b (schedule_eligible m σ b hb)
  have : b = d := hwf.prio_inj b d (Nat.le_antisymm h2 h1)
  rw [hb, this]

/-! ## The issue-cycle progress dichotomy for a serving domain -/

/-- **Donation progress.** When the core is idle and the scheduler issues
for a domain serving gate `g` (with the payer funded), then either

* the activation's `donated` covers the instruction cost: it strictly
  decreases by that cost and the instruction is in flight, or
* the donation is exhausted: the forced unwind (`haltWith … .budget`)
  fires *this cycle* — which by `haltDom_caller_running` resumes the
  blocked caller immediately.

Either way the serving chain makes strict progress in the T6 measure. -/
theorem corePhase_issue_serving (m : Manifest) (σ : MachineState)
    (d : DomainId) (g : GateId) (a : Activation) (w : Loom.Word32)
    (instr : Loom.Isa.InstrDecl sig Semantics WcetClass)
    (hinf : σ.inflight = none) (hsched : schedule m σ = some d)
    (hfetch : fetch σ d = some w)
    (hdec : Loom.Isa.decode isa w = some instr)
    (hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget)
    (hserv : (σ.doms d).serving = some g)
    (hact : (σ.gates g).act = some a) :
    (instr.cost.cost ≤ a.donated ∧
       ((corePhase m σ).gates g).act =
         some { a with donated := a.donated - instr.cost.cost } ∧
       (corePhase m σ).inflight =
         some { dom := d, word := w, cyclesLeft := instr.cost.cost }) ∨
    (a.donated < instr.cost.cost ∧ corePhase m σ = haltWith σ d .budget) := by
  unfold corePhase
  simp only [hinf, hsched, hfetch, hdec, hserv, hact]
  rw [if_pos hbud]
  by_cases hd : instr.cost.cost ≤ a.donated
  · left
    rw [if_pos hd]
    refine ⟨hd, ?_, rfl⟩
    simp [MachineState.setDom, Loom.Fun.update_same]
  · right
    rw [if_neg hd]
    exact ⟨Nat.lt_of_not_le hd, rfl⟩

/-- **Stall characterization.** An issue cycle where the scheduled
domain's payer cannot cover the instruction cost changes nothing: the
core stalls until refill. Stall cycles spend *no* budget anywhere, so
they cannot be charged to any budget account — which is why the T6
statement carries the `StallFree` hypothesis (see the stall-lock
refutation in `Theorems/T6.lean`). -/
theorem corePhase_stall (m : Manifest) (σ : MachineState)
    (d : DomainId) (w : Loom.Word32) (instr : Loom.Isa.InstrDecl sig Semantics WcetClass)
    (hinf : σ.inflight = none) (hsched : schedule m σ = some d)
    (hfetch : fetch σ d = some w)
    (hdec : Loom.Isa.decode isa w = some instr)
    (hbud : ¬ instr.cost.cost ≤ (σ.doms (σ.payer d)).budget) :
    corePhase m σ = σ := by
  unfold corePhase
  simp only [hinf, hsched, hfetch, hdec]
  rw [if_neg hbud]

/-! ## The whole-cycle core classification -/

/-- A stall cycle: the core is idle, the scheduler picked `e`, fetch and
decode succeeded, but `e`'s payer cannot cover the instruction's cost.
`corePhase` then changes *nothing* (`corePhase_stall`): the cycle is lost
and no budget moves — stalls are uncountable against budgets, the reason
for T6's `StallFree` hypothesis. -/
def StallsAt (m : Manifest) (σ : MachineState) : Prop :=
  ∃ e w instr, σ.inflight = none ∧ schedule m σ = some e ∧
    fetch σ e = some w ∧ Loom.Isa.decode isa w = some instr ∧
    ¬ instr.cost.cost ≤ (σ.doms (σ.payer e)).budget

/-- **The exhaustive core-cycle classification** — the case split every
cycle of the T6 counting argument goes through. One `corePhase` is exactly
one of:

* **burn** — an in-flight instruction with cycles to go counts down;
* **retire** — the in-flight instruction's last cycle;
* **idle** — the core is free and nobody is eligible;
* **fault-halt** — the scheduled domain halts this cycle (fetch or decode
  failure, protocol violation, or donation exhaustion — every arm of the
  form `haltWith`, so if the victim was serving, its caller resumes);
* **stall** — the scheduled domain's payer cannot cover the cost; nothing
  changes;
* **issue** — the instruction is latched with `cyclesLeft = cost` and the
  payer is charged `cost` upfront (every other budget untouched). -/
theorem corePhase_cases (m : Manifest) (σ : MachineState) :
    (∃ fl, σ.inflight = some fl ∧ 1 < fl.cyclesLeft ∧
      corePhase m σ =
        { σ with inflight := some { fl with cyclesLeft := fl.cyclesLeft - 1 } }) ∨
    (∃ fl, σ.inflight = some fl ∧ fl.cyclesLeft ≤ 1 ∧
      corePhase m σ = retire { σ with inflight := none } fl.dom fl.word) ∨
    (σ.inflight = none ∧ schedule m σ = none ∧ corePhase m σ = σ) ∨
    (∃ e f, σ.inflight = none ∧ schedule m σ = some e ∧
      corePhase m σ = haltWith σ e f) ∨
    (StallsAt m σ ∧ corePhase m σ = σ) ∨
    (∃ e w instr, σ.inflight = none ∧ schedule m σ = some e ∧
      fetch σ e = some w ∧ Loom.Isa.decode isa w = some instr ∧
      instr.cost.cost ≤ (σ.doms (σ.payer e)).budget ∧
      (corePhase m σ).inflight = some ⟨e, w, instr.cost.cost⟩ ∧
      ∀ e', ((corePhase m σ).doms e').budget =
        if e' = σ.payer e then (σ.doms e').budget - instr.cost.cost
        else (σ.doms e').budget) := by
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · refine .inr (.inl ⟨fl, rfl, hc, ?_⟩)
        unfold corePhase; simp only [hinf, hc, if_true]
      · refine .inl ⟨fl, rfl, by omega, ?_⟩
        unfold corePhase; simp only [hinf, hc, if_false]
  | none =>
      cases hsched : schedule m σ with
      | none =>
          refine .inr (.inr (.inl ⟨rfl, rfl, ?_⟩))
          unfold corePhase; simp only [hinf, hsched]
      | some e =>
          cases hfetch : fetch σ e with
          | none =>
              refine .inr (.inr (.inr (.inl ⟨e, .memoryAuthority, rfl, rfl, ?_⟩)))
              unfold corePhase; simp only [hinf, hsched, hfetch]
          | some w =>
              cases hdec : Loom.Isa.decode isa w with
              | none =>
                  refine .inr (.inr (.inr (.inl
                    ⟨e, .illegalInstruction, rfl, rfl, ?_⟩)))
                  unfold corePhase; simp only [hinf, hsched, hfetch, hdec]
              | some instr =>
                  by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer e)).budget
                  · cases hserv : (σ.doms e).serving with
                    | none =>
                        refine .inr (.inr (.inr (.inr (.inr
                          ⟨e, w, instr, rfl, rfl, hfetch, hdec, hbud, ?_, ?_⟩))))
                        · unfold corePhase
                          simp only [hinf, hsched, hfetch, hdec, hbud,
                            if_true, hserv]
                        · intro e'
                          unfold corePhase
                          simp only [hinf, hsched, hfetch, hdec, hbud,
                            if_true, hserv]
                          by_cases he' : e' = σ.payer e
                          · subst he'
                            simp [MachineState.setDom, Loom.Fun.update_same]
                          · simp [MachineState.setDom, he']
                    | some g =>
                        cases hact : (σ.gates g).act with
                        | none =>
                            refine .inr (.inr (.inr (.inl
                              ⟨e, .protocol, rfl, rfl, ?_⟩)))
                            unfold corePhase
                            simp only [hinf, hsched, hfetch, hdec, hbud,
                              if_true, hserv, hact]
                        | some a =>
                            by_cases hdon : instr.cost.cost ≤ a.donated
                            · refine .inr (.inr (.inr (.inr (.inr
                                ⟨e, w, instr, rfl, rfl, hfetch, hdec, hbud, ?_, ?_⟩))))
                              · unfold corePhase
                                simp only [hinf, hsched, hfetch, hdec, hbud,
                                  if_true, hserv, hact, hdon]
                              · intro e'
                                unfold corePhase
                                simp only [hinf, hsched, hfetch, hdec, hbud,
                                  if_true, hserv, hact, hdon]
                                by_cases he' : e' = σ.payer e
                                · subst he'
                                  simp [MachineState.setDom,
                                    Loom.Fun.update_same]
                                · simp [MachineState.setDom, he']
                            · refine .inr (.inr (.inr (.inl
                                ⟨e, .budget, rfl, rfl, ?_⟩)))
                              unfold corePhase
                              simp only [hinf, hsched, hfetch, hdec, hbud,
                                if_true, hserv, hact, hdon, if_false]
                  · refine .inr (.inr (.inr (.inr (.inl
                      ⟨⟨e, w, instr, hinf, hsched, hfetch, hdec, hbud⟩, ?_⟩))))
                    exact corePhase_stall m σ e w instr hinf hsched hfetch hdec hbud

/-! ## Budget mass outside a domain -/

/-- Total budget held by every domain other than `x`. In T6, `x` is the
blocked caller's chain origin — the one budget only the serving chain
draws on — and `massExcept` is the main term of the interference
potential: foreign issues strictly decrease it, refills grow it by at
most `Q` per period boundary, and nothing else moves it. -/
def massExcept (σ : MachineState) (x : DomainId) : Nat :=
  ∑ e ∈ Finset.univ.erase x, (σ.doms e).budget

/-- Pointwise budget domination gives mass domination. -/
theorem massExcept_mono {σ σ' : MachineState} (x : DomainId)
    (h : ∀ e, (σ'.doms e).budget ≤ (σ.doms e).budget) :
    massExcept σ' x ≤ massExcept σ x :=
  Finset.sum_le_sum (fun e _ => h e)

/-- `corePhase` never raises the outside mass (issues charge, retires
only lower budgets, halts and stalls leave them alone). -/
theorem corePhase_massExcept_le (m : Manifest) (σ : MachineState)
    (x : DomainId) : massExcept (corePhase m σ) x ≤ massExcept σ x :=
  massExcept_mono x (fun e => Wip.corePhase_budget_le m σ e)

/-- **The exact charge equation**: a transition that subtracts `c` from
one domain `p ≠ x` and touches no other budget moves the outside mass
down by exactly `c` — the strict-decrease brick of the T6 potential
(instantiated with the issue arm of `corePhase_cases`, where `p` is the
scheduled domain's payer and `c ≥ 1` by `cost_pos`). -/
theorem massExcept_sub {σ σ' : MachineState} (x p : DomainId) (c : Nat)
    (hpx : p ≠ x) (hc : c ≤ (σ.doms p).budget)
    (hp : (σ'.doms p).budget = (σ.doms p).budget - c)
    (hne : ∀ e, e ≠ p → (σ'.doms e).budget = (σ.doms e).budget) :
    massExcept σ' x + c = massExcept σ x := by
  have hmem : p ∈ Finset.univ.erase x :=
    Finset.mem_erase.mpr ⟨hpx, Finset.mem_univ p⟩
  have hrest : ∑ e ∈ (Finset.univ.erase x).erase p, (σ'.doms e).budget
      = ∑ e ∈ (Finset.univ.erase x).erase p, (σ.doms e).budget :=
    Finset.sum_congr rfl (fun e he => hne e (Finset.ne_of_mem_erase he))
  unfold massExcept
  rw [← Finset.add_sum_erase _ _ hmem,
      ← Finset.add_sum_erase _ (fun e => (σ.doms e).budget) hmem, hrest, hp]
  omega

/-! ## The `run = halted → serving = none` reachability invariant (T6 obligation 1)

A domain that has halted holds no serving mark. Needed by the T6 chain
structure to exclude a "half-halted chain" — a callee whose `run` is
`.halted` but whose `serving` still points at its gate, which `Wf` alone
does *not* forbid (`gate_serving` constrains the *caller*'s run, never the
callee's). The single writer of `run := .halted` is `haltBase`
(`Kernel.lean`), which simultaneously sets `serving := none`; the two
`serving := some` writers (`gate_call`'s callee, `gate_return`'s restore)
both leave `run` at `.running`. The predicate is therefore an inductive
invariant. -/

/-- Every halted domain has a cleared serving mark. -/
def HaltedServingNone (σ : MachineState) : Prop :=
  ∀ d, (σ.doms d).run = .halted → (σ.doms d).serving = none

/-- A calm transition (run and serving of every domain preserved) carries
`HaltedServingNone` — the discharge for every non-gate, non-halt op and for
the `.err` outcome of *every* op (`TouchExec`'s err arm is `CalmOut`). -/
theorem CalmOut.hsn {cd : DomainId} {σ σ' : MachineState}
    (h : CalmOut cd σ σ') (hσ : HaltedServingNone σ) : HaltedServingNone σ' := by
  intro d hd
  rw [h.1 d]
  exact hσ d (by rw [← h.2.1 d]; exact hd)

/-- `haltDom` preserves the invariant: the halted target gets `serving :=
none`, the resumed caller (if any) goes `running` (never halted), everyone
else is untouched. The halt mechanism is exactly what keeps the invariant
inductive. -/
theorem haltDom_hsn (σ : MachineState) (d : DomainId) (cv : Loom.Word32)
    (hσ : HaltedServingNone σ) : HaltedServingNone (σ.haltDom d cv) := by
  cases hserv : (σ.doms d).serving with
  | none =>
      rw [haltDom_base σ d cv hserv]
      intro e he
      simp only [haltBase_serving]
      simp only [haltBase_run] at he
      by_cases hed : e = d
      · simp [hed]
      · rw [if_neg hed] at he ⊢; exact hσ e he
  | some g =>
      cases hact : (σ.gates g).act with
      | none =>
          rw [haltDom_base' σ d cv g hserv hact]
          intro e he
          simp only [haltBase_serving]
          simp only [haltBase_run] at he
          by_cases hed : e = d
          · simp [hed]
          · rw [if_neg hed] at he ⊢; exact hσ e he
      | some a =>
          rw [haltDom_unwind σ d cv g a hserv hact]
          intro e he
          simp only [unwindGate_serving, haltBase_serving]
          simp only [unwindGate_run, haltBase_run] at he
          by_cases hec : e = a.caller
          · rw [if_pos hec] at he; exact absurd he (by simp)
          · rw [if_neg hec] at he
            by_cases hed : e = d
            · simp [hed]
            · rw [if_neg hed] at he ⊢; exact hσ e he

/-- `refillPhase` preserves the invariant (it moves only budgets, never run
or serving). -/
theorem refillPhase_hsn (m : Manifest) (σ : MachineState)
    (hσ : HaltedServingNone σ) : HaltedServingNone (refillPhase m σ) := by
  intro d hd
  rw [refillPhase_serving]
  exact hσ d (by rw [← refillPhase_run m σ d]; exact hd)

/-- The boot state satisfies the invariant vacuously: every domain boots
with `serving = none`. -/
theorem initState_hsn (m : Manifest) : HaltedServingNone (m.initState) := by
  intro d _; rfl

/-- `gate_call`'s activation-entry end state preserves the invariant: the
callee gains `serving = some gid` but keeps `run = running`; the caller goes
`blocked` (never halted); everyone else is framed back to `σ0`. -/
theorem gateCall_end_hsn (τ σ0 : MachineState) (caller cal : DomainId) (gid : GateId)
    (G : GateState) (argHandle : Loom.Word32) (entry : Addr)
    (hcalne : cal ≠ caller)
    (hfrun : ∀ d', (τ.doms d').run = (σ0.doms d').run)
    (hfserv : ∀ d', (τ.doms d').serving = (σ0.doms d').serving)
    (hcalrun : (σ0.doms cal).run = .running)
    (hσ : HaltedServingNone σ0) :
    HaltedServingNone ((({ τ with gates := Loom.Fun.update τ.gates gid G }).setDom cal
        (fun ds => { ds with
          regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
          pc := entry, serving := some gid })).setDom caller
        (fun ds => { ds with run := .blocked gid })) := by
  have hXd : ({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).doms
      = τ.doms := rfl
  intro e he
  by_cases hecaller : e = caller
  · subst hecaller
    rw [setDom_doms_same] at he; simp at he
  · rw [setDom_doms_ne _ _ _ _ hecaller] at he ⊢
    by_cases hecal : e = cal
    · subst hecal
      rw [setDom_doms_same] at he
      simp only [hXd] at he; simp [hfrun, hcalrun] at he
    · rw [setDom_doms_ne _ _ _ _ hecal] at he ⊢
      simp only [hXd] at he ⊢
      rw [hfserv e]; exact hσ e (by rw [← hfrun e]; exact he)

/-- `gate_return`'s end state preserves the invariant: the returning callee
keeps `run = running`; the resumed caller goes `running`; nobody halts. -/
theorem gateReturn_end_hsn (τ σ0 : MachineState) (cd : DomainId) (gid : GateId)
    (act : Activation) (reply : Loom.Word32) (G : GateState)
    (hfrun : ∀ d', (τ.doms d').run = (σ0.doms d').run)
    (hfserv : ∀ d', (τ.doms d').serving = (σ0.doms d').serving)
    (hrun : (σ0.doms cd).run = .running)
    (hserv : (σ0.doms cd).serving = some gid)
    (hgact : (σ0.gates gid).act = some act)
    (hwf : Wf σ0) (hσ : HaltedServingNone σ0) :
    HaltedServingNone (((({ τ with gates := Loom.Fun.update τ.gates gid G }).setDom cd
        (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc
                             serving := act.savedServing })).setDom act.caller
        (fun ds => { ds with run := .running })).setDom act.caller
        (fun ds => ds.setReg act.callerRd reply)) := by
  have hXd : ({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).doms
      = τ.doms := rfl
  have hcallerblk : (σ0.doms act.caller).run = .blocked gid :=
    (hwf.gate_serving gid act hgact).2.1
  have hcne : act.caller ≠ cd := by
    intro h; rw [h, hrun] at hcallerblk; exact absurd hcallerblk (by simp)
  intro e he
  by_cases hecl : e = act.caller
  · subst hecl
    rw [setDom_doms_same, setDom_doms_same] at he
    simp at he
  · rw [setDom_doms_ne _ _ _ _ hecl] at he ⊢
    rw [setDom_doms_ne _ _ _ _ hecl] at he ⊢
    by_cases hecd : e = cd
    · subst hecd
      rw [setDom_doms_same] at he
      simp only [hXd] at he; simp [hfrun, hrun] at he
    · rw [setDom_doms_ne _ _ _ _ hecd] at he ⊢
      simp only [hXd] at he ⊢
      rw [hfserv e]; exact hσ e (by rw [← hfrun e]; exact he)

/-! ## Refill facts -/

/-- `refillPhase` moves a budget only at that domain's period boundary
(and never at boot), where it restores exactly `budgetQ` — the refund
term of the T6 potential is `Q` per boundary crossed and nothing more. -/
theorem refillPhase_budget_cases (m : Manifest) (σ : MachineState)
    (e : DomainId) :
    ((refillPhase m σ).doms e).budget = (σ.doms e).budget ∨
    (σ.cycle ≠ 0 ∧ σ.cycle % (m.doms e).periodP = 0 ∧
      ((refillPhase m σ).doms e).budget = (m.doms e).budgetQ) := by
  unfold refillPhase
  by_cases h0 : σ.cycle = 0
  · exact .inl (by simp [h0])
  · simp only [h0, if_false]
    by_cases hb : σ.cycle % (m.doms e).periodP = 0
    · exact .inr ⟨h0, hb, by simp [hb]⟩
    · exact .inl (by simp [hb])

open Loom.Isa SpecM Machines.Lnp64u.Isa Machines.Lnp64u.Isa.Wip

/-! ## Assembling the `run = halted → serving = none` invariant

`exec_hsn` sweeps the ISA: the 22 calm ops preserve run/serving pointwise
(`CalmLe`/`CalmOut.hsn`); `gate_call`/`gate_return` never halt anyone
(`gateCall_end_hsn`/`gateReturn_end_hsn`); `halt` nullifies serving as it
halts (`haltDom_hsn`). Lifted through `retire`/`corePhase`/`step` and finally
to every reachable state. -/

/-- A calm `ok` outcome carries the invariant (the ISA-sweep workhorse). -/
theorem CalmLe.hsn_ok {cd : DomainId} {mm : SpecM Unit} (h : CalmLe cd mm)
    {σ a σ'} (he : mm σ = .ok a σ') (hσ : HaltedServingNone σ) :
    HaltedServingNone σ' :=
  ((h σ).1 a σ' he).hsn hσ

/-- `gate_call` preserves the invariant on its `ok` (activation-entry) path:
the callee gains `serving` but stays running, the caller merely blocks. -/
theorem gatecall_hsn (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hrun : (σ.doms c.d).run = .running) (hσ : HaltedServingNone σ) :
    ∀ a σ', (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = .ok a σ' →
      HaltedServingNone σ' := by
  have body : ∀ (out : Res Unit),
      (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = out →
      ∀ a σ', out = .ok a σ' → HaltedServingNone σ' := by
    intro out hout
    unfold Machines.Lnp64u.Isa.Wip.gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 => rw [hcl] at hout; subst hout; exact fun a σ' h => by simp at h
    | fault f => rw [hcl] at hout; subst hout; exact fun a σ' h => by simp at h
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r; simp only at hout
        cases hk : e.kind with
        | mem base len perms => rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
                                exact fun a σ' h => by simp at h
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                           exact fun a σ' h => by simp at h
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                         exact fun a σ' h => by simp at h
            | ok u1 σ1 =>
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                               exact fun a σ' h => by simp at h
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                             exact fun a σ' h => by simp at h
                | ok u2 σ2 =>
                    have hc2 := require_cond _ _ σ hr2; have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                   exact fun a σ' h => by simp at h
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                 exact fun a σ' h => by simp at h
                    | ok u3 σ3 =>
                        have hc3 := require_cond _ _ σ hr3; have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                       exact fun a σ' h => by simp at h
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                     exact fun a σ' h => by simp at h
                        | ok u4 σ4 =>
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (Machines.Lnp64u.Isa.Wip.gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                           exact fun a σ' h => by simp at h
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                         exact fun a σ' h => by simp at h
                            | ok u5 σ5 =>
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact fun a σ' h => by simp at h
                                | err e6 τ => rw [htbh] at hout; subst hout
                                              exact fun a σ' h => by simp at h
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    obtain ⟨hfrun, hfserv, _, _⟩ :=
                                      transferByHandle_frame c.d cal _ σ argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom,
                                      SpecM.modify] at hout
                                    subst hout
                                    have hcalne : cal ≠ c.d := of_decide_eq_true hc2
                                    have hcalrunσ : (σ.doms cal).run = .running := of_decide_eq_true hc3
                                    intro a σ' h
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    exact gateCall_end_hsn τ σ c.d cal gid _ _ _ hcalne
                                      hfrun hfserv hcalrunσ hσ
  exact fun a σ' h => body _ rfl a σ' h

/-- `gate_return` preserves the invariant on its `ok` path: the returning
callee stays running, the resumed caller goes running; nobody halts. -/
theorem gatereturn_hsn (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hrun : (σ.doms c.d).run = .running) (hσ : HaltedServingNone σ) :
    ∀ a σ',
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = .ok a σ' →
      HaltedServingNone σ' := by
  have body : ∀ (out : Res Unit),
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = out →
      ∀ a σ', out = .ok a σ' → HaltedServingNone σ' := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none => rw [hserv] at hout; simp [SpecM.fatal] at hout; subst hout
              exact fun a σ' h => by simp at h
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none => simp only [hgact] at hout; simp [SpecM.fatal] at hout; subst hout
                  exact fun a σ' h => by simp at h
        | some act =>
            simp only [hgact] at hout; simp only [SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f => rw [htbh] at hout; subst hout; exact fun a σ' h => by simp at h
            | err e0 τ => rw [htbh] at hout; subst hout; exact fun a σ' h => by simp at h
            | ok reply τ =>
                rw [htbh] at hout
                obtain ⟨hfrun, hfserv, _, _⟩ := transferByHandle_frame c.d act.caller _ σ reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                  SpecM.setReg] at hout
                subst hout
                intro a σ' h
                simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                exact gateReturn_end_hsn τ σ c.d gid act reply _ hfrun hfserv hrun hserv hgact hwf hσ
  exact fun a σ' h => body _ rfl a σ' h

/-- **Every instruction preserves the invariant** (both outcomes). The err
arm is uniform (`TouchExec`'s err is `CalmOut`); the ok arm sweeps the ISA:
calm ops via `CalmLe`, the gate ops via `gatecall_hsn`/`gatereturn_hsn`,
`halt` via `haltDom_hsn`. -/
theorem exec_hsn (instr) (hmem : instr ∈ isa) (c : Ctx) (σ : MachineState)
    (hwf : Wf σ) (hrun : (σ.doms c.d).run = .running) (hσ : HaltedServingNone σ) :
    (∀ a σ', instr.sem.exec c σ = .ok a σ' → HaltedServingNone σ') ∧
    (∀ er σ', instr.sem.exec c σ = .err er σ' → HaltedServingNone σ') := by
  refine ⟨?_, fun er σ' he =>
    ((exec_touch instr hmem c σ hwf hrun).2 er σ' he).hsn hσ⟩
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  intro a σ' he
  rcases List.mem_append.mp hmem' with hb | hs
  · exact CalmLe.hsn_ok (cd := c.d) (base_calm instr hb c) he hσ
  · fin_cases hs
    case _ => -- cap_dup
      refine CalmLe.hsn_ok (cd := c.d) ?_ he hσ
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.reg _ _) fun dw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (match e.kind with
        | .mem base len perms =>
            Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h
        | .gate gid =>
            (Pure.pure (CapKind.gate gid) : SpecM CapKind) >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h)
      cases e.kind with
      | mem b l p =>
          exact CalmLe.bind (CalmLe.narrow _ _ _ _) fun kind =>
            CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
      | gate i =>
          exact CalmLe.bind (CalmLe.pure _) fun kind =>
            CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
    case _ => -- cap_drop
      refine CalmLe.hsn_ok (cd := c.d) ?_ he hσ
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (SpecM.get >>= fun σ0 =>
        SpecM.set ((((match σ0.parentOf c.d s with
            | some p => σ0.reparent ⟨c.d, s, g⟩ p
            | none => σ0.orphanChildren ⟨c.d, s, g⟩).clearSlot c.d s).sweepRegions).sweepMover) >>=
          fun _ => SpecM.setReg c.d c.op.rd 0)
      refine CalmLe.getD _ fun σ0 => ?_
      constructor
      · intro a σ' he
        cases hp : σ0.parentOf c.d s with
        | some p =>
            rw [hp] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            refine CalmOut.trans ?_
              (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
            exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
        | none =>
            rw [hp] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            refine CalmOut.trans ?_
              (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
            exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
      · intro er σ' he
        cases hp : σ0.parentOf c.d s with
        | some p => rw [hp] at he
                    simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
        | none => rw [hp] at he
                  simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
    case _ => -- cap_revoke
      refine CalmLe.hsn_ok (cd := c.d) ?_ he hσ
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (SpecM.require (decide (e.kind.cls = .mem)) .badCap >>= fun _ =>
        SpecM.get >>= fun σ0 =>
        SpecM.set (((σ0.destroyMarked (σ0.marks ⟨c.d, s, g⟩)).sweepRegions).sweepMover) >>=
        fun _ => SpecM.setReg c.d c.op.rd 0)
      refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
      refine CalmLe.getD _ fun σ0 => ?_
      constructor
      · intro a σ' he
        simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
        injection he with _ h2; subst h2
        refine CalmOut.trans ?_
          (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
        exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
      · intro er σ' he
        simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
    case _ => -- mem_grant
      refine CalmLe.hsn_ok (cd := c.d) ?_ he hσ
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.reg _ _) fun dw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (match e.kind with
        | .gate _ => (SpecM.raise .badCap : SpecM Unit)
        | .mem base len perms =>
            Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived (descDom dw) kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h)
      cases e.kind with
      | gate gid => exact CalmLe.raise _
      | mem base len perms =>
          exact CalmLe.bind (CalmLe.narrow _ _ _ _) fun kind =>
            CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
    case _ => -- map
      refine CalmLe.hsn_ok (cd := c.d) ?_ he hσ
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (match e.kind with
        | .gate _ => (SpecM.raise .badCap : SpecM Unit)
        | .mem base len perms =>
            SpecM.updDom c.d (fun ds =>
              { ds with regions :=
                  (Loom.Fun.update ds.regions
                    ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
                    (some { base := base, len := len, perms := perms
                            backing := ⟨c.d, s, g⟩ })) }) >>= fun _ =>
            SpecM.setReg c.d c.op.rd 0)
      cases e.kind with
      | gate gid => exact CalmLe.raise _
      | mem base len perms =>
          exact CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
            fun _ => CalmLe.setReg _ _ _
    case _ => -- unmap
      refine CalmLe.hsn_ok (cd := c.d) ?_ he hσ
      exact CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
        fun _ => CalmLe.setReg _ _ _
    case _ => -- gate_call
      exact gatecall_hsn c σ hwf hrun hσ a σ' he
    case _ => -- gate_return
      exact gatereturn_hsn c σ hwf hrun hσ a σ' he
    case _ => -- move
      refine CalmLe.hsn_ok (cd := c.d) ?_ he hσ
      refine CalmLe.getD _ fun σg => (?_ : CalmLe c.d _) σg
      refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
      refine CalmLe.bind (CalmLe.reg _ _) fun aw => ?_
      refine CalmLe.bind (CalmLe.load _ _) fun srcH => ?_
      refine CalmLe.bind (CalmLe.load _ _) fun dstH => ?_
      refine CalmLe.bind (CalmLe.load _ _) fun lenW => ?_
      refine CalmLe.bind (CalmLe.load _ _) fun stW => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun rs => ?_
      obtain ⟨ss, gs_, es⟩ := rs
      refine CalmLe.bind (CalmLe.capLive _ _) fun rd_ => ?_
      obtain ⟨sd, gd, ed⟩ := rd_
      show CalmLe c.d (match es.kind, ed.kind with
        | .mem sb sl sp, .mem db dl dp =>
            SpecM.require sp.r .permDenied >>= fun _ =>
            SpecM.require dp.w .permDenied >>= fun _ =>
            SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat))
              .outOfRange >>= fun _ =>
            SpecM.get >>= fun σ1 =>
            SpecM.demand (σ1.domCovers c.d (stW.setWidth 12)
              { r := false, w := true, x := false }) .memoryAuthority >>= fun _ =>
            SpecM.set ({ σ1 with mover :=
              (some { owner := c.d, src := ⟨c.d, ss, gs_⟩, dst := ⟨c.d, sd, gd⟩
                      srcCur := sb, dstCur := db, remaining := lenW.toNat
                      statusAddr := stW.setWidth 12 }) }) >>= fun _ =>
            SpecM.setReg c.d c.op.rd 0
        | _, _ => (SpecM.raise .badCap : SpecM Unit))
      cases es.kind with
      | gate gi =>
          cases ed.kind with
          | gate _ => exact CalmLe.raise _
          | mem db dl dp => exact CalmLe.raise _
      | mem sb sl sp =>
          cases ed.kind with
          | gate _ => exact CalmLe.raise _
          | mem db dl dp =>
              refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
              refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
              refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
              refine CalmLe.getD _ fun σ1 => ?_
              constructor
              · intro a σ' he
                by_cases hcov : σ1.domCovers c.d (stW.setWidth 12)
                    { r := false, w := true, x := false }
                · simp only [SpecM.demand, hcov, if_true, specM_pure, specM_bind, SpecM.set,
                    SpecM.setReg, SpecM.modify] at he
                  injection he with _ h2; subst h2
                  refine CalmOut.trans ?_
                    (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
                  exact CalmOut.of_doms_eq (fun e' => rfl)
                · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
              · intro er σ' he
                by_cases hcov : σ1.domCovers c.d (stW.setWidth 12)
                    { r := false, w := true, x := false }
                · simp [SpecM.demand, hcov, specM_pure, specM_bind, SpecM.set,
                    SpecM.setReg, SpecM.modify] at he
                · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
    case _ => -- yield
      refine CalmLe.hsn_ok (cd := c.d) ?_ he hσ
      exact CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
        fun _ => CalmLe.setReg _ _ _
    case _ => -- halt
      simp only [SpecM.modify] at he; injection he with _ h2; subst h2
      exact haltDom_hsn σ c.d 0 hσ

/-- The invariant transports across any transition that preserves every
domain's run and serving marks. -/
theorem hsn_of_doms_run_serving {σ σ' : MachineState}
    (hr : ∀ e, (σ'.doms e).run = (σ.doms e).run)
    (hs : ∀ e, (σ'.doms e).serving = (σ.doms e).serving)
    (hσ : HaltedServingNone σ) : HaltedServingNone σ' :=
  fun d hd => (hs d) ▸ hσ d ((hr d) ▸ hd)

/-- Charging a payer's budget preserves the invariant (budget is neither run
nor serving). -/
theorem setDomBudget_hsn (σ : MachineState) (p : DomainId) (n : Nat)
    (hσ : HaltedServingNone σ) :
    HaltedServingNone (σ.setDom p (fun ds => { ds with budget := ds.budget - n })) := by
  refine hsn_of_doms_run_serving (fun e => ?_) (fun e => ?_) hσ
  · unfold MachineState.setDom
    by_cases h : e = p
    · subst h; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ h]
  · unfold MachineState.setDom
    by_cases h : e = p
    · subst h; simp [Loom.Fun.update_same]
    · simp [Loom.Fun.update_ne _ _ _ _ h]

/-- `retire` preserves the invariant: the pc bump and errno write hit no
run/serving mark, the instruction effect is `exec_hsn`, decode failure and
faults are `haltDom_hsn`. -/
theorem retire_hsn (σ : MachineState) (d : DomainId) (w : Loom.Word32)
    (hwf : Wf σ) (hrun : (σ.doms d).run = .running) (hinf : σ.inflight = none)
    (hσ : HaltedServingNone σ) : HaltedServingNone (retire σ d w) := by
  unfold retire
  split
  · exact haltDom_hsn σ d _ hσ
  · rename_i instr hdec
    set σ1 := σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }) with hσ1
    have hall : ∀ (d' : DomainId),
        ((σ1.doms d').caps = (σ.doms d').caps) ∧
        ((σ1.doms d').lineage = (σ.doms d').lineage) ∧
        ((σ1.doms d').slotGen = (σ.doms d').slotGen) ∧
        ((σ1.doms d').regions = (σ.doms d').regions) ∧
        ((σ1.doms d').run = (σ.doms d').run) ∧
        ((σ1.doms d').serving = (σ.doms d').serving) ∧
        ((σ1.doms d').regs = (σ.doms d').regs) ∧
        ((σ1.doms d').cause = (σ.doms d').cause) := by
      intro d'; rw [hσ1]; unfold MachineState.setDom
      by_cases hp : d' = d
      · subst hp; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hp]
    have hwf1 : Wf σ1 := by
      refine wf_of_skeleton_sameGates σ σ1
        (fun d' => (hall d').1) (fun d' => (hall d').2.1) (fun d' => (hall d').2.2.1)
        (fun d' => (hall d').2.2.2.1) (fun d' => (hall d').2.2.2.2.1)
        (fun d' => (hall d').2.2.2.2.2.1) rfl rfl ?_ hwf
      intro fl' hfl'; rw [show σ1.inflight = σ.inflight from rfl, hinf] at hfl'
      exact absurd hfl' (by simp)
    have hrun1 : (σ1.doms d).run = .running := by rw [(hall d).2.2.2.2.1]; exact hrun
    have hσ1hsn : HaltedServingNone σ1 :=
      hsn_of_doms_run_serving (fun e => (hall e).2.2.2.2.1)
        (fun e => (hall e).2.2.2.2.2.1) hσ
    obtain ⟨hok, herr⟩ := exec_hsn instr (Loom.Isa.decode_mem isa hdec)
      { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 hwf1 hrun1 hσ1hsn
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
    | ok a σ' => simp only [hexr]; exact hok a σ' hexr
    | err er σ' =>
        simp only [hexr]
        refine hsn_of_doms_run_serving (fun e => ?_) (fun e => ?_) (herr er σ' hexr)
        · unfold MachineState.setDom
          by_cases hp : e = d
          · subst hp; simp [Loom.Fun.update_same, setReg_run]
          · simp [Loom.Fun.update_ne _ _ _ _ hp]
        · unfold MachineState.setDom
          by_cases hp : e = d
          · subst hp; simp [Loom.Fun.update_same, setReg_serving]
          · simp [Loom.Fun.update_ne _ _ _ _ hp]
    | fault f => simp only [hexr]; exact haltDom_hsn σ d _ hσ

/-- The core phase preserves the invariant: countdown/idle/stall leave doms
alone, issues touch only budgets, retirements are `retire_hsn`, halts are
`haltDom_hsn`. -/
theorem corePhase_hsn (m : Manifest) (σ : MachineState) (hwf : Wf σ)
    (hσ : HaltedServingNone σ) : HaltedServingNone (corePhase m σ) := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · simp only [hc, if_true]
        have hwfI : Wf { σ with inflight := none } :=
          wf_of_skeleton_sameGates σ { σ with inflight := none }
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) rfl rfl (by simp) hwf
        exact retire_hsn { σ with inflight := none } fl.dom fl.word hwfI
          (hwf.inflight_running fl hinf) rfl hσ
      · simp only [hc, if_false]; exact hσ
  | none =>
      simp only []
      split
      · exact hσ
      · rename_i d hsched
        have hdrun : (σ.doms d).run = .running := schedule_running m σ d hsched
        split
        · exact haltDom_hsn σ d _ hσ
        · rename_i w hfetch
          split
          · exact haltDom_hsn σ d _ hσ
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              cases hservd : (σ.doms d).serving with
              | none =>
                  simp only [hservd]
                  exact setDomBudget_hsn σ (σ.payer d) _ hσ
              | some g =>
                  simp only [hservd]
                  cases hactg : (σ.gates g).act with
                  | none => exact haltDom_hsn σ d _ hσ
                  | some a =>
                      simp only [hactg]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        exact setDomBudget_hsn σ (σ.payer d) _ hσ
                      · simp only [hdon, if_false]
                        exact haltDom_hsn σ d _ hσ
            · simp only [hbud, if_false]; exact hσ

/-- One cycle preserves the invariant. -/
theorem step_hsn (m : Manifest) (σ : MachineState) (hwf : Wf σ)
    (hσ : HaltedServingNone σ) : HaltedServingNone (step m σ) := by
  have hc : HaltedServingNone (corePhase m (refillPhase m σ)) :=
    corePhase_hsn m _ (refillPhase_preserves_wf m σ hwf) (refillPhase_hsn m σ hσ)
  refine hsn_of_doms_run_serving (fun e => ?_) (fun e => ?_) hc
  · rw [congrFun (step_doms m σ) e]
  · rw [congrFun (step_doms m σ) e]

/-- **The `run = halted → serving = none` invariant** (T6 obligation 1): in
every reachable state, a halted domain holds no serving mark — no
half-halted serving chain exists. Unconditional over all reachable states of
any well-formed manifest. -/
theorem halted_serving_none_invariant (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant HaltedServingNone := by
  intro σ hreach
  induction hreach with
  | init hi => exact hi ▸ initState_hsn m
  | @step s s' hprev hstep ih =>
      have hst : step m s = s' := hstep
      exact hst ▸ step_hsn m s (wfa_invariant m hwf s hprev).1 ih

/-! ## The cycle counter (T6 obligation 3 support)

No instruction's `exec` ever writes the `cycle` counter: every state
primitive touches `doms`/`gates`/`mover`/`mem` only. `CycleEq` is the
`SpecM`-level combinator (mirroring `InflightEq`) carrying this through the
exec semantics of all 25 opcodes; `retire_cycle`/`corePhase_cycle` lift it
to the phase glue, and `step_cycle` is the whole-cycle counter equation the
T6 potential counting is stated against. -/

@[simp] theorem setDom_cycle (σ : MachineState) (d : DomainId)
    (f : DomainState → DomainState) : (σ.setDom d f).cycle = σ.cycle := rfl

@[simp] theorem write_cycle (σ : MachineState) (a : Addr) (v : Loom.Word32) :
    (σ.write a v).cycle = σ.cycle := rfl

@[simp] theorem reparent_cycle (σ : MachineState) (old new : CapRef) :
    (σ.reparent old new).cycle = σ.cycle := rfl

@[simp] theorem orphanChildren_cycle (σ : MachineState) (old : CapRef) :
    (σ.orphanChildren old).cycle = σ.cycle := rfl

@[simp] theorem clearSlot_cycle (σ : MachineState) (d : DomainId) (s : Slot) :
    (σ.clearSlot d s).cycle = σ.cycle := rfl

@[simp] theorem destroyMarked_cycle (σ : MachineState) (mk : DomainId → Slot → Bool) :
    (σ.destroyMarked mk).cycle = σ.cycle := rfl

@[simp] theorem sweepRegions_cycle (σ : MachineState) :
    σ.sweepRegions.cycle = σ.cycle := rfl

@[simp] theorem sweepMover_cycle (σ : MachineState) : σ.sweepMover.cycle = σ.cycle := by
  unfold MachineState.sweepMover
  cases σ.mover with
  | none => rfl
  | some job =>
      by_cases h1 : σ.liveRef job.src && σ.liveRef job.dst
      · simp [h1]
      · simp only [h1, if_false]
        by_cases h2 : ({ σ with mover := none } : MachineState).domCovers job.owner
            job.statusAddr { r := false, w := true, x := false }
        · simp [h2, MachineState.write]
        · simp [h2]

/-- `haltDom` never touches `cycle`: `haltBase` is a `setDom`, and the gate
unwind is a gates-record update plus a `setDom`. -/
theorem haltDom_cycle (σ : MachineState) (d : DomainId) (c : Loom.Word32) :
    (σ.haltDom d c).cycle = σ.cycle := by
  unfold MachineState.haltDom
  split
  · rfl
  · split
    · rfl
    · rfl

/-- A `SpecM` computation leaves `cycle` untouched on every `ok`/`err`
outcome (`fault` carries no state). -/
def CycleEq {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', mm σ = .ok a σ' → σ'.cycle = σ.cycle) ∧
       (∀ e σ', mm σ = .err e σ' → σ'.cycle = σ.cycle)

theorem CycleEq.of_preserves {α : Type} (mm : SpecM α)
    (hok : ∀ σ a σ', mm σ = .ok a σ' → σ'.cycle = σ.cycle)
    (herr : ∀ σ e σ', mm σ = .err e σ' → σ'.cycle = σ.cycle) :
    CycleEq mm :=
  fun σ => ⟨hok σ, herr σ⟩

theorem CycleEq.pure {α : Type} (a : α) : CycleEq (Pure.pure a : SpecM α) :=
  CycleEq.of_preserves _
    (fun σ a' σ' he => by rw [specM_pure] at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he => by rw [specM_pure] at he; simp at he)

theorem CycleEq.bind {α β : Type} {m : SpecM α} {f : α → SpecM β}
    (hm : CycleEq m) (hf : ∀ a, CycleEq (f a)) : CycleEq (m >>= f) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 rw [(hf a σ1).1 b σ' he, (hm σ).1 a σ1 hmσ]
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : m σ with
    | ok a σ1 => rw [hmσ] at he
                 rw [(hf a σ1).2 e σ' he, (hm σ).1 a σ1 hmσ]
    | err e1 σ1 => rw [hmσ] at he; injection he with h1 h2; subst h2; exact (hm σ).2 e1 σ1 hmσ
    | fault g => rw [hmσ] at he; simp at he

theorem CycleEq.iteBool {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : CycleEq m1) (h2 : CycleEq m2) : CycleEq (if b then m1 else m2) := by
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false]
  · exact h2
  · exact h1

theorem CycleEq.reg (d : DomainId) (r : RegId) : CycleEq (SpecM.reg d r) :=
  CycleEq.of_preserves _
    (fun σ a σ' he => by unfold SpecM.reg at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he => by unfold SpecM.reg at he; simp at he)

theorem CycleEq.raise {α : Type} (e : Errno) : CycleEq (SpecM.raise e : SpecM α) :=
  CycleEq.of_preserves _
    (fun σ a σ' he => by unfold SpecM.raise at he; simp at he)
    (fun σ e' σ' he => by unfold SpecM.raise at he; injection he with _ h2; subst h2; rfl)

theorem CycleEq.require (cond : Bool) (e : Errno) : CycleEq (SpecM.require cond e) :=
  CycleEq.of_preserves _
    (fun σ a σ' he => by rw [require_ok cond e σ he])
    (fun σ e' σ' he => by rw [require_err_state cond e σ he])

theorem CycleEq.demand (cond : Bool) (f : Fault) : CycleEq (SpecM.demand cond f) :=
  CycleEq.of_preserves _
    (fun σ a σ' he => by rw [demand_ok cond f σ he])
    (fun σ e σ' he => by
      unfold SpecM.demand at he; split at he
      · simp [specM_pure] at he
      · simp [SpecM.fatal] at he)

theorem CycleEq.load (d : DomainId) (a : Addr) : CycleEq (SpecM.load d a) :=
  CycleEq.of_preserves _
    (fun σ v σ' he => by rw [load_ok d a σ he])
    (fun σ e σ' he => by rw [load_err_state d a σ he])

theorem CycleEq.get : CycleEq SpecM.get :=
  CycleEq.of_preserves _
    (fun σ a σ' he => by unfold SpecM.get at he; injection he with _ h2; subst h2; rfl)
    (fun σ e σ' he => by unfold SpecM.get at he; simp at he)

/-- A `modify` whose function preserves `cycle` is `CycleEq`. -/
theorem CycleEq.modifyPres (f : MachineState → MachineState)
    (hf : ∀ σ, (f σ).cycle = σ.cycle) : CycleEq (SpecM.modify f) :=
  CycleEq.of_preserves _
    (fun σ a σ' he => by
      unfold SpecM.modify at he; injection he with _ h2; subst h2; exact hf σ)
    (fun σ e σ' he => by unfold SpecM.modify at he; simp at he)

theorem CycleEq.setReg (d : DomainId) (r : RegId) (v : Loom.Word32) :
    CycleEq (SpecM.setReg d r v) :=
  CycleEq.modifyPres _ (fun _ => rfl)

theorem CycleEq.updDom (d : DomainId) (f : DomainState → DomainState) :
    CycleEq (SpecM.updDom d f) :=
  CycleEq.modifyPres _ (fun _ => rfl)

theorem CycleEq.store (d : DomainId) (a : Addr) (v : Loom.Word32) :
    CycleEq (SpecM.store d a v) := by
  intro σ; unfold SpecM.store; refine ⟨?_, ?_⟩
  · intro x σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2; subst h2; rfl
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

theorem CycleEq.halt (c : Ctx) :
    CycleEq (SpecM.modify (fun σ => σ.haltDom c.d 0)) :=
  CycleEq.modifyPres _ (fun σ => haltDom_cycle σ c.d 0)

theorem CycleEq.capLive (d : DomainId) (hw : Loom.Word32) :
    CycleEq (Machines.Lnp64u.Isa.capLive d hw) :=
  CycleEq.of_preserves _
    (fun σ r σ' he => by rw [(Machines.Lnp64u.Isa.Wip.capLive_ok d hw σ he).1])
    (fun σ e σ' he => by rw [Machines.Lnp64u.Isa.Wip.capLive_err_state d hw σ he])

theorem CycleEq.narrow (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32) :
    CycleEq (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  CycleEq.of_preserves _
    (fun σ k σ' he => by rw [(Machines.Lnp64u.Isa.Wip.narrow_ok base len perms dw σ he).1])
    (fun σ e σ' he => by rw [Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms dw σ he])

theorem CycleEq.allocDerived (owner : DomainId) (kind : CapKind) (parent : CapRef) :
    CycleEq (Machines.Lnp64u.Isa.allocDerived owner kind parent) := by
  intro σ; refine ⟨?_, ?_⟩
  · intro hw σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp [SpecM.raise] at he
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp [SpecM.raise] at he
        | some lc =>
            rw [hfc] at he
            simp only [SpecM.set, specM_bind, specM_pure] at he
            injection he with _ h2
            rw [← h2]; rfl
  · intro e σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
        | some lc => rw [hfc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- **The base opcodes never touch `cycle`.** Their `exec` only writes
regs/pc/memory. -/
theorem base_cycle_eq : ∀ instr ∈ Machines.Lnp64u.Isa.base, ∀ c : Ctx,
    CycleEq (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.setReg _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.setReg _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.setReg _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.setReg _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.setReg _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.setReg _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.setReg _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.setReg _ _ _)
  · exact CycleEq.setReg _ _ _
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.load _ _) (fun _ => CycleEq.setReg _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.store _ _ _))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.iteBool _ (CycleEq.updDom _ _) (CycleEq.pure ())))
  · exact CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.bind (CycleEq.reg _ _) (fun _ => CycleEq.iteBool _ (CycleEq.updDom _ _) (CycleEq.pure ())))
  · exact CycleEq.bind (CycleEq.reg _ _)
      (fun _ => CycleEq.bind (CycleEq.setReg _ _ _) (fun _ => CycleEq.updDom _ _))

/-- **`transferCap` never touches `cycle`**: install-at-recipient, reparent,
`clearSlot`, and both sweeps are `doms`/`mover`/`mem`-level only. -/
theorem transferCap_cycle (σ : MachineState) (from_ : DomainId) (s : Slot) (to_ : DomainId)
    (τ : MachineState) (ref : CapRef) (h : σ.transferCap from_ s to_ = some (τ, ref)) :
    τ.cycle = σ.cycle := by
  unfold MachineState.transferCap at h
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hfs : σ.freeSlot to_ with
      | none => rw [hfs] at h; simp at h
      | some s2 =>
          rw [hfs] at h; simp only [Option.bind_some] at h
          have key : ∀ (σ₁ : MachineState), σ₁.cycle = σ.cycle →
              some (((((σ₁.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
                ⟨to_, s2, (σ.doms to_).slotGen s2⟩).clearSlot from_ s).sweepRegions).sweepMover),
                (⟨to_, s2, (σ.doms to_).slotGen s2⟩ : CapRef))
                = some (τ, ref) →
              τ.cycle = σ.cycle := by
            intro σ₁ hpre heq
            injection heq with heq; injection heq with hτ _; subst hτ
            rw [sweepMover_cycle, sweepRegions_cycle, clearSlot_cycle,
                reparent_cycle]
            exact hpre
          cases hl : e.lineage with
          | none =>
              rw [hl] at h; simp only [Option.pure_def, Option.bind_some] at h
              exact key (σ.setDom to_ (fun ds =>
                  { ds with caps := Loom.Fun.update ds.caps s2 (some { kind := e.kind, lineage := none }) }))
                rfl h
          | some l =>
              rw [hl] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
              cases hc : (σ.doms from_).lineage l with
              | none => rw [hc] at h; simp at h
              | some cell =>
                  rw [hc] at h; simp only [Option.bind_some] at h
                  cases hfc : σ.freeCell to_ with
                  | none => rw [hfc] at h; simp at h
                  | some l' =>
                      rw [hfc] at h; simp only [Option.pure_def, Option.bind_some] at h
                      exact key (σ.setDom to_ (fun ds =>
                          { ds with
                            caps := Loom.Fun.update ds.caps s2 (some { kind := e.kind, lineage := some l' })
                            lineage := Loom.Fun.update ds.lineage l' (some cell) }))
                        rfl h

theorem transferByHandle_cycle_eq (d to_ : DomainId) (hw : Loom.Word32) :
    CycleEq (Machines.Lnp64u.Isa.transferByHandle d to_ hw) := by
  intro σ
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    exact ⟨fun a σ' he => by
        simp only [specM_pure] at he; obtain ⟨_, rfl⟩ := he; rfl,
      fun e σ' he => by simp [specM_pure] at he⟩
  · simp only [if_neg hz, specM_bind]
    constructor
    · intro a σ' he
      cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none => rw [htc] at he; simp [SpecM.raise] at he
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp only [SpecM.set, specM_bind, specM_pure] at he
              injection he with _ h2; subst h2
              exact transferCap_cycle σ d sslot to_ σ2 ref htc
    · intro er σ' he
      cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state d _ σ hcl; rw [hcl] at he
          injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none =>
              rw [htc] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2; rfl
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- `gate_call` never touches `cycle`: the capability transfer preserves it
and the activation / serving / run bookkeeping is `gates`/`doms`-level. -/
theorem gatecall_cycle_eq (c : Ctx) : CycleEq (Machines.Lnp64u.Isa.Wip.gateCallExec c) := by
  intro σ
  have body : ∀ (out : Res Unit), Machines.Lnp64u.Isa.Wip.gateCallExec c σ = out →
      (∀ a σ', out = .ok a σ' → σ'.cycle = σ.cycle) ∧
      (∀ e σ', out = .err e σ' → σ'.cycle = σ.cycle) := by
    intro out hout
    unfold Machines.Lnp64u.Isa.Wip.gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
        rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hs; rfl⟩
    | fault f => rw [hcl] at hout; subst hout
                 exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r; simp only at hout
        cases hk : e.kind with
        | mem base len perms =>
            rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
              simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; rfl⟩
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 => have hst := require_err_state _ _ σ hr1; rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | ok u1 σ1 =>
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 => have hst := require_err_state _ _ σ hr2; rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                               exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                 simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                | ok u2 σ2 =>
                    have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 => have hst := require_err_state _ _ σ hr3; rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                   exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                     simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                    | ok u3 σ3 =>
                        have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 => have hst := require_err_state _ _ σ hr4; rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                       exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                         simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                        | ok u4 σ4 =>
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (Machines.Lnp64u.Isa.Wip.gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 => have hst := require_err_state _ _ σ hr5; rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                           exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                             simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; subst hst; rfl⟩
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout; exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                            | ok u5 σ5 =>
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
                                | err e6 τ =>
                                    rw [htbh] at hout; subst hout
                                    have hτ := (transferByHandle_cycle_eq c.d cal _ σ).2 e6 τ htbh
                                    exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    have hτ := (transferByHandle_cycle_eq c.d cal _ σ).1 argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify] at hout
                                    subst hout
                                    refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    exact hτ
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩

/-- `gate_return` never touches `cycle`: the reply transfer preserves it and
the context restore is `gates`/`doms`-level. -/
theorem gatereturn_cycle_eq (c : Ctx) :
    CycleEq ((do
      let σ0 ← SpecM.get
      match (σ0.doms c.d).serving with
      | none => SpecM.fatal .protocol
      | some gid =>
          match (σ0.gates gid).act with
          | none => SpecM.fatal .protocol
          | some act => do
              let rw ← SpecM.reg c.d c.op.rs1
              let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
              let σ1 ← SpecM.get
              SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
              SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
              SpecM.updDom act.caller (fun ds => { ds with run := .running })
              SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) := by
  intro σ
  have body : ∀ (out : Res Unit),
      ((do
        let σ0 ← SpecM.get
        match (σ0.doms c.d).serving with
        | none => SpecM.fatal .protocol
        | some gid =>
            match (σ0.gates gid).act with
            | none => SpecM.fatal .protocol
            | some act => do
                let rw ← SpecM.reg c.d c.op.rs1
                let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                let σ1 ← SpecM.get
                SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                SpecM.updDom act.caller (fun ds => { ds with run := .running })
                SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = out →
      (∀ a σ', out = .ok a σ' → σ'.cycle = σ.cycle) ∧
      (∀ e σ', out = .err e σ' → σ'.cycle = σ.cycle) := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none => rw [hserv] at hout; simp only [SpecM.fatal] at hout; subst hout
              exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none => simp only [hgact] at hout; simp only [SpecM.fatal] at hout; subst hout
                  exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
        | some act =>
            simp only [hgact, SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f => rw [htbh] at hout; subst hout
                         exact ⟨fun a σ' h => by simp at h, fun e σ' h => by simp at h⟩
            | err e1 τ =>
                rw [htbh] at hout; subst hout
                have hτ := (transferByHandle_cycle_eq c.d act.caller _ σ).2 e1 τ htbh
                exact ⟨fun a σ' h => by simp at h, fun e σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hτ⟩
            | ok reply τ =>
                rw [htbh] at hout
                have hτ := (transferByHandle_cycle_eq c.d act.caller _ σ).1 reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                           SpecM.setReg] at hout
                subst hout
                refine ⟨fun a σ' h => ?_, fun e σ' h => by simp at h⟩
                simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                exact hτ
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun e σ' h => (body _ h).2 e σ' rfl⟩

/-- `move` never touches `cycle`: a read-only prefix, then a `mover`-record
write plus the `rd` write-back. -/
theorem move_cycle_eq (c : Ctx) : CycleEq (Machines.Lnp64u.Isa.Wip.moveExec c) := by
  intro σ; refine ⟨fun x σ' he => ?_, fun x σ' he => ?_⟩
  ·
    simp only [Machines.Lnp64u.Isa.Wip.moveExec, SpecM.get, specM_bind] at he
    cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
    | err e0 σ0 => rw [hr0] at he; simp at he
    | fault f => rw [hr0] at he; simp at he
    | ok u0 σ0 =>
        have hh0 := require_ok _ _ σ hr0; subst σ0
        rw [hr0] at he; simp only [SpecM.reg] at he
        set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
        cases hl1 : load c.d B σ with
        | err e σe => rw [hl1] at he; simp at he
        | fault f => rw [hl1] at he; simp at he
        | ok srcH σ1 =>
            have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
            cases hl2 : load c.d (B + 1) σ with
            | err e σe => rw [hl2] at he; simp at he
            | fault f => rw [hl2] at he; simp at he
            | ok dstH σ2 =>
                have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
                cases hl3 : load c.d (B + 2) σ with
                | err e σe => rw [hl3] at he; simp at he
                | fault f => rw [hl3] at he; simp at he
                | ok lenW σ3 =>
                    have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                    cases hl4 : load c.d (B + 3) σ with
                    | err e σe => rw [hl4] at he; simp at he
                    | fault f => rw [hl4] at he; simp at he
                    | ok stW σ4 =>
                        have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                        cases hc1 : Machines.Lnp64u.Isa.capLive c.d srcH σ with
                        | err e σe => rw [hc1] at he; simp at he
                        | fault f => rw [hc1] at he; simp at he
                        | ok rs σ5 =>
                            have hcs := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hc1
                            obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                            rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                            cases hc2 : Machines.Lnp64u.Isa.capLive c.d dstH σ with
                            | err e σe => rw [hc2] at he; simp at he
                            | fault f => rw [hc2] at he; simp at he
                            | ok rdd σ6 =>
                                have hcd := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hc2
                                obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                                rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                                cases hks : es.kind with
                                | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                            | gate _ => rw [hkd] at he; simp [SpecM.raise] at he
                                            | mem _ _ _ => rw [hkd] at he; simp [SpecM.raise] at he
                                | mem sb sl sp =>
                                    cases hkd : ed.kind with
                                    | gate _ => rw [hks, hkd] at he; simp [SpecM.raise] at he
                                    | mem db dl dp =>
                                        rw [hks, hkd] at he; simp only [specM_bind] at he
                                        cases hq1 : SpecM.require sp.r .permDenied σ with
                                        | err e σe => rw [hq1] at he; simp at he
                                        | fault f => rw [hq1] at he; simp at he
                                        | ok _ σq1 =>
                                            have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                            cases hq2 : SpecM.require dp.w .permDenied σ with
                                            | err e σe => rw [hq2] at he; simp at he
                                            | fault f => rw [hq2] at he; simp at he
                                            | ok _ σq2 =>
                                                have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                                cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                                | err e σe => rw [hq3] at he; simp at he
                                                | fault f => rw [hq3] at he; simp at he
                                                | ok _ σq3 =>
                                                    have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                    cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                    | err e σe => rw [hd] at he; simp at he
                                                    | fault f => rw [hd] at he; simp at he
                                                    | ok _ σdd =>
                                                        have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                        simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
                                                        injection he with _ h2; subst h2
                                                        rfl
  ·
    simp only [Machines.Lnp64u.Isa.Wip.moveExec, SpecM.get, specM_bind] at he
    cases hr0 : SpecM.require σ.mover.isNone .moverBusy σ with
    | err e0 σ0 => have hq := require_err_state _ _ σ hr0; rw [hr0] at he; injection he with _ h2; subst h2; subst hq; rfl
    | fault f => rw [hr0] at he; simp at he
    | ok u0 σ0 =>
        have hh0 := require_ok _ _ σ hr0; subst σ0
        rw [hr0] at he; simp only [SpecM.reg] at he
        set B : Addr := ((σ.doms c.d).reg c.op.rs1).setWidth 12 with hB
        cases hl1 : load c.d B σ with
        | err e σe => have hq := load_err_state _ _ σ hl1; rw [hl1] at he; injection he with _ h2; subst h2; subst hq; rfl
        | fault f => rw [hl1] at he; simp at he
        | ok srcH σ1 =>
            have hh1 := load_ok _ _ σ hl1; subst σ1; rw [hl1] at he; simp only [specM_bind] at he
            cases hl2 : load c.d (B + 1) σ with
            | err e σe => have hq := load_err_state _ _ σ hl2; rw [hl2] at he; injection he with _ h2; subst h2; subst hq; rfl
            | fault f => rw [hl2] at he; simp at he
            | ok dstH σ2 =>
                have hh2 := load_ok _ _ σ hl2; subst σ2; rw [hl2] at he; simp only [specM_bind] at he
                cases hl3 : load c.d (B + 2) σ with
                | err e σe => have hq := load_err_state _ _ σ hl3; rw [hl3] at he; injection he with _ h2; subst h2; subst hq; rfl
                | fault f => rw [hl3] at he; simp at he
                | ok lenW σ3 =>
                    have hh3 := load_ok _ _ σ hl3; subst σ3; rw [hl3] at he; simp only [specM_bind] at he
                    cases hl4 : load c.d (B + 3) σ with
                    | err e σe => have hq := load_err_state _ _ σ hl4; rw [hl4] at he; injection he with _ h2; subst h2; subst hq; rfl
                    | fault f => rw [hl4] at he; simp at he
                    | ok stW σ4 =>
                        have hh4 := load_ok _ _ σ hl4; subst σ4; rw [hl4] at he; simp only [specM_bind] at he
                        cases hc1 : Machines.Lnp64u.Isa.capLive c.d srcH σ with
                        | err e σe => have hq := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hc1; rw [hc1] at he; injection he with _ h2; subst h2; subst hq; rfl
                        | fault f => rw [hc1] at he; simp at he
                        | ok rs σ5 =>
                            have hcs := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hc1
                            obtain ⟨hhs, hslive⟩ := hcs; subst σ5
                            rw [hc1] at he; obtain ⟨ss, gs_, es⟩ := rs; simp only at he hslive
                            cases hc2 : Machines.Lnp64u.Isa.capLive c.d dstH σ with
                            | err e σe => have hq := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hc2; rw [hc2] at he; injection he with _ h2; subst h2; subst hq; rfl
                            | fault f => rw [hc2] at he; simp at he
                            | ok rdd σ6 =>
                                have hcd := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hc2
                                obtain ⟨hhd, hdlive⟩ := hcd; subst σ6
                                rw [hc2] at he; obtain ⟨sd, gd, ed⟩ := rdd; simp only at he hdlive
                                cases hks : es.kind with
                                | gate _ => rw [hks] at he; cases hkd : ed.kind with
                                            | gate _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
                                            | mem _ _ _ => rw [hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
                                | mem sb sl sp =>
                                    cases hkd : ed.kind with
                                    | gate _ => rw [hks, hkd] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
                                    | mem db dl dp =>
                                        rw [hks, hkd] at he; simp only [specM_bind] at he
                                        cases hq1 : SpecM.require sp.r .permDenied σ with
                                        | err e σe => have hq := require_err_state _ _ σ hq1; rw [hq1] at he; injection he with _ h2; subst h2; subst hq; rfl
                                        | fault f => rw [hq1] at he; simp at he
                                        | ok _ σq1 =>
                                            have := require_ok _ _ σ hq1; subst σq1; rw [hq1] at he; simp only [specM_bind] at he
                                            cases hq2 : SpecM.require dp.w .permDenied σ with
                                            | err e σe => have hq := require_err_state _ _ σ hq2; rw [hq2] at he; injection he with _ h2; subst h2; subst hq; rfl
                                            | fault f => rw [hq2] at he; simp at he
                                            | ok _ σq2 =>
                                                have := require_ok _ _ σ hq2; subst σq2; rw [hq2] at he; simp only [specM_bind] at he
                                                cases hq3 : SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat)) .outOfRange σ with
                                                | err e σe => have hq := require_err_state _ _ σ hq3; rw [hq3] at he; injection he with _ h2; subst h2; subst hq; rfl
                                                | fault f => rw [hq3] at he; simp at he
                                                | ok _ σq3 =>
                                                    have := require_ok _ _ σ hq3; subst σq3; rw [hq3] at he; simp only [SpecM.get, specM_bind] at he
                                                    cases hd : SpecM.demand (σ.domCovers c.d (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority σ with
                                                    | err e σe => exact absurd hd (by simp [SpecM.demand]; split <;> simp [SpecM.fatal])
                                                    | fault f => rw [hd] at he; simp at he
                                                    | ok _ σdd =>
                                                        have := demand_ok _ _ σ hd; subst σdd; rw [hd] at he
                                                        simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he

/-- **The system opcodes never touch `cycle`** — the capability/gate/Mover
kernel operations are `doms`/`gates`/`mover`/`mem`-level only. -/
theorem system_cycle_eq : ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ c : Ctx,
    CycleEq (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  case _ => -- cap_dup
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          have hstep : ∀ (kd : CapKind) (hh : Loom.Word32) (τ : MachineState),
              Machines.Lnp64u.Isa.allocDerived c.d kd ⟨c.d, sl, gg⟩ σ = .ok hh τ →
              (SpecM.setReg c.d c.op.rd hh) τ = .ok a σ' →
              σ'.cycle = σ.cycle := by
            intro kd hh τ hal hsr
            have h1 := (CycleEq.allocDerived c.d kd ⟨c.d, sl, gg⟩ σ).1 hh τ hal
            have h2 := (CycleEq.setReg c.d c.op.rd hh τ).1 a σ' hsr
            exact h2.trans h1
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : Machines.Lnp64u.Isa.allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => rw [hal] at he; simp at he
              | fault f => rw [hal] at he; simp at he
              | ok hh τ => rw [hal] at he; exact hstep _ hh τ hal he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : Machines.Lnp64u.Isa.narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : Machines.Lnp64u.Isa.allocDerived c.d kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => rw [hal] at he; simp at he
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; exact hstep _ hh τ hal he
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g =>
              rw [hk] at he; simp only [specM_pure, specM_bind] at he
              cases hal : Machines.Lnp64u.Isa.allocDerived c.d (.gate g) ⟨c.d, sl, gg⟩ σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state c.d _ _ σ hal
                             rw [hal] at he; injection he with _ h2; subst h2; subst hs; rfl
              | fault f => rw [hal] at he; simp at he
              | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : Machines.Lnp64u.Isa.narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms _ σ hn
                             rw [hn] at he; injection he with _ h2; subst h2; subst hs; rfl
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : Machines.Lnp64u.Isa.allocDerived c.d kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state c.d _ _ σ hal
                                 rw [hal] at he; injection he with _ h2; subst h2; subst hs; rfl
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_drop
    intro σ; constructor
    · intro a σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, _⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind] at he
          have key : ∀ (σ' : MachineState), σ'.cycle = σ.cycle →
              (SpecM.set (((σ'.clearSlot c.d sl).sweepRegions).sweepMover) >>=
                fun _ => SpecM.setReg c.d c.op.rd 0) σ = .ok a σ'' →
              σ''.cycle = σ.cycle := by
            intro σ' hpre hset
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at hset
            injection hset with _ h2; subst h2
            rw [setDom_cycle, sweepMover_cycle, sweepRegions_cycle, clearSlot_cycle]
            exact hpre
          cases hp : σ.parentOf c.d sl with
          | some p => rw [hp] at he
                      exact key _ (reparent_cycle σ _ _) he
          | none => rw [hp] at he
                    exact key _ (orphanChildren_cycle σ _) he
    · intro e σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, _⟩ := r; simp only at he
          simp only [SpecM.get, specM_bind] at he
          cases hp : σ.parentOf c.d sl with
          | some p => rw [hp] at he; simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          | none => rw [hp] at he; simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
  case _ => -- cap_revoke
    intro σ; constructor
    · intro a σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.require] at he
          by_cases hcls : decide (e.kind.cls = .mem) = true
          · simp only [hcls, if_true, specM_pure, specM_bind, SpecM.get] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            rw [setDom_cycle, sweepMover_cycle, sweepRegions_cycle,
                destroyMarked_cycle]
          · rw [if_neg hcls] at he; simp [SpecM.raise, specM_bind] at he
    · intro e σ'' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          simp only [SpecM.require] at he
          by_cases hcls : decide (e.kind.cls = .mem) = true
          · simp only [hcls, if_true, specM_pure, specM_bind, SpecM.get] at he
            simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
          · rw [if_neg hcls] at he; simp only [SpecM.raise, specM_bind] at he
            injection he with _ h2; subst h2; rfl
  case _ => -- mem_grant
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : Machines.Lnp64u.Isa.narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => rw [hn] at he; simp at he
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : Machines.Lnp64u.Isa.allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => rw [hal] at he; simp at he
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ =>
                      rw [hal] at he
                      have h1 := (CycleEq.allocDerived (descDom _) kd ⟨c.d, sl, gg⟩ σ).1 hh τ hal
                      have h2 := (CycleEq.setReg c.d c.op.rd hh τ).1 a σ' he
                      exact h2.trans h1
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
          | mem base len perms =>
              rw [hk] at he; simp only [specM_bind] at he
              cases hn : Machines.Lnp64u.Isa.narrow base len perms ((σ.doms c.d).reg c.op.rs2) σ with
              | err e1 σ1 => have hs := Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms _ σ hn
                             rw [hn] at he; injection he with _ h2; subst h2; subst hs; rfl
              | fault f => rw [hn] at he; simp at he
              | ok kd σ1 =>
                  have hσn := (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms _ σ hn).1; subst σ1
                  rw [hn] at he; simp only [specM_bind] at he
                  cases hal : Machines.Lnp64u.Isa.allocDerived (descDom ((σ.doms c.d).reg c.op.rs2)) kd ⟨c.d, sl, gg⟩ σ with
                  | err e2 σ2 => have hs := Machines.Lnp64u.Isa.Wip.allocDerived_err_state (descDom _) _ _ σ hal
                                 rw [hal] at he; injection he with _ h2; subst h2; subst hs; rfl
                  | fault f => rw [hal] at he; simp at he
                  | ok hh τ => rw [hal] at he; simp [SpecM.setReg, SpecM.modify] at he
  case _ => -- map
    intro σ; constructor
    · intro a σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp [SpecM.raise] at he
          | mem base len perms =>
              rw [hk] at he
              simp only [SpecM.updDom, SpecM.modify, SpecM.setReg, specM_bind, SpecM.set] at he
              injection he with _ h2; subst h2
              rfl
    · intro e σ' he
      simp only [SpecM.reg, specM_bind] at he
      cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
      | err e0 σ0 => have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
                     rw [hcl] at he; injection he with _ h2; subst h2; subst hs; rfl
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sl, gg, e⟩ := r; simp only at he
          cases hk : e.kind with
          | gate g => rw [hk] at he; simp only [SpecM.raise] at he; injection he with _ h2; subst h2; rfl
          | mem base len perms =>
              rw [hk] at he
              simp [SpecM.updDom, SpecM.modify, SpecM.setReg, specM_bind, SpecM.set] at he
  case _ => -- unmap
    exact CycleEq.bind (CycleEq.updDom _ _) (fun _ => CycleEq.setReg _ _ _)
  case _ => exact gatecall_cycle_eq c
  case _ => exact gatereturn_cycle_eq c
  case _ => exact move_cycle_eq c
  case _ => -- yield
    exact CycleEq.bind (CycleEq.updDom _ _) (fun _ => CycleEq.setReg _ _ _)
  case _ => exact CycleEq.halt c

/-- **No instruction's exec ever touches `cycle`.** -/
theorem exec_cycle_eq : ∀ instr ∈ isa, ∀ c : Ctx, CycleEq (instr.sem.exec c) := by
  intro instr hmem c
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hs
  · exact base_cycle_eq instr hb c
  · exact system_cycle_eq instr hs c

/-- **`retire` never advances `cycle`**: the pc bump, exec effect, errno
write-back, and halts all preserve it. -/
theorem retire_cycle (σ : MachineState) (d : DomainId) (w : Loom.Word32) :
    (retire σ d w).cycle = σ.cycle := by
  unfold retire
  split
  · exact haltDom_cycle σ d _
  · rename_i instr hdec
    have hex := exec_cycle_eq instr (Loom.Isa.decode_mem isa hdec)
      { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }))
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w }
        (σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })) with
    | ok a σ' =>
        simp only [hexr]
        exact hex.1 a σ' hexr
    | err e σ' =>
        simp only [hexr]
        exact hex.2 e σ' hexr
    | fault f =>
        simp only [hexr]
        exact haltDom_cycle σ d _

/-- The refill phase never advances `cycle`. -/
theorem refillPhase_cycle (m : Manifest) (σ : MachineState) :
    (refillPhase m σ).cycle = σ.cycle := by
  unfold refillPhase; split <;> rfl

/-- The Mover phase never advances `cycle`. -/
theorem moverPhase_cycle (σ : MachineState) : (moverPhase σ).cycle = σ.cycle := by
  unfold moverPhase moverStatus MachineState.write
  cases σ.mover with
  | none => rfl
  | some job => dsimp only; split_ifs <;> rfl

/-- The core phase never advances `cycle`: countdown/idle/stall are frame,
retirements are `retire_cycle`, halts are `haltDom_cycle`, issues touch only
budgets/gates/inflight. -/
theorem corePhase_cycle (m : Manifest) (σ : MachineState) :
    (corePhase m σ).cycle = σ.cycle := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · simp only [hc, if_true]
        exact retire_cycle { σ with inflight := none } fl.dom fl.word
      · simp only [hc, if_false]
  | none =>
      simp only []
      split
      · rfl
      · rename_i d hsched
        split
        · exact haltDom_cycle σ d _
        · rename_i w hfetch
          split
          · exact haltDom_cycle σ d _
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              cases hservd : (σ.doms d).serving with
              | none => rfl
              | some g =>
                  simp only [hservd]
                  cases hactg : (σ.gates g).act with
                  | none => exact haltDom_cycle σ d _
                  | some a =>
                      simp only [hactg]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        rfl
                      · simp only [hdon, if_false]
                        exact haltDom_cycle σ d _
            · simp only [hbud, if_false]

/-- **The cycle counter advances by exactly one per step** (T6 obligation 3
support): no phase — and in particular no instruction's `exec` — ever writes
`cycle`; only the final bump does. -/
theorem step_cycle (m : Manifest) (σ : MachineState) :
    (step m σ).cycle = σ.cycle + 1 := by
  show (moverPhase (corePhase m (refillPhase m σ))).cycle + 1 = σ.cycle + 1
  rw [moverPhase_cycle, corePhase_cycle, refillPhase_cycle]

/-- The cycle counter after `n` steps. -/
theorem stepN_cycle (m : Manifest) : ∀ (n : Nat) (σ : MachineState),
    (stepN m n σ).cycle = σ.cycle + n
  | 0, _ => rfl
  | n + 1, σ => by
      show (stepN m n (step m σ)).cycle = σ.cycle + (n + 1)
      rw [stepN_cycle m n (step m σ), step_cycle]
      omega

/-! ## Halted is absorbing (T6 potential support)

A halted domain never runs again: the only two `run`-reviving writers are
`gate_return`'s caller resume and the forced unwind's caller resume, and in
both cases `Wf.gate_serving` pins the resumed caller to `.blocked g` — never
`.halted`. Every other transition preserves each domain's `run` (calm ops)
or writes only `.halted`/`.blocked` (halts, `gate_call`). Swept `CalmOut`-
style through the ISA, `retire`, `corePhase`, and `step`. -/

/-- Every `σ`-halted domain is still halted in `σ'`. -/
def HaltedStays (σ σ' : MachineState) : Prop :=
  ∀ e, (σ.doms e).run = .halted → (σ'.doms e).run = .halted

theorem HaltedStays.of_run_eq {σ σ' : MachineState}
    (h : ∀ e, (σ'.doms e).run = (σ.doms e).run) : HaltedStays σ σ' :=
  fun e he => (h e).trans he

/-- A calm transition preserves every domain's `run`, so halted stays. -/
theorem CalmOut.haltedStays {cd : DomainId} {σ σ' : MachineState}
    (h : CalmOut cd σ σ') : HaltedStays σ σ' :=
  HaltedStays.of_run_eq h.2.1

/-- A calm `ok` outcome keeps halted domains halted (the ISA-sweep
workhorse). -/
theorem CalmLe.halted_ok {cd : DomainId} {α : Type} {mm : SpecM α} (h : CalmLe cd mm)
    {σ : MachineState} {a : α} {σ' : MachineState} (he : mm σ = .ok a σ') :
    HaltedStays σ σ' :=
  ((h σ).1 a σ' he).haltedStays

/-- `haltDom` keeps halted domains halted: the target goes (or stays)
halted, the resumed caller of an unwind was `.blocked` (never halted, by
`Wf.gate_serving`), everyone else is untouched. -/
theorem haltDom_halted (σ : MachineState) (d : DomainId) (cv : Loom.Word32)
    (hwf : Wf σ) : HaltedStays σ (σ.haltDom d cv) := by
  cases hserv : (σ.doms d).serving with
  | none =>
      rw [haltDom_base σ d cv hserv]
      intro e he
      simp only [haltBase_run]
      by_cases hed : e = d
      · simp [hed]
      · rw [if_neg hed]; exact he
  | some g =>
      cases hact : (σ.gates g).act with
      | none =>
          rw [haltDom_base' σ d cv g hserv hact]
          intro e he
          simp only [haltBase_run]
          by_cases hed : e = d
          · simp [hed]
          · rw [if_neg hed]; exact he
      | some a =>
          rw [haltDom_unwind σ d cv g a hserv hact]
          have hcallerblk : (σ.doms a.caller).run = .blocked g :=
            (hwf.gate_serving g a hact).2.1
          intro e he
          simp only [unwindGate_run, haltBase_run]
          by_cases hec : e = a.caller
          · subst hec; rw [hcallerblk] at he; exact absurd he (by simp)
          · rw [if_neg hec]
            by_cases hed : e = d
            · simp [hed]
            · rw [if_neg hed]; exact he

/-- `gate_call`'s activation-entry end state keeps halted domains halted:
the caller (executing, hence running) merely blocks, the callee (running by
the `require`) gains `serving` but keeps `run = running`; everyone else is
framed back to `σ0`. -/
theorem gateCall_end_halted (τ σ0 : MachineState) (caller cal : DomainId) (gid : GateId)
    (G : GateState) (argHandle : Loom.Word32) (entry : Addr)
    (hfrun : ∀ d', (τ.doms d').run = (σ0.doms d').run)
    (hcallerrun : (σ0.doms caller).run = .running)
    (hcalrun : (σ0.doms cal).run = .running) :
    HaltedStays σ0 ((({ τ with gates := Loom.Fun.update τ.gates gid G }).setDom cal
        (fun ds => { ds with
          regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
          pc := entry, serving := some gid })).setDom caller
        (fun ds => { ds with run := .blocked gid })) := by
  have hXd : ({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).doms
      = τ.doms := rfl
  intro e he
  by_cases hecaller : e = caller
  · subst hecaller; rw [hcallerrun] at he; exact absurd he (by simp)
  · rw [setDom_doms_ne _ _ _ _ hecaller]
    by_cases hecal : e = cal
    · subst hecal; rw [hcalrun] at he; exact absurd he (by simp)
    · rw [setDom_doms_ne _ _ _ _ hecal]
      simp only [hXd]
      rw [hfrun e]; exact he

/-- `gate_return`'s end state keeps halted domains halted: the returning
callee is running, the resumed caller was `.blocked` (`Wf.gate_serving`);
everyone else is framed back to `σ0`. -/
theorem gateReturn_end_halted (τ σ0 : MachineState) (cd : DomainId) (gid : GateId)
    (act : Activation) (reply : Loom.Word32) (G : GateState)
    (hfrun : ∀ d', (τ.doms d').run = (σ0.doms d').run)
    (hrun : (σ0.doms cd).run = .running)
    (hgact : (σ0.gates gid).act = some act)
    (hwf : Wf σ0) :
    HaltedStays σ0 (((({ τ with gates := Loom.Fun.update τ.gates gid G }).setDom cd
        (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc
                             serving := act.savedServing })).setDom act.caller
        (fun ds => { ds with run := .running })).setDom act.caller
        (fun ds => ds.setReg act.callerRd reply)) := by
  have hXd : ({ τ with gates := Loom.Fun.update τ.gates gid G } : MachineState).doms
      = τ.doms := rfl
  have hcallerblk : (σ0.doms act.caller).run = .blocked gid :=
    (hwf.gate_serving gid act hgact).2.1
  intro e he
  by_cases hecl : e = act.caller
  · subst hecl; rw [hcallerblk] at he; exact absurd he (by simp)
  · rw [setDom_doms_ne _ _ _ _ hecl, setDom_doms_ne _ _ _ _ hecl]
    by_cases hecd : e = cd
    · subst hecd; rw [hrun] at he; exact absurd he (by simp)
    · rw [setDom_doms_ne _ _ _ _ hecd]
      simp only [hXd]
      rw [hfrun e]; exact he

/-- `gate_call` keeps halted domains halted on its `ok` (activation-entry)
path. -/
theorem gatecall_halted (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hrun : (σ.doms c.d).run = .running) :
    ∀ a σ', (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = .ok a σ' →
      HaltedStays σ σ' := by
  have body : ∀ (out : Res Unit),
      (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = out →
      ∀ a σ', out = .ok a σ' → HaltedStays σ σ' := by
    intro out hout
    unfold Machines.Lnp64u.Isa.Wip.gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 => rw [hcl] at hout; subst hout; exact fun a σ' h => by simp at h
    | fault f => rw [hcl] at hout; subst hout; exact fun a σ' h => by simp at h
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r; simp only at hout
        cases hk : e.kind with
        | mem base len perms => rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
                                exact fun a σ' h => by simp at h
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                           exact fun a σ' h => by simp at h
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                         exact fun a σ' h => by simp at h
            | ok u1 σ1 =>
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                               exact fun a σ' h => by simp at h
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                             exact fun a σ' h => by simp at h
                | ok u2 σ2 =>
                    have hc2 := require_cond _ _ σ hr2; have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                   exact fun a σ' h => by simp at h
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                 exact fun a σ' h => by simp at h
                    | ok u3 σ3 =>
                        have hc3 := require_cond _ _ σ hr3; have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                       exact fun a σ' h => by simp at h
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                     exact fun a σ' h => by simp at h
                        | ok u4 σ4 =>
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (Machines.Lnp64u.Isa.Wip.gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                           exact fun a σ' h => by simp at h
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                         exact fun a σ' h => by simp at h
                            | ok u5 σ5 =>
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact fun a σ' h => by simp at h
                                | err e6 τ => rw [htbh] at hout; subst hout
                                              exact fun a σ' h => by simp at h
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    obtain ⟨hfrun, hfserv, _, _⟩ :=
                                      transferByHandle_frame c.d cal _ σ argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom,
                                      SpecM.modify] at hout
                                    subst hout
                                    have hcalrunσ : (σ.doms cal).run = .running := of_decide_eq_true hc3
                                    intro a σ' h
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    exact gateCall_end_halted τ σ c.d cal gid _ _ _
                                      hfrun hrun hcalrunσ
  exact fun a σ' h => body _ rfl a σ' h

/-- `gate_return` keeps halted domains halted on its `ok` path. -/
theorem gatereturn_halted (c : Ctx) (σ : MachineState) (hwf : Wf σ)
    (hrun : (σ.doms c.d).run = .running) :
    ∀ a σ',
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = .ok a σ' →
      HaltedStays σ σ' := by
  have body : ∀ (out : Res Unit),
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = out →
      ∀ a σ', out = .ok a σ' → HaltedStays σ σ' := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none => rw [hserv] at hout; simp [SpecM.fatal] at hout; subst hout
              exact fun a σ' h => by simp at h
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none => simp only [hgact] at hout; simp [SpecM.fatal] at hout; subst hout
                  exact fun a σ' h => by simp at h
        | some act =>
            simp only [hgact] at hout; simp only [SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f => rw [htbh] at hout; subst hout; exact fun a σ' h => by simp at h
            | err e0 τ => rw [htbh] at hout; subst hout; exact fun a σ' h => by simp at h
            | ok reply τ =>
                rw [htbh] at hout
                obtain ⟨hfrun, hfserv, _, _⟩ := transferByHandle_frame c.d act.caller _ σ reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                  SpecM.setReg] at hout
                subst hout
                intro a σ' h
                simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                exact gateReturn_end_halted τ σ c.d gid act reply _ hfrun hrun hgact hwf
  exact fun a σ' h => body _ rfl a σ' h

/-- **Every instruction keeps halted domains halted** (both outcomes). The
err arm is uniform (`TouchExec`'s err is `CalmOut`); the ok arm sweeps the
ISA: calm ops via `CalmLe`, the gate ops via `gatecall_halted`/
`gatereturn_halted`, `halt` via `haltDom_halted`. -/
theorem exec_halted (instr) (hmem : instr ∈ isa) (c : Ctx) (σ : MachineState)
    (hwf : Wf σ) (hrun : (σ.doms c.d).run = .running) :
    (∀ a σ', instr.sem.exec c σ = .ok a σ' → HaltedStays σ σ') ∧
    (∀ er σ', instr.sem.exec c σ = .err er σ' → HaltedStays σ σ') := by
  refine ⟨?_, fun er σ' he =>
    ((exec_touch instr hmem c σ hwf hrun).2 er σ' he).haltedStays⟩
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  intro a σ' he
  rcases List.mem_append.mp hmem' with hb | hs
  · exact CalmLe.halted_ok (cd := c.d) (base_calm instr hb c) he
  · fin_cases hs
    case _ => -- cap_dup
      refine CalmLe.halted_ok (cd := c.d) ?_ he
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.reg _ _) fun dw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (match e.kind with
        | .mem base len perms =>
            Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h
        | .gate gid =>
            (Pure.pure (CapKind.gate gid) : SpecM CapKind) >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h)
      cases e.kind with
      | mem b l p =>
          exact CalmLe.bind (CalmLe.narrow _ _ _ _) fun kind =>
            CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
      | gate i =>
          exact CalmLe.bind (CalmLe.pure _) fun kind =>
            CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
    case _ => -- cap_drop
      refine CalmLe.halted_ok (cd := c.d) ?_ he
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (SpecM.get >>= fun σ0 =>
        SpecM.set ((((match σ0.parentOf c.d s with
            | some p => σ0.reparent ⟨c.d, s, g⟩ p
            | none => σ0.orphanChildren ⟨c.d, s, g⟩).clearSlot c.d s).sweepRegions).sweepMover) >>=
          fun _ => SpecM.setReg c.d c.op.rd 0)
      refine CalmLe.getD _ fun σ0 => ?_
      constructor
      · intro a σ' he
        cases hp : σ0.parentOf c.d s with
        | some p =>
            rw [hp] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            refine CalmOut.trans ?_
              (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
            exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
        | none =>
            rw [hp] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            refine CalmOut.trans ?_
              (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
            exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
      · intro er σ' he
        cases hp : σ0.parentOf c.d s with
        | some p => rw [hp] at he
                    simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
        | none => rw [hp] at he
                  simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
    case _ => -- cap_revoke
      refine CalmLe.halted_ok (cd := c.d) ?_ he
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (SpecM.require (decide (e.kind.cls = .mem)) .badCap >>= fun _ =>
        SpecM.get >>= fun σ0 =>
        SpecM.set (((σ0.destroyMarked (σ0.marks ⟨c.d, s, g⟩)).sweepRegions).sweepMover) >>=
        fun _ => SpecM.setReg c.d c.op.rd 0)
      refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
      refine CalmLe.getD _ fun σ0 => ?_
      constructor
      · intro a σ' he
        simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
        injection he with _ h2; subst h2
        refine CalmOut.trans ?_
          (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
        exact ⟨fun e' => by simp, fun e' => by simp, fun e' _ => ⟨by simp, by simp, by simp⟩⟩
      · intro er σ' he
        simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
    case _ => -- mem_grant
      refine CalmLe.halted_ok (cd := c.d) ?_ he
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.reg _ _) fun dw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (match e.kind with
        | .gate _ => (SpecM.raise .badCap : SpecM Unit)
        | .mem base len perms =>
            Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived (descDom dw) kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h)
      cases e.kind with
      | gate gid => exact CalmLe.raise _
      | mem base len perms =>
          exact CalmLe.bind (CalmLe.narrow _ _ _ _) fun kind =>
            CalmLe.bind (CalmLe.allocDerived _ _ _) fun h => CalmLe.setReg _ _ _
    case _ => -- map
      refine CalmLe.halted_ok (cd := c.d) ?_ he
      refine CalmLe.bind (CalmLe.reg _ _) fun hw => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show CalmLe c.d (match e.kind with
        | .gate _ => (SpecM.raise .badCap : SpecM Unit)
        | .mem base len perms =>
            SpecM.updDom c.d (fun ds =>
              { ds with regions :=
                  (Loom.Fun.update ds.regions
                    ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
                    (some { base := base, len := len, perms := perms
                            backing := ⟨c.d, s, g⟩ })) }) >>= fun _ =>
            SpecM.setReg c.d c.op.rd 0)
      cases e.kind with
      | gate gid => exact CalmLe.raise _
      | mem base len perms =>
          exact CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
            fun _ => CalmLe.setReg _ _ _
    case _ => -- unmap
      refine CalmLe.halted_ok (cd := c.d) ?_ he
      exact CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
        fun _ => CalmLe.setReg _ _ _
    case _ => -- gate_call
      exact gatecall_halted c σ hwf hrun a σ' he
    case _ => -- gate_return
      exact gatereturn_halted c σ hwf hrun a σ' he
    case _ => -- move
      refine CalmLe.halted_ok (cd := c.d) ?_ he
      refine CalmLe.getD _ fun σg => (?_ : CalmLe c.d _) σg
      refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
      refine CalmLe.bind (CalmLe.reg _ _) fun aw => ?_
      refine CalmLe.bind (CalmLe.load _ _) fun srcH => ?_
      refine CalmLe.bind (CalmLe.load _ _) fun dstH => ?_
      refine CalmLe.bind (CalmLe.load _ _) fun lenW => ?_
      refine CalmLe.bind (CalmLe.load _ _) fun stW => ?_
      refine CalmLe.bind (CalmLe.capLive _ _) fun rs => ?_
      obtain ⟨ss, gs_, es⟩ := rs
      refine CalmLe.bind (CalmLe.capLive _ _) fun rd_ => ?_
      obtain ⟨sd, gd, ed⟩ := rd_
      show CalmLe c.d (match es.kind, ed.kind with
        | .mem sb sl sp, .mem db dl dp =>
            SpecM.require sp.r .permDenied >>= fun _ =>
            SpecM.require dp.w .permDenied >>= fun _ =>
            SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat))
              .outOfRange >>= fun _ =>
            SpecM.get >>= fun σ1 =>
            SpecM.demand (σ1.domCovers c.d (stW.setWidth 12)
              { r := false, w := true, x := false }) .memoryAuthority >>= fun _ =>
            SpecM.set ({ σ1 with mover :=
              (some { owner := c.d, src := ⟨c.d, ss, gs_⟩, dst := ⟨c.d, sd, gd⟩
                      srcCur := sb, dstCur := db, remaining := lenW.toNat
                      statusAddr := stW.setWidth 12 }) }) >>= fun _ =>
            SpecM.setReg c.d c.op.rd 0
        | _, _ => (SpecM.raise .badCap : SpecM Unit))
      cases es.kind with
      | gate gi =>
          cases ed.kind with
          | gate _ => exact CalmLe.raise _
          | mem db dl dp => exact CalmLe.raise _
      | mem sb sl sp =>
          cases ed.kind with
          | gate _ => exact CalmLe.raise _
          | mem db dl dp =>
              refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
              refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
              refine CalmLe.bind (CalmLe.require _ _) fun _ => ?_
              refine CalmLe.getD _ fun σ1 => ?_
              constructor
              · intro a σ' he
                by_cases hcov : σ1.domCovers c.d (stW.setWidth 12)
                    { r := false, w := true, x := false }
                · simp only [SpecM.demand, hcov, if_true, specM_pure, specM_bind, SpecM.set,
                    SpecM.setReg, SpecM.modify] at he
                  injection he with _ h2; subst h2
                  refine CalmOut.trans ?_
                    (CalmOut.setDomExec _ c.d _ (setReg_serving _ _ _) (setReg_run _ _ _))
                  exact CalmOut.of_doms_eq (fun e' => rfl)
                · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
              · intro er σ' he
                by_cases hcov : σ1.domCovers c.d (stW.setWidth 12)
                    { r := false, w := true, x := false }
                · simp [SpecM.demand, hcov, specM_pure, specM_bind, SpecM.set,
                    SpecM.setReg, SpecM.modify] at he
                · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
    case _ => -- yield
      refine CalmLe.halted_ok (cd := c.d) ?_ he
      exact CalmLe.bind (CalmLe.updDomExec _ _ (fun _ => rfl) (fun _ => rfl))
        fun _ => CalmLe.setReg _ _ _
    case _ => -- halt
      simp only [SpecM.modify] at he; injection he with _ h2; subst h2
      exact haltDom_halted σ c.d 0 hwf

/-- `retire` keeps halted domains halted: the pc bump and errno write hit no
`run` mark, the instruction effect is `exec_halted`, decode failure and
faults are `haltDom_halted`. -/
theorem retire_halted (σ : MachineState) (d : DomainId) (w : Loom.Word32)
    (hwf : Wf σ) (hrun : (σ.doms d).run = .running) (hinf : σ.inflight = none) :
    HaltedStays σ (retire σ d w) := by
  unfold retire
  split
  · exact haltDom_halted σ d _ hwf
  · rename_i instr hdec
    set σ1 := σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }) with hσ1
    have hall : ∀ (d' : DomainId),
        ((σ1.doms d').caps = (σ.doms d').caps) ∧
        ((σ1.doms d').lineage = (σ.doms d').lineage) ∧
        ((σ1.doms d').slotGen = (σ.doms d').slotGen) ∧
        ((σ1.doms d').regions = (σ.doms d').regions) ∧
        ((σ1.doms d').run = (σ.doms d').run) ∧
        ((σ1.doms d').serving = (σ.doms d').serving) ∧
        ((σ1.doms d').regs = (σ.doms d').regs) ∧
        ((σ1.doms d').cause = (σ.doms d').cause) := by
      intro d'; rw [hσ1]; unfold MachineState.setDom
      by_cases hp : d' = d
      · subst hp; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hp]
    have hwf1 : Wf σ1 := by
      refine wf_of_skeleton_sameGates σ σ1
        (fun d' => (hall d').1) (fun d' => (hall d').2.1) (fun d' => (hall d').2.2.1)
        (fun d' => (hall d').2.2.2.1) (fun d' => (hall d').2.2.2.2.1)
        (fun d' => (hall d').2.2.2.2.2.1) rfl rfl ?_ hwf
      intro fl' hfl'; rw [show σ1.inflight = σ.inflight from rfl, hinf] at hfl'
      exact absurd hfl' (by simp)
    have hrun1 : (σ1.doms d).run = .running := by rw [(hall d).2.2.2.2.1]; exact hrun
    obtain ⟨hok, herr⟩ := exec_halted instr (Loom.Isa.decode_mem isa hdec)
      { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 hwf1 hrun1
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
    | ok a σ' =>
        simp only [hexr]
        intro e he
        exact hok a σ' hexr e (by rw [(hall e).2.2.2.2.1]; exact he)
    | err er σ' =>
        simp only [hexr]
        intro e he
        have hpost : ((σ'.setDom d fun ds => ds.setReg (operandsOf w).rd er.toWord).doms e).run
            = (σ'.doms e).run := by
          unfold MachineState.setDom
          by_cases hp : e = d
          · subst hp; simp [Loom.Fun.update_same, setReg_run]
          · simp [Loom.Fun.update_ne _ _ _ _ hp]
        rw [hpost]
        exact herr er σ' hexr e (by rw [(hall e).2.2.2.2.1]; exact he)
    | fault f =>
        simp only [hexr]
        exact haltDom_halted σ d _ hwf

/-- Charging a payer's budget moves no `run` mark. -/
theorem setDomBudget_run_eq (σ : MachineState) (p : DomainId) (n : Nat) (e : DomainId) :
    ((σ.setDom p (fun ds => { ds with budget := ds.budget - n })).doms e).run
      = (σ.doms e).run := by
  unfold MachineState.setDom
  by_cases h : e = p
  · subst h; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ h]

/-- The core phase keeps halted domains halted: countdown/idle/stall leave
doms alone, issues touch only budgets, retirements are `retire_halted`,
halts are `haltDom_halted`. -/
theorem corePhase_halted (m : Manifest) (σ : MachineState) (hwf : Wf σ) :
    HaltedStays σ (corePhase m σ) := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · simp only [hc, if_true]
        have hwfI : Wf { σ with inflight := none } :=
          wf_of_skeleton_sameGates σ { σ with inflight := none }
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) rfl rfl (by simp) hwf
        exact retire_halted { σ with inflight := none } fl.dom fl.word hwfI
          (hwf.inflight_running fl hinf) rfl
      · simp only [hc, if_false]
        exact HaltedStays.of_run_eq (fun e => rfl)
  | none =>
      simp only []
      split
      · exact HaltedStays.of_run_eq (fun e => rfl)
      · rename_i d hsched
        split
        · exact haltDom_halted σ d _ hwf
        · rename_i w hfetch
          split
          · exact haltDom_halted σ d _ hwf
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              cases hservd : (σ.doms d).serving with
              | none =>
                  simp only [hservd]
                  exact HaltedStays.of_run_eq
                    (fun e => setDomBudget_run_eq σ (σ.payer d) _ e)
              | some g =>
                  simp only [hservd]
                  cases hactg : (σ.gates g).act with
                  | none => exact haltDom_halted σ d _ hwf
                  | some a =>
                      simp only [hactg]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        exact HaltedStays.of_run_eq
                          (fun e => setDomBudget_run_eq σ (σ.payer d) _ e)
                      · simp only [hdon, if_false]
                        exact haltDom_halted σ d _ hwf
            · simp only [hbud, if_false]
              exact HaltedStays.of_run_eq (fun e => rfl)

/-- **Halted is absorbing** (T6 potential support, per cycle): under `Wf`
(available at every reachable state via `wfa_invariant`), a halted domain is
still halted after one machine cycle — the `#non-halted` term of the T6
potential never increases. -/
theorem halted_stays (m : Manifest) (σ : MachineState) (hwf : Wf σ)
    (e : DomainId) (h : (σ.doms e).run = .halted) :
    ((step m σ).doms e).run = .halted := by
  rw [congrFun (step_doms m σ) e]
  exact corePhase_halted m (refillPhase m σ) (refillPhase_preserves_wf m σ hwf) e
    (by rw [refillPhase_run]; exact h)

/-- Halted is absorbing along any run from a reachable state. -/
theorem stepN_halted (m : Manifest) (hwf : m.WF) (σ : MachineState)
    (hreach : (machine m).Reachable σ) (e : DomainId)
    (h : (σ.doms e).run = .halted) :
    ∀ n, ((stepN m n σ).doms e).run = .halted := by
  intro n
  induction n generalizing σ with
  | zero => exact h
  | succ k ih =>
      exact ih (step m σ) (Loom.TSys.Reachable.step hreach rfl)
        (halted_stays m σ (wfa_invariant m hwf σ hreach).1 e h)

/-! ## Origin refill eligibility (T6 obligation 4)

Within one period of any cycle, the refill phase restores a domain's budget
to its full quota `Q`; with `hpos` (`0 < Q`) the chain origin is therefore
funded — and the chain head `Eligible` — at some cycle of every window of
`periodP ≤ hyperL` cycles, unless a chain issue spends the refund first
(which is itself a progress event). Stated on `refillPhase m (stepN m k σ)`
because that is exactly the state `corePhase` runs in within
`step m (stepN m k σ)` (cf. `StallFree`). -/

/-- **Refill within one period**: for every state and domain there is a
period boundary at most `periodP` cycles ahead, where `refillPhase`
restores the budget to exactly `budgetQ`. Uses `step_cycle`: the counter
advances by one per step, so boundaries are hit on schedule. -/
theorem refill_within_period (m : Manifest) (hwf : m.WF) (σ : MachineState)
    (e : DomainId) :
    ∃ k ≤ (m.doms e).periodP,
      ((refillPhase m (stepN m k σ)).doms e).budget = (m.doms e).budgetQ := by
  have hP : 0 < (m.doms e).periodP := hwf.period_pos e
  by_cases hc : σ.cycle % (m.doms e).periodP = 0 ∧ σ.cycle ≠ 0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    show ((refillPhase m σ).doms e).budget = _
    unfold refillPhase
    rw [if_neg hc.2]
    simp [hc.1]
  · refine ⟨(m.doms e).periodP - σ.cycle % (m.doms e).periodP, Nat.sub_le _ _, ?_⟩
    have hcyc : (stepN m ((m.doms e).periodP - σ.cycle % (m.doms e).periodP) σ).cycle
        = σ.cycle + ((m.doms e).periodP - σ.cycle % (m.doms e).periodP) :=
      stepN_cycle m _ σ
    have hlt : σ.cycle % (m.doms e).periodP < (m.doms e).periodP :=
      Nat.mod_lt _ hP
    -- the landing cycle is the next multiple of the period
    have hmul : σ.cycle + ((m.doms e).periodP - σ.cycle % (m.doms e).periodP)
        = (m.doms e).periodP * (σ.cycle / (m.doms e).periodP + 1) := by
      have hdm : (m.doms e).periodP * (σ.cycle / (m.doms e).periodP)
          + σ.cycle % (m.doms e).periodP = σ.cycle :=
        Nat.div_add_mod σ.cycle (m.doms e).periodP
      have hsucc : (m.doms e).periodP * (σ.cycle / (m.doms e).periodP + 1)
          = (m.doms e).periodP * (σ.cycle / (m.doms e).periodP) + (m.doms e).periodP :=
        Nat.mul_succ _ _
      omega
    have hb : (stepN m ((m.doms e).periodP - σ.cycle % (m.doms e).periodP) σ).cycle
        % (m.doms e).periodP = 0 := by
      rw [hcyc, hmul]; exact Nat.mul_mod_right _ _
    have h0 : (stepN m ((m.doms e).periodP - σ.cycle % (m.doms e).periodP) σ).cycle ≠ 0 := by
      rw [hcyc, hmul]
      exact Nat.ne_of_gt (Nat.mul_pos hP (Nat.succ_pos _))
    unfold refillPhase
    rw [if_neg h0]
    simp [hb]

/-- **Origin refill eligibility** (T6 obligation 4): with positive quota
(`hpos`), within one period — hence within one hyperperiod — of any cycle
the origin's budget is restored to `Q > 0` at the very state the core phase
runs in. Combined with the chain-structure item (only chain issues draw the
origin's budget down, `payer_ne_of_serving_none`), the chain head is
`Eligible` from that point until the next progress event. -/
theorem origin_refill_eligible (m : Manifest) (hwf : m.WF) (σ : MachineState)
    (e : DomainId) (hpos : 0 < (m.doms e).budgetQ) :
    ∃ k ≤ hyperL m, 0 < ((refillPhase m (stepN m k σ)).doms e).budget := by
  obtain ⟨k, hk, hb⟩ := refill_within_period m hwf σ e
  exact ⟨k, Nat.le_trans hk (periodP_le_hyperL m hwf e), by rw [hb]; exact hpos⟩

/-! ## The chain-relevant transition classification (T6 obligation 2/5 core)

The T6 measure and counting arguments need, per instruction, exactly what
happens to the *chain observables*: the gate records, every domain's
`run`/`serving`/`maxDonation`, and (for the budget ledgers) every
non-executing domain's budget. `ChainOut`/`ChainLe` is the frame predicate
satisfied by the 22 calm ops; `GateCallShape`/`GateReturnShape` are the full
postcondition characterizations of the two gate ops; `halt` is `haltDom`
verbatim. `exec_chain_cases` is the resulting exhaustive classification —
the 6th (and final) ISA sweep of this development. -/

/-- The chain-observable frame: gate records untouched, every domain's
`run`/`serving`/`maxDonation` untouched, every non-executing domain's
budget untouched (`yield` zeroes its own budget, nothing touches others'). -/
def ChainOut (cd : DomainId) (σ σ' : MachineState) : Prop :=
  σ'.gates = σ.gates ∧
  (∀ e, (σ'.doms e).run = (σ.doms e).run) ∧
  (∀ e, (σ'.doms e).serving = (σ.doms e).serving) ∧
  (∀ e, (σ'.doms e).maxDonation = (σ.doms e).maxDonation) ∧
  (∀ e, e ≠ cd → (σ'.doms e).budget = (σ.doms e).budget)

theorem ChainOut.refl (cd : DomainId) (σ : MachineState) : ChainOut cd σ σ :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem ChainOut.of_eq {cd : DomainId} {σ σ' : MachineState} (h : σ' = σ) :
    ChainOut cd σ σ' := h ▸ ChainOut.refl cd σ

theorem ChainOut.trans {cd : DomainId} {σ σ1 σ2 : MachineState}
    (h1 : ChainOut cd σ σ1) (h2 : ChainOut cd σ1 σ2) : ChainOut cd σ σ2 :=
  ⟨h2.1.trans h1.1, fun e => (h2.2.1 e).trans (h1.2.1 e),
   fun e => (h2.2.2.1 e).trans (h1.2.2.1 e),
   fun e => (h2.2.2.2.1 e).trans (h1.2.2.2.1 e),
   fun e he => (h2.2.2.2.2 e he).trans (h1.2.2.2.2 e he)⟩

/-- `setDom` with an update preserving the chain fields is `ChainOut`. -/
theorem ChainOut.setDomOf (σ : MachineState) (cd d : DomainId)
    (f : DomainState → DomainState)
    (hr : (f (σ.doms d)).run = (σ.doms d).run)
    (hs : (f (σ.doms d)).serving = (σ.doms d).serving)
    (hm : (f (σ.doms d)).maxDonation = (σ.doms d).maxDonation)
    (hb : d ≠ cd → (f (σ.doms d)).budget = (σ.doms d).budget) :
    ChainOut cd σ (σ.setDom d f) := by
  refine ⟨rfl, fun e => ?_, fun e => ?_, fun e => ?_, fun e he => ?_⟩ <;>
    by_cases hed : e = d
  · subst hed; rw [setDom_doms_same]; exact hr
  · rw [setDom_doms_ne _ _ _ _ hed]
  · subst hed; rw [setDom_doms_same]; exact hs
  · rw [setDom_doms_ne _ _ _ _ hed]
  · subst hed; rw [setDom_doms_same]; exact hm
  · rw [setDom_doms_ne _ _ _ _ hed]
  · subst hed; rw [setDom_doms_same]; exact hb he
  · rw [setDom_doms_ne _ _ _ _ hed]

/-- A calm outcome relation for `SpecM` fragments: both `ok` and `err`
land in `ChainOut` (mirrors `CalmLe`). -/
def ChainLe (cd : DomainId) {α : Type} (mm : SpecM α) : Prop :=
  ∀ σ, (∀ a σ', mm σ = .ok a σ' → ChainOut cd σ σ') ∧
       (∀ e σ', mm σ = .err e σ' → ChainOut cd σ σ')

theorem ChainLe.of_state_eq {cd : DomainId} {α : Type} {mm : SpecM α}
    (h : ∀ σ, (∀ a σ', mm σ = .ok a σ' → σ' = σ) ∧
              (∀ e σ', mm σ = .err e σ' → σ' = σ)) : ChainLe cd mm :=
  fun σ => ⟨fun a σ' he => ChainOut.of_eq ((h σ).1 a σ' he),
            fun e σ' he => ChainOut.of_eq ((h σ).2 e σ' he)⟩

theorem ChainLe.pure {cd : DomainId} {α : Type} (a : α) :
    ChainLe cd (Pure.pure a : SpecM α) :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun a' σ' he => by rw [specM_pure] at he; injection he with _ h2; exact h2.symm ▸ rfl,
     fun e σ' he => by rw [specM_pure] at he; simp at he⟩

theorem ChainLe.bind {cd : DomainId} {α β : Type} {mm : SpecM α} {f : α → SpecM β}
    (hm : ChainLe cd mm) (hf : ∀ a, ChainLe cd (f a)) : ChainLe cd (mm >>= f) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro b σ' he
    rw [specM_bind] at he
    cases hmσ : mm σ with
    | ok a σ1 => rw [hmσ] at he
                 exact ChainOut.trans ((hm σ).1 a σ1 hmσ) ((hf a σ1).1 b σ' he)
    | err e σ1 => rw [hmσ] at he; simp at he
    | fault g => rw [hmσ] at he; simp at he
  · intro e σ' he
    rw [specM_bind] at he
    cases hmσ : mm σ with
    | ok a σ1 => rw [hmσ] at he
                 exact ChainOut.trans ((hm σ).1 a σ1 hmσ) ((hf a σ1).2 e σ' he)
    | err e1 σ1 => rw [hmσ] at he; injection he with h1 h2; subst h2
                   exact (hm σ).2 e1 σ1 hmσ
    | fault g => rw [hmσ] at he; simp at he

theorem ChainLe.iteBool {cd : DomainId} {α : Type} (b : Bool) {m1 m2 : SpecM α}
    (h1 : ChainLe cd m1) (h2 : ChainLe cd m2) :
    ChainLe cd (if b then m1 else m2) := by
  cases b
  · simpa using h2
  · simpa using h1

theorem ChainLe.reg {cd : DomainId} (d : DomainId) (r : RegId) :
    ChainLe cd (SpecM.reg d r) :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun a σ' he => by unfold SpecM.reg at he; injection he with _ h2; exact h2.symm,
     fun e σ' he => by unfold SpecM.reg at he; simp at he⟩

theorem ChainLe.get {cd : DomainId} : ChainLe cd SpecM.get :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun a σ' he => by unfold SpecM.get at he; injection he with _ h2; exact h2.symm,
     fun e σ' he => by unfold SpecM.get at he; simp at he⟩

theorem ChainLe.raise {cd : DomainId} {α : Type} (e : Errno) :
    ChainLe cd (SpecM.raise e : SpecM α) :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun a σ' he => by unfold SpecM.raise at he; simp at he,
     fun e' σ' he => by unfold SpecM.raise at he; injection he with _ h2; exact h2.symm⟩

theorem ChainLe.require {cd : DomainId} (cond : Bool) (e : Errno) :
    ChainLe cd (SpecM.require cond e) :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun a σ' he => (require_ok cond e σ he).symm ▸ rfl,
     fun e' σ' he => (require_err_state cond e σ he).symm ▸ rfl⟩

theorem ChainLe.demand {cd : DomainId} (cond : Bool) (f : Fault) :
    ChainLe cd (SpecM.demand cond f) :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun a σ' he => (demand_ok cond f σ he).symm ▸ rfl,
     fun e σ' he => by
       unfold SpecM.demand at he; split at he
       · simp [specM_pure] at he
       · simp [SpecM.fatal] at he⟩

theorem ChainLe.load {cd : DomainId} (d : DomainId) (a : Addr) :
    ChainLe cd (SpecM.load d a) :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun v σ' he => (load_ok d a σ he).symm ▸ rfl,
     fun e σ' he => (load_err_state d a σ he).symm ▸ rfl⟩

theorem ChainLe.capLive {cd : DomainId} (d : DomainId) (hw : Loom.Word32) :
    ChainLe cd (Machines.Lnp64u.Isa.capLive d hw) :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun r σ' he => (Machines.Lnp64u.Isa.Wip.capLive_ok d hw σ he).1.symm ▸ rfl,
     fun e σ' he => (Machines.Lnp64u.Isa.Wip.capLive_err_state d hw σ he).symm ▸ rfl⟩

theorem ChainLe.narrow {cd : DomainId} (base : Addr) (len : BitVec 13) (perms : Perms)
    (dw : Loom.Word32) : ChainLe cd (Machines.Lnp64u.Isa.narrow base len perms dw) :=
  ChainLe.of_state_eq fun σ =>
    ⟨fun k σ' he => (Machines.Lnp64u.Isa.Wip.narrow_ok base len perms dw σ he).1.symm ▸ rfl,
     fun e σ' he => (Machines.Lnp64u.Isa.Wip.narrow_err_state base len perms dw σ he).symm ▸ rfl⟩

/-- A `modify` whose function is `ChainOut` is `ChainLe`. -/
theorem ChainLe.modifyOf {cd : DomainId} (f : MachineState → MachineState)
    (hf : ∀ σ, ChainOut cd σ (f σ)) : ChainLe cd (SpecM.modify f) :=
  fun σ => ⟨fun a σ' he => by
              unfold SpecM.modify at he; injection he with _ h2; exact h2 ▸ hf σ,
            fun e σ' he => by unfold SpecM.modify at he; simp at he⟩

theorem ChainLe.setReg (cd d : DomainId) (r : RegId) (v : Loom.Word32) :
    ChainLe cd (SpecM.setReg d r v) :=
  ChainLe.modifyOf _ fun σ =>
    ChainOut.setDomOf σ cd d _ (setReg_run _ _ _) (setReg_serving _ _ _)
      (by unfold DomainState.setReg; split <;> rfl)
      (fun _ => by unfold DomainState.setReg; split <;> rfl)

theorem ChainLe.updDomOf (cd d : DomainId) (f : DomainState → DomainState)
    (hr : ∀ ds, (f ds).run = ds.run) (hs : ∀ ds, (f ds).serving = ds.serving)
    (hm : ∀ ds, (f ds).maxDonation = ds.maxDonation)
    (hb : ∀ ds, d ≠ cd → (f ds).budget = ds.budget) :
    ChainLe cd (SpecM.updDom d f) :=
  ChainLe.modifyOf _ fun σ =>
    ChainOut.setDomOf σ cd d f (hr _) (hs _) (hm _) (fun h => hb _ h)

theorem ChainLe.store {cd : DomainId} (d : DomainId) (a : Addr) (v : Loom.Word32) :
    ChainLe cd (SpecM.store d a v) := by
  intro σ; unfold SpecM.store
  refine ⟨?_, ?_⟩
  · intro x σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp only [SpecM.demand, hc, if_true, specM_pure, specM_bind, SpecM.set] at he
      injection he with _ h2; subst h2
      exact ChainOut.refl cd σ
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he
  · intro e σ' he
    simp only [SpecM.get, specM_bind] at he
    by_cases hc : σ.domCovers d a { r := false, w := true, x := false }
    · simp [SpecM.demand, hc, specM_pure, specM_bind, SpecM.set] at he
    · simp [SpecM.demand, hc, SpecM.fatal, specM_bind] at he

theorem ChainLe.allocDerived {cd : DomainId} (owner : DomainId) (kind : CapKind)
    (parent : CapRef) : ChainLe cd (Machines.Lnp64u.Isa.allocDerived owner kind parent) := by
  intro σ
  refine ⟨?_, ?_⟩
  · intro hw σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp [SpecM.raise] at he
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp [SpecM.raise] at he
        | some lc =>
            rw [hfc] at he
            simp only [SpecM.set, specM_bind, specM_pure] at he
            injection he with _ h2; subst h2
            exact ChainOut.setDomOf σ cd owner _ rfl rfl rfl (fun _ => rfl)
  · intro e σ' he
    unfold Machines.Lnp64u.Isa.allocDerived at he
    simp only [SpecM.get, specM_bind] at he
    cases hfs : σ.freeSlot owner with
    | none => rw [hfs] at he; simp only [SpecM.raise] at he
              injection he with _ h2; exact h2.symm ▸ ChainOut.refl cd σ
    | some sl =>
        rw [hfs] at he
        cases hfc : σ.freeCell owner with
        | none => rw [hfc] at he; simp only [SpecM.raise] at he
                  injection he with _ h2; exact h2.symm ▸ ChainOut.refl cd σ
        | some lc => rw [hfc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-- Case on the current state first (mirrors `CalmLe.getD`). -/
theorem ChainLe.getD {cd : DomainId} {α : Type} (f : MachineState → SpecM α)
    (hf : ∀ σ, (∀ a σ', f σ σ = .ok a σ' → ChainOut cd σ σ') ∧
               (∀ e σ', f σ σ = .err e σ' → ChainOut cd σ σ')) :
    ChainLe cd (SpecM.get >>= f) := by
  intro σ
  have hb : (SpecM.get >>= f) σ = f σ σ := rfl
  exact ⟨fun a σ' he => (hf σ).1 a σ' (hb ▸ he),
         fun e σ' he => (hf σ).2 e σ' (hb ▸ he)⟩

/-- Every base opcode is chain-calm. -/
theorem base_chain_le (cd : DomainId) : ∀ instr ∈ Machines.Lnp64u.Isa.base, ∀ c : Ctx,
    ChainLe cd (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.setReg _ _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.setReg _ _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.setReg _ _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.setReg _ _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.setReg _ _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.setReg _ _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.setReg _ _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.setReg _ _ _ _)
  · exact ChainLe.setReg _ _ _ _
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.load _ _) (fun _ => ChainLe.setReg _ _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.store _ _ _))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ =>
      ChainLe.iteBool _ (ChainLe.updDomOf _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)) (ChainLe.pure ())))
  · exact ChainLe.bind (ChainLe.reg _ _) (fun _ => ChainLe.bind (ChainLe.reg _ _) (fun _ =>
      ChainLe.iteBool _ (ChainLe.updDomOf _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)) (ChainLe.pure ())))
  · exact ChainLe.bind (ChainLe.reg _ _)
      (fun _ => ChainLe.bind (ChainLe.setReg _ _ _ _)
        (fun _ => ChainLe.updDomOf _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)))

/-! ### Kernel-op chain frames -/

theorem reparent_chainOut (cd : DomainId) (σ : MachineState) (o n : CapRef) :
    ChainOut cd σ (σ.reparent o n) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem orphanChildren_chainOut (cd : DomainId) (σ : MachineState) (o : CapRef) :
    ChainOut cd σ (σ.orphanChildren o) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem clearSlot_chainOut (cd : DomainId) (σ : MachineState) (d : DomainId) (s : Slot) :
    ChainOut cd σ (σ.clearSlot d s) :=
  ChainOut.setDomOf σ cd d _ rfl rfl rfl (fun _ => rfl)

theorem destroyMarked_chainOut (cd : DomainId) (σ : MachineState)
    (mk : DomainId → Slot → Bool) : ChainOut cd σ (σ.destroyMarked mk) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem sweepRegions_chainOut (cd : DomainId) (σ : MachineState) :
    ChainOut cd σ σ.sweepRegions :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem sweepMover_chainOut (cd : DomainId) (σ : MachineState) :
    ChainOut cd σ σ.sweepMover := by
  unfold MachineState.sweepMover
  cases σ.mover with
  | none => exact ChainOut.refl cd σ
  | some job =>
      by_cases h1 : σ.liveRef job.src && σ.liveRef job.dst
      · simp only [h1, if_true]; exact ChainOut.refl cd σ
      · simp only [h1, if_false]
        by_cases h2 : ({ σ with mover := none } : MachineState).domCovers job.owner
            job.statusAddr { r := false, w := true, x := false }
        · simp only [h2, if_true]
          exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
        · simp only [h2, if_false]
          exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem transferCap_chainOut (cd : DomainId) (σ : MachineState) (from_ : DomainId)
    (s : Slot) (to_ : DomainId) (τ : MachineState) (ref : CapRef)
    (h : σ.transferCap from_ s to_ = some (τ, ref)) : ChainOut cd σ τ := by
  unfold MachineState.transferCap at h
  cases he : (σ.doms from_).caps s with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hfs : σ.freeSlot to_ with
      | none => rw [hfs] at h; simp at h
      | some s2 =>
          rw [hfs] at h; simp only [Option.bind_some] at h
          have key : ∀ (σ₁ : MachineState), ChainOut cd σ σ₁ →
              some (((((σ₁.reparent ⟨from_, s, (σ.doms from_).slotGen s⟩
                ⟨to_, s2, (σ.doms to_).slotGen s2⟩).clearSlot from_ s).sweepRegions).sweepMover),
                (⟨to_, s2, (σ.doms to_).slotGen s2⟩ : CapRef))
                = some (τ, ref) →
              ChainOut cd σ τ := by
            intro σ₁ hpre heq
            injection heq with heq; injection heq with hτ _; subst hτ
            exact hpre.trans ((reparent_chainOut cd σ₁ _ _).trans
              ((clearSlot_chainOut cd _ from_ s).trans
                ((sweepRegions_chainOut cd _).trans (sweepMover_chainOut cd _))))
          cases hl : e.lineage with
          | none =>
              rw [hl] at h; simp only [Option.pure_def, Option.bind_some] at h
              exact key _ (ChainOut.setDomOf σ cd to_ _ rfl rfl rfl (fun _ => rfl)) h
          | some l =>
              rw [hl] at h; simp only [Option.bind_eq_bind, Option.bind_some] at h
              cases hc : (σ.doms from_).lineage l with
              | none => rw [hc] at h; simp at h
              | some cell =>
                  rw [hc] at h; simp only [Option.bind_some] at h
                  cases hfc : σ.freeCell to_ with
                  | none => rw [hfc] at h; simp at h
                  | some l' =>
                      rw [hfc] at h; simp only [Option.pure_def, Option.bind_some] at h
                      exact key _ (ChainOut.setDomOf σ cd to_ _ rfl rfl rfl (fun _ => rfl)) h

theorem transferByHandle_chain_le (cd : DomainId) (d to_ : DomainId) (hw : Loom.Word32) :
    ChainLe cd (Machines.Lnp64u.Isa.transferByHandle d to_ hw) := by
  intro σ
  unfold Machines.Lnp64u.Isa.transferByHandle
  by_cases hz : hw = 0
  · rw [if_pos hz]
    exact ⟨fun a σ' he => by
        simp only [specM_pure] at he; obtain ⟨_, rfl⟩ := he; exact ChainOut.refl cd σ,
      fun e σ' he => by simp [specM_pure] at he⟩
  · simp only [if_neg hz, specM_bind]
    constructor
    · intro a σ' he
      cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
      | err e0 σ0 => rw [hcl] at he; simp at he
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none => rw [htc] at he; simp [SpecM.raise] at he
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp only [SpecM.set, specM_bind, specM_pure] at he
              injection he with _ h2; subst h2
              exact transferCap_chainOut cd σ d sslot to_ σ2 ref htc
    · intro er σ' he
      cases hcl : Machines.Lnp64u.Isa.capLive d hw σ with
      | err e0 σ0 =>
          have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state d _ σ hcl; rw [hcl] at he
          injection he with _ h2; subst h2; exact ChainOut.of_eq hs
      | fault f => rw [hcl] at he; simp at he
      | ok r σ0 =>
          obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok d _ σ hcl; subst σ0
          rw [hcl] at he; obtain ⟨sslot, gg, ee⟩ := r
          simp only [SpecM.get, specM_bind] at he
          cases htc : σ.transferCap d sslot to_ with
          | none =>
              rw [htc] at he; simp only [SpecM.raise] at he
              injection he with _ h2; subst h2; exact ChainOut.refl cd σ
          | some pr =>
              obtain ⟨σ2, ref⟩ := pr
              rw [htc] at he; simp [SpecM.set, specM_bind, specM_pure] at he

/-! ### The two gate ops' full chain postconditions -/

/-- The full chain-observable postcondition of a successful `gate_call` by
`c.d`: the target gate `gid` was free, its callee `cal` was running,
unmarked, and distinct from the caller; the fresh activation records
`c.d` as caller with depth `gateDepth c σ ≤ maxChainDepth` and donation
`(σ.doms c.d).maxDonation`; every other gate record, every domain's
`maxDonation`, every non-caller budget, every non-callee serving mark and
every non-caller run mark is untouched; the callee now serves `gid` and the
caller is `.blocked gid`. -/
def GateCallShape (c : Ctx) (σ σ' : MachineState) : Prop :=
  ∃ gid act,
    (σ.gates gid).act = none ∧
    (σ.gates gid).config.callee ≠ c.d ∧
    (σ.doms (σ.gates gid).config.callee).run = .running ∧
    (σ.doms (σ.gates gid).config.callee).serving = none ∧
    act.caller = c.d ∧
    act.depth = Machines.Lnp64u.Isa.Wip.gateDepth c σ ∧
    act.depth ≤ maxChainDepth ∧
    act.donated = (σ.doms c.d).maxDonation ∧
    (∀ g', g' ≠ gid → σ'.gates g' = σ.gates g') ∧
    (σ'.gates gid).act = some act ∧
    (σ'.gates gid).config = (σ.gates gid).config ∧
    (∀ e, (σ'.doms e).maxDonation = (σ.doms e).maxDonation) ∧
    (∀ e, e ≠ c.d → (σ'.doms e).budget = (σ.doms e).budget) ∧
    (∀ e, e ≠ (σ.gates gid).config.callee → (σ'.doms e).serving = (σ.doms e).serving) ∧
    (σ'.doms (σ.gates gid).config.callee).serving = some gid ∧
    (∀ e, e ≠ c.d → (σ'.doms e).run = (σ.doms e).run) ∧
    (σ'.doms c.d).run = .blocked gid

/-- The full chain-observable postcondition of a successful `gate_return` by
`c.d` (serving `gid` with activation `act`): the gate record is freed, every
other gate record, every `maxDonation`, every non-`c.d` budget and serving
mark is untouched; `c.d`'s serving mark is restored to `act.savedServing`;
every domain except the resumed caller keeps its run mark and the caller
runs. -/
def GateReturnShape (c : Ctx) (σ σ' : MachineState) : Prop :=
  ∃ gid act,
    (σ.doms c.d).serving = some gid ∧
    (σ.gates gid).act = some act ∧
    (∀ g', g' ≠ gid → σ'.gates g' = σ.gates g') ∧
    (σ'.gates gid).act = none ∧
    (σ'.gates gid).config = (σ.gates gid).config ∧
    (∀ e, (σ'.doms e).maxDonation = (σ.doms e).maxDonation) ∧
    (∀ e, e ≠ c.d → (σ'.doms e).budget = (σ.doms e).budget) ∧
    (∀ e, e ≠ c.d → (σ'.doms e).serving = (σ.doms e).serving) ∧
    (σ'.doms c.d).serving = act.savedServing ∧
    (∀ e, e ≠ act.caller → (σ'.doms e).run = (σ.doms e).run) ∧
    (σ'.doms act.caller).run = .running

/-- `gate_call`'s chain classification: err leaves the state unchanged, ok
produces exactly `GateCallShape`. -/
theorem gatecall_chain (c : Ctx) (σ : MachineState) :
    (∀ a σ', (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = .ok a σ' →
       GateCallShape c σ σ') ∧
    (∀ er σ', (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = .err er σ' → σ' = σ) := by
  have body : ∀ (out : Res Unit),
      (Machines.Lnp64u.Isa.Wip.gateCallExec c) σ = out →
      (∀ a σ', out = .ok a σ' → GateCallShape c σ σ') ∧
      (∀ er σ', out = .err er σ' → σ' = σ) := by
    intro out hout
    unfold Machines.Lnp64u.Isa.Wip.gateCallExec at hout
    simp only [SpecM.reg, specM_bind] at hout
    cases hcl : Machines.Lnp64u.Isa.capLive c.d ((σ.doms c.d).reg c.op.rs1) σ with
    | err e0 σ0 =>
        have hs := Machines.Lnp64u.Isa.Wip.capLive_err_state c.d _ σ hcl
        rw [hcl] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hs⟩
    | fault f => rw [hcl] at hout; subst hout
                 exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
    | ok r σ0 =>
        obtain ⟨hσeq, _⟩ := Machines.Lnp64u.Isa.Wip.capLive_ok c.d _ σ hcl; subst σ0
        rw [hcl] at hout; obtain ⟨s0, g0, e⟩ := r; simp only at hout
        cases hk : e.kind with
        | mem base len perms =>
            rw [hk] at hout; simp only [SpecM.raise] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
              simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; rfl⟩
        | gate gid =>
            rw [hk] at hout; simp only [SpecM.get, specM_bind] at hout
            set cal := (σ.gates gid).config.callee with hcaldef
            cases hr1 : SpecM.require (σ.gates gid).act.isNone .gateBusy σ with
            | err e1 σ1 =>
                have hst := require_err_state _ _ σ hr1
                rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
            | fault f => rw [hr1] at hout; simp only [specM_bind] at hout; subst hout
                         exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
            | ok u1 σ1 =>
                have hc1 := require_cond _ _ σ hr1
                have hst := require_ok _ _ σ hr1; subst σ1
                rw [hr1] at hout; simp only [specM_bind] at hout
                cases hr2 : SpecM.require (decide (cal ≠ c.d)) .gateBusy σ with
                | err e2 σ2 =>
                    have hst := require_err_state _ _ σ hr2
                    rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                    exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
                | fault f => rw [hr2] at hout; simp only [specM_bind] at hout; subst hout
                             exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                | ok u2 σ2 =>
                    have hc2 := require_cond _ _ σ hr2
                    have hst := require_ok _ _ σ hr2; subst σ2
                    rw [hr2] at hout; simp only [specM_bind] at hout
                    cases hr3 : SpecM.require (decide ((σ.doms cal).run = .running)) .gateBusy σ with
                    | err e3 σ3 =>
                        have hst := require_err_state _ _ σ hr3
                        rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                          simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
                    | fault f => rw [hr3] at hout; simp only [specM_bind] at hout; subst hout
                                 exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                    | ok u3 σ3 =>
                        have hc3 := require_cond _ _ σ hr3
                        have hst := require_ok _ _ σ hr3; subst σ3
                        rw [hr3] at hout; simp only [specM_bind] at hout
                        cases hr4 : SpecM.require (σ.doms cal).serving.isNone .gateBusy σ with
                        | err e4 σ4 =>
                            have hst := require_err_state _ _ σ hr4
                            rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                              simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
                        | fault f => rw [hr4] at hout; simp only [specM_bind] at hout; subst hout
                                     exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                        | ok u4 σ4 =>
                            have hc4 := require_cond _ _ σ hr4
                            have hst := require_ok _ _ σ hr4; subst σ4
                            rw [hr4] at hout; simp only [specM_bind] at hout
                            cases hr5 : SpecM.require (decide (Machines.Lnp64u.Isa.Wip.gateDepth c σ ≤ maxChainDepth)) .gateBusy σ with
                            | err e5 σ5 =>
                                have hst := require_err_state _ _ σ hr5
                                rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hst⟩
                            | fault f => rw [hr5] at hout; simp only [specM_bind] at hout; subst hout
                                         exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                            | ok u5 σ5 =>
                                have hc5 := require_cond _ _ σ hr5
                                have hst := require_ok _ _ σ hr5; subst σ5
                                rw [hr5] at hout; simp only [specM_bind, SpecM.reg] at hout
                                cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d cal ((σ.doms c.d).reg c.op.rs2) σ with
                                | fault f => rw [htbh] at hout; subst hout
                                             exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
                                | err e6 τ =>
                                    have hs := transferByHandle_err_state c.d cal _ σ e6 τ htbh
                                    rw [htbh] at hout; subst hout
                                    exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                                      simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hs⟩
                                | ok argHandle τ =>
                                    rw [htbh] at hout
                                    have hτ : ChainOut c.d σ τ :=
                                      (transferByHandle_chain_le c.d c.d cal _ σ).1 argHandle τ htbh
                                    simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom,
                                      SpecM.modify] at hout
                                    subst hout
                                    refine ⟨fun a σ' h => ?_, fun er σ' h => by simp at h⟩
                                    simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                                    -- assemble the shape
                                    have hcalne : cal ≠ c.d := of_decide_eq_true hc2
                                    have hgnone : (σ.gates gid).act = none :=
                                      Option.isNone_iff_eq_none.mp hc1
                                    set act0 : Activation :=
                                      { caller := c.d, callerRd := c.op.rd
                                        savedRegs := (τ.doms cal).regs
                                        savedPc := (τ.doms cal).pc
                                        savedServing := (τ.doms cal).serving
                                        depth := Machines.Lnp64u.Isa.Wip.gateDepth c σ
                                        donated := (τ.doms c.d).maxDonation } with hact0
                                    set G0 : GateState :=
                                      { σ.gates gid with act := some act0 } with hG0
                                    have hXgates : ({ τ with
                                        gates := Loom.Fun.update τ.gates gid G0 } : MachineState).doms
                                        = τ.doms := rfl
                                    refine ⟨gid, act0,
                                      hgnone, hcalne, of_decide_eq_true hc3,
                                      Option.isNone_iff_eq_none.mp hc4,
                                      rfl, rfl, of_decide_eq_true hc5,
                                      hτ.2.2.2.1 c.d,
                                      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                                    · intro g' hg'
                                      show Loom.Fun.update τ.gates gid _ g' = σ.gates g'
                                      rw [Loom.Fun.update_ne _ _ _ _ hg']
                                      exact congrFun hτ.1 g'
                                    · show (Loom.Fun.update τ.gates gid _ gid).act = _
                                      rw [Loom.Fun.update_same]
                                    · show (Loom.Fun.update τ.gates gid _ gid).config = _
                                      rw [Loom.Fun.update_same]
                                    · intro e'
                                      by_cases hecd : e' = c.d
                                      · subst hecd
                                        rw [setDom_doms_same]
                                        show ((_ : MachineState).doms c.d).maxDonation = _
                                        rw [setDom_doms_ne _ _ _ _ hcalne.symm, hXgates]
                                        exact hτ.2.2.2.1 c.d
                                      · rw [setDom_doms_ne _ _ _ _ hecd]
                                        by_cases hecal : e' = cal
                                        · subst hecal
                                          rw [setDom_doms_same]
                                          show ((({ τ.doms cal with
                                            regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
                                            pc := (σ.gates gid).config.entry
                                            serving := some gid } : DomainState)).maxDonation) = _
                                          exact hτ.2.2.2.1 cal
                                        · rw [setDom_doms_ne _ _ _ _ hecal, hXgates]
                                          exact hτ.2.2.2.1 e'
                                    · intro e' hecd
                                      rw [setDom_doms_ne _ _ _ _ hecd]
                                      by_cases hecal : e' = cal
                                      · subst hecal
                                        rw [setDom_doms_same]
                                        exact hτ.2.2.2.2 cal hecd
                                      · rw [setDom_doms_ne _ _ _ _ hecal, hXgates]
                                        exact hτ.2.2.2.2 e' hecd
                                    · intro e' hecal
                                      rw [← hcaldef] at hecal
                                      by_cases hecd : e' = c.d
                                      · subst hecd
                                        rw [setDom_doms_same]
                                        show ((_ : MachineState).doms c.d).serving = _
                                        rw [setDom_doms_ne _ _ _ _ hcalne.symm, hXgates]
                                        exact hτ.2.2.1 c.d
                                      · rw [setDom_doms_ne _ _ _ _ hecd,
                                            setDom_doms_ne _ _ _ _ hecal, hXgates]
                                        exact hτ.2.2.1 e'
                                    · rw [← hcaldef,
                                          setDom_doms_ne _ _ _ _ hcalne, setDom_doms_same]
                                    · intro e' hecd
                                      rw [setDom_doms_ne _ _ _ _ hecd]
                                      by_cases hecal : e' = cal
                                      · subst hecal
                                        rw [setDom_doms_same]
                                        exact hτ.2.1 cal
                                      · rw [setDom_doms_ne _ _ _ _ hecal, hXgates]
                                        exact hτ.2.1 e'
                                    · rw [setDom_doms_same]
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun er σ' h => (body _ h).2 er σ' rfl⟩

/-- `gate_return`'s chain classification: err leaves the state unchanged, ok
produces exactly `GateReturnShape` (mirrors `gatecall_chain`). -/
theorem gatereturn_chain (c : Ctx) (σ : MachineState) :
    (∀ a σ',
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = .ok a σ' →
      GateReturnShape c σ σ') ∧
    (∀ er σ',
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = .err er σ' →
      σ' = σ) := by
  have body : ∀ (out : Res Unit),
      ((do let σ0 ← SpecM.get
           match (σ0.doms c.d).serving with
           | none => SpecM.fatal .protocol
           | some gid =>
               match (σ0.gates gid).act with
               | none => SpecM.fatal .protocol
               | some act => do
                   let rw ← reg c.d c.op.rs1
                   let reply ← Machines.Lnp64u.Isa.transferByHandle c.d act.caller rw
                   let σ1 ← SpecM.get
                   SpecM.set ({ σ1 with gates := Loom.Fun.update σ1.gates gid { (σ1.gates gid) with act := none } })
                   SpecM.updDom c.d (fun ds => { ds with regs := act.savedRegs, pc := act.savedPc, serving := act.savedServing })
                   SpecM.updDom act.caller (fun ds => { ds with run := .running })
                   SpecM.setReg act.caller act.callerRd reply) : SpecM Unit) σ = out →
      (∀ a σ', out = .ok a σ' → GateReturnShape c σ σ') ∧
      (∀ er σ', out = .err er σ' → σ' = σ) := by
    intro out hout
    simp only [SpecM.get, specM_bind] at hout
    cases hserv : (σ.doms c.d).serving with
    | none =>
        rw [hserv] at hout; simp [SpecM.fatal] at hout; subst hout
        exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
    | some gid =>
        simp only [hserv] at hout
        cases hgact : (σ.gates gid).act with
        | none =>
            simp only [hgact] at hout; simp [SpecM.fatal] at hout; subst hout
            exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
        | some act =>
            simp only [hgact] at hout; simp only [SpecM.reg, specM_bind] at hout
            cases htbh : Machines.Lnp64u.Isa.transferByHandle c.d act.caller
                ((σ.doms c.d).reg c.op.rs1) σ with
            | fault f => rw [htbh] at hout; subst hout
                         exact ⟨fun a σ' h => by simp at h, fun er σ' h => by simp at h⟩
            | err e0 τ =>
                have hs := transferByHandle_err_state c.d act.caller _ σ e0 τ htbh
                rw [htbh] at hout; subst hout
                exact ⟨fun a σ' h => by simp at h, fun er σ' h => by
                  simp only [Res.err.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hs⟩
            | ok reply τ =>
                rw [htbh] at hout
                have hτ : ChainOut c.d σ τ :=
                  (transferByHandle_chain_le c.d c.d act.caller _ σ).1 reply τ htbh
                simp only [SpecM.get, specM_bind, SpecM.set, SpecM.updDom, SpecM.modify,
                  SpecM.setReg] at hout
                subst hout
                refine ⟨fun a σ' h => ?_, fun er σ' h => by simp at h⟩
                simp only [Res.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
                set X : MachineState := { τ with
                  gates := Loom.Fun.update τ.gates gid
                    { (τ.gates gid) with act := none } } with hX
                have hXd : X.doms = τ.doms := rfl
                refine ⟨gid, act, hserv, hgact, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro g' hg'
                  show Loom.Fun.update τ.gates gid _ g' = σ.gates g'
                  rw [Loom.Fun.update_ne _ _ _ _ hg']
                  exact congrFun hτ.1 g'
                · show (Loom.Fun.update τ.gates gid _ gid).act = none
                  rw [Loom.Fun.update_same]
                · show (Loom.Fun.update τ.gates gid _ gid).config = _
                  rw [Loom.Fun.update_same]
                  show (τ.gates gid).config = (σ.gates gid).config
                  rw [congrFun hτ.1 gid]
                · -- maxDonation
                  intro e'
                  by_cases hecl : e' = act.caller
                  · subst hecl
                    rw [setDom_doms_same]
                    show (((_ : MachineState).doms act.caller).setReg
                      act.callerRd reply).maxDonation = _
                    rw [setDom_doms_same]
                    unfold DomainState.setReg
                    split
                    · by_cases hecd : act.caller = c.d
                      · rw [hecd, setDom_doms_same, hXd]; exact hτ.2.2.2.1 c.d
                      · rw [setDom_doms_ne _ _ _ _ hecd, hXd]; exact hτ.2.2.2.1 act.caller
                    · by_cases hecd : act.caller = c.d
                      · rw [hecd, setDom_doms_same, hXd]; exact hτ.2.2.2.1 c.d
                      · rw [setDom_doms_ne _ _ _ _ hecd, hXd]; exact hτ.2.2.2.1 act.caller
                  · rw [setDom_doms_ne _ _ _ _ hecl, setDom_doms_ne _ _ _ _ hecl]
                    by_cases hecd : e' = c.d
                    · subst hecd
                      rw [setDom_doms_same, hXd]; exact hτ.2.2.2.1 c.d
                    · rw [setDom_doms_ne _ _ _ _ hecd, hXd]; exact hτ.2.2.2.1 e'
                · -- budgets outside c.d
                  intro e' hecd
                  by_cases hecl : e' = act.caller
                  · subst hecl
                    rw [setDom_doms_same]
                    show (((_ : MachineState).doms act.caller).setReg
                      act.callerRd reply).budget = _
                    rw [setDom_doms_same]
                    unfold DomainState.setReg
                    split
                    · rw [setDom_doms_ne _ _ _ _ hecd, hXd]; exact hτ.2.2.2.2 act.caller hecd
                    · rw [setDom_doms_ne _ _ _ _ hecd, hXd]; exact hτ.2.2.2.2 act.caller hecd
                  · rw [setDom_doms_ne _ _ _ _ hecl, setDom_doms_ne _ _ _ _ hecl,
                        setDom_doms_ne _ _ _ _ hecd, hXd]
                    exact hτ.2.2.2.2 e' hecd
                · -- serving outside c.d
                  intro e' hecd
                  by_cases hecl : e' = act.caller
                  · subst hecl
                    rw [setDom_doms_same]
                    show (((_ : MachineState).doms act.caller).setReg
                      act.callerRd reply).serving = _
                    rw [setDom_doms_same]
                    unfold DomainState.setReg
                    split
                    · rw [setDom_doms_ne _ _ _ _ hecd, hXd]; exact hτ.2.2.1 act.caller
                    · rw [setDom_doms_ne _ _ _ _ hecd, hXd]; exact hτ.2.2.1 act.caller
                  · rw [setDom_doms_ne _ _ _ _ hecl, setDom_doms_ne _ _ _ _ hecl,
                        setDom_doms_ne _ _ _ _ hecd, hXd]
                    exact hτ.2.2.1 e'
                · -- serving of c.d restored
                  by_cases hecl : c.d = act.caller
                  · rw [← hecl, setDom_doms_same]
                    show (((_ : MachineState).doms c.d).setReg
                      act.callerRd reply).serving = _
                    unfold DomainState.setReg
                    split
                    · rw [setDom_doms_same, setDom_doms_same]
                    · rw [setDom_doms_same, setDom_doms_same]
                  · rw [setDom_doms_ne _ _ _ _ hecl, setDom_doms_ne _ _ _ _ hecl,
                        setDom_doms_same]
                · -- run outside act.caller
                  intro e' hecl
                  rw [setDom_doms_ne _ _ _ _ hecl, setDom_doms_ne _ _ _ _ hecl]
                  by_cases hecd : e' = c.d
                  · subst hecd
                    rw [setDom_doms_same]
                    show ((X.doms c.d)).run = _
                    rw [hXd]; exact hτ.2.1 c.d
                  · rw [setDom_doms_ne _ _ _ _ hecd, hXd]; exact hτ.2.1 e'
                · -- the caller runs
                  rw [setDom_doms_same]
                  show (((_ : MachineState).doms act.caller).setReg
                    act.callerRd reply).run = _
                  rw [setDom_doms_same]
                  unfold DomainState.setReg
                  split <;> rfl
  exact ⟨fun a σ' h => (body _ h).1 a σ' rfl, fun er σ' h => (body _ h).2 er σ' rfl⟩

/-- **The exec-level chain classification** (the 6th ISA sweep): every
instruction's `exec` either frames the chain observables (`ChainOut` — the
22 calm ops and *every* err outcome), or is a successful `gate_call`
(`GateCallShape`), a successful `gate_return` (`GateReturnShape`), or the
voluntary `halt` (`haltDom`). -/
theorem exec_chain (instr) (hmem : instr ∈ isa) (c : Ctx) (σ : MachineState) :
    (∀ a σ', instr.sem.exec c σ = .ok a σ' →
      ChainOut c.d σ σ' ∨ GateCallShape c σ σ' ∨ GateReturnShape c σ σ' ∨
      σ' = σ.haltDom c.d 0) ∧
    (∀ er σ', instr.sem.exec c σ = .err er σ' → ChainOut c.d σ σ') := by
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  have ofChainLe : ∀ {mm : SpecM Unit}, ChainLe c.d mm →
      (instr.sem.exec c σ = mm σ) →
      (∀ a σ', instr.sem.exec c σ = .ok a σ' →
        ChainOut c.d σ σ' ∨ GateCallShape c σ σ' ∨ GateReturnShape c σ σ' ∨
        σ' = σ.haltDom c.d 0) ∧
      (∀ er σ', instr.sem.exec c σ = .err er σ' → ChainOut c.d σ σ') := by
    intro mm h heq
    exact ⟨fun a σ' he => .inl ((h σ).1 a σ' (heq ▸ he)),
           fun er σ' he => (h σ).2 er σ' (heq ▸ he)⟩
  rcases List.mem_append.mp hmem' with hb | hs
  · exact ofChainLe (base_chain_le c.d instr hb c) rfl
  · fin_cases hs
    case _ => -- cap_dup
      refine ofChainLe ?_ rfl
      refine ChainLe.bind (ChainLe.reg _ _) fun hw => ?_
      refine ChainLe.bind (ChainLe.reg _ _) fun dw => ?_
      refine ChainLe.bind (ChainLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show ChainLe c.d (match e.kind with
        | .mem base len perms =>
            Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h
        | .gate gid =>
            (Pure.pure (CapKind.gate gid) : SpecM CapKind) >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived c.d kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h)
      cases e.kind with
      | mem b l p =>
          exact ChainLe.bind (ChainLe.narrow _ _ _ _) fun kind =>
            ChainLe.bind (ChainLe.allocDerived _ _ _) fun h => ChainLe.setReg _ _ _ _
      | gate i =>
          exact ChainLe.bind (ChainLe.pure _) fun kind =>
            ChainLe.bind (ChainLe.allocDerived _ _ _) fun h => ChainLe.setReg _ _ _ _
    case _ => -- cap_drop
      refine ofChainLe ?_ rfl
      refine ChainLe.bind (ChainLe.reg _ _) fun hw => ?_
      refine ChainLe.bind (ChainLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show ChainLe c.d (SpecM.get >>= fun σ0 =>
        SpecM.set ((((match σ0.parentOf c.d s with
            | some p => σ0.reparent ⟨c.d, s, g⟩ p
            | none => σ0.orphanChildren ⟨c.d, s, g⟩).clearSlot c.d s).sweepRegions).sweepMover) >>=
          fun _ => SpecM.setReg c.d c.op.rd 0)
      refine ChainLe.getD _ fun σ0 => ?_
      constructor
      · intro a σ' he
        cases hp : σ0.parentOf c.d s with
        | some p =>
            rw [hp] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            refine ChainOut.trans ?_
              (ChainOut.setDomOf _ c.d c.d _ (setReg_run _ _ _) (setReg_serving _ _ _)
                (by unfold DomainState.setReg; split <;> rfl)
                (fun _ => by unfold DomainState.setReg; split <;> rfl))
            exact (reparent_chainOut c.d σ0 _ _).trans
              ((clearSlot_chainOut c.d _ c.d s).trans
                ((sweepRegions_chainOut c.d _).trans (sweepMover_chainOut c.d _)))
        | none =>
            rw [hp] at he
            simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
            injection he with _ h2; subst h2
            refine ChainOut.trans ?_
              (ChainOut.setDomOf _ c.d c.d _ (setReg_run _ _ _) (setReg_serving _ _ _)
                (by unfold DomainState.setReg; split <;> rfl)
                (fun _ => by unfold DomainState.setReg; split <;> rfl))
            exact (orphanChildren_chainOut c.d σ0 _).trans
              ((clearSlot_chainOut c.d _ c.d s).trans
                ((sweepRegions_chainOut c.d _).trans (sweepMover_chainOut c.d _)))
      · intro er σ' he
        cases hp : σ0.parentOf c.d s with
        | some p => rw [hp] at he
                    simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
        | none => rw [hp] at he
                  simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
    case _ => -- cap_revoke
      refine ofChainLe ?_ rfl
      refine ChainLe.bind (ChainLe.reg _ _) fun hw => ?_
      refine ChainLe.bind (ChainLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show ChainLe c.d (SpecM.require (decide (e.kind.cls = .mem)) .badCap >>= fun _ =>
        SpecM.get >>= fun σ0 =>
        SpecM.set (((σ0.destroyMarked (σ0.marks ⟨c.d, s, g⟩)).sweepRegions).sweepMover) >>=
        fun _ => SpecM.setReg c.d c.op.rd 0)
      refine ChainLe.bind (ChainLe.require _ _) fun _ => ?_
      refine ChainLe.getD _ fun σ0 => ?_
      constructor
      · intro a σ' he
        simp only [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
        injection he with _ h2; subst h2
        refine ChainOut.trans ?_
          (ChainOut.setDomOf _ c.d c.d _ (setReg_run _ _ _) (setReg_serving _ _ _)
            (by unfold DomainState.setReg; split <;> rfl)
            (fun _ => by unfold DomainState.setReg; split <;> rfl))
        exact (destroyMarked_chainOut c.d σ0 _).trans
          ((sweepRegions_chainOut c.d _).trans (sweepMover_chainOut c.d _))
      · intro er σ' he
        simp [SpecM.set, specM_bind, SpecM.setReg, SpecM.modify] at he
    case _ => -- mem_grant
      refine ofChainLe ?_ rfl
      refine ChainLe.bind (ChainLe.reg _ _) fun hw => ?_
      refine ChainLe.bind (ChainLe.reg _ _) fun dw => ?_
      refine ChainLe.bind (ChainLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show ChainLe c.d (match e.kind with
        | .gate _ => (SpecM.raise .badCap : SpecM Unit)
        | .mem base len perms =>
            Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
            Machines.Lnp64u.Isa.allocDerived (descDom dw) kind ⟨c.d, s, g⟩ >>= fun h =>
            SpecM.setReg c.d c.op.rd h)
      cases e.kind with
      | gate gid => exact ChainLe.raise _
      | mem base len perms =>
          exact ChainLe.bind (ChainLe.narrow _ _ _ _) fun kind =>
            ChainLe.bind (ChainLe.allocDerived _ _ _) fun h => ChainLe.setReg _ _ _ _
    case _ => -- map
      refine ofChainLe ?_ rfl
      refine ChainLe.bind (ChainLe.reg _ _) fun hw => ?_
      refine ChainLe.bind (ChainLe.capLive _ _) fun r => ?_
      obtain ⟨s, g, e⟩ := r
      show ChainLe c.d (match e.kind with
        | .gate _ => (SpecM.raise .badCap : SpecM Unit)
        | .mem base len perms =>
            SpecM.updDom c.d (fun ds =>
              { ds with regions :=
                  (Loom.Fun.update ds.regions
                    ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
                    (some { base := base, len := len, perms := perms
                            backing := ⟨c.d, s, g⟩ })) }) >>= fun _ =>
            SpecM.setReg c.d c.op.rd 0)
      cases e.kind with
      | gate gid => exact ChainLe.raise _
      | mem base len perms =>
          exact ChainLe.bind
            (ChainLe.updDomOf _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
              (fun _ _ => rfl))
            fun _ => ChainLe.setReg _ _ _ _
    case _ => -- unmap
      refine ofChainLe ?_ rfl
      exact ChainLe.bind
        (ChainLe.updDomOf _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ _ => rfl))
        fun _ => ChainLe.setReg _ _ _ _
    case _ => -- gate_call
      exact ⟨fun a σ' he => .inr (.inl ((gatecall_chain c σ).1 a σ' he)),
             fun er σ' he => ChainOut.of_eq ((gatecall_chain c σ).2 er σ' he)⟩
    case _ => -- gate_return
      exact ⟨fun a σ' he => .inr (.inr (.inl ((gatereturn_chain c σ).1 a σ' he))),
             fun er σ' he => ChainOut.of_eq ((gatereturn_chain c σ).2 er σ' he)⟩
    case _ => -- move
      refine ofChainLe ?_ rfl
      refine ChainLe.getD _ fun σg => (?_ : ChainLe c.d _) σg
      refine ChainLe.bind (ChainLe.require _ _) fun _ => ?_
      refine ChainLe.bind (ChainLe.reg _ _) fun aw => ?_
      refine ChainLe.bind (ChainLe.load _ _) fun srcH => ?_
      refine ChainLe.bind (ChainLe.load _ _) fun dstH => ?_
      refine ChainLe.bind (ChainLe.load _ _) fun lenW => ?_
      refine ChainLe.bind (ChainLe.load _ _) fun stW => ?_
      refine ChainLe.bind (ChainLe.capLive _ _) fun rs => ?_
      obtain ⟨ss, gs_, es⟩ := rs
      refine ChainLe.bind (ChainLe.capLive _ _) fun rd_ => ?_
      obtain ⟨sd, gd, ed⟩ := rd_
      show ChainLe c.d (match es.kind, ed.kind with
        | .mem sb sl sp, .mem db dl dp =>
            SpecM.require sp.r .permDenied >>= fun _ =>
            SpecM.require dp.w .permDenied >>= fun _ =>
            SpecM.require (decide (lenW.toNat ≤ sl.toNat) && decide (lenW.toNat ≤ dl.toNat))
              .outOfRange >>= fun _ =>
            SpecM.get >>= fun σ1 =>
            SpecM.demand (σ1.domCovers c.d (stW.setWidth 12)
              { r := false, w := true, x := false }) .memoryAuthority >>= fun _ =>
            SpecM.set ({ σ1 with mover :=
              (some { owner := c.d, src := ⟨c.d, ss, gs_⟩, dst := ⟨c.d, sd, gd⟩
                      srcCur := sb, dstCur := db, remaining := lenW.toNat
                      statusAddr := stW.setWidth 12 }) }) >>= fun _ =>
            SpecM.setReg c.d c.op.rd 0
        | _, _ => (SpecM.raise .badCap : SpecM Unit))
      cases es.kind with
      | gate gi =>
          cases ed.kind with
          | gate _ => exact ChainLe.raise _
          | mem db dl dp => exact ChainLe.raise _
      | mem sb sl sp =>
          cases ed.kind with
          | gate _ => exact ChainLe.raise _
          | mem db dl dp =>
              refine ChainLe.bind (ChainLe.require _ _) fun _ => ?_
              refine ChainLe.bind (ChainLe.require _ _) fun _ => ?_
              refine ChainLe.bind (ChainLe.require _ _) fun _ => ?_
              refine ChainLe.getD _ fun σ1 => ?_
              constructor
              · intro a σ' he
                by_cases hcov : σ1.domCovers c.d (stW.setWidth 12)
                    { r := false, w := true, x := false }
                · simp only [SpecM.demand, hcov, if_true, specM_pure, specM_bind, SpecM.set,
                    SpecM.setReg, SpecM.modify] at he
                  injection he with _ h2; subst h2
                  refine ChainOut.trans ?_
                    (ChainOut.setDomOf _ c.d c.d _ (setReg_run _ _ _) (setReg_serving _ _ _)
                      (by unfold DomainState.setReg; split <;> rfl)
                      (fun _ => by unfold DomainState.setReg; split <;> rfl))
                  exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
                · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
              · intro er σ' he
                by_cases hcov : σ1.domCovers c.d (stW.setWidth 12)
                    { r := false, w := true, x := false }
                · simp [SpecM.demand, hcov, specM_pure, specM_bind, SpecM.set,
                    SpecM.setReg, SpecM.modify] at he
                · simp [SpecM.demand, hcov, SpecM.fatal, specM_bind] at he
    case _ => -- yield
      refine ofChainLe ?_ rfl
      exact ChainLe.bind
        (ChainLe.updDomOf _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ h => absurd rfl h))
        fun _ => ChainLe.setReg _ _ _ _
    case _ => -- halt
      constructor
      · intro a σ' he
        refine .inr (.inr (.inr ?_))
        simp only [SpecM.modify] at he
        injection he with _ h2; exact h2.symm
      · intro er σ' he
        simp [SpecM.modify] at he

end Machines.Lnp64u
