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

end Machines.Lnp64u
