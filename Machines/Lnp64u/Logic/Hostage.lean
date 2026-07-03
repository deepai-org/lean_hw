import Machines.Lnp64u.Logic.Budget
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

end Machines.Lnp64u
