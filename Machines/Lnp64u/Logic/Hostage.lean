import Machines.Lnp64u.Logic.Wf

/-!
# T6 support: hyperperiod, donation ceiling, unwind and scheduler lemmas

The per-cycle ingredients of the `no_hostage` liveness proof (T6). All
lemmas here are sorry-free; the assembly into the full resume bound lives
in `Theorems/T6.lean`.

Contents:
* `hyperL` / `maxDonationBound` — the manifest-computable quantities the
  (repaired) `resumeBound` is built from, with positivity/divisibility/
  ceiling lemmas.
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
core stalls until refill. (In the T6 counting argument such cycles are
charged to the payer's spent budget since its last refill.) -/
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

end Machines.Lnp64u
