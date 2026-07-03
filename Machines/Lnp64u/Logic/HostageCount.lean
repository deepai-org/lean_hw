import Machines.Lnp64u.Logic.HostageFrame
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# T6 interference counting (obligation 3/5 core)

The per-cycle potential `Ψ = 2·massExcept + inflight-remaining + #non-halted`
drops by ≥ 1 on every frozen (non-chain) cycle once the origin is funded —
idle is impossible (the head is eligible), stalls are excluded (`StallFree`),
and every other arm burns occupancy, budget, or a domain. Refills refund at
most `gainAt` per cycle; over `n` cycles the refund is bounded through
`StrictlySchedulable` by `(n/L + 1)·(L-1)/2 + 2·budgetMass`.
-/

namespace Machines.Lnp64u

open Loom

/-- Remaining occupancy of the latched instruction. -/
def inflightLeft (σ : MachineState) : Nat :=
  match σ.inflight with
  | some fl => fl.cyclesLeft
  | none => 0

theorem inflightLeft_none {σ : MachineState} (h : σ.inflight = none) :
    inflightLeft σ = 0 := by
  unfold inflightLeft
  rw [h]

theorem inflightLeft_some {σ : MachineState} {fl : InFlight}
    (h : σ.inflight = some fl) : inflightLeft σ = fl.cyclesLeft := by
  unfold inflightLeft
  rw [h]

/-- Number of non-halted domains. -/
def nonHalted (σ : MachineState) : Nat :=
  (Finset.univ.filter (fun e : DomainId => (σ.doms e).run ≠ .halted)).card

theorem nonHalted_le (σ : MachineState) : nonHalted σ ≤ numDomains := by
  have h1 := Finset.card_filter_le Finset.univ
    (fun e : DomainId => (σ.doms e).run ≠ .halted)
  simpa using h1

theorem nonHalted_mono {σ σ' : MachineState} (h : HaltedStays σ σ') :
    nonHalted σ' ≤ nonHalted σ := by
  refine Finset.card_le_card ?_
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  intro hh
  exact he (h e hh)

theorem nonHalted_lt {σ σ' : MachineState} (h : HaltedStays σ σ')
    {e₀ : DomainId} (h₀ : (σ.doms e₀).run ≠ .halted)
    (h₀' : (σ'.doms e₀).run = .halted) : nonHalted σ' < nonHalted σ := by
  refine Finset.card_lt_card ?_
  constructor
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    intro hh
    exact he (h e hh)
  · intro hsup
    have := hsup (Finset.mem_filter.mpr ⟨Finset.mem_univ e₀, h₀⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this h₀'

/-- **The T6 potential.** -/
def psi (σ : MachineState) (o : DomainId) : Nat :=
  2 * massExcept σ o + inflightLeft σ + nonHalted σ

/-- The refill inflow outside `o` this cycle. -/
def gainAt (m : Manifest) (σ : MachineState) (o : DomainId) : Nat :=
  if σ.cycle = 0 then 0
  else ∑ e ∈ Finset.univ.erase o,
    (if σ.cycle % (m.doms e).periodP = 0 then (m.doms e).budgetQ else 0)

/-- Refills raise the outside mass by at most `gainAt`. -/
theorem massExcept_refill (m : Manifest) (σ : MachineState) (o : DomainId) :
    massExcept (refillPhase m σ) o ≤ massExcept σ o + gainAt m σ o := by
  unfold massExcept gainAt
  by_cases h0 : σ.cycle = 0
  · simp only [h0, if_true]
    refine Nat.le_trans (Finset.sum_le_sum ?_) (Nat.le_add_right _ _)
    intro e _
    unfold refillPhase
    rw [if_pos h0]
  · simp only [h0, if_false]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro e _
    rcases refillPhase_budget_cases m σ e with h' | ⟨_, hbd, h'⟩
    · rw [h']
      exact Nat.le_add_right _ _
    · rw [h', if_pos hbd]
      omega

/-- The outside mass is bounded by the budget mass (given `BudgetCap`). -/
theorem massExcept_le_budgetMass (m : Manifest) (σ : MachineState)
    (hcap : BudgetCap m σ) (o : DomainId) : massExcept σ o ≤ budgetMass m := by
  unfold massExcept budgetMass
  have h1 : ∑ e ∈ Finset.univ.erase o, (σ.doms e).budget ≤
      ∑ e ∈ Finset.univ.erase o, (m.doms e).budgetQ :=
    Finset.sum_le_sum (fun e _ => hcap e)
  have h2 : ∑ e ∈ Finset.univ.erase o, (m.doms e).budgetQ ≤
      ∑ e : DomainId, (m.doms e).budgetQ :=
    Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  have h3 : ∑ e : DomainId, (m.doms e).budgetQ =
      ((List.finRange numDomains).map (fun e => (m.doms e).budgetQ)).sum := by
    rw [Fin.sum_univ_def]
  omega

/-- Multiples of `P` in a window of `n` cycles: at most `n / P + 2`. -/
theorem card_multiples (P : Nat) (hP : 0 < P) (c₀ n : Nat) :
    ((Finset.range n).filter (fun t => (c₀ + t) % P = 0)).card ≤ n / P + 2 := by
  have hsub : ∀ t ∈ (Finset.range n).filter (fun t => (c₀ + t) % P = 0),
      (c₀ + t) / P ∈ Finset.Icc (c₀ / P) ((c₀ + n) / P) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    refine Finset.mem_Icc.mpr ⟨Nat.div_le_div_right (Nat.le_add_right _ _), ?_⟩
    exact Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun t => (c₀ + t) / P)
      ((Finset.range n).filter (fun t => (c₀ + t) % P = 0)) := by
    intro t₁ h₁ t₂ h₂ heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at h₁ h₂
    have hd₁ : P * ((c₀ + t₁) / P) = c₀ + t₁ := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h₁.2)
    have hd₂ : P * ((c₀ + t₂) / P) = c₀ + t₂ := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h₂.2)
    simp only at heq
    rw [heq] at hd₁
    omega
  have hcard : ((Finset.range n).filter (fun t => (c₀ + t) % P = 0)).card ≤
      (Finset.Icc (c₀ / P) ((c₀ + n) / P)).card := by
    refine Finset.card_le_card_of_injOn (fun t => (c₀ + t) / P) ?_ hinj
    intro a ha
    exact hsub a ha
  have hicc : (Finset.Icc (c₀ / P) ((c₀ + n) / P)).card =
      (c₀ + n) / P + 1 - c₀ / P := Nat.card_Icc _ _
  have hdiv : (c₀ + n) / P ≤ c₀ / P + n / P + 1 := by
    rw [Nat.add_div hP]
    split <;> omega
  rw [hicc] at hcard
  generalize hC : (c₀ + n) / P = C at hcard hdiv
  generalize hA : c₀ / P = A at hcard hdiv
  generalize hB : n / P = B at hdiv ⊢
  omega

/-- Summed inflow over a window, per domain, then totalled: the refund term
of the T6 potential. -/
theorem gainSum_le (m : Manifest) (hwfm : m.WF) (σ : MachineState) (o : DomainId)
    (n : Nat) :
    ∑ t ∈ Finset.range n, gainAt m (stepN m t σ) o ≤
    ∑ e ∈ Finset.univ.erase o, (m.doms e).budgetQ * (n / (m.doms e).periodP + 2) := by
  have hswap : ∑ t ∈ Finset.range n, gainAt m (stepN m t σ) o ≤
      ∑ t ∈ Finset.range n, ∑ e ∈ Finset.univ.erase o,
        (if (σ.cycle + t) % (m.doms e).periodP = 0 ∧ σ.cycle + t ≠ 0
         then (m.doms e).budgetQ else 0) := by
    refine Finset.sum_le_sum ?_
    intro t _
    unfold gainAt
    rw [stepN_cycle]
    by_cases h0 : σ.cycle + t = 0
    · rw [if_pos h0]
      exact Nat.zero_le _
    · rw [if_neg h0]
      refine Finset.sum_le_sum ?_
      intro e _
      by_cases hb : (σ.cycle + t) % (m.doms e).periodP = 0
      · rw [if_pos hb, if_pos ⟨hb, h0⟩]
      · rw [if_neg hb, if_neg (fun hc => hb hc.1)]
  rw [Finset.sum_comm] at hswap
  refine Nat.le_trans hswap (Finset.sum_le_sum ?_)
  intro e _
  have hP : 0 < (m.doms e).periodP := hwfm.period_pos e
  have h1 : ∑ t ∈ Finset.range n,
      (if (σ.cycle + t) % (m.doms e).periodP = 0 ∧ σ.cycle + t ≠ 0
       then (m.doms e).budgetQ else 0) ≤
      ∑ t ∈ (Finset.range n).filter
        (fun t => (σ.cycle + t) % (m.doms e).periodP = 0), (m.doms e).budgetQ := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum ?_
    intro t _
    by_cases hc : (σ.cycle + t) % (m.doms e).periodP = 0 ∧ σ.cycle + t ≠ 0
    · rw [if_pos hc, if_pos hc.1]
    · rw [if_neg hc]
      exact Nat.zero_le _
  have h1' : ∑ t ∈ (Finset.range n).filter
      (fun t => (σ.cycle + t) % (m.doms e).periodP = 0), (m.doms e).budgetQ =
      ((Finset.range n).filter
        (fun t => (σ.cycle + t) % (m.doms e).periodP = 0)).card * (m.doms e).budgetQ :=
    Finset.sum_const_nat (fun _ _ => rfl)
  rw [h1'] at h1
  refine Nat.le_trans h1 ?_
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (card_multiples _ hP _ _)

/-- The refund bound in hyperperiod terms: strict schedulability turns the
per-window inflow into `(n/L + 1)·(L-1)/2`-style slack. Stated doubled to
stay in `Nat`. -/
theorem gainSum_bound (m : Manifest) (hwfm : m.WF)
    (hsched : 2 * ((List.finRange numDomains).map
      (fun d => (m.doms d).budgetQ * (hyperL m / (m.doms d).periodP))).sum < hyperL m)
    (σ : MachineState) (o : DomainId) (n : Nat) :
    2 * ∑ t ∈ Finset.range n, gainAt m (stepN m t σ) o ≤
    (n / hyperL m + 1) * (hyperL m - 1) + 4 * budgetMass m := by
  have hL : 0 < hyperL m := hyperL_pos m hwfm
  have h1 := gainSum_le m hwfm σ o n
  -- per-domain: Q·(n/P + 2) ≤ Q·(n/L + 1)·(L/P) + 2Q
  have h2 : ∑ e ∈ Finset.univ.erase o, (m.doms e).budgetQ * (n / (m.doms e).periodP + 2) ≤
      (n / hyperL m + 1) *
        (∑ e : DomainId, (m.doms e).budgetQ * (hyperL m / (m.doms e).periodP)) +
      2 * budgetMass m := by
    have h3 : ∀ e : DomainId,
        (m.doms e).budgetQ * (n / (m.doms e).periodP + 2) ≤
        (n / hyperL m + 1) * ((m.doms e).budgetQ * (hyperL m / (m.doms e).periodP)) +
          2 * (m.doms e).budgetQ := by
      intro e
      have hP : 0 < (m.doms e).periodP := hwfm.period_pos e
      have hdvd : (m.doms e).periodP ∣ hyperL m := periodP_dvd_hyperL m e
      have hnP : n / (m.doms e).periodP ≤ (n / hyperL m + 1) * (hyperL m / (m.doms e).periodP) := by
        have hnle : n ≤ (n / hyperL m + 1) * hyperL m := by
          have h₁ := Nat.div_add_mod n (hyperL m)
          have h₂ := Nat.mod_lt n hL
          have hmul : (n / hyperL m + 1) * hyperL m =
              hyperL m * (n / hyperL m) + hyperL m := by ring
          omega
        calc n / (m.doms e).periodP
            ≤ ((n / hyperL m + 1) * hyperL m) / (m.doms e).periodP :=
              Nat.div_le_div_right hnle
          _ = (n / hyperL m + 1) * (hyperL m / (m.doms e).periodP) :=
              Nat.mul_div_assoc _ hdvd
      calc (m.doms e).budgetQ * (n / (m.doms e).periodP + 2)
          = (m.doms e).budgetQ * (n / (m.doms e).periodP) + 2 * (m.doms e).budgetQ := by
            rw [Nat.mul_add]
            omega
        _ ≤ (m.doms e).budgetQ * ((n / hyperL m + 1) * (hyperL m / (m.doms e).periodP)) +
              2 * (m.doms e).budgetQ := by
            have := Nat.mul_le_mul_left (m.doms e).budgetQ hnP
            omega
        _ = (n / hyperL m + 1) * ((m.doms e).budgetQ * (hyperL m / (m.doms e).periodP)) +
              2 * (m.doms e).budgetQ := by
            ring_nf
    have h4 : ∑ e ∈ Finset.univ.erase o, (m.doms e).budgetQ * (n / (m.doms e).periodP + 2) ≤
        ∑ e ∈ Finset.univ.erase o,
          ((n / hyperL m + 1) * ((m.doms e).budgetQ * (hyperL m / (m.doms e).periodP)) +
            2 * (m.doms e).budgetQ) :=
      Finset.sum_le_sum (fun e _ => h3 e)
    rw [Finset.sum_add_distrib] at h4
    have h5 : ∑ e ∈ Finset.univ.erase o,
        (n / hyperL m + 1) * ((m.doms e).budgetQ * (hyperL m / (m.doms e).periodP)) ≤
        (n / hyperL m + 1) *
          ∑ e : DomainId, (m.doms e).budgetQ * (hyperL m / (m.doms e).periodP) := by
      rw [← Finset.mul_sum]
      refine Nat.mul_le_mul_left _ ?_
      exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    have h6 : ∑ e ∈ Finset.univ.erase o, 2 * (m.doms e).budgetQ ≤ 2 * budgetMass m := by
      rw [← Finset.mul_sum]
      refine Nat.mul_le_mul_left _ ?_
      have := Finset.sum_le_sum_of_subset (f := fun e => (m.doms e).budgetQ)
        (Finset.erase_subset o Finset.univ)
      unfold budgetMass
      rw [← Fin.sum_univ_def]
      exact this
    omega
  have h7 : ∑ e : DomainId, (m.doms e).budgetQ * (hyperL m / (m.doms e).periodP) =
      ((List.finRange numDomains).map
        (fun d => (m.doms d).budgetQ * (hyperL m / (m.doms d).periodP))).sum := by
    rw [Fin.sum_univ_def]
  have h8 : 2 * ((n / hyperL m + 1) *
      (∑ e : DomainId, (m.doms e).budgetQ * (hyperL m / (m.doms e).periodP))) ≤
      (n / hyperL m + 1) * (hyperL m - 1) := by
    rw [h7]
    have h9 : 2 * ((List.finRange numDomains).map
        (fun d => (m.doms d).budgetQ * (hyperL m / (m.doms d).periodP))).sum ≤
        hyperL m - 1 := by omega
    calc 2 * ((n / hyperL m + 1) * ((List.finRange numDomains).map
          (fun d => (m.doms d).budgetQ * (hyperL m / (m.doms d).periodP))).sum)
        = (n / hyperL m + 1) * (2 * ((List.finRange numDomains).map
          (fun d => (m.doms d).budgetQ * (hyperL m / (m.doms d).periodP))).sum) := by
          ring_nf
      _ ≤ (n / hyperL m + 1) * (hyperL m - 1) := Nat.mul_le_mul_left _ h9
  omega

/-! ## Per-cycle transports -/

theorem psi_congr {σ σ' : MachineState} (hd : σ'.doms = σ.doms)
    (hi : σ'.inflight = σ.inflight) (o : DomainId) : psi σ' o = psi σ o := by
  unfold psi massExcept nonHalted inflightLeft
  rw [hd, hi]

theorem nonHalted_congr {σ σ' : MachineState}
    (h : ∀ e, (σ'.doms e).run = (σ.doms e).run) : nonHalted σ' = nonHalted σ := by
  unfold nonHalted
  congr 1
  refine Finset.filter_congr ?_
  intro e _
  rw [h e]

theorem massExcept_congr {σ σ' : MachineState}
    (h : ∀ e, (σ'.doms e).budget = (σ.doms e).budget) (o : DomainId) :
    massExcept σ' o = massExcept σ o :=
  Finset.sum_congr rfl (fun e _ => h e)

/-- **The per-cycle master dichotomy** (T6 obligation 5's engine). One step
from a reachable state with `d` blocked on `gd`, chain `(l, h)`, and no
head instruction in flight is: `d` resumes; a clean strict measure drop
(pop); a head issue (quantified drop, head in flight); or a frozen cycle —
chain, measure, payer and origin budget carried, still quiet, and (when the
origin is funded at the refill point) the potential drops. -/
theorem cycle_master (m : Manifest) (hwfm : m.WF)
    (hstall : ∀ σ, (machine m).Reachable σ → ¬ StallsAt m (refillPhase m σ))
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    {d : DomainId} {gd : GateId} (hb : (σ.doms d).run = .blocked gd)
    {l : List GateId} {h : DomainId} (hcf : ChainFrom σ d l h)
    (hquiet : ∀ fl, σ.inflight = some fl → fl.dom ≠ h) :
    ((step m σ).doms d).run ≠ .blocked gd ∨
    (((step m σ).doms d).run = .blocked gd ∧ (step m σ).inflight = none ∧
      chainMeasure m (step m σ) d < chainMeasure m σ d) ∨
    (((step m σ).doms d).run = .blocked gd ∧
      ChainFrom (step m σ) d l h ∧ (step m σ).payer d = σ.payer d ∧
      chainMeasure m (step m σ) d + chainW m ^ (maxChainDepth - l.length)
        ≤ chainMeasure m σ d ∧
      (∃ fl, (step m σ).inflight = some fl ∧ fl.dom = h)) ∨
    (((step m σ).doms d).run = .blocked gd ∧
      ChainFrom (step m σ) d l h ∧
      chainMeasure m (step m σ) d = chainMeasure m σ d ∧
      (step m σ).payer d = σ.payer d ∧
      ((step m σ).doms (σ.payer d)).budget
        = ((refillPhase m σ).doms (σ.payer d)).budget ∧
      (∀ fl, (step m σ).inflight = some fl → fl.dom ≠ h) ∧
      (0 < ((refillPhase m σ).doms (σ.payer d)).budget →
        psi (step m σ) (σ.payer d) + 1 ≤ psi σ (σ.payer d) + 2 * gainAt m σ (σ.payer d))) := by
  -- invariants
  have hwfσ : Wf σ := (wfa_invariant m hwfm σ hreach).1
  have hci : ChainInv m σ := chain_invariant m hwfm σ hreach
  have hdlσ : DepthLink σ := hci.depthLink
  set ρ := refillPhase m σ with hρdef
  have hwfρ : Wf ρ := refillPhase_preserves_wf m σ hwfσ
  have hdlρ : DepthLink ρ :=
    DepthLink.of_frame (refillPhase_gates m σ) (fun e => refillPhase_serving m σ e) hdlσ
  have hgρ : ρ.gates = σ.gates := refillPhase_gates m σ
  have hrρ : ∀ e, (ρ.doms e).run = (σ.doms e).run := fun e => refillPhase_run m σ e
  have hsρ : ∀ e, (ρ.doms e).serving = (σ.doms e).serving :=
    fun e => refillPhase_serving m σ e
  have hiρ : ρ.inflight = σ.inflight := refillPhase_inflight m σ
  have hbρ : (ρ.doms d).run = .blocked gd := by rw [hrρ d]; exact hb
  have hcfρ : ChainFrom ρ d l h :=
    hcf.frame (fun g' _ => by unfold gateCallee; rw [hgρ]) (fun y _ => hrρ y)
  have hlen : l.length ≤ maxChainDepth := chain_length_le hwfσ hdlσ hcf
  have hne : l ≠ [] := by
    cases hcf with
    | top hr => rw [hr] at hb; exact absurd hb (by simp)
    | link _ _ => simp
  have hdh : d ≠ h := by
    intro hE
    rw [hE, hcf.top_running] at hb
    exact absurd hb (by simp)
  have hheadserv : (ρ.doms h).serving = some (l.getLast hne) :=
    hcfρ.head_serving hwfρ hne
  have hpayρ : ρ.payer d = σ.payer d :=
    chainOrigin_congr maxChainDepth d (fun y _ => hsρ y) (fun y gv _ _ => by rw [hgρ])
  have hmeasρ : measAux (chainW m) ρ (maxChainDepth - 1) l =
      measAux (chainW m) σ (maxChainDepth - 1) l :=
    measAux_congr (fun g' _ => by rw [hgρ]) _
  have hmeasσ : chainMeasure m σ d = measAux (chainW m) σ (maxChainDepth - 1) l :=
    chainMeasure_of_chain hcf hlen
  have hd2 : (step m σ).doms = (corePhase m ρ).doms := by
    rw [hρdef]
    exact step_doms m σ
  have hg2 : (step m σ).gates = (corePhase m ρ).gates := by
    rw [hρdef]
    show (moverPhase (corePhase m (refillPhase m σ))).gates = _
    exact moverPhase_gates _
  have hi2 : (step m σ).inflight = (corePhase m ρ).inflight := by
    rw [hρdef]
    exact Wip.step_inflight_reduce m σ
  have hreach2 : (machine m).Reachable (step m σ) := Loom.TSys.Reachable.step hreach rfl
  have hwf2 : Wf (step m σ) := (wfa_invariant m hwfm _ hreach2).1
  have hci2 : ChainInv m (step m σ) := chain_invariant m hwfm _ hreach2
  -- glue: a FrozenStep ρ→κ turns into the F-arm's structural fields
  have glue : FrozenStep d l h ρ (corePhase m ρ) →
      (((step m σ).doms d).run = .blocked gd ∧
       ChainFrom (step m σ) d l h ∧
       chainMeasure m (step m σ) d = chainMeasure m σ d ∧
       (step m σ).payer d = σ.payer d ∧
       ((step m σ).doms (σ.payer d)).budget = (ρ.doms (σ.payer d)).budget) := by
    intro hfz
    have hfz2 : FrozenStep d l h (corePhase m ρ) (step m σ) :=
      FrozenStep.of_eq_parts hfz.chain hd2 hg2
    have hfz3 : FrozenStep d l h ρ (step m σ) := hfz.trans hfz2
    refine ⟨?_, hfz3.chain, ?_, ?_, ?_⟩
    · rw [hfz3.run_d]
      exact hbρ
    · have hml : (step m σ).doms d = (step m σ).doms d := rfl
      have hlenf : l.length ≤ maxChainDepth := hlen
      rw [chainMeasure_of_chain hfz3.chain hlenf, hmeasσ]
      rw [← hmeasρ]
      exact measAux_congr (fun g' hg' => hfz3.acts g' hg') _
    · rw [hfz3.payer, hpayρ]
    · have := hfz3.budget_o
      rw [hpayρ] at this
      exact this
  rcases corePhase_chain m ρ hwfρ with
    ⟨heq, hinfρ, hns⟩ |
    ⟨fl, hflρ, hgt, heq⟩ |
    ⟨fl, hflρ, hle, hrunfl, hinfκ, hsh⟩ |
    ⟨e, hinfρ, hsch, hrune, hinfκ, hsh⟩ |
    ⟨e, w, c, hinfρ, hsch, hrune, hcpos, hcle, hcbud, hinfs, hsh⟩
  · -- idle / stall
    have hfz : FrozenStep d l h ρ (corePhase m ρ) := FrozenStep.of_eq_parts hcfρ
      (by rw [heq]) (by rw [heq])
    obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := glue hfz
    refine .inr (.inr (.inr ⟨hF1, hF2, hF3, hF4, hF5, ?_, ?_⟩))
    · intro fl hfl
      rw [hi2, heq, hiρ] at hfl
      exact hquiet fl hfl
    · intro hfund
      exfalso
      rcases hns with hnone | hstl
      · have helig : Eligible ρ h := by
          refine ⟨hcfρ.top_running, ?_⟩
          rw [payer_chain hwfρ hdlρ hcfρ, hpayρ]
          exact hfund
        have := schedule_isSome_of_eligible m ρ h helig
        rw [hnone] at this
        simp at this
      · exact hstall σ hreach hstl
  · -- burn
    have hκd : (corePhase m ρ).doms = ρ.doms := by rw [heq]
    have hκg : (corePhase m ρ).gates = ρ.gates := by rw [heq]
    have hfz : FrozenStep d l h ρ (corePhase m ρ) := FrozenStep.of_eq_parts hcfρ hκd hκg
    obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := glue hfz
    refine .inr (.inr (.inr ⟨hF1, hF2, hF3, hF4, hF5, ?_, ?_⟩))
    · intro fl' hfl'
      rw [hi2, heq] at hfl'
      simp only at hfl'
      injection hfl' with hfl'
      rw [← hfl']
      show fl.dom ≠ h
      exact hquiet fl (by rw [← hiρ]; exact hflρ)
    · intro hfund
      have hmass : massExcept (step m σ) (σ.payer d) = massExcept ρ (σ.payer d) :=
        massExcept_congr (fun e => by rw [congrFun hd2 e, congrFun hκd e]) _
      have hmassρ := massExcept_refill m σ (σ.payer d)
      rw [← hρdef] at hmassρ
      have hilσ : inflightLeft σ = fl.cyclesLeft :=
        inflightLeft_some (by rw [← hiρ]; exact hflρ)
      have hil2 : inflightLeft (step m σ) = fl.cyclesLeft - 1 := by
        have hif : (step m σ).inflight = some { fl with cyclesLeft := fl.cyclesLeft - 1 } := by
          rw [hi2, heq]
        rw [inflightLeft_some hif]
      have hnh : nonHalted (step m σ) = nonHalted σ := by
        refine nonHalted_congr (fun e => ?_)
        rw [congrFun hd2 e, congrFun hκd e, hrρ e]
      have hnhρ : nonHalted ρ = nonHalted σ := nonHalted_congr hrρ
      unfold psi
      rw [hmass, hil2, hnh, hilσ]
      omega
  · -- retire (foreign or head-calm)
    have hflσ : σ.inflight = some fl := by rw [← hiρ]; exact hflρ
    have hflh : fl.dom ≠ h := hquiet fl hflσ
    have hfz : FrozenStep d l h ρ (corePhase m ρ) := by
      rcases hsh with hS | hS | hS | hS
      · exact FrozenStep.of_chainOut hwfρ hdlρ hbρ hcfρ hS hrunfl
      · exact FrozenStep.of_callShape hwfρ hdlρ hbρ hcfρ hS hrunfl hflh
      · exact FrozenStep.of_retShape hwfρ hdlρ hbρ hcfρ hS hrunfl hflh
      · exact FrozenStep.of_haltShape hwfρ hdlρ hbρ hcfρ hS hrunfl hflh
    obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := glue hfz
    refine .inr (.inr (.inr ⟨hF1, hF2, hF3, hF4, hF5, ?_, ?_⟩))
    · intro fl' hfl'
      rw [hi2, hinfκ] at hfl'
      exact absurd hfl' (by simp)
    · intro hfund
      have hmass2 : massExcept (step m σ) (σ.payer d) = massExcept (corePhase m ρ) (σ.payer d) :=
        massExcept_congr (fun e => by rw [congrFun hd2 e]) _
      have hmassκ : massExcept (corePhase m ρ) (σ.payer d) ≤ massExcept ρ (σ.payer d) :=
        corePhase_massExcept_le m ρ _
      have hmassρ := massExcept_refill m σ (σ.payer d)
      rw [← hρdef] at hmassρ
      have hilσ : inflightLeft σ = fl.cyclesLeft := inflightLeft_some hflσ
      have hpos1 : 1 ≤ fl.cyclesLeft := hci.inflightPos fl hflσ
      have hil2 : inflightLeft (step m σ) = 0 :=
        inflightLeft_none (by rw [hi2]; exact hinfκ)
      have hnh2 : nonHalted (step m σ) = nonHalted (corePhase m ρ) :=
        nonHalted_congr (fun e => by rw [congrFun hd2 e])
      have hnhκ : nonHalted (corePhase m ρ) ≤ nonHalted ρ :=
        nonHalted_mono (corePhase_halted m ρ hwfρ)
      have hnhρ : nonHalted ρ = nonHalted σ := nonHalted_congr hrρ
      unfold psi
      rw [hmass2, hil2, hnh2, hilσ]
      omega
  · -- fault-halt at issue time
    by_cases heh : e = h
    · -- HEAD halt: pop or resume
      subst heh
      obtain ⟨hmax, hbudo, hrh, hsdnone, hsoκ, hcase⟩ := hsh
      rcases hcase with ⟨hgeq, hro⟩ | ⟨g, a, hsg, hag, hacne, hgo, hga, hgc, hcr, hro⟩
      · -- gates untouched: impossible, the head serves a live gate
        exfalso
        obtain ⟨a0, ha0⟩ := hcfρ.gates_act hwfρ (l.getLast hne) (List.getLast_mem hne)
        have hact2 : ((step m σ).gates (l.getLast hne)).act = some a0 := by
          rw [hg2, hgeq]
          exact ha0
        have hcal2 : ((step m σ).gates (l.getLast hne)).config.callee = e := by
          rw [hg2, hgeq]
          exact (hwfρ.serving_gate e _ hheadserv).1
        have := (hwf2.gate_serving _ a0 hact2).1
        rw [hcal2] at this
        rw [congrFun hd2 e] at this
        rw [hsdnone] at this
        exact absurd this (by simp)
      · -- unwind: the popped gate is the head's
        have hgL : g = l.getLast hne := Option.some.inj (hsg.symm.trans hheadserv)
        by_cases hcd : a.caller = d
        · -- the caller is d itself: resumed
          refine .inl ?_
          rw [congrFun hd2 d, ← hcd, hcr]
          simp
        · -- pop: strict prefix
          have hcmem : a.caller ∈ chainMembers ρ d l :=
            hcfρ.act_caller_mem hwfρ g (hgL ▸ List.getLast_mem hne) a hag
          have hsplit := hcfρ.breakAt
            (fun g' hg' => by
              unfold gateCallee
              by_cases hE : g' = g
              · rw [hE, hgc]
              · rw [hgo g' hE])
            hcmem hacne hcr
            (fun y hy hyb hyh => hro y hyh hyb)
          obtain ⟨l₁, g0, l₂, hlsplit, hcfκ⟩ := hsplit
          have hlen₁ : l₁.length ≤ maxChainDepth := by
            have : l₁.length ≤ l.length := by
              rw [hlsplit]
              simp
            omega
          have hcf2 : ChainFrom (step m σ) d l₁ a.caller :=
            hcfκ.frame (fun g' _ => by unfold gateCallee; rw [hg2]) (fun y _ => by rw [hd2])
          refine .inr (.inl ⟨?_, ?_, ?_⟩)
          · rw [congrFun hd2 d, hro d hdh (Ne.symm hcd), hrρ d]
            exact hb
          · rw [hi2, hinfκ]
          · rw [chainMeasure_of_chain hcf2 hlen₁, hmeasσ, ← hmeasρ]
            have hstep1 : measAux (chainW m) (step m σ) (maxChainDepth - 1) l₁ =
                measAux (chainW m) (corePhase m ρ) (maxChainDepth - 1) l₁ :=
              measAux_congr (fun g' _ => by rw [hg2]) _
            rw [hstep1]
            have hWpos : 0 < chainW m := by
              have := chainW_ge_two m
              omega
            have hpw : ∀ g' ∈ l₁, actVal (corePhase m ρ) g' ≤ actVal ρ g' := by
              intro g' _
              by_cases hE : g' = g
              · rw [hE, actVal_none hga]
                exact Nat.zero_le _
              · rw [actVal_congr (congrArg GateState.act (hgo g' hE))]
            have hg0pos : 1 ≤ actVal ρ g0 := by
              obtain ⟨a1, ha1⟩ := hcfρ.gates_act hwfρ g0
                (by rw [hlsplit]; exact List.mem_append_right _ List.mem_cons_self)
              exact actVal_pos ha1
            rw [hlsplit]
            exact measAux_prefix_lt hWpos l₁ g0 l₂ (maxChainDepth - 1) hpw hg0pos
    · -- foreign halt: frozen, one domain burns
      have hfz : FrozenStep d l h ρ (corePhase m ρ) :=
        FrozenStep.of_haltShape hwfρ hdlρ hbρ hcfρ hsh hrune heh
      obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := glue hfz
      refine .inr (.inr (.inr ⟨hF1, hF2, hF3, hF4, hF5, ?_, ?_⟩))
      · intro fl' hfl'
        rw [hi2, hinfκ] at hfl'
        exact absurd hfl' (by simp)
      · intro hfund
        have hmass2 : massExcept (step m σ) (σ.payer d) = massExcept (corePhase m ρ) (σ.payer d) :=
          massExcept_congr (fun e' => by rw [congrFun hd2 e']) _
        have hmassκ : massExcept (corePhase m ρ) (σ.payer d) ≤ massExcept ρ (σ.payer d) :=
          corePhase_massExcept_le m ρ _
        have hmassρ := massExcept_refill m σ (σ.payer d)
        rw [← hρdef] at hmassρ
        have hil1 : inflightLeft σ = 0 := inflightLeft_none (by rw [← hiρ]; exact hinfρ)
        have hil2 : inflightLeft (step m σ) = 0 :=
          inflightLeft_none (by rw [hi2]; exact hinfκ)
        have hnh2 : nonHalted (step m σ) = nonHalted (corePhase m ρ) :=
          nonHalted_congr (fun e' => by rw [congrFun hd2 e'])
        have hnhκ : nonHalted (corePhase m ρ) < nonHalted ρ := by
          refine nonHalted_lt (corePhase_halted m ρ hwfρ) (e₀ := e) ?_ hsh.2.2.1
          rw [hrune]
          simp
        have hnhρ : nonHalted ρ = nonHalted σ := nonHalted_congr hrρ
        unfold psi
        rw [hmass2, hil2, hnh2, hil1]
        omega
  · -- issue
    by_cases heh : e = h
    · -- HEAD issue: donated draw-down
      subst heh
      obtain ⟨hro, hso, hmaxd, hbp, hbo, hgates⟩ := hsh
      rcases hgates with ⟨hsv, _⟩ | ⟨g, a, hsv, hag, hdon, hgo, hga, hgc⟩
      · rw [hheadserv] at hsv
        exact absurd hsv (by simp)
      · have hgL : g = l.getLast hne := Option.some.inj (hsv.symm.trans hheadserv)
        have hconf : ∀ g', ((corePhase m ρ).gates g').config = (ρ.gates g').config := by
          intro g'
          by_cases hE : g' = g
          · rw [hE, hgc]
          · rw [hgo g' hE]
        have hcfκ : ChainFrom (corePhase m ρ) d l e :=
          hcfρ.frame (fun g' _ => by unfold gateCallee; rw [hconf g']) (fun y _ => hro y)
        have hcf2 : ChainFrom (step m σ) d l e :=
          hcfκ.frame (fun g' _ => by unfold gateCallee; rw [hg2]) (fun y _ => by rw [hd2])
        have hpayκ : (corePhase m ρ).payer d = ρ.payer d := by
          refine payer_frame_of hwfρ hbρ (fun y gy _ => hso y) ?_
          intro y gy gv hgy hsv2
          have hne' : gv ≠ g := by
            intro hE
            subst hE
            have h1 : (ρ.gates gv).config.callee = y := (hwfρ.serving_gate y gv hsv2).1
            have h2 : (ρ.gates gv).config.callee = e := (hwfρ.serving_gate e gv hsv).1
            have hye : y = e := h1.symm.trans h2
            exact absurd (hrune.symm.trans (hye ▸ hgy)) (by simp)
          rw [hgo gv hne']
        have hpay2 : (step m σ).payer d = σ.payer d := by
          have hstep : (step m σ).payer d = (corePhase m ρ).payer d :=
            chainOrigin_congr maxChainDepth d (fun y _ => by rw [hd2])
              (fun y gv _ _ => by rw [hg2])
          rw [hstep, hpayκ, hpayρ]
        refine .inr (.inr (.inl ⟨?_, hcf2, hpay2, ?_, ?_⟩))
        · rw [congrFun hd2 d, hro d, hrρ d]
          exact hb
        · -- the quantified measure drop
          rw [chainMeasure_of_chain hcf2 hlen, hmeasσ, ← hmeasρ]
          have hstep1 : measAux (chainW m) (step m σ) (maxChainDepth - 1) l =
              measAux (chainW m) (corePhase m ρ) (maxChainDepth - 1) l :=
            measAux_congr (fun g' _ => by rw [hg2]) _
          rw [hstep1]
          -- decompose l at its last element
          have hsplit : l.dropLast ++ [l.getLast hne] = l := List.dropLast_append_getLast hne
          have hlen' : l.dropLast.length = l.length - 1 := by
            rw [List.length_dropLast]
          have hexp : maxChainDepth - 1 - l.dropLast.length = maxChainDepth - l.length := by
            have h1 : 1 ≤ l.length := by
              cases l with
              | nil => exact absurd rfl hne
              | cons _ _ => simp
            omega
          have hκl : measAux (chainW m) (corePhase m ρ) (maxChainDepth - 1) l =
              measAux (chainW m) (corePhase m ρ) (maxChainDepth - 1) l.dropLast +
                actVal (corePhase m ρ) (l.getLast hne) * chainW m ^ (maxChainDepth - l.length) := by
            conv_lhs => rw [← hsplit]
            rw [measAux_append, hexp]
          have hρl : measAux (chainW m) ρ (maxChainDepth - 1) l =
              measAux (chainW m) ρ (maxChainDepth - 1) l.dropLast +
                actVal ρ (l.getLast hne) * chainW m ^ (maxChainDepth - l.length) := by
            conv_lhs => rw [← hsplit]
            rw [measAux_append, hexp]
          have havκ : actVal (corePhase m ρ) g = a.donated - c + 1 := by
            simp only [actVal, hga]
          have havρ : actVal ρ g = a.donated + 1 := by
            simp only [actVal, hag]
          have hdle : measAux (chainW m) (corePhase m ρ) (maxChainDepth - 1) l.dropLast ≤
              measAux (chainW m) ρ (maxChainDepth - 1) l.dropLast := by
            refine measAux_le_pointwise ?_ _
            intro g' _
            by_cases hE : g' = g
            · rw [hE, havκ, havρ]
              omega
            · rw [actVal_congr (congrArg GateState.act (hgo g' hE))]
          rw [hκl, hρl, ← hgL, havκ, havρ]
          have hkey : (a.donated - c + 1) * chainW m ^ (maxChainDepth - l.length) +
              chainW m ^ (maxChainDepth - l.length) ≤
              (a.donated + 1) * chainW m ^ (maxChainDepth - l.length) := by
            have h1 : (a.donated - c + 1) + 1 ≤ a.donated + 1 := by omega
            calc (a.donated - c + 1) * chainW m ^ (maxChainDepth - l.length) +
                chainW m ^ (maxChainDepth - l.length)
                = ((a.donated - c + 1) + 1) * chainW m ^ (maxChainDepth - l.length) := by
                  ring
              _ ≤ (a.donated + 1) * chainW m ^ (maxChainDepth - l.length) :=
                  Nat.mul_le_mul_right _ h1
          omega
        · exact ⟨⟨e, w, c⟩, by rw [hi2]; exact hinfs, rfl⟩
    · -- foreign issue: frozen, budget burns
      have hfz : FrozenStep d l h ρ (corePhase m ρ) :=
        FrozenStep.of_issueShape hwfρ hdlρ hbρ hcfρ hsh hrune heh rfl
      obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := glue hfz
      refine .inr (.inr (.inr ⟨hF1, hF2, hF3, hF4, hF5, ?_, ?_⟩))
      · intro fl' hfl'
        rw [hi2, hinfs] at hfl'
        injection hfl' with hfl'
        rw [← hfl']
        exact heh
      · intro hfund
        obtain ⟨hro, hso, hmaxd, hbp, hbo, hgates⟩ := hsh
        have hpne : ρ.payer e ≠ σ.payer d := by
          intro hE
          exact heh (running_payer_eq_top hwfρ hdlρ hcfρ e hrune (by rw [hE, ← hpayρ]))
        have hmassk : massExcept (corePhase m ρ) (σ.payer d) + c = massExcept ρ (σ.payer d) := by
          refine massExcept_sub _ _ c hpne hcbud hbp hbo
        have hmass2 : massExcept (step m σ) (σ.payer d) = massExcept (corePhase m ρ) (σ.payer d) :=
          massExcept_congr (fun e' => by rw [congrFun hd2 e']) _
        have hmassρ := massExcept_refill m σ (σ.payer d)
        rw [← hρdef] at hmassρ
        have hil1 : inflightLeft σ = 0 := inflightLeft_none (by rw [← hiρ]; exact hinfρ)
        have hil2 : inflightLeft (step m σ) = c :=
          inflightLeft_some (by rw [hi2]; exact hinfs)
        have hnh2 : nonHalted (step m σ) = nonHalted σ := by
          refine nonHalted_congr (fun e' => ?_)
          rw [congrFun hd2 e', hro e', hrρ e']
        unfold psi
        rw [hmass2, hil2, hnh2, hil1]
        omega

end Machines.Lnp64u
