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

end Machines.Lnp64u
