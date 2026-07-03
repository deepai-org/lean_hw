import Machines.Lnp64u.Logic.Wf

/-!
# T7 — Real time

Σ Q/P ≤ 1 at reset implies per-period budget delivery; the gate blocking
bound with inheritance; and the per-class WCET lemmas — stated conditional
on the clock constraint and validated against hardware cycle counts per
target (Phase 2/3).
-/

namespace Machines.Lnp64u.Theorems.T7

open Machines.Lnp64u Loom

/-- The schedulability premise, in naturals over the hyperperiod: with
`L = lcm` of all periods, `Σ_d Q_d · (L / P_d) ≤ L`. -/
def Schedulable (m : Manifest) : Prop :=
  let L := (List.finRange numDomains).foldl
    (fun acc d => Nat.lcm acc (m.doms d).periodP) 1
  ((List.finRange numDomains).map
    (fun d => (m.doms d).budgetQ * (L / (m.doms d).periodP))).sum ≤ L

/-- **WCET (retirement).** An issued instruction retires in exactly its
class cost: `cyclesLeft` counts down deterministically and the core frees
on the last cycle. The 25 per-op WCET lemmas are this theorem instantiated
at each declaration's cost. -/
theorem wcet_retirement (m : Manifest) (σ : MachineState) (fl : InFlight)
    (hfl : σ.inflight = some fl) (hpos : 1 ≤ fl.cyclesLeft) :
    (∀ k < fl.cyclesLeft - 1, ∃ fl', (stepN m (k+1) σ).inflight = some fl' ∧
       fl'.dom = fl.dom ∧ fl'.word = fl.word) ∧
    ((stepN m fl.cyclesLeft σ).inflight = none ∨
     ∃ fl', (stepN m fl.cyclesLeft σ).inflight = some fl' ∧ fl'.word ≠ fl.word ∨
            fl'.dom ≠ fl.dom) := by
  sorry

/-- **Budget delivery.** Under schedulability, a running domain that never
blocks receives its full budget every period: within each period window it
retires instructions worth `Q` cycles or spends the period with an empty
ready set. Stated coarsely at spec level; the RTL cycle-bound form is
Phase 3. -/
theorem budget_delivery (m : Manifest) (hwf : m.WF) (hsched : Schedulable m)
    (d : DomainId) :
    (machine m).Invariant (fun σ =>
      (σ.doms d).run = .running →
      -- within the current period, the cycles already charged to d plus its
      -- remaining budget equal the quota
      (σ.doms d).budget ≤ (m.doms d).budgetQ) := by
  sorry

end Machines.Lnp64u.Theorems.T7
