-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tests.Lnp64uCore
import Machines.Lnp64u.Theorems.RMC
import Machines.Lnp64u.Theorems.T1
import Machines.Lnp64u.Theorems.T5
import Machines.Lnp64u.Theorems.T6
import Machines.Lnp64u.Theorems.T7

/-!
# LNP64-µ hypothesis witnesses

This file is a vacuity tripwire for the theorem hypotheses called out in
`TRUST.md`: the finite manifest-side premise families are inhabited by
concrete checked-in configurations.

The lockstep manifests witness the ordinary implementation-facing premises
(`Manifest.WF`, `RMC.Fits`, and T7 schedulability).  T5's isolation premise
intentionally needs a more locked-down configuration than the system-op demo:
domain 0 has a full memory-only slot table, no incoming gates, disjoint roots,
and no decodable globally-sensitive opcodes under its roots.

`T6.StallFree` is deliberately not claimed here.  It is a semantic
reachability side condition over `(machine m).Reachable`, not a finite
manifest predicate; D11 should delete it, or a separate proof should discharge
it for a specific deployment.
-/

namespace Tests.Lnp64uWitnesses

open Machines.Lnp64u
open Machines.Lnp64u.NonInt
open Machines.Lnp64u.Theorems

/-! ## Existing lockstep manifest -/

theorem base_wf : Tests.Lnp64uCore.testManifest.WF := by
  constructor
  · intro d d' h
    fin_cases d <;> fin_cases d' <;> simp [Tests.Lnp64uCore.testManifest] at h ⊢
  · intro d
    fin_cases d <;> decide
  · intro d
    fin_cases d <;> decide
  · intro d
    fin_cases d <;> decide
  · intro d s base len perms h
    fin_cases d <;> fin_cases s <;> simp [Tests.Lnp64uCore.testManifest] at h ⊢
    all_goals
      rcases h with ⟨rfl, rfl, rfl⟩
      decide

theorem base_fits : RMC.Fits Tests.Lnp64uCore.testManifest := by
  constructor <;> intro d <;> fin_cases d <;> decide

theorem base_schedulable : T7.Schedulable Tests.Lnp64uCore.testManifest := by
  change 32 ≤ 32
  decide

theorem base_positive_budgets :
    ∀ d : DomainId, 0 < (Tests.Lnp64uCore.testManifest.doms d).budgetQ := by
  decide

/-! ## A concrete T5/T6 finite-premise witness -/

def isoDomain : DomainId := 0

def isolatedManifest : Manifest where
  doms := fun d =>
    { priority := [4, 3, 2, 1].getD d.val 0
      budgetQ := 4
      periodP := 64
      maxDonation := 8
      entry := 0
      initCaps := fun _ =>
        if d = isoDomain then
          some (.mem 0 1 { r := true, w := false, x := true })
        else
          none
      initRegions := fun r =>
        if r = (0 : RegionId) then some 0 else none }
  gates := fun _ => { callee := 1, entry := 0 }
  rom := fun _ => 0xffffffff

theorem isolated_wf : isolatedManifest.WF := by
  constructor
  · intro d d' h
    fin_cases d <;> fin_cases d' <;> simp [isolatedManifest] at h ⊢
  · intro d
    fin_cases d <;> decide
  · intro d
    fin_cases d <;> decide
  · intro d
    fin_cases d <;> decide
  · intro d s base len perms h
    fin_cases d <;> fin_cases s <;> simp [isolatedManifest, isoDomain] at h ⊢
    all_goals
      rcases h with ⟨rfl, rfl, rfl⟩
      decide

theorem isolated_fits : RMC.Fits isolatedManifest := by
  constructor <;> intro d <;> fin_cases d <;> decide

theorem isolated_schedulable : T7.Schedulable isolatedManifest := by
  change 16 ≤ 64
  decide

theorem isolated_strictly_schedulable : T6.StrictlySchedulable isolatedManifest := by
  change 32 < 64
  decide

theorem isolated_positive_budgets :
    ∀ d : DomainId, 0 < (isolatedManifest.doms d).budgetQ := by
  decide

theorem isolated_top_priority : TopPriority isolatedManifest isoDomain := by
  intro d hd
  fin_cases d <;> simp [isolatedManifest, isoDomain] at hd ⊢

theorem isolated_isolated : Isolated isolatedManifest isoDomain := by
  constructor
  · intro s g h
    fin_cases s <;> simp [isolatedManifest, isoDomain] at h
  · intro g
    fin_cases g <;> simp [isolatedManifest, isoDomain]
  · intro d' s s' b l p b' l' p' hd hcap hcap'
    fin_cases d' <;> simp [isoDomain] at hd
    all_goals
      fin_cases s'
      all_goals simp [isolatedManifest, isoDomain] at hcap'
  · intro s
    fin_cases s <;> simp [isolatedManifest, isoDomain]
  · intro a hroot i hdec
    have hnone : Loom.Isa.decode isa (4294967295#32 : Loom.Word32) = none :=
      T1.decode_illegal (4294967295#32 : Loom.Word32) (by decide)
    simp [isolatedManifest] at hdec
    rw [hnone] at hdec
    cases hdec
  · intro s s' b l p b' l' p' hcap hcap' hw hx
    fin_cases s <;> simp [isolatedManifest, isoDomain] at hcap
    all_goals
      rcases hcap with ⟨rfl, rfl, rfl⟩
      simp at hw

theorem isolated_agree_self : AgreeOn isolatedManifest isolatedManifest isoDomain := by
  constructor
  · rfl
  · intro a _
    rfl

/-- T5's finite manifest hypotheses are jointly satisfiable. -/
theorem t5_finite_hypotheses :
    isolatedManifest.WF ∧ isolatedManifest.WF ∧
    Isolated isolatedManifest isoDomain ∧ Isolated isolatedManifest isoDomain ∧
    TopPriority isolatedManifest isoDomain ∧ TopPriority isolatedManifest isoDomain ∧
    AgreeOn isolatedManifest isolatedManifest isoDomain := by
  exact ⟨isolated_wf, isolated_wf, isolated_isolated, isolated_isolated,
    isolated_top_priority, isolated_top_priority, isolated_agree_self⟩

/-- T6's finite manifest hypotheses are jointly satisfiable.

This deliberately excludes `T6.StallFree`, the semantic reachability
condition discussed in the module docstring.
-/
theorem t6_finite_hypotheses :
    isolatedManifest.WF ∧ T6.StrictlySchedulable isolatedManifest ∧
      (∀ d : DomainId, 0 < (isolatedManifest.doms d).budgetQ) := by
  exact ⟨isolated_wf, isolated_strictly_schedulable, isolated_positive_budgets⟩

/-- R-MC's reset/lockstep manifest-side hypotheses are jointly satisfiable. -/
theorem rmc_finite_hypotheses :
    isolatedManifest.WF ∧ RMC.Fits isolatedManifest := by
  exact ⟨isolated_wf, isolated_fits⟩

end Tests.Lnp64uWitnesses
