import Machines.Lnp64u.Logic.NonInt

/-!
# T5 — Noninterference (architectural, path-free pairs)

Donation deliberately couples timing along authority paths, so the theorem
quantifies over pairs with *no* path, and observes architectural state
modulo stuttering: an isolated domain's destuttered trajectory is a
function of its own configuration and code only. Stated as a two-manifest
(2-safety) property.

**Adjudication notes (recorded in full in `Logic/NonInt.lean`).** The
original statement was falsified twice and repaired proof-forcedly:

1. `Isolated` + `AgreeOn` alone admitted a priority hog (scheduling
   channel), grants-in (table-occupancy channel), and `d`'s own
   `mem_grant`/`move` (global-state reads). Repair: `TopPriority` in both
   manifests, plus `Isolated.slots_full` and `Isolated.code_local`.
2. (This pass.) The observation itself leaked: `destutter` over full
   `DomainState`s demands equality of the kept representatives, whose
   `budget` field provably drifts between the runs (absolute-cycle refill
   vs. drifted issue cycles); and per-capability W^X did not stop `d`
   from *rewriting its own code* through a writable root overlapping an
   executable root, resurrecting the banned opcodes. Repair: the
   trajectory is a projection to `Obs` (`regs`/`pc`/`run`/`cause`), and
   `Isolated.wx_disjoint` separates `d`'s writable roots from its
   executable ones.

The proof is a stuttering simulation assembled from the `NonInt` engines:
`Coupled` is maintained at aligned instants; on run-1 cycles that neither
retire nor fault `d` the observation stutters (`frame_step`/`issue_step`);
at a `d`-event run 2 catches up through a frozen window (`progress`) and
performs the matching event (`issue_step`/`retire_step_lockstep`), giving
the same new observation; destuttering erases the drift.
-/

namespace Machines.Lnp64u.Theorems.T5

open Machines.Lnp64u Loom NonInt

/-! ## Destutter extension steps -/

/-- Run 1 stutters one cycle: the destuttered trajectory is unchanged. -/
private theorem dest_ext_stutter (m : Manifest) (d : DomainId) (N : Nat)
    (h : obsOf ((stepN m (N + 1) m.initState).doms d) =
         obsOf ((stepN m N m.initState).doms d)) :
    destutter (trajectory m d (N + 2)) = destutter (trajectory m d (N + 1)) := by
  rw [trajectory_succ m d (N + 1)]
  exact destutter_snoc_stutter _ _ (by rw [trajectory_getLast, ← h])

/-- Run 1 appends one observation while run 2 appends `j` stutters and then
the *same* observation: the destuttered trajectories stay equal. -/
private theorem dest_ext_burst (m₁ m₂ : Manifest) (d : DomainId) (N K j : Nat)
    (hdest : destutter (trajectory m₁ d (N + 1)) =
             destutter (trajectory m₂ d (K + 1)))
    (hlast : obsOf ((stepN m₁ N m₁.initState).doms d) =
             obsOf ((stepN m₂ K m₂.initState).doms d))
    (hfro : ∀ i, 1 ≤ i → i ≤ j →
      obsOf ((stepN m₂ (K + i) m₂.initState).doms d) =
      obsOf ((stepN m₂ K m₂.initState).doms d))
    (hy : obsOf ((stepN m₁ (N + 1) m₁.initState).doms d) =
          obsOf ((stepN m₂ (K + j + 1) m₂.initState).doms d)) :
    destutter (trajectory m₁ d (N + 2)) =
      destutter (trajectory m₂ d (K + j + 2)) := by
  set x := obsOf ((stepN m₂ K m₂.initState).doms d) with hxdef
  set y := obsOf ((stepN m₁ (N + 1) m₁.initState).doms d) with hydef
  -- run 2's trajectory decomposes as prefix ++ stutters ++ [y]
  have hmap : (List.range j).map
      (fun i => obsOf ((stepN m₂ (K + 1 + i) m₂.initState).doms d)) =
      List.replicate j x := by
    refine List.eq_replicate_iff.mpr ⟨by simp, ?_⟩
    intro b hb
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨i, hi, hbi⟩ := hb
    rw [← hbi, show K + 1 + i = K + (1 + i) from by omega]
    exact hfro (1 + i) (by omega) (by omega)
  have hseg : trajectory m₂ d (K + j + 2) =
      (trajectory m₂ d (K + 1) ++ List.replicate j x) ++ [y] := by
    have harith : K + j + 2 = (K + 1) + (j + 1) := by omega
    rw [harith, trajectory_add m₂ d (K + 1) (j + 1), List.range_succ,
      List.map_append, hmap, ← List.append_assoc]
    congr 1
    show [obsOf ((stepN m₂ (K + 1 + j) m₂.initState).doms d)] = [y]
    rw [show K + 1 + j = K + j + 1 from by omega, ← hy]
  have hlast₁ : (trajectory m₁ d (N + 1)).getLast? = some x := by
    rw [trajectory_getLast, hlast]
  have hlast₂ : (trajectory m₂ d (K + 1) ++ List.replicate j x).getLast? = some x :=
    getLast?_append_replicate _ x j (by rw [trajectory_getLast])
  calc destutter (trajectory m₁ d (N + 2))
      = destutter (trajectory m₁ d (N + 1) ++ [y]) := by
        rw [trajectory_succ m₁ d (N + 1)]
    _ = destutter ((trajectory m₂ d (K + 1) ++ List.replicate j x) ++ [y]) := by
        refine destutter_snoc_congr y ?_ hlast₁ hlast₂
        rw [hdest, destutter_append_replicate _ x j (by rw [trajectory_getLast])]
    _ = destutter (trajectory m₂ d (K + j + 2)) := by rw [hseg]

/-! ## Run-2 catch-up bursts -/

section Catchup

variable (m₁ m₂ : Manifest) (d : DomainId)

/-- Run 1 halts `d` at an issue instant (fetch or decode fault): run 2,
from a coupled quiescent state, reaches its own matching issue instant and
halts `d` identically. -/
theorem catchup_halt
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    (hiso₁ : Isolated m₁ d) (hiso₂ : Isolated m₂ d)
    (hpri₂ : TopPriority m₂ d) (hag : AgreeOn m₁ m₂ d)
    (σ₁ σ₂ : MachineState)
    (hins₁ : Insulated m₁ d σ₁) (hins₂ : Insulated m₂ d σ₂)
    (hcpl : Coupled m₁ d σ₁ σ₂) (hq₂ : NonInt.Quiet d σ₂)
    (hinf₁ : σ₁.inflight = none)
    (hsched₁ : schedule m₁ (refillPhase m₁ σ₁) = some d)
    (hbad : fetch σ₁ d = none ∨
      ∃ w, fetch σ₁ d = some w ∧ Loom.Isa.decode isa w = none) :
    ∃ j, (∀ i, i ≤ j → obsOf ((stepN m₂ i σ₂).doms d) = obsOf (σ₂.doms d)) ∧
      Coupled m₁ d (step m₁ σ₁) (stepN m₂ (j + 1) σ₂) ∧
      Insulated m₂ d (stepN m₂ (j + 1) σ₂) ∧
      NonInt.Quiet d (stepN m₂ (j + 1) σ₂) ∧ NonInt.Quiet d (step m₁ σ₁) := by
  have hdom : m₁.doms d = m₂.doms d := hag.1
  -- d is running and its per-period budget is positive
  have hrun₁ : (σ₁.doms d).run = .running := by
    have := schedule_running m₁ (refillPhase m₁ σ₁) d hsched₁
    rwa [refillPhase_run] at this
  have hrun₂ : (σ₂.doms d).run = .running := by rw [← hcpl.run]; exact hrun₁
  have hQpos : 0 < (m₂.doms d).budgetQ := by
    have helig := schedule_eligible m₁ (refillPhase m₁ σ₁) d hsched₁
    have hpay : (refillPhase m₁ σ₁).payer d = d :=
      payer_eq_self _ d (by rw [refillPhase_serving]; exact hins₁.serving_none)
    have hb := helig.2
    rw [hpay] at hb
    have := refillPhase_budget_le m₁ σ₁ d hins₁.budget_le
    rw [← hdom]
    omega
  -- run 2 progresses to its own issue instant
  obtain ⟨j, hfro, hinf₀, hsched₀, _⟩ :=
    Wip.progress m₂ d σ₂ h₂ hpri₂ hiso₂ hins₂ hq₂ hrun₂ 1 Nat.one_pos hQpos
      (Or.inl rfl)
  have hins₀ : Insulated m₂ d (stepN m₂ j σ₂) :=
    Wip.insulated_stepN m₂ d h₂ hiso₂ j σ₂ hins₂
  have hfro₀ : DFrozen m₂ d σ₂ (stepN m₂ j σ₂) := (hfro j (Nat.le_refl _)).1
  have hcpl₀ : Coupled m₁ d σ₁ (stepN m₂ j σ₂) :=
    hcpl.frozen_right hfro₀ hdom
  have hfetch₀ : fetch (stepN m₂ j σ₂) d = fetch σ₁ d := by
    rw [fetch_frozen hins₂ hfro₀]; exact (fetch_coupled hins₁ hcpl).symm
  -- run 1's halt
  rcases Wip.issue_step m₁ d σ₁ h₁ hiso₁ hins₁ hinf₁ hsched₁ with
    ⟨hf₁, hdh₁⟩ | ⟨w, hf₁, hd₁, hdh₁⟩ | ⟨w, i₁, hf₁, hd₁, _, _, _⟩ |
    ⟨w, i₁, hf₁, hd₁, _, _, _⟩
  · -- fetch fault in run 1 ⇒ fetch fault in run 2
    rcases Wip.issue_step m₂ d (stepN m₂ j σ₂) h₂ hiso₂ hins₀ hinf₀ hsched₀ with
      ⟨hf₂, hdh₂⟩ | ⟨w', hf₂, _, _⟩ | ⟨w', i₂, hf₂, _, _, _, _⟩ |
      ⟨w', i₂, hf₂, _, _, _, _⟩
    · refine ⟨j, fun i hi => ((hfro i hi).1).obs_eq, ?_, ?_, ?_, ?_⟩
      · rw [Machines.Lnp64u.Wip.stepN_succ]
        exact coupled_of_dhalt hcpl₀ hdom hdh₁ hdh₂
      · rw [Machines.Lnp64u.Wip.stepN_succ]
        exact Wip.insulated_step m₂ d _ h₂ hiso₂ hins₀
      · rw [Machines.Lnp64u.Wip.stepN_succ]
        intro fl hfl
        rw [hdh₂.inflight] at hfl
        cases hfl
      · intro fl hfl
        rw [hdh₁.inflight] at hfl
        cases hfl
    all_goals rw [hfetch₀, hf₁] at hf₂; cases hf₂
  · -- decode fault in run 1 ⇒ decode fault in run 2
    rcases Wip.issue_step m₂ d (stepN m₂ j σ₂) h₂ hiso₂ hins₀ hinf₀ hsched₀ with
      ⟨hf₂, _⟩ | ⟨w', hf₂, hd₂, hdh₂⟩ | ⟨w', i₂, hf₂, hd₂, _, _, _⟩ |
      ⟨w', i₂, hf₂, hd₂, _, _, _⟩
    · rw [hfetch₀, hf₁] at hf₂; cases hf₂
    · refine ⟨j, fun i hi => ((hfro i hi).1).obs_eq, ?_, ?_, ?_, ?_⟩
      · rw [Machines.Lnp64u.Wip.stepN_succ]
        exact coupled_of_dhalt hcpl₀ hdom hdh₁ hdh₂
      · rw [Machines.Lnp64u.Wip.stepN_succ]
        exact Wip.insulated_step m₂ d _ h₂ hiso₂ hins₀
      · rw [Machines.Lnp64u.Wip.stepN_succ]
        intro fl hfl
        rw [hdh₂.inflight] at hfl
        cases hfl
      · intro fl hfl
        rw [hdh₁.inflight] at hfl
        cases hfl
    all_goals
      rw [hfetch₀, hf₁] at hf₂
      injection hf₂ with hww
      rw [← hww, hd₁] at hd₂
      cases hd₂
  all_goals
    rcases hbad with hf | ⟨w', hf, hd⟩
    · rw [hf₁] at hf; cases hf
    · rw [hf₁] at hf
      injection hf with hww
      subst hww
      rw [hd] at hd₁
      cases hd₁

/-- Run 1 retires `d`'s in-flight instruction: run 2, from a coupled
quiescent state, issues the same word, flies it, and retires it — landing
coupled with run 1. -/
theorem catchup_retire
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    (hiso₁ : Isolated m₁ d) (hiso₂ : Isolated m₂ d)
    (hpri₂ : TopPriority m₂ d) (hag : AgreeOn m₁ m₂ d)
    (σ₁ σ₂ : MachineState)
    (hins₁ : Insulated m₁ d σ₁) (hins₂ : Insulated m₂ d σ₂)
    (hcpl : Coupled m₁ d σ₁ σ₂) (hq₂ : NonInt.Quiet d σ₂)
    (fl : InFlight) (instr : Loom.Isa.InstrDecl sig Semantics WcetClass)
    (hfl : σ₁.inflight = some fl) (hfd : fl.dom = d)
    (hfetch : fetch σ₁ d = some fl.word)
    (hdec : Loom.Isa.decode isa fl.word = some instr)
    (hcQ : instr.cost.cost ≤ (m₁.doms d).budgetQ)
    (hcl : fl.cyclesLeft ≤ 1) :
    ∃ j, (∀ i, i ≤ j → obsOf ((stepN m₂ i σ₂).doms d) = obsOf (σ₂.doms d)) ∧
      Coupled m₁ d (step m₁ σ₁) (stepN m₂ (j + 1) σ₂) ∧
      Insulated m₂ d (stepN m₂ (j + 1) σ₂) ∧
      NonInt.Quiet d (stepN m₂ (j + 1) σ₂) ∧ NonInt.Quiet d (step m₁ σ₁) := by
  have hdom : m₁.doms d = m₂.doms d := hag.1
  set c := instr.cost.cost with hcdef
  have hc0 : 0 < c := cost_pos _
  have hrun₁ : (σ₁.doms d).run = .running := by
    have := hins₁.wf.inflight_running fl hfl
    rwa [hfd] at this
  have hrun₂ : (σ₂.doms d).run = .running := by rw [← hcpl.run]; exact hrun₁
  have hcQ₂ : c ≤ (m₂.doms d).budgetQ := by rw [← hdom]; exact hcQ
  -- 1. progress to run 2's issue instant
  obtain ⟨j₀, hfro, hinf₀, hsched₀, hbud₀⟩ :=
    Wip.progress m₂ d σ₂ h₂ hpri₂ hiso₂ hins₂ hq₂ hrun₂ c hc0 hcQ₂
      (Or.inr ⟨fl.word, instr, by rw [← fetch_coupled hins₁ hcpl]; exact hfetch,
        hdec, hcdef.symm⟩)
  have hins₀ : Insulated m₂ d (stepN m₂ j₀ σ₂) :=
    Wip.insulated_stepN m₂ d h₂ hiso₂ j₀ σ₂ hins₂
  have hfro₀ : DFrozen m₂ d σ₂ (stepN m₂ j₀ σ₂) := (hfro j₀ (Nat.le_refl _)).1
  have hfetch₀ : fetch (stepN m₂ j₀ σ₂) d = some fl.word := by
    rw [fetch_frozen hins₂ hfro₀, ← fetch_coupled hins₁ hcpl]
    exact hfetch
  -- 2. run 2 latches the same word with the same cost
  rcases Wip.issue_step m₂ d (stepN m₂ j₀ σ₂) h₂ hiso₂ hins₀ hinf₀ hsched₀ with
    ⟨hf₂, _⟩ | ⟨w', hf₂, hd₂, _⟩ | ⟨w', i₂, hf₂, hd₂, hlt₂, _, _⟩ |
    ⟨w', i₂, hf₂, hd₂, hle₂, hfz₂, hlat₂⟩
  · rw [hfetch₀] at hf₂; cases hf₂
  · rw [hfetch₀] at hf₂
    injection hf₂ with hww
    rw [← hww, hdec] at hd₂
    cases hd₂
  · rw [hfetch₀] at hf₂
    injection hf₂ with hww
    subst hww
    rw [hdec] at hd₂
    injection hd₂ with hii
    subst hii
    omega
  rw [hfetch₀] at hf₂
  injection hf₂ with hww
  subst hww
  rw [hdec] at hd₂
  injection hd₂ with hii
  subst hii
  -- τ₁: the state right after run 2's issue
  have hτ₁succ : stepN m₂ (j₀ + 1) σ₂ = step m₂ (stepN m₂ j₀ σ₂) :=
    Machines.Lnp64u.Wip.stepN_succ m₂ j₀ σ₂
  have hins₁' : Insulated m₂ d (stepN m₂ (j₀ + 1) σ₂) := by
    rw [hτ₁succ]; exact Wip.insulated_step m₂ d _ h₂ hiso₂ hins₀
  have hfz₁ : DFrozen m₂ d σ₂ (stepN m₂ (j₀ + 1) σ₂) := by
    rw [hτ₁succ]; exact hfro₀.trans hfz₂
  have hlat₁ : (stepN m₂ (j₀ + 1) σ₂).inflight = some ⟨d, fl.word, c⟩ := by
    rw [hτ₁succ]; exact hlat₂
  -- 3. countdown: c - 1 frozen cycles
  have hcount : ∀ k, k ≤ c - 1 →
      DFrozen m₂ d σ₂ (stepN m₂ (j₀ + 1 + k) σ₂) ∧
      (stepN m₂ (j₀ + 1 + k) σ₂).inflight = some ⟨d, fl.word, c - k⟩ ∧
      Insulated m₂ d (stepN m₂ (j₀ + 1 + k) σ₂) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hfz₁, by rw [hlat₁, Nat.sub_zero], hins₁'⟩
    | succ n ih =>
        intro hn
        obtain ⟨hfz, hinf, hins⟩ := ih (by omega)
        have hsucc : stepN m₂ (j₀ + 1 + (n + 1)) σ₂ =
            step m₂ (stepN m₂ (j₀ + 1 + n) σ₂) := by
          rw [show j₀ + 1 + (n + 1) = (j₀ + 1 + n) + 1 from by omega]
          exact Machines.Lnp64u.Wip.stepN_succ m₂ _ σ₂
        have h1n : 1 < c - n := by omega
        have hframe : DFrozen m₂ d (stepN m₂ (j₀ + 1 + n) σ₂)
            (step m₂ (stepN m₂ (j₀ + 1 + n) σ₂)) := by
          refine Wip.frame_step m₂ d _ h₂ hiso₂ hins ?_ ?_
          · intro fl' hfl' _
            rw [hinf] at hfl'
            injection hfl' with hfl''
            rw [← hfl'']
            exact h1n
          · intro h
            rw [hinf] at h
            cases h
        have hcd : (step m₂ (stepN m₂ (j₀ + 1 + n) σ₂)).inflight =
            some ⟨d, fl.word, c - n - 1⟩ :=
          Machines.Lnp64u.Wip.step_inflight_countdown m₂ _ _ hinf h1n
        refine ⟨?_, ?_, ?_⟩
        · rw [hsucc]; exact hfz.trans hframe
        · rw [hsucc, hcd, show c - n - 1 = c - (n + 1) from by omega]
        · rw [hsucc]; exact Wip.insulated_step m₂ d _ h₂ hiso₂ hins
  obtain ⟨hfzT, hinfT, hinsT⟩ := hcount (c - 1) (Nat.le_refl _)
  have hcT : c - (c - 1) = 1 := by omega
  rw [hcT] at hinfT
  -- 4. lockstep retirement
  set jT := j₀ + 1 + (c - 1) with hjT
  have hflT : σ₁.inflight = some ⟨d, fl.word, fl.cyclesLeft⟩ := by
    rw [hfl]
    congr 1
    cases fl
    simp only at hfd ⊢
    rw [hfd]
  have hcplT : Coupled m₁ d σ₁ (stepN m₂ jT σ₂) := hcpl.frozen_right hfzT hdom
  have hpost : Coupled m₁ d (step m₁ σ₁) (step m₂ (stepN m₂ jT σ₂)) :=
    Wip.retire_step_lockstep m₁ m₂ d σ₁ (stepN m₂ jT σ₂) h₁ h₂ hiso₁ hiso₂ hag
      hins₁ hinsT hcplT fl.word fl.cyclesLeft 1 hcl (Nat.le_refl _)
      hflT hinfT hfetch
  refine ⟨jT, ?_, ?_, ?_, ?_, ?_⟩
  · -- observation frozen through the wait, the issue, and the flight
    intro i hi
    by_cases hij : i ≤ j₀
    · exact ((hfro i hij).1).obs_eq
    · have hk : i = j₀ + 1 + (i - (j₀ + 1)) := by omega
      have hkb : i - (j₀ + 1) ≤ c - 1 := by omega
      obtain ⟨hfz, _, _⟩ := hcount (i - (j₀ + 1)) hkb
      rw [hk]
      exact hfz.obs_eq
  · rw [show jT + 1 = jT + 1 from rfl, Machines.Lnp64u.Wip.stepN_succ m₂ jT σ₂]
    exact hpost
  · rw [Machines.Lnp64u.Wip.stepN_succ m₂ jT σ₂]
    exact Wip.insulated_step m₂ d _ h₂ hiso₂ hinsT
  · rw [Machines.Lnp64u.Wip.stepN_succ m₂ jT σ₂]
    intro fl' hfl'
    rw [Machines.Lnp64u.Wip.step_inflight_retire m₂ _ _ hinfT (Nat.le_refl _)] at hfl'
    cases hfl'
  · intro fl' hfl'
    rw [Machines.Lnp64u.Wip.step_inflight_retire m₁ σ₁ _ hflT hcl] at hfl'
    cases hfl'

end Catchup

/-! ## The aligned-instant simulation -/

/-- The two-run simulation invariant, driven by run 1's cycle count: at
every instant `N` of run 1 there is an aligned instant `K` of run 2 with
equal destuttered trajectories, both runs insulated, `d`'s slices coupled,
run 2 quiescent, and run 1 either quiescent or mid-flight with a
re-derivable latched word. -/
theorem sim (m₁ m₂ : Manifest) (h₁ : m₁.WF) (h₂ : m₂.WF)
    (d : DomainId) (hiso₁ : Isolated m₁ d) (hiso₂ : Isolated m₂ d)
    (hpri₂ : TopPriority m₂ d) (hag : AgreeOn m₁ m₂ d) :
    ∀ N : Nat, ∃ K : Nat,
      destutter (trajectory m₁ d (N + 1)) = destutter (trajectory m₂ d (K + 1)) ∧
      Insulated m₁ d (stepN m₁ N m₁.initState) ∧
      Insulated m₂ d (stepN m₂ K m₂.initState) ∧
      Coupled m₁ d (stepN m₁ N m₁.initState) (stepN m₂ K m₂.initState) ∧
      NonInt.Quiet d (stepN m₂ K m₂.initState) ∧
      (NonInt.Quiet d (stepN m₁ N m₁.initState) ∨
        Midflight m₁ d (stepN m₁ N m₁.initState)) := by
  have hdom : m₁.doms d = m₂.doms d := hag.1
  intro N
  induction N with
  | zero =>
      refine ⟨0, ?_, insulated_init m₁ d h₁ hiso₁, insulated_init m₂ d h₂ hiso₂,
        coupled_init m₁ m₂ d hag, ?_, Or.inl ?_⟩
      · show destutter (trajectory m₁ d 1) = destutter (trajectory m₂ d 1)
        rw [trajectory_one, trajectory_one]
        show destutter [obsOf (m₁.initState.doms d)] =
          destutter [obsOf (m₂.initState.doms d)]
        rw [(coupled_init m₁ m₂ d hag).obs_eq]
      · intro fl hfl
        exact absurd hfl (by show m₂.initState.inflight ≠ some fl; simp [Manifest.initState])
      · intro fl hfl
        exact absurd hfl (by show m₁.initState.inflight ≠ some fl; simp [Manifest.initState])
  | succ N ih =>
      obtain ⟨K, hdest, hins₁, hins₂, hcpl, hq₂, harm⟩ := ih
      set σ₁ := stepN m₁ N m₁.initState with hσ₁
      set σ₂ := stepN m₂ K m₂.initState with hσ₂
      have hsuccA : stepN m₁ (N + 1) m₁.initState = step m₁ σ₁ :=
        Machines.Lnp64u.Wip.stepN_succ m₁ N m₁.initState
      have hinsA : Insulated m₁ d (stepN m₁ (N + 1) m₁.initState) := by
        rw [hsuccA]; exact Wip.insulated_step m₁ d σ₁ h₁ hiso₁ hins₁
      -- a reusable "run-1 stutters" package
      have stutter_pack :
          DFrozen m₁ d σ₁ (step m₁ σ₁) →
          NonInt.Quiet d (step m₁ σ₁) ∨ Midflight m₁ d (step m₁ σ₁) →
          ∃ K' : Nat,
            destutter (trajectory m₁ d (N + 1 + 1)) =
              destutter (trajectory m₂ d (K' + 1)) ∧
            Insulated m₁ d (stepN m₁ (N + 1) m₁.initState) ∧
            Insulated m₂ d (stepN m₂ K' m₂.initState) ∧
            Coupled m₁ d (stepN m₁ (N + 1) m₁.initState) (stepN m₂ K' m₂.initState) ∧
            NonInt.Quiet d (stepN m₂ K' m₂.initState) ∧
            (NonInt.Quiet d (stepN m₁ (N + 1) m₁.initState) ∨
              Midflight m₁ d (stepN m₁ (N + 1) m₁.initState)) := by
        intro hfz harm'
        refine ⟨K, ?_, hinsA, hins₂, ?_, hq₂, by rw [hsuccA]; exact harm'⟩
        · rw [show N + 1 + 1 = N + 2 from rfl,
            dest_ext_stutter m₁ d N (by rw [hsuccA]; exact hfz.obs_eq)]
          exact hdest
        · rw [hsuccA]
          exact hcpl.frozen_left hfz
      -- a reusable "run-2 bursts" package
      have burst_pack :
          ∀ j : Nat,
          (∀ i, i ≤ j → obsOf ((stepN m₂ i σ₂).doms d) = obsOf (σ₂.doms d)) →
          Coupled m₁ d (step m₁ σ₁) (stepN m₂ (j + 1) σ₂) →
          Insulated m₂ d (stepN m₂ (j + 1) σ₂) →
          NonInt.Quiet d (stepN m₂ (j + 1) σ₂) →
          NonInt.Quiet d (step m₁ σ₁) →
          ∃ K' : Nat,
            destutter (trajectory m₁ d (N + 1 + 1)) =
              destutter (trajectory m₂ d (K' + 1)) ∧
            Insulated m₁ d (stepN m₁ (N + 1) m₁.initState) ∧
            Insulated m₂ d (stepN m₂ K' m₂.initState) ∧
            Coupled m₁ d (stepN m₁ (N + 1) m₁.initState) (stepN m₂ K' m₂.initState) ∧
            NonInt.Quiet d (stepN m₂ K' m₂.initState) ∧
            (NonInt.Quiet d (stepN m₁ (N + 1) m₁.initState) ∨
              Midflight m₁ d (stepN m₁ (N + 1) m₁.initState)) := by
        intro j hfro hcpl' hins' hq' hq1'
        have habs : ∀ i, stepN m₂ i σ₂ = stepN m₂ (K + i) m₂.initState := by
          intro i
          rw [hσ₂, ← stepN_add]
        refine ⟨K + j + 1, ?_, hinsA, ?_, ?_, ?_, Or.inl (by rw [hsuccA]; exact hq1')⟩
        · rw [show N + 1 + 1 = N + 2 from rfl,
            show K + j + 1 + 1 = K + j + 2 from rfl]
          refine dest_ext_burst m₁ m₂ d N K j hdest hcpl.obs_eq ?_ ?_
          · intro i h1i hij
            rw [← habs i]
            exact hfro i hij
          · rw [hsuccA, show K + j + 1 = K + (j + 1) from by omega, ← habs (j + 1)]
            exact hcpl'.obs_eq
        · rw [show K + j + 1 = K + (j + 1) from by omega, ← habs (j + 1)]
          exact hins'
        · rw [hsuccA, show K + j + 1 = K + (j + 1) from by omega, ← habs (j + 1)]
          exact hcpl'
        · rw [show K + j + 1 = K + (j + 1) from by omega, ← habs (j + 1)]
          exact hq'
      -- case split on run 1's cycle
      rcases hinf₁ : σ₁.inflight with _ | fl
      · -- idle core: does run 1 issue for d?
        by_cases hsd : schedule m₁ (refillPhase m₁ σ₁) = some d
        · -- issue instant for d
          rcases Wip.issue_step m₁ d σ₁ h₁ hiso₁ hins₁ hinf₁ hsd with
            ⟨hf, hdh⟩ | ⟨w, hf, hd, hdh⟩ | ⟨w, instr, hf, hd, hlt, hfz, hni⟩ |
            ⟨w, instr, hf, hd, hle, hfz, hlat⟩
          · -- fetch fault: run 2 catches up with the same halt
            obtain ⟨j, hfro, hcpl', hins', hq', hq1'⟩ :=
              catchup_halt m₁ m₂ d h₁ h₂ hiso₁ hiso₂ hpri₂ hag σ₁ σ₂
                hins₁ hins₂ hcpl hq₂ hinf₁ hsd (Or.inl hf)
            exact burst_pack j hfro hcpl' hins' hq' hq1'
          · -- decode fault: same
            obtain ⟨j, hfro, hcpl', hins', hq', hq1'⟩ :=
              catchup_halt m₁ m₂ d h₁ h₂ hiso₁ hiso₂ hpri₂ hag σ₁ σ₂
                hins₁ hins₂ hcpl hq₂ hinf₁ hsd (Or.inr ⟨w, hf, hd⟩)
            exact burst_pack j hfro hcpl' hins' hq' hq1'
          · -- stall: run 1 stutters, stays quiescent
            refine stutter_pack hfz (Or.inl ?_)
            intro fl' hfl'
            rw [hni] at hfl'
            cases hfl'
          · -- latch: run 1 stutters into mid-flight
            refine stutter_pack hfz (Or.inr ?_)
            refine ⟨⟨d, w, instr.cost.cost⟩, instr, hlat, rfl, ?_, ?_, Nat.le_refl _, ?_⟩
            · show fetch (step m₁ σ₁) d = some w
              rw [fetch_frozen hins₁ hfz]
              exact hf
            · exact hd
            · calc instr.cost.cost ≤ ((refillPhase m₁ σ₁).doms d).budget := hle
                _ ≤ (m₁.doms d).budgetQ :=
                    refillPhase_budget_le m₁ σ₁ d hins₁.budget_le
        · -- no d-issue: frame
          have hfz : DFrozen m₁ d σ₁ (step m₁ σ₁) :=
            Wip.frame_step m₁ d σ₁ h₁ hiso₁ hins₁
              (fun fl' hfl' _ => by rw [hinf₁] at hfl'; cases hfl')
              (fun _ => hsd)
          refine stutter_pack hfz (Or.inl ?_)
          exact Wip.step_quiet m₁ d σ₁
            (fun fl' hfl' => by rw [hinf₁] at hfl'; cases hfl') (fun _ => hsd)
      · -- an instruction is in flight
        by_cases hfd : fl.dom = d
        · -- it is d's: the arm must be Midflight
          rcases harm with hq1 | hmid
          · exact absurd hfd (hq1 fl hinf₁)
          · obtain ⟨fl', instr, hfl', hfd', hfetch', hdec', hclc, hcQ⟩ := hmid
            rw [hinf₁] at hfl'
            injection hfl' with hfl'
            subst hfl'
            by_cases hcl : fl.cyclesLeft ≤ 1
            · -- retirement: run 2 catches up through issue + flight + retire
              obtain ⟨j, hfro, hcpl', hins', hq', hq1'⟩ :=
                catchup_retire m₁ m₂ d h₁ h₂ hiso₁ hiso₂ hpri₂ hag σ₁ σ₂
                  hins₁ hins₂ hcpl hq₂ fl instr hinf₁ hfd' hfetch' hdec' hcQ hcl
              exact burst_pack j hfro hcpl' hins' hq' hq1'
            · -- countdown: run 1 stutters, stays mid-flight
              have h1c : 1 < fl.cyclesLeft := by omega
              have hfz : DFrozen m₁ d σ₁ (step m₁ σ₁) :=
                Wip.frame_step m₁ d σ₁ h₁ hiso₁ hins₁
                  (fun fl'' hfl'' _ => by
                    rw [hinf₁] at hfl''
                    injection hfl'' with hfl''
                    rw [← hfl'']
                    exact h1c)
                  (fun h => by rw [hinf₁] at h; cases h)
              refine stutter_pack hfz (Or.inr ?_)
              refine ⟨{ fl with cyclesLeft := fl.cyclesLeft - 1 }, instr,
                Machines.Lnp64u.Wip.step_inflight_countdown m₁ σ₁ fl hinf₁ h1c,
                hfd', ?_, hdec', by show fl.cyclesLeft - 1 ≤ instr.cost.cost; omega, hcQ⟩
              show fetch (step m₁ σ₁) d = some fl.word
              rw [fetch_frozen hins₁ hfz]
              exact hfetch'
        · -- someone else's: frame
          have hfz : DFrozen m₁ d σ₁ (step m₁ σ₁) :=
            Wip.frame_step m₁ d σ₁ h₁ hiso₁ hins₁
              (fun fl' hfl' hfd' => by
                rw [hinf₁] at hfl'
                injection hfl' with hfl'
                rw [← hfl'] at hfd'
                exact absurd hfd' hfd)
              (fun h => by rw [hinf₁] at h; cases h)
          refine stutter_pack hfz (Or.inl ?_)
          exact Wip.step_quiet m₁ d σ₁
            (fun fl' hfl' => by
              rw [hinf₁] at hfl'
              injection hfl' with hfl'
              rw [← hfl']
              exact hfd)
            (fun h => by rw [hinf₁] at h; cases h)

/-- **T5.** An isolated, top-priority domain's destuttered observed
trajectory is independent of everything outside its own configuration and
code: under agreement, one machine's destuttered trajectory is a prefix of
the other's (run long enough). -/
theorem noninterference (m₁ m₂ : Manifest) (h₁ : m₁.WF) (h₂ : m₂.WF)
    (d : DomainId) (hiso₁ : Isolated m₁ d) (hiso₂ : Isolated m₂ d)
    (hpri₁ : TopPriority m₁ d) (hpri₂ : TopPriority m₂ d)
    (hag : AgreeOn m₁ m₂ d) :
    ∀ n, ∃ k, (destutter (trajectory m₁ d n)) <+: (destutter (trajectory m₂ d k)) := by
  intro n
  cases n with
  | zero =>
      exact ⟨0, by show destutter [] <+: _; exact List.nil_prefix⟩
  | succ N =>
      obtain ⟨K, hdest, _⟩ := sim m₁ m₂ h₁ h₂ d hiso₁ hiso₂ hpri₂ hag N
      exact ⟨K + 1, hdest ▸ List.prefix_refl _⟩

end Machines.Lnp64u.Theorems.T5
