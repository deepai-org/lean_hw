-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCMover
import Machines.Lnp64u.Theorems.RMCRefill
import Machines.Lnp64u.Logic.Hostage
import Mathlib.Logic.Function.Iterate

/-!
# R-MC support: the scheduler bridge

The idle-core half of the square needs the circuit's scheduler to match
`Step.schedule` on the post-refill state:

* `payerE_eval` — the unrolled serving-chain walk (`chainNextE` iterated
  `maxChainDepth` times through 4-way muxes) is `MachineState.payer` on
  the abstraction. A stopped walk is a fixpoint of the step, so the
  fuel-bounded spec recursion equals plain function iteration
  (`chainOrigin_eq_iterate`).
* `eligE_eval` — the eligibility circuit (running + post-refill payer
  budget nonzero, through the `effBudgetE` bypass) is `Eligible` on the
  post-refill spec state.
* `issueFold_run_of_none` / `issueFold_run_of_first` — the priority-
  ordered issue fold runs nothing when no domain is eligible, and runs
  exactly the scheduled (max-priority eligible) domain's issue circuit
  otherwise (`mergeSort` sortedness + `WF.prio_inj`).
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## The payer walk -/

/-- One spec-side step of the serving-chain walk (`chainOrigin`'s body). -/
def specNext (τ : MachineState) (c : DomainId) : DomainId :=
  match (τ.doms c).serving with
  | none => c
  | some g =>
      match (τ.gates g).act with
      | some a => a.caller
      | none => c

/-- Fuel-bounded recursion is iteration: a stopped walk is a fixpoint. -/
theorem chainOrigin_eq_iterate (τ : MachineState) :
    ∀ (f : Nat) (c : DomainId), τ.chainOrigin f c = (specNext τ)^[f] c
  | 0, c => rfl
  | f + 1, c => by
      rw [Function.iterate_succ_apply]
      show (match (τ.doms c).serving with
        | none => c
        | some g => match (τ.gates g).act with
          | some a => τ.chainOrigin f a.caller
          | none => c) = _
      cases hs : (τ.doms c).serving with
      | none =>
          have hfix : specNext τ c = c := by simp only [specNext, hs]
          rw [hfix, Function.iterate_fixed hfix]
      | some g =>
          show (match (τ.gates g).act with
            | some a => τ.chainOrigin f a.caller
            | none => c) = _
          cases ha : (τ.gates g).act with
          | some a =>
              have hnx : specNext τ c = a.caller := by
                simp only [specNext, hs, ha]
              rw [hnx]
              exact chainOrigin_eq_iterate τ f a.caller
          | none =>
              have hfix : specNext τ c = c := by
                simp only [specNext, hs, ha]
              rw [hfix, Function.iterate_fixed hfix]

/-- The per-static-domain chain step decodes to `specNext` on the
abstraction. -/
theorem chainNextE_eval (σ : Loom.Hw.St) (c : DomainId) :
    finOfBv (by decide) ((Hw.chainNextE c).eval σ)
      = specNext (Hw.abs σ) c := by
  show finOfBv _ (if ((Expr.reg 1 (Hw.dsrvV c)).eval σ &&&
      (Hw.muxFin (fun gg => .reg 1 (Hw.gactV gg))
        (.reg 2 (Hw.dsrv c))).eval σ) = 1#1
    then (Hw.muxFin (fun gg => .reg 2 (Hw.gcaller gg))
      (.reg 2 (Hw.dsrv c))).eval σ
    else BitVec.ofNat 2 c.val) = _
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates),
    muxFin_eval (by decide : 2 ^ 2 = numGates)]
  set g : GateId := finOfBv (by decide)
    ((Expr.reg 2 (Hw.dsrv c)).eval σ) with hg
  show finOfBv _ (if (σ.regs (Hw.dsrvV c) 1 &&& σ.regs (Hw.gactV g) 1) = 1#1
    then σ.regs (Hw.gcaller g) 2 else BitVec.ofNat 2 c.val) = _
  unfold specNext
  by_cases hsv : σ.regs (Hw.dsrvV c) 1 = 1#1
  · have hserv : ((Hw.abs σ).doms c).serving = some g := by
      show (if σ.regs (Hw.dsrvV c) 1 = 1#1 then _ else _) = _
      rw [if_pos hsv]
      rfl
    rw [hserv]
    show _ = (match ((Hw.abs σ).gates g).act with
      | some a => a.caller
      | none => c)
    by_cases hact : σ.regs (Hw.gactV g) 1 = 1#1
    · have haa : ((Hw.abs σ).gates g).act = some
          { caller := finOfBv (by decide) (σ.regs (Hw.gcaller g) 2)
            callerRd := finOfBv (by decide) (σ.regs (Hw.gcallerRd g) 3)
            savedRegs := fun r => σ.regs (Hw.gsreg g r) 32
            savedPc := σ.regs (Hw.gspc g) 12
            savedServing :=
              if σ.regs (Hw.gssrvV g) 1 = 1#1 then
                some (finOfBv (by decide) (σ.regs (Hw.gssrv g) 2))
              else none
            depth := (σ.regs (Hw.gdepth g) 3).toNat
            donated := (σ.regs (Hw.gdon g) 32).toNat } := by
        show (if σ.regs (Hw.gactV g) 1 = 1#1 then _ else _) = _
        rw [if_pos hact]
        rfl
      rw [haa]
      rw [if_pos (by rw [hsv, hact]; decide)]
    · have haa : ((Hw.abs σ).gates g).act = none := by
        show (if σ.regs (Hw.gactV g) 1 = 1#1 then _ else _) = _
        rw [if_neg hact]
      rw [haa]
      rw [if_neg (show ¬(σ.regs (Hw.dsrvV c) 1 &&& σ.regs (Hw.gactV g) 1
          = 1#1) from by
        rw [bv1_ne_one.mp hact]
        generalize σ.regs (Hw.dsrvV c) 1 = b
        revert b; decide)]
      apply Fin.ext
      show (BitVec.ofNat 2 c.val).toNat = c.val
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := c.isLt; omega)
  · have hserv : ((Hw.abs σ).doms c).serving = none := by
      show (if σ.regs (Hw.dsrvV c) 1 = 1#1 then _ else _) = _
      rw [if_neg hsv]
    rw [hserv]
    show _ = c
    rw [if_neg (show ¬(σ.regs (Hw.dsrvV c) 1 &&& σ.regs (Hw.gactV g) 1
        = 1#1) from by
      rw [bv1_ne_one.mp hsv]
      generalize σ.regs (Hw.gactV g) 1 = b
      revert b; decide)]
    apply Fin.ext
    show (BitVec.ofNat 2 c.val).toNat = c.val
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := c.isLt; omega)

/-- The unrolled payer walk is `MachineState.payer` on the abstraction. -/
theorem payerE_eval (σ : Loom.Hw.St) (d : DomainId) :
    finOfBv (by decide) ((Hw.payerE d).eval σ) = (Hw.abs σ).payer d := by
  have hfold : ∀ (n : Nat) (e : Expr 2),
      finOfBv (by decide : 2 ^ 2 = numDomains)
        (((List.range n).foldl (fun e' _ => Hw.muxFin Hw.chainNextE e') e).eval σ)
      = (specNext (Hw.abs σ))^[n] (finOfBv (by decide) (e.eval σ)) := by
    intro n
    induction n with
    | zero => intro e; rfl
    | succ k ih =>
        intro e
        rw [List.range_succ, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        rw [muxFin_eval (by decide : 2 ^ 2 = numDomains)]
        rw [Function.iterate_succ_apply']
        rw [← ih e]
        exact chainNextE_eval σ _
  show finOfBv _ (((List.range maxChainDepth).foldl
    (fun e' _ => Hw.muxFin Hw.chainNextE e') (Hw.dLit d)).eval σ) = _
  rw [hfold maxChainDepth (Hw.dLit d)]
  rw [MachineState.payer, chainOrigin_eq_iterate]
  congr 1
  apply Fin.ext
  show (BitVec.ofNat 2 d.val).toNat = d.val
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := d.isLt; omega)


/-! ## Eligibility -/

/-- Refill does not move the payer walk (it only touches budgets and the
hidden counters; the walk reads `serving` and the gate table). -/
theorem refillPhase_chainOrigin (m : Manifest) (τ : MachineState) :
    ∀ (f : Nat) (c : DomainId),
      (refillPhase m τ).chainOrigin f c = τ.chainOrigin f c
  | 0, _ => rfl
  | f + 1, c => by
      have hL : (refillPhase m τ).chainOrigin (f + 1) c =
          (match (τ.doms c).serving with
            | none => c
            | some g => match (τ.gates g).act with
              | some a => (refillPhase m τ).chainOrigin f a.caller
              | none => c) := by
        show (match ((refillPhase m τ).doms c).serving with
          | none => c
          | some g => match ((refillPhase m τ).gates g).act with
            | some a => (refillPhase m τ).chainOrigin f a.caller
            | none => c) = _
        rw [refillPhase_serving, refillPhase_gates]
      rw [hL]
      show _ = (match (τ.doms c).serving with
        | none => c
        | some g => match (τ.gates g).act with
          | some a => τ.chainOrigin f a.caller
          | none => c)
      cases hs : (τ.doms c).serving with
      | none => rfl
      | some g =>
          show (match (τ.gates g).act with
            | some a => (refillPhase m τ).chainOrigin f a.caller
            | none => c) = (match (τ.gates g).act with
            | some a => τ.chainOrigin f a.caller
            | none => c)
          cases ha : (τ.gates g).act with
          | none => rfl
          | some a =>
              show (refillPhase m τ).chainOrigin f a.caller = _
              exact refillPhase_chainOrigin m τ f a.caller

theorem refillPhase_payer (m : Manifest) (τ : MachineState) (d : DomainId) :
    (refillPhase m τ).payer d = τ.payer d :=
  refillPhase_chainOrigin m τ maxChainDepth d

/-- Canonical run states: `= 0` reads back as `.running` (the decode
fallback `3` is excluded by the coupling). -/
private theorem decRun_running_iff (b g : BitVec 2) (h : b ≠ 3#2) :
    (Hw.decRun b g = .running) ↔ b = 0#2 := by
  have hb : b = 0#2 ∨ b = 1#2 ∨ b = 2#2 ∨ b = 3#2 := by
    revert b
    decide
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp [Hw.decRun] at h ⊢

/-- The eligibility circuit is `Eligible` on the post-refill state. -/
theorem eligE_eval (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2) (d : DomainId) :
    ((Hw.eligE m d).eval σ = 1#1) ↔
      Eligible (refillPhase m (Hw.abs σ)) d := by
  set p : DomainId := (Hw.abs σ).payer d with hp
  have hpayer : (refillPhase m (Hw.abs σ)).payer d = p :=
    refillPhase_payer m (Hw.abs σ) d
  -- the effective-budget mux reads the payer's post-refill budget
  have hbud : ((Hw.muxFin (fun q => Hw.effBudgetE m q) (Hw.payerE d)).eval σ).toNat
      = ((refillPhase m (Hw.abs σ)).doms p).budget := by
    rw [muxFin_eval (by decide : 2 ^ 2 = numDomains)]
    rw [show finOfBv (by decide : 2 ^ 2 = numDomains) ((Hw.payerE d).eval σ)
      = p from payerE_eval σ d]
    show (if (Hw.refillCondE p).eval σ = 1#1
      then (BitVec.ofNat 32 (m.doms p).budgetQ)
      else σ.regs (Hw.dbudget p) 32).toNat = _
    rw [refillPhase_dbudget]
    have hQ : (m.doms p).budgetQ < 2 ^ 32 :=
      Nat.lt_of_le_of_lt (hwf.budget_le p) (hfit.period_lt p)
    have hzero : ((Hw.refillCondE p).eval σ = 1#1) ↔
        ((Hw.abs σ).cycle.toNat % (m.doms p).periodP = 0) := by
      show ((if σ.regs (Hw.drctr p) 32 = (Expr.lit (0 : BitVec 32)).eval σ
        then (1 : BitVec 1) else 0) = 1) ↔ _
      rw [bv1_ite_eq_one]
      constructor
      · intro h
        have := hsync p
        rw [show (Expr.lit (0:BitVec 32)).eval σ = 0#32 from rfl] at h
        rw [h] at this
        simpa [Hw.abs] using this.symm
      · intro h
        show σ.regs (Hw.drctr p) 32 = 0#32
        apply BitVec.eq_of_toNat_eq
        rw [hsync p]
        simpa [Hw.abs] using h
    by_cases hb : (Hw.refillCondE p).eval σ = 1#1
    · rw [if_pos hb, if_pos (hzero.mp hb)]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [if_neg hb, if_neg (fun hc => hb (hzero.mpr hc))]
      rfl
  -- assemble
  show ((Expr.eq (.reg 2 (Hw.drun d)) (.lit 0)).eval σ &&&
    (Expr.not (.eq (Hw.muxFin (fun q => Hw.effBudgetE m q) (Hw.payerE d))
      (.lit 0))).eval σ = 1#1) ↔ _
  rw [bv1_and_eq_one]
  constructor
  · rintro ⟨h1, h2⟩
    rw [eqE_eval] at h1
    rw [notE_eval] at h2
    constructor
    · show ((refillPhase m (Hw.abs σ)).doms d).run = .running
      rw [refillPhase_run]
      show Hw.decRun (σ.regs (Hw.drun d) 2) (σ.regs (Hw.drunG d) 2) = .running
      rw [decRun_running_iff _ _ (hrc d)]
      exact h1
    · show 0 < ((refillPhase m (Hw.abs σ)).doms
        ((refillPhase m (Hw.abs σ)).payer d)).budget
      rw [hpayer, ← hbud]
      have hne : ¬((Hw.muxFin (fun q => Hw.effBudgetE m q)
          (Hw.payerE d)).eval σ = 0#32) := by
        intro hc
        have : (Expr.eq (Hw.muxFin (fun q => Hw.effBudgetE m q)
            (Hw.payerE d)) (.lit 0)).eval σ = 1#1 := by
          rw [eqE_eval]
          exact hc
        rw [h2] at this
        exact absurd this (by decide)
      have : ((Hw.muxFin (fun q => Hw.effBudgetE m q)
          (Hw.payerE d)).eval σ).toNat ≠ 0 := fun hc =>
        hne (BitVec.eq_of_toNat_eq (by simpa using hc))
      omega
  · rintro ⟨h1, h2⟩
    constructor
    · rw [eqE_eval]
      have h1' : ((refillPhase m (Hw.abs σ)).doms d).run = .running := h1
      rw [refillPhase_run] at h1'
      exact (decRun_running_iff _ _ (hrc d)).mp h1'
    · rw [notE_eval]
      apply bv1_ne_one.mp
      intro hc
      rw [eqE_eval] at hc
      rw [hpayer, ← hbud] at h2
      rw [show (Expr.lit (0 : BitVec 32)).eval σ = 0#32 from rfl] at hc
      rw [hc] at h2
      simp at h2


/-! ## The issue fold -/

/-- With no eligible domain, the fold runs nothing. -/
theorem issueFold_run_of_none (m : Manifest) (σ acc : Loom.Hw.St)
    (hnone : ∀ d : DomainId, (Hw.eligE m d).eval σ ≠ 1#1) :
    ∀ l : List DomainId,
      ((l.foldr (fun d acc' => Act.ite (Hw.eligE m d) (Hw.issueFor m d) acc')
        Act.skip).run σ acc) = acc
  | [] => rfl
  | d :: t => by
      show (if (Hw.eligE m d).eval σ = 1#1 then _ else _) = _
      rw [if_neg (hnone d)]
      exact issueFold_run_of_none m σ acc hnone t

/-- The fold over a priority-sorted list runs exactly the top-priority
eligible domain's issue circuit. -/
theorem issueFold_run_of_first (m : Manifest) (hwf : m.WF)
    (σ acc : Loom.Hw.St) (d : DomainId)
    (hd : (Hw.eligE m d).eval σ = 1#1)
    (htop : ∀ e : DomainId, (Hw.eligE m e).eval σ = 1#1 →
      (m.doms e).priority ≤ (m.doms d).priority) :
    ∀ l : List DomainId, d ∈ l →
      l.Pairwise (fun a b => (m.doms b).priority ≤ (m.doms a).priority) →
      ((l.foldr (fun e acc' => Act.ite (Hw.eligE m e) (Hw.issueFor m e) acc')
        Act.skip).run σ acc) = (Hw.issueFor m d).run σ acc
  | [], hmem, _ => absurd hmem (List.not_mem_nil)
  | h :: t, hmem, hpw => by
      show (if (Hw.eligE m h).eval σ = 1#1 then _ else _) = _
      by_cases hh : (Hw.eligE m h).eval σ = 1#1
      · rw [if_pos hh]
        rcases List.mem_cons.mp hmem with rfl | hdt
        · rfl
        · have h1 : (m.doms h).priority ≤ (m.doms d).priority := htop h hh
          have h2 : (m.doms d).priority ≤ (m.doms h).priority :=
            (List.pairwise_cons.mp hpw).1 d hdt
          rw [hwf.prio_inj h d (Nat.le_antisymm h1 h2)]
      · rw [if_neg hh]
        have hdt : d ∈ t := by
          rcases List.mem_cons.mp hmem with rfl | hdt
          · exact absurd hd hh
          · exact hdt
        exact issueFold_run_of_first m hwf σ acc d hd htop t hdt
          (List.pairwise_cons.mp hpw).2

/-- `schedOrder` is priority-sorted (descending). -/
theorem schedOrder_pairwise (m : Manifest) :
    (Hw.schedOrder m).Pairwise
      (fun a b => (m.doms b).priority ≤ (m.doms a).priority) := by
  have hp := List.pairwise_mergeSort
    (le := fun a b : DomainId => decide ((m.doms b).priority ≤ (m.doms a).priority))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at *
      omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega)
    (List.finRange numDomains)
  exact hp.imp (fun h => by simpa using h)

theorem schedOrder_mem (m : Manifest) (d : DomainId) :
    d ∈ Hw.schedOrder m :=
  (List.mergeSort_perm (List.finRange numDomains) _).mem_iff.mpr
    (List.mem_finRange d)

/-- `schedule` is `none` exactly when nothing is eligible. -/
theorem schedule_none_iff (m : Manifest) (τ : MachineState) :
    schedule m τ = none ↔ ∀ d, ¬ Eligible τ d := by
  constructor
  · intro h d he
    have := schedule_isSome_of_eligible m τ d he
    rw [h] at this
    exact absurd this (by simp)
  · intro h
    cases hs : schedule m τ with
    | none => rfl
    | some b => exact absurd (schedule_eligible m τ b hs) (h b)

/-! ## The idle-core selections -/

/-- Idle core, nothing eligible: the core rule runs nothing. -/
theorem coreAct_run_idle_none (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1)
    (hnone : ∀ d : DomainId, (Hw.eligE m d).eval σ ≠ 1#1) :
    (Hw.coreAct m).run σ acc = acc := by
  show (if (Expr.reg 1 "if_v").eval σ = 1#1 then _ else _) = _
  rw [if_neg (show ¬((Expr.reg 1 "if_v").eval σ = 1#1) from hifv0)]
  exact issueFold_run_of_none m σ acc hnone _

/-- Idle core, top-priority eligible `d`: the core rule runs `d`'s issue
circuit. -/
theorem coreAct_run_idle_issue (m : Manifest) (hwf : m.WF)
    (σ acc : Loom.Hw.St) (d : DomainId)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1)
    (hd : (Hw.eligE m d).eval σ = 1#1)
    (htop : ∀ e : DomainId, (Hw.eligE m e).eval σ = 1#1 →
      (m.doms e).priority ≤ (m.doms d).priority) :
    (Hw.coreAct m).run σ acc = (Hw.issueFor m d).run σ acc := by
  show (if (Expr.reg 1 "if_v").eval σ = 1#1 then _ else _) = _
  rw [if_neg (show ¬((Expr.reg 1 "if_v").eval σ = 1#1) from hifv0)]
  exact issueFold_run_of_first m hwf σ acc d hd htop _
    (schedOrder_mem m d) (schedOrder_pairwise m)

end Machines.Lnp64u.Theorems.RMC
