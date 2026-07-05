-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Hw.Core
import Loom.Hw.Compile
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.IntervalCases

/-!
# R-MC support: rule frame lemmas and write-shape checkers

The generic frame layer of the R-MC bridge (NEXTSTEPS §1.2), audit-legal
(no `native_decide`): all syntactic facts about the rules' write sets
reduce in the kernel via `of_decide_eq_true rfl` — `Act.regWrites` discards
expressions, so the facts reduce even with a *symbolic* manifest.

Contents:

* `core_cycle_unfold` — one design cycle as the four rules' `Act.run`
  composition (later writes win).
* `issueFold_notin` / `coreAct_notin` — write-set membership for the
  manifest-dependent parts of the core rule (the issue fold's *order*
  depends on `m` through `schedOrder`, but its write set doesn't; list
  induction turns per-domain kernel facts into the fold fact).
* `WritesLit` — a decidable checker "every write to this register is a
  literal from this list", with the semantic preservation theorem
  `run_WritesLit`. This is what makes `Coupled.run_canon` purely
  syntactic: every circuit that writes a `d*_run` register writes the
  literal `0`, `1`, or `2`.
* Concrete frame instances for the registers `coupled_step` tracks:
  `drctr d`, `"cycle"`, `drun d`.
* Value characterizations: `refillAct_run_drctr` (the mod-`P` counter
  step) and `cycle_regs_cycle` (the tick increment).
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxRecDepth 1000000


/-- The manifest's `Nat` scheduling parameters fit the 32-bit datapath
registers that carry them (`budgetQ < 2 ^ 32` follows via `WF.budget_le`).
Vacuous for any realistic manifest; `demoManifest` satisfies it by
`decide`-scale arithmetic. -/
structure Fits (m : Manifest) : Prop where
  period_lt : ∀ d : DomainId, (m.doms d).periodP < 2 ^ 32
  maxdon_lt : ∀ d : DomainId, (m.doms d).maxDonation < 2 ^ 32

/-! ## The cycle as the four rules' composition -/

theorem core_cycle_unfold (m : Manifest) (σ : Loom.Hw.St) :
    (Hw.core m).cycle σ =
      Hw.tickAct.run σ (Hw.moverAct.run σ
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))) := rfl

/-! ## Frame plumbing -/

/-- Wrapper naming `Compile.run_regs_notin` for rewrite chains. -/
theorem frame {rn : String} {w : Nat} {a : Act}
    (h : (rn, w) ∉ a.regWrites) (σ acc : Loom.Hw.St) :
    (a.run σ acc).regs rn w = acc.regs rn w :=
  Loom.Hw.Compile.run_regs_notin rn w a h σ acc

/-- The issue fold (over *any* domain order — `schedOrder m` is
manifest-dependent) writes only what some `issueFor` writes. -/
theorem issueFold_notin (m : Manifest) (rn : String) (w : Nat)
    (h : ∀ d : DomainId, (rn, w) ∉ (Hw.issueFor m d).regWrites) :
    ∀ l : List DomainId,
      (rn, w) ∉ (l.foldr
        (fun d acc => Act.ite (Hw.eligE m d) (Hw.issueFor m d) acc)
        Act.skip).regWrites
  | [] => by simp [Act.regWrites]
  | d :: t => by
      simpa [Act.regWrites] using
        And.intro (h d) (issueFold_notin m rn w h t)

/-- Write-set membership for the core rule, decomposed into its four
manifest-independent components plus the per-domain issue circuits. -/
theorem coreAct_notin (m : Manifest) (rn : String) (w : Nat)
    (hret : (rn, w) ∉ Hw.retireAct.regWrites)
    (hcl : (rn, w) ≠ ("if_cl", 8))
    (hrvi : (rn, w) ∉ Hw.rvInit.regWrites)
    (hrvs : (rn, w) ∉ Hw.rvStep.regWrites)
    (hiss : ∀ d : DomainId, (rn, w) ∉ (Hw.issueFor m d).regWrites) :
    (rn, w) ∉ (Hw.coreAct m).regWrites := by
  have hfold := issueFold_notin m rn w hiss (Hw.schedOrder m)
  simp only [Hw.coreAct, Act.regWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, not_or]
  exact ⟨⟨hret, hcl, hrvi, hrvs⟩, hfold⟩

/-! ## Literal-write checker -/

/-- Every write to `(rn, wd)` in the act writes a literal from `good`
(kernel-decidable; expressions elsewhere are ignored). -/
def WritesLit (rn : String) (wd : Nat) (good : List (BitVec wd)) : Act → Bool
  | .skip => true
  | .seq a b => WritesLit rn wd good a && WritesLit rn wd good b
  | .ite _ t e => WritesLit rn wd good t && WritesLit rn wd good e
  | .memWrite _ _ _ _ _ _ => true
  | .write w r v =>
      if r = rn then
        if h : w = wd then
          match v with
          | .lit x => decide ((h ▸ x) ∈ good)
          | _ => false
        else true
      else true

/-- The semantic content of `WritesLit`: any property holding of the
tracked register and of every `good` literal is preserved by the run. -/
theorem run_WritesLit {rn : String} {wd : Nat} {good : List (BitVec wd)}
    {P : BitVec wd → Prop} (hgood : ∀ x ∈ good, P x) :
    ∀ (a : Act), WritesLit rn wd good a = true →
      ∀ (σ acc : Loom.Hw.St), P (acc.regs rn wd) →
        P ((a.run σ acc).regs rn wd)
  | .skip, _, _, _, hP => hP
  | .seq a b, h, σ, acc, hP => by
      simp only [WritesLit, Bool.and_eq_true] at h
      exact run_WritesLit hgood b h.2 σ _ (run_WritesLit hgood a h.1 σ acc hP)
  | .ite c t e, h, σ, acc, hP => by
      simp only [WritesLit, Bool.and_eq_true] at h
      show P ((if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).regs rn wd)
      split
      · exact run_WritesLit hgood t h.1 σ acc hP
      · exact run_WritesLit hgood e h.2 σ acc hP
  | .memWrite .., _, _, _, hP => hP
  | .write w r v, h, σ, acc, hP => by
      show P ((acc.regs.set r (v.eval σ)) rn wd)
      simp only [RegEnv.set]
      by_cases hr : rn = r
      · rw [if_pos hr]
        by_cases hw : w = wd
        · subst hw
          rw [dif_pos rfl]
          show P (v.eval σ)
          simp only [WritesLit] at h
          rw [if_pos hr.symm] at h
          simp only [dite_true] at h
          cases v
          · exact hgood _ (of_decide_eq_true h)
          all_goals simp at h
        · rw [dif_neg hw]; exact hP
      · rw [if_neg hr]; exact hP

/-- `WritesLit` for the issue fold, from the per-domain facts. -/
theorem issueFold_WritesLit (m : Manifest) (rn : String) (wd : Nat)
    (good : List (BitVec wd))
    (h : ∀ d : DomainId, WritesLit rn wd good (Hw.issueFor m d) = true) :
    ∀ l : List DomainId,
      WritesLit rn wd good
        (l.foldr (fun d acc => Act.ite (Hw.eligE m d) (Hw.issueFor m d) acc)
          Act.skip) = true
  | [] => rfl
  | d :: t => by
      simp only [List.foldr, WritesLit, Bool.and_eq_true]
      exact ⟨h d, issueFold_WritesLit m rn wd good h t⟩

/-- `WritesLit` for the core rule, decomposed like `coreAct_notin`.
`hcl` covers the countdown write (`if_cl` is written with a non-literal
subtraction, so the checker needs the name to differ). -/
theorem coreAct_WritesLit (m : Manifest) (rn : String) (wd : Nat)
    (good : List (BitVec wd))
    (hret : WritesLit rn wd good Hw.retireAct = true)
    (hcl : rn ≠ "if_cl")
    (hrvi : WritesLit rn wd good Hw.rvInit = true)
    (hrvs : WritesLit rn wd good Hw.rvStep = true)
    (hiss : ∀ d : DomainId, WritesLit rn wd good (Hw.issueFor m d) = true) :
    WritesLit rn wd good (Hw.coreAct m) = true := by
  have hfold := issueFold_WritesLit m rn wd good hiss (Hw.schedOrder m)
  have hcnt : WritesLit rn wd good
      (.write 8 "if_cl" (.sub (.reg 8 "if_cl") (.lit 1))) = true := by
    simp only [WritesLit]
    rw [if_neg (fun hh : "if_cl" = rn => hcl hh.symm)]
  simp only [Hw.coreAct, WritesLit, Bool.and_eq_true]
  exact ⟨⟨hret, hcnt, ⟨hrvi, hrvs⟩, trivial⟩, hfold⟩

/-! ## Projection helpers -/

/-- Distribute a register read over a branch in the accumulated state. -/
@[simp] theorem regs_ite (c : Prop) [Decidable c] (a b : Loom.Hw.St)
    (rn : String) (w : Nat) :
    (if c then a else b).regs rn w = if c then a.regs rn w else b.regs rn w := by
  split <;> rfl

/-- Collapse an `Expr.eq`/`Expr`-level boolean test against `1#1`. -/
@[simp] theorem bv1_ite_eq_one {P : Prop} [Decidable P] :
    ((if P then (1 : BitVec 1) else 0) = 1) = P := by
  by_cases h : P <;> simp [h]

/-! ## Concrete frame instances (kernel-reduced write-set facts) -/

theorem finRange_dom :
    (List.finRange numDomains) = [(0 : DomainId), 1, 2, 3] := by decide

section Instances

variable (m : Manifest) (d x : DomainId)

/- `drctr d` is written only by the refill rule. -/

private theorem retire_notin_drctr :
    (Hw.drctr d, 32) ∉ Hw.retireAct.regWrites := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem rvInit_notin_drctr :
    (Hw.drctr d, 32) ∉ Hw.rvInit.regWrites := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem rvStep_notin_drctr :
    (Hw.drctr d, 32) ∉ Hw.rvStep.regWrites := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem issueFor_notin_drctr :
    (Hw.drctr d, 32) ∉ (Hw.issueFor m x).regWrites := by
  fin_cases d <;> fin_cases x <;> exact of_decide_eq_true rfl

private theorem mover_notin_drctr :
    (Hw.drctr d, 32) ∉ Hw.moverAct.regWrites := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem tick_notin_drctr :
    (Hw.drctr d, 32) ∉ Hw.tickAct.regWrites := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem drctr_ne_ifcl : (Hw.drctr d, 32) ≠ ("if_cl", 8) := by
  fin_cases d <;> exact of_decide_eq_true rfl

theorem coreAct_notin_drctr : (Hw.drctr d, 32) ∉ (Hw.coreAct m).regWrites :=
  coreAct_notin m _ _ (retire_notin_drctr d) (drctr_ne_ifcl d)
    (rvInit_notin_drctr d) (rvStep_notin_drctr d)
    (fun x => issueFor_notin_drctr m d x)

/- `"cycle"` is written only by the tick rule. -/

private theorem refill_notin_cycle :
    ("cycle", 32) ∉ (Hw.refillAct m).regWrites := of_decide_eq_true rfl

private theorem retire_notin_cycle :
    ("cycle", 32) ∉ Hw.retireAct.regWrites := of_decide_eq_true rfl

private theorem rvInit_notin_cycle :
    ("cycle", 32) ∉ Hw.rvInit.regWrites := of_decide_eq_true rfl

private theorem rvStep_notin_cycle :
    ("cycle", 32) ∉ Hw.rvStep.regWrites := of_decide_eq_true rfl

private theorem issueFor_notin_cycle :
    ("cycle", 32) ∉ (Hw.issueFor m x).regWrites := by
  fin_cases x <;> exact of_decide_eq_true rfl

private theorem mover_notin_cycle :
    ("cycle", 32) ∉ Hw.moverAct.regWrites := of_decide_eq_true rfl

theorem coreAct_notin_cycle : ("cycle", 32) ∉ (Hw.coreAct m).regWrites :=
  coreAct_notin m _ _ retire_notin_cycle (by decide)
    rvInit_notin_cycle rvStep_notin_cycle (fun x => issueFor_notin_cycle m x)

/- `drun d` is only ever written with the literals 0, 1, 2, and only by
the core rule. -/

private theorem refill_notin_drun :
    (Hw.drun d, 2) ∉ (Hw.refillAct m).regWrites := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem mover_notin_drun :
    (Hw.drun d, 2) ∉ Hw.moverAct.regWrites := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem tick_notin_drun :
    (Hw.drun d, 2) ∉ Hw.tickAct.regWrites := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem retire_lit_drun :
    WritesLit (Hw.drun d) 2 [0#2, 1#2, 2#2] Hw.retireAct = true := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem rvInit_lit_drun :
    WritesLit (Hw.drun d) 2 [0#2, 1#2, 2#2] Hw.rvInit = true := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem rvStep_lit_drun :
    WritesLit (Hw.drun d) 2 [0#2, 1#2, 2#2] Hw.rvStep = true := by
  fin_cases d <;> exact of_decide_eq_true rfl

private theorem issueFor_lit_drun :
    WritesLit (Hw.drun d) 2 [0#2, 1#2, 2#2] (Hw.issueFor m x) = true := by
  fin_cases d <;> fin_cases x <;> exact of_decide_eq_true rfl

private theorem drun_ne_ifcl : Hw.drun d ≠ "if_cl" := by
  fin_cases d <;> exact of_decide_eq_true rfl

theorem coreAct_lit_drun :
    WritesLit (Hw.drun d) 2 [0#2, 1#2, 2#2] (Hw.coreAct m) = true :=
  coreAct_WritesLit m _ _ _ (retire_lit_drun d) (drun_ne_ifcl d)
    (rvInit_lit_drun d) (rvStep_lit_drun d)
    (fun x => issueFor_lit_drun m d x)

end Instances

/-! ## Post-cycle value characterizations -/

/-- After a full design cycle, the hidden refill counter holds exactly what
the refill rule wrote (the other three rules never touch it). -/
theorem cycle_regs_drctr (m : Manifest) (σ : Loom.Hw.St) (d : DomainId) :
    ((Hw.core m).cycle σ).regs (Hw.drctr d) 32 =
      ((Hw.refillAct m).run σ σ).regs (Hw.drctr d) 32 := by
  rw [core_cycle_unfold, frame (tick_notin_drctr d),
    frame (mover_notin_drctr d), frame (coreAct_notin_drctr m d)]

/-- The tick rule's increment reads the *pre-cycle* counter (D9). -/
theorem cycle_regs_cycle (m : Manifest) (σ : Loom.Hw.St) :
    ((Hw.core m).cycle σ).regs "cycle" 32 = σ.regs "cycle" 32 + 1 := by
  rw [core_cycle_unfold]
  simp [Hw.tickAct, Act.run, RegEnv.set, Expr.eval]

/-- The refill rule's counter step: roll to `0` at `P - 1`, else increment
(reads pre-cycle, writes last per domain). -/
theorem refillAct_run_drctr (m : Manifest) (σ acc : Loom.Hw.St) (d : DomainId) :
    ((Hw.refillAct m).run σ acc).regs (Hw.drctr d) 32 =
      if σ.regs (Hw.drctr d) 32 = BitVec.ofNat 32 ((m.doms d).periodP - 1)
      then 0#32 else σ.regs (Hw.drctr d) 32 + 1 := by
  fin_cases d <;>
    simp +decide [Hw.refillAct, finRange_dom, Hw.seqAll, Act.run, Expr.eval,
      Hw.refillCondE, RegEnv.set, Hw.drctr, Hw.dbudget, numDomains]

/-- The mod-`P` counter step tracks the wrapping 32-bit increment:
`P ∣ 2 ^ 32` (`Manifest.WF.period_dvd`) makes the two roll-overs coincide,
so `rctr` rolling `P - 1 → 0` is exactly `cycle` crossing a period
boundary — including the `2 ^ 32` wrap itself. -/
theorem rctr_step_sync {P : Nat} (hpos : 0 < P) (hdvd : P ∣ 2 ^ 32)
    (hlt : P < 2 ^ 32) (r c : BitVec 32)
    (hsync : r.toNat = c.toNat % P) :
    (if r = BitVec.ofNat 32 (P - 1) then 0#32 else r + 1).toNat
      = (c + 1).toNat % P := by
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  have hmod : (c + 1).toNat % P = (c.toNat % P + 1 % P) % P := by
    rw [BitVec.toNat_add, h1, Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod]
  have hk : c.toNat % P < P := Nat.mod_lt _ hpos
  rcases Nat.lt_or_ge 1 P with hP2 | hP1
  · have h1P : 1 % P = 1 := Nat.mod_eq_of_lt hP2
    have hPm1 : (BitVec.ofNat 32 (P - 1)).toNat = P - 1 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    split
    · next heq =>
        have hcp : c.toNat % P = P - 1 := by rw [← hsync, heq, hPm1]
        rw [hmod, h1P, hcp]
        simp [Nat.sub_add_cancel (Nat.one_le_of_lt hP2), Nat.mod_self]
    · next hne =>
        have hne' : r.toNat ≠ P - 1 := fun h => hne (by
          apply BitVec.eq_of_toNat_eq; rw [h, hPm1])
        have hlt' : c.toNat % P < P - 1 := by omega
        have hr1 : (r + 1).toNat = r.toNat + 1 := by
          rw [BitVec.toNat_add, h1]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hr1, hmod, h1P, Nat.mod_eq_of_lt (by omega), hsync]
  · have hP1' : P = 1 := by omega
    subst hP1'
    simp only [Nat.mod_one]
    have hr0 : r = BitVec.ofNat 32 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega
    simp [hr0]

/-- After a full design cycle the `drun` registers still avoid the decode
fallback `3#2` (every write is a literal 0/1/2, and only the core rule
writes them). -/
theorem cycle_regs_drun_ne (m : Manifest) (σ : Loom.Hw.St) (d : DomainId)
    (h : σ.regs (Hw.drun d) 2 ≠ 3#2) :
    ((Hw.core m).cycle σ).regs (Hw.drun d) 2 ≠ 3#2 := by
  rw [core_cycle_unfold, frame (tick_notin_drun d), frame (mover_notin_drun d)]
  refine run_WritesLit (P := (· ≠ 3#2)) ?_ _ (coreAct_lit_drun m d) σ _ ?_
  · intro x hx
    fin_cases hx <;> decide
  · rw [frame (refill_notin_drun m d)]
    exact h

end Machines.Lnp64u.Theorems.RMC
