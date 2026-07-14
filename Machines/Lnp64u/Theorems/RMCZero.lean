-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCCanon
import Machines.Lnp64u.Theorems.RMCBridge
import Machines.Lnp64u.Theorems.RMCResetDom

/-!
# R-MC support: the r0-is-zero invariant

The spec's architectural register read (`DomainState.reg`) hardwires `r0`
to zero, while `Hw.readReg` muxes over the real register file — including
`dreg d 0`. The two agree because the `r0` registers are invariantly zero:

* boot writes `0` (`bootDom.regs = fun _ => 0`, gates have no activation);
* `writeReg` discards index-0 writes (the spec's `setReg` mirror);
* the only other writers are `gate_call`'s callee-file wipe (a literal
  `0` at index 0, and the caller-file save `gsreg g 0 := dreg c 0`) and
  `gate_return`'s restore (`dreg d 0 := gsreg g 0`) — both stay inside
  the zero family.

Proof-forced `Coupled` clause (repo pattern): the checker below walks
every rule once (`ZeroWritesAll`, mirroring `RMCCanon.CanonWritesAll`)
and shows each write to a zero-family register is a mux tree over
zero-family leaves.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-- The zero-family registers: every domain's `r0` and its gate-saved
mirror. -/
def r0Names : List String :=
  ((List.finRange numDomains).map fun d => Hw.dreg d 0)
  ++ ((List.finRange numGates).map fun g => Hw.gsreg g 0)

/-- All zero-family registers hold zero. -/
def R0Zero (σ : Loom.Hw.St) : Prop :=
  ∀ n ∈ r0Names, σ.regs n 32 = 0#32

theorem dreg0_mem_r0Names (d : DomainId) : Hw.dreg d 0 ∈ r0Names := by
  fin_cases d <;> decide +kernel

theorem gsreg0_mem_r0Names (g : GateId) : Hw.gsreg g 0 ∈ r0Names := by
  fin_cases g <;> decide +kernel

/-- Zero-family leaves: the literal zero and zero-family register reads. -/
def isZeroLeaf (e : Expr 32) : Bool :=
  match e with
  | .lit v => v == 0#32
  | .reg _ n => decide (n ∈ r0Names)
  | _ => false

/-- Zero-family expressions: mux trees over zero-family leaves (the shape
`muxFin` produces for the gate save/restore files). Fuel-based for the
same reason as `RMCCanon.isCanonE`. -/
def isZeroE : Nat → Expr 32 → Bool
  | 0, _ => false
  | fuel + 1, .mux _ t f => isZeroE fuel t && isZeroE fuel f
  | _ + 1, e => isZeroLeaf e

theorem isZeroLeaf_eval {σ : Loom.Hw.St} (hσ : R0Zero σ)
    (e : Expr 32) (h : isZeroLeaf e = true) : e.eval σ = 0#32 := by
  unfold isZeroLeaf at h
  split at h
  · exact of_decide_eq_true h
  · exact hσ _ (of_decide_eq_true h)
  · simp at h

theorem isZeroE_eval {σ : Loom.Hw.St} (hσ : R0Zero σ) :
    ∀ (fuel : Nat) (e : Expr 32), isZeroE fuel e = true → e.eval σ = 0#32
  | 0, e, h => by simp [isZeroE] at h
  | fuel + 1, .mux c t f, h => by
      simp only [isZeroE, Bool.and_eq_true] at h
      show (if c.eval σ = 1#1 then t.eval σ else f.eval σ) = 0#32
      split
      · exact isZeroE_eval hσ fuel t h.1
      · exact isZeroE_eval hσ fuel f h.2
  | _ + 1, .lit v, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .reg _ n, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .memRead _ _ a, h =>
      isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .and a b, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .or a b, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .xor a b, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .not a, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .add a b, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .sub a b, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .shl a b, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .shr a b, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .slice a lo _, h =>
      isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .zext a _, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)
  | _ + 1, .sext a _, h => isZeroLeaf_eval hσ _ (by simpa [isZeroE] using h)

/-- Every write to a zero-family register (at width 32) has an `isZeroE`
value. -/
def ZeroWritesAll : Act → Bool
  | .skip => true
  | .seq a b => ZeroWritesAll a && ZeroWritesAll b
  | .ite _ t e => ZeroWritesAll t && ZeroWritesAll e
  | .memWrite _ _ _ _ _ _ => true
  | .write w r v =>
      if r ∈ r0Names then
        if h : w = 32 then isZeroE canonFuel (h ▸ v) else true
      else true

theorem run_ZeroWritesAll {σ : Loom.Hw.St} (hσ : R0Zero σ)
    {rn : String} (hrn : rn ∈ r0Names) :
    ∀ (a : Act), ZeroWritesAll a = true →
      ∀ (acc : Loom.Hw.St), acc.regs rn 32 = 0#32 →
        (a.run σ acc).regs rn 32 = 0#32
  | .skip, _, _, hP => hP
  | .seq a b, h, acc, hP => by
      simp only [ZeroWritesAll, Bool.and_eq_true] at h
      exact run_ZeroWritesAll hσ hrn b h.2 _
        (run_ZeroWritesAll hσ hrn a h.1 acc hP)
  | .ite c t e, h, acc, hP => by
      simp only [ZeroWritesAll, Bool.and_eq_true] at h
      show (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).regs rn 32
        = 0#32
      split
      · exact run_ZeroWritesAll hσ hrn t h.1 acc hP
      · exact run_ZeroWritesAll hσ hrn e h.2 acc hP
  | .memWrite .., _, _, hP => hP
  | .write w r v, h, acc, hP => by
      show (acc.regs.set r (v.eval σ)) rn 32 = 0#32
      simp only [RegEnv.set]
      by_cases hr : rn = r
      · rw [if_pos hr]
        by_cases hw : w = 32
        · subst hw
          rw [dif_pos rfl]
          simp only [ZeroWritesAll] at h
          rw [if_pos (hr ▸ hrn)] at h
          simp only [dite_true] at h
          exact isZeroE_eval hσ canonFuel v h
        · rw [dif_neg hw]; exact hP
      · rw [if_neg hr]; exact hP

/-! ## Per-rule instances (single kernel walks) -/

private theorem retire_zero : ZeroWritesAll Hw.retireAct = true := by
  decide +kernel

private theorem rvInit_zero : ZeroWritesAll Hw.rvInit = true := by
  decide +kernel

private theorem rvStep_zero : ZeroWritesAll Hw.rvStep = true := by
  decide +kernel

private theorem issueFor_zero (m : Manifest) (x : DomainId) :
    ZeroWritesAll (Hw.issueFor m x) = true := by
  fin_cases x <;> exact rfl

private theorem mover_zero : ZeroWritesAll Hw.moverAct = true := by
  decide +kernel

private theorem refill_zero (m : Manifest) :
    ZeroWritesAll (Hw.refillAct m) = true := rfl

private theorem tick_zero : ZeroWritesAll Hw.tickAct = true := by
  decide +kernel

private theorem issueFold_zero (m : Manifest) :
    ∀ l : List DomainId,
      ZeroWritesAll
        (l.foldr (fun d acc => Act.ite (Hw.eligE m d) (Hw.issueFor m d) acc)
          Act.skip) = true
  | [] => rfl
  | d :: t => by
      simp only [List.foldr, ZeroWritesAll, Bool.and_eq_true]
      exact ⟨issueFor_zero m d, issueFold_zero m t⟩

private theorem coreAct_zero (m : Manifest) :
    ZeroWritesAll (Hw.coreAct m) = true := by
  have hfold := issueFold_zero m (Hw.schedOrder m)
  have hcnt : ZeroWritesAll
      (.write 8 "if_cl" (.sub (.reg 8 "if_cl") (.lit 1))) = true := by
    simp only [ZeroWritesAll]
    rw [if_neg (by decide +kernel : ¬"if_cl" ∈ r0Names)]
  simp only [Hw.coreAct, ZeroWritesAll, Bool.and_eq_true]
  exact ⟨⟨retire_zero, hcnt, ⟨rvInit_zero, rvStep_zero⟩, trivial⟩, hfold⟩

/-! ## Cycle preservation and reset -/

/-- One design cycle keeps the zero family at zero. -/
theorem cycle_r0_zero (m : Manifest) (σ : Loom.Hw.St)
    (hσ : R0Zero σ) : R0Zero ((Hw.core m).cycle σ) := by
  intro rn hrn
  rw [core_cycle_unfold]
  refine run_ZeroWritesAll hσ hrn _ tick_zero _ ?_
  refine run_ZeroWritesAll hσ hrn _ mover_zero _ ?_
  refine run_ZeroWritesAll hσ hrn _ (coreAct_zero m) _ ?_
  refine run_ZeroWritesAll hσ hrn _ (refill_zero m) _ ?_
  exact hσ rn hrn

set_option maxRecDepth 400000 in
set_option maxHeartbeats 16000000 in
/-- The gate-saved `r0` mirrors boot at zero (no activation at reset). -/
theorem reset_gsreg0 (m : Manifest) : ∀ (g : GateId),
    (Hw.core m).reset.regs (Hw.gsreg g 0) 32
      = ((m.initState.gates g).act.map fun x => x.savedRegs 0).getD 0
  | ⟨0, _⟩ => reset_lookup m 553 (by omega)
  | ⟨1, _⟩ => reset_lookup m 571 (by omega)
  | ⟨2, _⟩ => reset_lookup m 589 (by omega)
  | ⟨3, _⟩ => reset_lookup m 607 (by omega)

/-- The zero family boots at zero. -/
theorem reset_r0_zero (m : Manifest) : R0Zero (Hw.core m).reset := by
  intro n hn
  rcases List.mem_append.mp hn with h | h
  · obtain ⟨d, -, rfl⟩ := List.mem_map.mp h
    rw [reset_dreg]
    simp [Manifest.initState, Manifest.bootDom]
  · obtain ⟨g, -, rfl⟩ := List.mem_map.mp h
    rw [reset_gsreg0]
    simp [Manifest.initState]

/-! ## The architectural-read bridge -/

/-- `Hw.readReg` at a decoded index is the spec's architectural read: the
`r0` mux leg reads a zero-family register. -/
theorem readReg_eval (σ : Loom.Hw.St) (hz : R0Zero σ) (d : DomainId)
    (rE : Expr 3) (r : RegId) (hr : r.val = (rE.eval σ).toNat) :
    (Hw.readReg d rE).eval σ = ((Hw.abs σ).doms d).reg r := by
  rw [Hw.readReg, muxFin_eval (by decide : 2 ^ 3 = numRegs)]
  have hidx : finOfBv (by decide : 2 ^ 3 = numRegs) (rE.eval σ) = r :=
    Fin.ext (show (finOfBv _ (rE.eval σ)).val = r.val from hr ▸ rfl)
  rw [hidx]
  show σ.regs (Hw.dreg d r) 32 = DomainState.reg _ r
  rw [DomainState.reg]
  by_cases h0 : r = (0 : Fin numRegs)
  · rw [if_pos h0, h0]
    exact hz _ (dreg0_mem_r0Names d)
  · rw [if_neg h0]
    rfl

end Machines.Lnp64u.Theorems.RMC
