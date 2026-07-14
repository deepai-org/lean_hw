-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireSw

/-!
# R-MC support: the region-op retirement arms (`map`/`unmap`)

Region edits are the second Mover interaction: the status-write
authority (`sAuth`) re-derives the *post-core* region file through the
`mapSet`/`unmapSet` composites. This file proves the fired forms of
those composites, the region-face `absDom` decomposition, and the
`unmap` arm; `map` follows with its check ladder.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 12800000
set_option maxRecDepth 400000

private theorem bv1_one_and3 (x : BitVec 1) : 1#1 &&& x = x := by
  revert x; decide

private theorem bv1_mid_zero (x y : BitVec 1) : x &&& (0#1 &&& y) = 0#1 := by
  revert x y; decide

/-- The fired `unmap` chain: on the owner at the selected region it is
the region-index test; elsewhere it is off. -/
private theorem unmapChain_eval (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hunm : (Hw.isMn "unmap").eval σ = 1#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val) :
    ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ
      = if c = E ∧ r = RI then 1#1 else 0#1 := by
  intro c r
  by_cases hc : c = E
  · subst hc
    show Hw.retiringE.eval σ &&& ((Hw.ifDomIs c).eval σ &&&
      ((Hw.isMn "unmap").eval σ &&&
        (Expr.eq Hw.riE (Hw.rLit r)).eval σ)) = _
    rw [hret, hifsel, hunm, bv1_one_and3, bv1_one_and3, bv1_one_and3]
    by_cases hr : r = RI
    · subst hr
      rw [if_pos ⟨rfl, rfl⟩]
      show (if Hw.riE.eval σ = (Hw.rLit r).eval σ then (1#1 : BitVec 1)
        else 0#1) = 1#1
      rw [if_pos (by rw [hri]; rfl)]
    · rw [if_neg (fun hc' => hr hc'.2)]
      show (if Hw.riE.eval σ = (Hw.rLit r).eval σ then (1#1 : BitVec 1)
        else 0#1) = 0#1
      rw [if_neg (by
        rw [hri]
        intro hc'
        apply hr
        apply Fin.ext
        have : (BitVec.ofNat 2 RI.val).toNat = (BitVec.ofNat 2 r.val).toNat :=
          by rw [hc']; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (show r.val < 2 ^ 2 from r.isLt),
          Nat.mod_eq_of_lt (show RI.val < 2 ^ 2 from RI.isLt)] at this
        omega)]
  · rw [if_neg (fun hc' => hc hc'.1)]
    show Hw.retiringE.eval σ &&& ((Hw.ifDomIs c).eval σ &&&
      ((Hw.isMn "unmap").eval σ &&&
        (Expr.eq Hw.riE (Hw.rLit r)).eval σ)) = 0#1
    rw [bv1_ne_one.mp (hifexcl c hc)]
    exact bv1_mid_zero _ _

/-- `rgnVPostE` under a fired `unmap`: dead at the selected region,
the validity register elsewhere. -/
private theorem rgnVPostE_unmap (σ : Loom.Hw.St) (E : DomainId)
    (hnr : Inert σ)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hunm : (Hw.isMn "unmap").eval σ = 1#1)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val)
    (c : DomainId) (r : RegionId) :
    (Hw.rgnVPostE c r).eval σ
      = if c = E ∧ r = RI then 0#1 else σ.regs (Hw.drgnV c r) 1 := by
  show (if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map",
      Hw.mapOkE c, .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1
    then (Expr.lit 1).eval σ
    else if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1
      then (Expr.lit 0).eval σ
      else (Expr.and (.reg 1 (Hw.drgnV c r))
        (.not (Hw.killedByCoreE _ _))).eval σ) = _
  rw [if_neg (by rw [hmapz c r]; decide)]
  rw [unmapChain_eval σ E hret hifsel hifexcl hunm RI hri c r]
  by_cases hcr : c = E ∧ r = RI
  · rw [if_pos hcr, if_pos rfl, if_pos hcr]
    rfl
  · rw [if_neg hcr, if_neg (by decide : ¬((0#1 : BitVec 1) = 1#1)),
      if_neg hcr]
    show σ.regs (Hw.drgnV c r) 1 &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
    rw [hnr.killed]
    generalize σ.regs (Hw.drgnV c r) 1 = b
    revert b
    decide

/-- The status-authority tree under a fired `unmap`, against any spec
state whose regions are the abstraction's with the selected one dead. -/
theorem sAuth_unmap_eval (σ : Loom.Hw.St) (E : DomainId)
    (hnr : Inert σ)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hunm : (Hw.isMn "unmap").eval σ = 1#1)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val)
    (τ : MachineState)
    (hrgnτ : ∀ (c : DomainId) (r : RegionId), ((τ.doms c)).regions r
      = if c = E ∧ r = RI then none else ((Hw.abs σ).doms c).regions r)
    (ow : Expr 2) (sa : Expr 12) :
    ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
      τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
        ⟨false, true, false⟩ = true := by
  rw [orAll_eval]
  rw [show (τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
      ⟨false, true, false⟩ = true) ↔
      (∃ r : RegionId, ∃ rg,
        (τ.doms (finOfBv (by decide) (ow.eval σ))).regions r = some rg
          ∧ rg.covers (sa.eval σ) ⟨false, true, false⟩ = true) from by
    rw [MachineState.domCovers]; simp]
  constructor
  · rintro ⟨e, hmem, heval⟩
    rw [List.mem_flatMap] at hmem
    obtain ⟨c, -, hmem⟩ := hmem
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hmem
    have h3 : ∀ e ∈ [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
        Hw.rgnCoversVal (Hw.rgnValPostE c r) sa ⟨false, true, false⟩],
        e.eval σ = 1#1 := (andAll_eval σ _).mp heval
    have h1 := h3 (Expr.eq ow (Hw.dLit c)) (by simp)
    have h2 := h3 (Hw.rgnVPostE c r) (by simp)
    have hcv := h3 (Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
      ⟨false, true, false⟩) (by simp)
    rw [eqE_eval] at h1
    have hc : finOfBv (by decide) (ow.eval σ) = c := (bv2_lit_iff _ c).mp h1
    rw [rgnVPostE_unmap σ E hnr hret hifsel hifexcl hunm hmapz RI hri c r]
      at h2
    by_cases hcr : c = E ∧ r = RI
    · rw [if_pos hcr] at h2
      exact absurd h2 (by decide)
    · rw [if_neg hcr] at h2
      rw [rgnCoversVal_eval, rgnValPostE_quiescent σ hmapz] at hcv
      refine ⟨r, Hw.decRegion (σ.regs (Hw.drgn c r) 42), ?_, hcv⟩
      rw [hc, hrgnτ c r, if_neg hcr, abs_regions, if_pos h2]
  · rintro ⟨r, rg, hsome, hcov⟩
    set c : DomainId := finOfBv (by decide) (ow.eval σ) with hcdef
    rw [hrgnτ c r] at hsome
    by_cases hcr : c = E ∧ r = RI
    · rw [if_pos hcr] at hsome
      exact absurd hsome (by simp)
    · rw [if_neg hcr] at hsome
      refine ⟨Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
          Hw.rgnCoversVal (Hw.rgnValPostE c r) sa ⟨false, true, false⟩],
        List.mem_flatMap.mpr ⟨c, List.mem_finRange c,
          List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩⟩, ?_⟩
      rw [abs_regions] at hsome
      by_cases hval : σ.regs (Hw.drgnV c r) 1 = 1#1
      · rw [if_pos hval] at hsome
        obtain rfl := Option.some.inj hsome
        rw [andAll_eval]
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · rw [eqE_eval]
          exact (bv2_lit_iff _ c).mpr rfl
        · rw [rgnVPostE_unmap σ E hnr hret hifsel hifexcl hunm hmapz RI hri
            c r, if_neg hcr]
          exact hval
        · rw [rgnCoversVal_eval, rgnValPostE_quiescent σ hmapz]
          exact hcov
      · rw [if_neg hval] at hsome
        exact absurd hsome (by simp)

end Machines.Lnp64u.Theorems.RMC
