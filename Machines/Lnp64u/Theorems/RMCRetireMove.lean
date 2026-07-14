-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireMap

/-!
# R-MC retirement: the `move` arm (NEXTSTEPS §1, tier 1)

Support bridges (stage M1) for the 15-check `move` ladder and its
Mover-job install: descriptor-word reads, the two capability selectors,
perm/range bit bridges, and the failing-`move` `Inert` constructor.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

/-! ## Descriptor-word reads -/

/-- The `i`-th descriptor word is a raw memory read at `rs1[11:0] + i`. -/
theorem moveW_eval (σ : Loom.Hw.St) (E : DomainId) (i : Nat) :
    (Hw.moveW E i).eval σ
      = σ.mems "mem" ((((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
          + BitVec.ofNat 12 i)).toNat 32 := rfl

/-- One-bit extract against `1#1` is the bit test. -/
theorem extract1_eq_one_iff {n : Nat} (a : BitVec n) (i : Nat) :
    (a.extractLsb' i 1 = 1#1) ↔ (a.getLsbD i = true) := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec 1 => v.getLsbD 0) h
    simpa [BitVec.getLsbD_extractLsb'] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k
    simpa [BitVec.getLsbD_extractLsb'] using h

/-! ## Perm-bit bridges (`decPerms` layout) -/

theorem decPerms_r (b : BitVec 3) : (Hw.decPerms b).r = b.getLsbD 0 := rfl
theorem decPerms_w (b : BitVec 3) : (Hw.decPerms b).w = b.getLsbD 1 := rfl

/-- `kR` reads the permission `r` bit of the packed kind word. -/
theorem kR_eval_iff (σ : Loom.Hw.St) (kw : Expr 32) (KW : BitVec 32)
    (hkw : kw.eval σ = KW) :
    ((Hw.kR kw).eval σ = 1#1)
      ↔ ((Hw.decPerms (KW.extractLsb' 26 3)).r = true) := by
  show (((kw.eval σ)).extractLsb' 26 1 = 1#1) ↔ _
  rw [hkw, decPerms_r, BitVec.getLsbD_extractLsb']
  simp [extract1_eq_one_iff]

/-- `kW` reads the permission `w` bit of the packed kind word. -/
theorem kW_eval_iff (σ : Loom.Hw.St) (kw : Expr 32) (KW : BitVec 32)
    (hkw : kw.eval σ = KW) :
    ((Hw.kW kw).eval σ = 1#1)
      ↔ ((Hw.decPerms (KW.extractLsb' 26 3)).w = true) := by
  show (((kw.eval σ)).extractLsb' 27 1 = 1#1) ↔ _
  rw [hkw, decPerms_w, BitVec.getLsbD_extractLsb']
  simp [extract1_eq_one_iff]

/-! ## The failing-`move` `Inert` constructor -/

/-- A retiring `move` whose check ladder failed keeps the Mover trees
quiescent: no kill op is latched, and `newJobSet` needs `ok`. -/
theorem Inert.of_move_fail (σ : Loom.Hw.St)
    (hkill : ∀ mn ∈ ["cap_drop", "cap_revoke", "gate_call", "gate_return"],
      (Hw.isMn mn).eval σ ≠ 1#1)
    (E : DomainId)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hok0 : ((Hw.moveJob E).ok).eval σ ≠ 1#1) : Inert σ where
  killed dm sl := by
    have hz : ∀ (mn : String) (Y : Expr 1),
        mn ∈ ["cap_drop", "cap_revoke", "gate_call", "gate_return"] →
        ¬(Expr.and (Hw.isMn mn) Y).eval σ = 1#1 := by
      intro mn Y hmn hc
      have hc' : (Hw.isMn mn).eval σ &&& Y.eval σ = 1#1 := hc
      rw [bv1_ne_one.mp (hkill mn hmn)] at hc'
      exact absurd (by
        rw [show (0#1 : BitVec 1) &&& Y.eval σ = 0#1 from by
          generalize Y.eval σ = b
          revert b
          decide] at hc'
        exact hc') (by decide)
    apply bv1_ne_one.mp
    intro hc
    have h2 := (andAll_eval σ _).mp
      (show (Hw.andAll [Hw.retiringE,
        Hw.orAll ((List.finRange numDomains).map fun d =>
          Expr.and (Hw.ifDomIs d) (Hw.orAll
            [ .and (Hw.isMn "cap_drop")
                (.and (Hw.dropOkE d) (Hw.dropKilled d dm sl)),
              .and (Hw.isMn "cap_revoke")
                (.and (Hw.revOkE d) (Hw.revKilled dm sl)),
              .and (Hw.isMn "gate_call")
                (.and (Hw.callOkE d) (Hw.callKilled d dm sl)),
              .and (Hw.isMn "gate_return")
                (.and (Hw.retOkE d) (Hw.retKilled d dm sl)) ]))]).eval σ
        = 1#1 from hc)
    have hor := h2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain ⟨e, hmem, he⟩ := (orAll_eval σ _).mp hor
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hmem
    have hand : (Hw.ifDomIs d).eval σ &&& (Hw.orAll
        [ .and (Hw.isMn "cap_drop")
            (.and (Hw.dropOkE d) (Hw.dropKilled d dm sl)),
          .and (Hw.isMn "cap_revoke")
            (.and (Hw.revOkE d) (Hw.revKilled dm sl)),
          .and (Hw.isMn "gate_call")
            (.and (Hw.callOkE d) (Hw.callKilled d dm sl)),
          .and (Hw.isMn "gate_return")
            (.and (Hw.retOkE d) (Hw.retKilled d dm sl)) ]).eval σ
        = 1#1 := he
    have hone : (Hw.orAll
        [ .and (Hw.isMn "cap_drop")
            (.and (Hw.dropOkE d) (Hw.dropKilled d dm sl)),
          .and (Hw.isMn "cap_revoke")
            (.and (Hw.revOkE d) (Hw.revKilled dm sl)),
          .and (Hw.isMn "gate_call")
            (.and (Hw.callOkE d) (Hw.callKilled d dm sl)),
          .and (Hw.isMn "gate_return")
            (.and (Hw.retOkE d) (Hw.retKilled d dm sl)) ]).eval σ = 1#1 := by
      by_cases hi : (Hw.ifDomIs d).eval σ = 1#1
      · rw [hi] at hand
        rw [show (1#1 : BitVec 1) &&& (Hw.orAll _).eval σ
            = (Hw.orAll _).eval σ from by
          generalize (Hw.orAll _).eval σ = b
          revert b
          decide] at hand
        exact hand
      · rw [bv1_ne_one.mp hi] at hand
        exact absurd (by
          rw [show (0#1 : BitVec 1) &&& (Hw.orAll _).eval σ = 0#1 from by
            generalize (Hw.orAll _).eval σ = b
            revert b
            decide] at hand
          exact hand) (by decide)
    obtain ⟨e2, hmem2, he2⟩ := (orAll_eval σ _).mp hone
    rcases hmem2 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, h⟩⟩⟩⟩
    · exact hz "cap_drop" _ (by decide) he2
    · exact hz "cap_revoke" _ (by decide) he2
    · exact hz "gate_call" _ (by decide) he2
    · exact hz "gate_return" _ (by decide) he2
    · exact absurd h (List.not_mem_nil)
  newJob d := by
    by_cases hd : d = E
    · subst hd
      exact andAll_zero_of_mem σ
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) hok0
    · exact andAll_zero_of_mem σ
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (hifexcl d hd)

end Machines.Lnp64u.Theorems.RMC
