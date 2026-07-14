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

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

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

/-- The kill trees are off whenever no kill op is latched. -/
theorem killedByCore_of_nokill (σ : Loom.Hw.St)
    (hkill : ∀ mn ∈ ["cap_drop", "cap_revoke", "gate_call", "gate_return"],
      (Hw.isMn mn).eval σ ≠ 1#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = 0#1 := by
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

/-- A retiring `move` whose check ladder failed keeps the Mover trees
quiescent: no kill op is latched, and `newJobSet` needs `ok`. -/
theorem Inert.of_move_fail (σ : Loom.Hw.St)
    (hkill : ∀ mn ∈ ["cap_drop", "cap_revoke", "gate_call", "gate_return"],
      (Hw.isMn mn).eval σ ≠ 1#1)
    (E : DomainId)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hok0 : ((Hw.moveJob E).ok).eval σ ≠ 1#1) : Inert σ where
  killed dm sl := killedByCore_of_nokill σ hkill dm sl
  newJob d := by
    by_cases hd : d = E
    · subst hd
      exact andAll_zero_of_mem σ
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) hok0
    · exact andAll_zero_of_mem σ
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (hifexcl d hd)



/-! ## Stage M3: the install faces -/

/-- `postJ` under a fired `move` in domain `E`: the new job's field. -/
theorem postJ_install {w : Nat} (σ : Loom.Hw.St) (E : DomainId)
    (h1 : (Hw.newJobSet E).eval σ = 1#1)
    (h0 : ∀ d : DomainId, d ≠ E → (Hw.newJobSet d).eval σ = 0#1)
    (f : DomainId → Expr w) (cur : Expr w) :
    (Hw.postJ f cur).eval σ = (f E).eval σ := by
  show (if (Hw.newJobSet 0).eval σ = 1#1 then (f 0).eval σ
    else if (Hw.newJobSet 1).eval σ = 1#1 then (f 1).eval σ
    else if (Hw.newJobSet 2).eval σ = 1#1 then (f 2).eval σ
    else if (Hw.newJobSet 3).eval σ = 1#1 then (f 3).eval σ
    else cur.eval σ) = _
  by_cases hE0 : (0 : DomainId) = E
  · subst hE0
    rw [if_pos h1]
  rw [if_neg (show ¬((Hw.newJobSet 0).eval σ = 1#1) from by
    rw [h0 0 hE0]
    decide)]
  by_cases hE1 : (1 : DomainId) = E
  · subst hE1
    rw [if_pos h1]
  rw [if_neg (show ¬((Hw.newJobSet 1).eval σ = 1#1) from by
    rw [h0 1 hE1]
    decide)]
  by_cases hE2 : (2 : DomainId) = E
  · subst hE2
    rw [if_pos h1]
  rw [if_neg (show ¬((Hw.newJobSet 2).eval σ = 1#1) from by
    rw [h0 2 hE2]
    decide)]
  have hE3 : (3 : DomainId) = E := by
    apply Fin.ext
    show 3 = E.val
    have hlt : E.val < 4 := E.isLt
    have v0 : E.val ≠ 0 := fun h => hE0 (Fin.ext h.symm)
    have v1 : E.val ≠ 1 := fun h => hE1 (Fin.ext h.symm)
    have v2 : E.val ≠ 2 := fun h => hE2 (Fin.ext h.symm)
    omega
  subst hE3
  rw [if_pos h1]

/-- The selector's packed backing ref is `encRef` of the handle fields. -/
theorem encRefE_sel_eval (σ : Loom.Hw.St) (E : DomainId) (hwE : Expr 32) :
    (Hw.encRefE (Hw.dLit E) (Hw.capSel E hwE).slot
      (Hw.capSel E hwE).gen).eval σ
    = Hw.encRef ⟨E, finOfBv (by decide) ((hwE.eval σ).extractLsb' 0 4),
        (hwE.eval σ).extractLsb' 4 8⟩ := by
  show (((hwE.eval σ).extractLsb' 4 8).setWidth 14 |||
    ((((hwE.eval σ).extractLsb' 0 4).setWidth 14 <<< (8#14).toNat) |||
      (((BitVec.ofNat 2 E.val).setWidth 14) <<< (12#14).toNat))) = _
  have hSv : BitVec.ofNat 14 (finOfBv (by decide : 2 ^ 4 = numSlots)
      ((hwE.eval σ).extractLsb' 0 4)).val
      = ((hwE.eval σ).extractLsb' 0 4).setWidth 14 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    rfl
  have hEv : BitVec.ofNat 14 E.val
      = (BitVec.ofNat 2 E.val).setWidth 14 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := E.isLt
    rw [Nat.mod_eq_of_lt (by omega : E.val < 2 ^ 2)]
  show _ = ((hwE.eval σ).extractLsb' 4 8).setWidth 14 |||
    (BitVec.ofNat 14 (finOfBv (by decide : 2 ^ 4 = numSlots)
      ((hwE.eval σ).extractLsb' 0 4)).val <<< 8) |||
    (BitVec.ofNat 14 E.val <<< 12)
  rw [hSv, hEv, BitVec.or_assoc]
  rfl

/-- `dLit` round-trips through `finOfBv`. -/
theorem finOfBv_dLit (E : DomainId) :
    finOfBv (by decide : 2 ^ 2 = numDomains) (BitVec.ofNat 2 E.val)
      = E := by
  apply Fin.ext
  show (BitVec.ofNat 2 E.val).toNat = E.val
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := E.isLt; omega)

/-- Low extract of a wide word is `setWidth`. -/
theorem extract0_eq_setWidth (x : BitVec 32) (k : Nat) :
    x.extractLsb' 0 k = x.setWidth k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

set_option maxHeartbeats 25600000 in
/-- The retiring-`move` install square glue: `square_retire_rgnop` with
the two Mover faces routed through the value-parameterized run bridges
(the seven fields carry the freshly-programmed job). -/
theorem square_retire_movejob (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = 0#1)
    (VSRC VDST : BitVec 14) (VOW : BitVec 2) (VSC VDC VSA : BitVec 12)
    (VREM : BitVec 13)
    (hjobV : (Expr.or (Hw.orAll ((List.finRange numDomains).map
        Hw.newJobSet))
      (.and (.reg 1 "mov_v")
        (.not (.and (.reg 1 "mov_v")
          (.or (Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot)
               (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot)))))).eval σ
      = 1#1)
    (hSRCe : (Hw.postJ (fun d => (Hw.moveJob d).srcEnc)
      (Expr.reg 14 "mov_src")).eval σ = VSRC)
    (hDSTe : (Hw.postJ (fun d => (Hw.moveJob d).dstEnc)
      (Expr.reg 14 "mov_dst")).eval σ = VDST)
    (hOWe : (Hw.postJ (fun d => Hw.dLit d)
      (Expr.reg 2 "mov_owner")).eval σ = VOW)
    (hSCe : (Hw.postJ (fun d => (Hw.moveJob d).srcCur)
      (Expr.reg 12 "mov_srccur")).eval σ = VSC)
    (hDCe : (Hw.postJ (fun d => (Hw.moveJob d).dstCur)
      (Expr.reg 12 "mov_dstcur")).eval σ = VDC)
    (hSAe : (Hw.postJ (fun d => (Hw.moveJob d).sa)
      (Expr.reg 12 "mov_status")).eval σ = VSA)
    (hREMe : (Hw.postJ (fun d => (Hw.moveJob d).rem)
      (Expr.reg 13 "mov_rem")).eval σ = VREM)
    (X : Act) (τ2 : MachineState)
    (hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w
        = ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
            ((Hw.refillAct m).run σ σ)).regs rn w)
    (hXifv : ("if_v", 1) ∉ X.regWrites)
    (hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2)
    (habsD : ∀ x, Hw.absDom ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
      ((Hw.refillAct m).run σ σ)) x = τ2.doms x)
    (habsG : ∀ g, Hw.absGate ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
      ((Hw.refillAct m).run σ σ)) g = τ2.gates g)
    (hcaps : ∀ x, (τ2.doms x).caps = ((Hw.abs σ).doms x).caps)
    (hgen : ∀ x, (τ2.doms x).slotGen = ((Hw.abs σ).doms x).slotGen)
    (hjs : τ2.mover = some
      { owner := finOfBv (by decide) VOW
        src := Hw.decRef VSRC
        dst := Hw.decRef VDST
        srcCur := VSC
        dstCur := VDC
        remaining := VREM.toNat
        statusAddr := VSA })
    (hauthτ2 : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
              Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true)
    (hmemτ2 : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = τ2.mem b)
    (hswτ2 : ∀ sc : Expr 12, Expr.eval σ
      (((List.finRange numDomains).foldr
        (fun d acc' =>
          Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
              Hw.domCoversE d
                (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                ⟨false, true, false⟩,
              .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
            (Hw.readReg d Hw.rs2E) acc')
        (.memRead 32 "mem" sc)))
      = τ2.mem (sc.eval σ))
    (hcyc : τ2.cycle = σ.regs "cycle" 32)
    (hτ2if : τ2.inflight = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  -- register frame down to the post-core accumulator
  have hp : ∀ (rn : String) (w : Nat),
      rn.startsWith "mov_" = false → ¬(rn = "cycle" ∧ w = 32) →
      ((Hw.core m).cycle σ).regs rn w
        = ((Hw.coreAct m).run σ σ1).regs rn w := by
    intro rn w h2 h4
    rw [core_cycle_unfold]
    rw [frame (show (rn, w) ∉ Hw.tickAct.regWrites from by
      intro hmem
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem
      exact h4 hmem)]
    rw [run_WritesPrefixed h2 w _ mover_prefixed]
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · -- cycle
    show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hspec, hcyc]
  · -- mem
    funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    rw [show (moverPhase (corePhase m τ1)).mem = (moverPhase τ2).mem from by
      rw [hspec]]
    exact moverAct_mem_run σ _ τ2 hkills
      (fun x => (hspec ▸ hcaps x : _)) (fun x => hspec ▸ hgen x)
      VSRC VDST VOW VSC VDC VSA VREM hjobV
      hSRCe hDSTe hOWe hSCe hDCe hSAe hREMe (hspec ▸ hjs)
      (fun ow sa => hspec ▸ hauthτ2 ow sa)
      hmemτ2 hswτ2 a
  · -- doms
    funext x
    have hRHS : (moverPhase (corePhase m τ1)).doms x = τ2.doms x := by
      rw [moverPhase_doms, hspec]
    show Hw.absDom ((Hw.core m).cycle σ) x = _
    rw [hRHS, ← habsD x]
    have hmovfree : ∀ q ∈ domReadNames x, q.1.startsWith "mov_" = false := by
      fin_cases x <;> decide +kernel
    have hcycfree : ∀ q ∈ domReadNames x, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases x <;> exact of_decide_eq_true rfl
    apply absDom_congr
    intro p hp'
    rw [← hcoreR p.1 p.2]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · -- gates
    funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g = τ2.gates g := by
      rw [moverPhase_gates, hspec]
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS, ← habsG g]
    have hmovfree : ∀ q ∈ gateReadNames g, q.1.startsWith "mov_" = false := by
      fin_cases g <;> decide +kernel
    have hcycfree : ∀ q ∈ gateReadNames g, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases g <;> exact of_decide_eq_true rfl
    apply absGate_congr
    intro p hp'
    rw [← hcoreR p.1 p.2]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · -- mover
    show Hw.absMover ((Hw.core m).cycle σ)
      = (moverPhase (corePhase m τ1)).mover
    rw [core_cycle_unfold]
    have htick : ∀ (rn : String) (w : Nat), ¬(rn = "cycle" ∧ w = 32) →
        (Hw.tickAct.run σ (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))).regs
          rn w = (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)).regs rn w := by
      intro rn w h4
      exact frame (by
        intro hmem
        simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
          Prod.mk.injEq] at hmem
        exact h4 hmem) σ _
    rw [show Hw.absMover (Hw.tickAct.run σ
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)))
        = Hw.absMover (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)) from by
      unfold Hw.absMover
      rw [htick "mov_v" 1 (by decide), htick "mov_owner" 2 (by decide),
        htick "mov_src" 14 (by decide), htick "mov_dst" 14 (by decide),
        htick "mov_srccur" 12 (by decide), htick "mov_dstcur" 12 (by decide),
        htick "mov_rem" 13 (by decide), htick "mov_status" 12 (by decide)]]
    rw [show (moverPhase (corePhase m τ1)).mover = (moverPhase τ2).mover
      from by rw [hspec]]
    exact absMover_moverAct_run σ _ τ2 hkills hcaps hgen
      VSRC VDST VOW VSC VDC VSA VREM hjobV
      hSRCe hDSTe hOWe hSCe hDCe hSAe hREMe hjs
  · -- inflight
    have hRHS : (moverPhase (corePhase m τ1)).inflight = none := by
      rw [moverPhase_inflight, hspec, hτ2if]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    rw [hp "if_v" 1 (by decide +kernel) (by decide), hcoreR "if_v" 1]
    rw [show ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ σ1).regs "if_v" 1
        = ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs "if_v" 1 from
      frame hXifv σ _]
    rw [show ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs "if_v" 1 = 0#1
      from by simp [Act.run, RegEnv.set, Expr.eval]]
    rw [if_neg (by decide)]

/-! ## The `move` arm: head + spec do-term (stage M2) -/

set_option maxHeartbeats 51200000 in
/-- The `move` retirement arm (opcode 24). -/
theorem square_retire_move (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hkc : KindCanon σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 24#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (24#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (24#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hmovemn : (Hw.isMn "move").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "move" = 24#6).symm
  have hret := retiringE_one σ hifv hcl
  have hkill : ∀ mn ∈ ["cap_drop", "cap_revoke", "gate_call",
      "gate_return"], (Hw.isMn mn).eval σ ≠ 1#1 := fun mn hmn =>
    isMn_ne_of_opc σ mn 24#6 hopc
      ((by decide +kernel : ∀ mn ∈ ["cap_drop", "cap_revoke", "gate_call",
        "gate_return"], (24#6 : BitVec 6) ≠ Hw.opcodeOf mn) mn hmn)
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 24#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 24#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 24#6 hopc (by decide +kernel))
  have hben5 : ∀ mn ∈ memMns, (Hw.isMn mn).eval σ ≠ 1#1 := fun mn hmn =>
    isMn_ne_of_opc σ mn 24#6 hopc
      ((by decide +kernel : ∀ mn ∈ memMns, (24#6 : BitVec 6)
        ≠ Hw.opcodeOf mn) mn hmn)
  have hselC := retireFor_sel_of_opc σ E "move" 24#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨Hw.ladder E (Hw.moveChecks E)
      (.seq (Hw.writeReg E Hw.rdE (.lit 0)) (Hw.pcAdvA E)),
      .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ)
      = refillPhase m (Hw.abs σ) := abs_refill m hwf hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y
    rw [← habs1]
    rfl
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  set AW := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hAW
  have hSPr : ∀ rs : RegId,
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg rs
        = ((Hw.abs σ).doms E).reg rs := fun rs => specReg_bridge m σ E rs
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ))
      = retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hDO : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (match ((SpecM.get >>= fun σ0 =>
          SpecM.require σ0.mover.isNone .moverBusy >>= fun _ =>
          SpecM.reg E (operandsOf W).rs1 >>= fun aw =>
          SpecM.load E (aw.setWidth 12) >>= fun srcH =>
          SpecM.load E (aw.setWidth 12 + 1) >>= fun dstH =>
          SpecM.load E (aw.setWidth 12 + 2) >>= fun lenW =>
          SpecM.load E (aw.setWidth 12 + 3) >>= fun stW =>
          Machines.Lnp64u.Isa.capLive E srcH >>= fun x =>
          match x with
          | (ss, gs_, es) =>
            Machines.Lnp64u.Isa.capLive E dstH >>= fun y =>
            match y with
            | (sd, gd, ed) =>
              match es.kind, ed.kind with
              | .mem sb sl sp, .mem db dl dp =>
                  SpecM.require sp.r .permDenied >>= fun _ =>
                  SpecM.require dp.w .permDenied >>= fun _ =>
                  SpecM.require (decide (lenW.toNat ≤ sl.toNat)
                      && decide (lenW.toNat ≤ dl.toNat))
                    .outOfRange >>= fun _ =>
                  SpecM.get >>= fun σq =>
                  SpecM.demand (σq.domCovers E (stW.setWidth 12) { r := false, w := true, x := false }) .memoryAuthority >>= fun _ =>
                  SpecM.set ({ σq with mover := some { owner := E, src := ⟨E, ss, gs_⟩, dst := ⟨E, sd, gd⟩, srcCur := sb, dstCur := db, remaining := lenW.toNat, statusAddr := stW.setWidth 12 } }) >>= fun _ =>
                  SpecM.setReg E (operandsOf W).rd 0
              | _, _ => SpecM.raise .badCap)
          (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))) with
        | .ok _ σ' => σ'
        | .err e σ' =>
            σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault fl => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E fl) := by
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl
  have hladder : ∀ acc : Loom.Hw.St, (Hw.retireFor E).run σ acc
      = (
          if (Expr.reg 1 "mov_v").eval σ = 1#1
          then (Hw.respA E (.err .moverBusy)).run σ acc
          else if (Expr.not (Hw.domCoversE E (.add (Hw.moveBase E) (.lit (BitVec.ofNat 12 0))) { r := true, w := false, x := false })).eval σ = 1#1
          then (Hw.respA E (.fault .memoryAuthority)).run σ acc
          else if (Expr.not (Hw.domCoversE E (.add (Hw.moveBase E) (.lit (BitVec.ofNat 12 1))) { r := true, w := false, x := false })).eval σ = 1#1
          then (Hw.respA E (.fault .memoryAuthority)).run σ acc
          else if (Expr.not (Hw.domCoversE E (.add (Hw.moveBase E) (.lit (BitVec.ofNat 12 2))) { r := true, w := false, x := false })).eval σ = 1#1
          then (Hw.respA E (.fault .memoryAuthority)).run σ acc
          else if (Expr.not (Hw.domCoversE E (.add (Hw.moveBase E) (.lit (BitVec.ofNat 12 3))) { r := true, w := false, x := false })).eval σ = 1#1
          then (Hw.respA E (.fault .memoryAuthority)).run σ acc
          else if (Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1
          then (Hw.respA E (.err .staleHandle)).run σ acc
          else if (Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1
          then (Hw.respA E (.err .badCap)).run σ acc
          else if (Expr.not (Hw.moveDstSel E).live).eval σ = 1#1
          then (Hw.respA E (.err .staleHandle)).run σ acc
          else if (Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1
          then (Hw.respA E (.err .badCap)).run σ acc
          else if (Expr.not (Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW) (Hw.kIsMem (Hw.moveDstSel E).kindW))).eval σ = 1#1
          then (Hw.respA E (.err .badCap)).run σ acc
          else if (Expr.not (Hw.kR (Hw.moveSrcSel E).kindW)).eval σ = 1#1
          then (Hw.respA E (.err .permDenied)).run σ acc
          else if (Expr.not (Hw.kW (Hw.moveDstSel E).kindW)).eval σ = 1#1
          then (Hw.respA E (.err .permDenied)).run σ acc
          else if (Expr.or (Expr.ult (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32) (Hw.moveW E 2)) (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32) (Hw.moveW E 2))).eval σ = 1#1
          then (Hw.respA E (.err .outOfRange)).run σ acc
          else if (Expr.not (Hw.domCoversE E (Hw.field (Hw.moveW E 3) 0 12) { r := false, w := true, x := false })).eval σ = 1#1
          then (Hw.respA E (.fault .memoryAuthority)).run σ acc
          else (Act.seq (Hw.writeReg E Hw.rdE (.lit 0)) (Hw.pcAdvA E)).run σ acc) := by
    intro acc
    rw [hselC acc]
    rfl
  have hrd : ∀ a : Addr, ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).read a = σ.mems "mem" a.toNat 32 :=
    fun a => rfl
  have hRD : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1 = AW :=
    hSPr (operandsOf W).rs1
  have hextAW : AW.extractLsb' 0 12 = AW.setWidth 12 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  have hmwE : ∀ i : Nat, (Hw.moveW E i).eval σ
      = σ.mems "mem" ((AW.setWidth 12 + BitVec.ofNat 12 i)).toNat 32 := by
    intro i
    rw [moveW_eval, hR1, hextAW]
  by_cases hbusy : σ.regs "mov_v" 1 = 1#1
  case pos =>
    -- Mover busy
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.reg 1 "mov_v" : Expr 1), (Resp.err .moverBusy)),
          List.mem_cons_self .., rfl⟩)
      have h2 : ~~~(σ.regs "mov_v" 1) = 1#1 := h1
      rw [hbusy] at h2
      exact absurd h2 (by decide))
    have hm1 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).mover = some
        { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
          src := Hw.decRef (σ.regs "mov_src" 14)
          dst := Hw.decRef (σ.regs "mov_dst" 14)
          srcCur := σ.regs "mov_srccur" 12
          dstCur := σ.regs "mov_dstcur" 12
          remaining := (σ.regs "mov_rem" 13).toNat
          statusAddr := σ.regs "mov_status" 12 } := by
      show Hw.absMover σ = _
      exact absMover_some σ hbusy
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.moverBusy.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_pos (show (Expr.reg 1 "mov_v").eval σ = 1#1 from hbusy)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hm1]
      rfl
  case neg =>
  have hmovN : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).mover = none := by
    show Hw.absMover σ = _
    exact absMover_none σ hbusy
  by_cases hc0 : (Hw.domCoversE E (.add (Hw.moveBase E)
      (.lit (BitVec.ofNat 12 0)))
      { r := true, w := false, x := false }).eval σ = 1#1
  case neg =>
    -- read fault on descriptor word 0
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false }) : Expr 1),
          (Resp.fault .memoryAuthority)),
          List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩)
      have h2 : ~~~(~~~((Hw.domCoversE E (.add (Hw.moveBase E)
          (.lit (BitVec.ofNat 12 0)))
          { r := true, w := false, x := false }).eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hc0] at h2
      exact absurd h2 (by decide))
    have haddr0 : ((Expr.add (Hw.moveBase E)
        (Expr.lit (BitVec.ofNat 12 0))).eval σ) = AW.setWidth 12 := by
      show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
        + BitVec.ofNat 12 0 = _
      rw [hR1, hextAW]
      exact BitVec.add_zero _
    have hcovF : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (AW.setWidth 12)
        { r := true, w := false, x := false } = false := by
      rw [spec_covers_bridge]
      rw [← Bool.not_eq_true]
      intro hcv
      exact hc0 ((domCoversE_eval σ E _ _).mpr (by rw [haddr0]; exact hcv))
    refine square_retire_fault_of m hwf hfit σ hsync hifv hcl hin hswz
      hmapz hunmapz
      (fun ad => by
        rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
        exact refill_pres_mem m σ "mem" ad 32)
      E rfl .memoryAuthority ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_pos (show (Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1 from by
          show ~~~((Hw.domCoversE E _ _).eval σ) = 1#1
          rw [bv1_ne_one.mp hc0]
          decide)]
      rfl
    · rw [hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand, specM_pure]
      simp only [hRD, hcovF]
      rfl
  case pos =>
  have haddr0 : ((Expr.add (Hw.moveBase E)
      (Expr.lit (BitVec.ofNat 12 0))).eval σ) = AW.setWidth 12 := by
    show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
      + BitVec.ofNat 12 0 = _
    rw [hR1, hextAW]
    exact BitVec.add_zero _
  have hcovT0 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (AW.setWidth 12)
      { r := true, w := false, x := false } = true := by
    rw [spec_covers_bridge]
    exact haddr0 ▸ (domCoversE_eval σ E _ _).mp hc0
  by_cases hc1 : (Hw.domCoversE E (.add (Hw.moveBase E)
      (.lit (BitVec.ofNat 12 1)))
      { r := true, w := false, x := false }).eval σ = 1#1
  case neg =>
    -- read fault on descriptor word 1
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false }) : Expr 1),
          (Resp.fault .memoryAuthority)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl⟩)
      have h2 : ~~~(~~~((Hw.domCoversE E (.add (Hw.moveBase E)
          (.lit (BitVec.ofNat 12 1)))
          { r := true, w := false, x := false }).eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hc1] at h2
      exact absurd h2 (by decide))
    have haddr1X : ((Expr.add (Hw.moveBase E)
        (Expr.lit (BitVec.ofNat 12 1))).eval σ) = AW.setWidth 12 + 1 := by
      show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
        + BitVec.ofNat 12 1 = _
      rw [hR1, hextAW]
      rfl
    have hcovF : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (AW.setWidth 12 + 1)
        { r := true, w := false, x := false } = false := by
      rw [spec_covers_bridge]
      rw [← Bool.not_eq_true]
      intro hcv
      exact hc1 ((domCoversE_eval σ E _ _).mpr (by rw [haddr1X]; exact hcv))
    refine square_retire_fault_of m hwf hfit σ hsync hifv hcl hin hswz
      hmapz hunmapz
      (fun ad => by
        rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
        exact refill_pres_mem m σ "mem" ad 32)
      E rfl .memoryAuthority ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_pos (show (Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1 from by
          show ~~~((Hw.domCoversE E _ _).eval σ) = 1#1
          rw [bv1_ne_one.mp hc1]
          decide)]
      rfl
    · rw [hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand, specM_pure]
      simp only [hRD, hcovT0, hcovF, reduceIte]
      rfl
  case pos =>
  have haddr1 : ((Expr.add (Hw.moveBase E)
      (Expr.lit (BitVec.ofNat 12 1))).eval σ) = AW.setWidth 12 + 1 := by
    show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
      + BitVec.ofNat 12 1 = _
    rw [hR1, hextAW]
    rfl
  have hcovT1 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (AW.setWidth 12 + 1)
      { r := true, w := false, x := false } = true := by
    rw [spec_covers_bridge]
    exact haddr1 ▸ (domCoversE_eval σ E _ _).mp hc1
  by_cases hc2 : (Hw.domCoversE E (.add (Hw.moveBase E)
      (.lit (BitVec.ofNat 12 2)))
      { r := true, w := false, x := false }).eval σ = 1#1
  case neg =>
    -- read fault on descriptor word 2
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false }) : Expr 1),
          (Resp.fault .memoryAuthority)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), rfl⟩)
      have h2 : ~~~(~~~((Hw.domCoversE E (.add (Hw.moveBase E)
          (.lit (BitVec.ofNat 12 2)))
          { r := true, w := false, x := false }).eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hc2] at h2
      exact absurd h2 (by decide))
    have haddr2X : ((Expr.add (Hw.moveBase E)
        (Expr.lit (BitVec.ofNat 12 2))).eval σ) = AW.setWidth 12 + 2 := by
      show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
        + BitVec.ofNat 12 2 = _
      rw [hR1, hextAW]
      rfl
    have hcovF : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (AW.setWidth 12 + 2)
        { r := true, w := false, x := false } = false := by
      rw [spec_covers_bridge]
      rw [← Bool.not_eq_true]
      intro hcv
      exact hc2 ((domCoversE_eval σ E _ _).mpr (by rw [haddr2X]; exact hcv))
    refine square_retire_fault_of m hwf hfit σ hsync hifv hcl hin hswz
      hmapz hunmapz
      (fun ad => by
        rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
        exact refill_pres_mem m σ "mem" ad 32)
      E rfl .memoryAuthority ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_pos (show (Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1 from by
          show ~~~((Hw.domCoversE E _ _).eval σ) = 1#1
          rw [bv1_ne_one.mp hc2]
          decide)]
      rfl
    · rw [hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovF, reduceIte]
      rfl
  case pos =>
  have haddr2 : ((Expr.add (Hw.moveBase E)
      (Expr.lit (BitVec.ofNat 12 2))).eval σ) = AW.setWidth 12 + 2 := by
    show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
      + BitVec.ofNat 12 2 = _
    rw [hR1, hextAW]
    rfl
  have hcovT2 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (AW.setWidth 12 + 2)
      { r := true, w := false, x := false } = true := by
    rw [spec_covers_bridge]
    exact haddr2 ▸ (domCoversE_eval σ E _ _).mp hc2
  by_cases hc3 : (Hw.domCoversE E (.add (Hw.moveBase E)
      (.lit (BitVec.ofNat 12 3)))
      { r := true, w := false, x := false }).eval σ = 1#1
  case neg =>
    -- read fault on descriptor word 3
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false }) : Expr 1),
          (Resp.fault .memoryAuthority)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), rfl⟩)
      have h2 : ~~~(~~~((Hw.domCoversE E (.add (Hw.moveBase E)
          (.lit (BitVec.ofNat 12 3)))
          { r := true, w := false, x := false }).eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hc3] at h2
      exact absurd h2 (by decide))
    have haddr3X : ((Expr.add (Hw.moveBase E)
        (Expr.lit (BitVec.ofNat 12 3))).eval σ) = AW.setWidth 12 + 3 := by
      show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
        + BitVec.ofNat 12 3 = _
      rw [hR1, hextAW]
      rfl
    have hcovF : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (AW.setWidth 12 + 3)
        { r := true, w := false, x := false } = false := by
      rw [spec_covers_bridge]
      rw [← Bool.not_eq_true]
      intro hcv
      exact hc3 ((domCoversE_eval σ E _ _).mpr (by rw [haddr3X]; exact hcv))
    refine square_retire_fault_of m hwf hfit σ hsync hifv hcl hin hswz
      hmapz hunmapz
      (fun ad => by
        rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
        exact refill_pres_mem m σ "mem" ad 32)
      E rfl .memoryAuthority ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_pos (show (Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1 from by
          show ~~~((Hw.domCoversE E _ _).eval σ) = 1#1
          rw [bv1_ne_one.mp hc3]
          decide)]
      rfl
    · rw [hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovF, reduceIte]
      rfl
  case pos =>
  have haddr3 : ((Expr.add (Hw.moveBase E)
      (Expr.lit (BitVec.ofNat 12 3))).eval σ) = AW.setWidth 12 + 3 := by
    show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 12
      + BitVec.ofNat 12 3 = _
    rw [hR1, hextAW]
    rfl
  have hcovT3 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (AW.setWidth 12 + 3)
      { r := true, w := false, x := false } = true := by
    rw [spec_covers_bridge]
    exact haddr3 ▸ (domCoversE_eval σ E _ _).mp hc3
  -- descriptor words and the two selectors
  have hmw0 : (Hw.moveW E 0).eval σ = (σ.mems "mem" (AW.setWidth 12).toNat 32) := by
    rw [hmwE 0]
    rw [show AW.setWidth 12 + BitVec.ofNat 12 0 = AW.setWidth 12 from
      BitVec.add_zero _]
  have hmw1 : (Hw.moveW E 1).eval σ = (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32) := hmwE 1
  have hSsval : (finOfBv (by decide : 2 ^ 4 = numSlots)
      ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4)).val
      = (((Hw.moveW E 0).eval σ).extractLsb' 0 4).toNat := by
    rw [hmw0]
    rfl
  have hSdval : (finOfBv (by decide : 2 ^ 4 = numSlots)
      ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4)).val
      = (((Hw.moveW E 1).eval σ).extractLsb' 0 4).toNat := by
    rw [hmw1]
    rfl
  have hlivSiff := capSel_live_eval σ E (Hw.moveW E 0) _ hSsval
  have hlivDiff := capSel_live_eval σ E (Hw.moveW E 1) _ hSdval
  rw [hmw0] at hlivSiff
  rw [hmw1] at hlivDiff
  have hkwS : (Hw.moveSrcSel E).kindW.eval σ
      = σ.regs (Hw.dcapKind E (finOfBv (by decide)
          ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32 :=
    capSel_kindW_eval σ E (Hw.moveW E 0) _ hSsval
  have hkwD : (Hw.moveDstSel E).kindW.eval σ
      = σ.regs (Hw.dcapKind E (finOfBv (by decide)
          ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32 :=
    capSel_kindW_eval σ E (Hw.moveW E 1) _ hSdval
  have hrd0 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).read (AW.setWidth 12) = (σ.mems "mem" (AW.setWidth 12).toNat 32) := hrd _
  have hrd1 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).read (AW.setWidth 12 + 1) = (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32) := hrd _
  by_cases hlvS : σ.regs (Hw.dcapV E (finOfBv (by decide)
        ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 1 = 1#1
      ∧ σ.regs (Hw.dgen E (finOfBv (by decide)
        ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 8 = (σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 4 8
      ∧ (σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 4 8 ≠ 0
  case neg =>
    -- source handle stale
    have hlive0S : ¬((Hw.moveSrcSel E).live.eval σ = 1#1) :=
      fun hcc => hlvS (hlivSiff.mp hcc)
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.moveSrcSel E).live : Expr 1),
          (Resp.err .staleHandle)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..))))), rfl⟩)
      have h2 : ~~~(~~~((Hw.moveSrcSel E).live.eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hlive0S] at h2
      exact absurd h2 (by decide))
    have hlcNS : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).liveCap
        (Handle.decode (σ.mems "mem" (AW.setWidth 12).toNat 32)).slot (Handle.decode (σ.mems "mem" (AW.setWidth 12).toNat 32)).gen = none := by
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_neg hlvS
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.staleHandle.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_pos (show (Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1 from by
          show ~~~((Hw.moveSrcSel E).live.eval σ) = 1#1
          rw [bv1_ne_one.mp hlive0S]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcNS]
      rfl
  case pos =>
  -- source selector passes liveness
  have hliv1S : (Hw.moveSrcSel E).live.eval σ = 1#1 := hlivSiff.mpr hlvS
  have hlcSS : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).liveCap
      (Handle.decode (σ.mems "mem" (AW.setWidth 12).toNat 32)).slot (Handle.decode (σ.mems "mem" (AW.setWidth 12).toNat 32)).gen
      = some { kind := Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32)
               lineage := if σ.regs (Hw.dcapLinV E (finOfBv (by decide)
                   ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 1 = 1#1
                 then some (finOfBv (by decide)
                   (σ.regs (Hw.dcapLin E (finOfBv (by decide)
                     ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 4))
                 else none } := by
    rw [specLiveCap_bridge, abs_liveCap]
    exact if_pos hlvS
  obtain ⟨ceS, hlcSS', hcekS⟩ :
      ∃ ce : CapEntry, (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).liveCap
        (Handle.decode (σ.mems "mem" (AW.setWidth 12).toNat 32)).slot (Handle.decode (σ.mems "mem" (AW.setWidth 12).toNat 32)).gen = some ce
      ∧ ce.kind = Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) := ⟨_, hlcSS, rfl⟩
  have hclsES : (Hw.moveSrcSel E).clsOk.eval σ
      = (if (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = (σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 12 1
        then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.moveSrcSel E).kindW.eval σ).extractLsb' 0 1
        = ((Hw.moveW E 0).eval σ).extractLsb' 12 1
      then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwS, hmw0]
  by_cases hbitS : (σ.mems "mem" (AW.setWidth 12).toNat 32).getLsbD 12 = (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).getLsbD 0
  case neg =>
    -- source class mismatch
    have hcls0S : ¬((Hw.moveSrcSel E).clsOk.eval σ = 1#1) := by
      rw [hclsES]
      intro h
      by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = (σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 12 1
      · exact hbitS ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) (σ.mems "mem" (AW.setWidth 12).toNat 32) 0 12).mp hcx).symm
      · rw [if_neg hcx] at h
        exact absurd h (by decide)
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.moveSrcSel E).clsOk : Expr 1),
          (Resp.err .badCap)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_self ..)))))), rfl⟩)
      have h2 : ~~~(~~~((Hw.moveSrcSel E).clsOk.eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hcls0S] at h2
      exact absurd h2 (by decide))
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1)
            from by
          show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
          rw [hliv1S]
          decide),
        if_pos (show (Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1 from by
          show ~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1
          rw [bv1_ne_one.mp hcls0S]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcSS', hcekS]
      rw [show (decide ((Handle.decode (σ.mems "mem" (AW.setWidth 12).toNat 32)).cls
          = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32)).cls)) = false from decide_eq_false
        (fun hA => hbitS ((cls_eq_iff_bits (σ.mems "mem" (AW.setWidth 12).toNat 32) (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32)).mp hA))]
      rfl
  case pos =>
  -- source class agrees
  have hcls1S : (Hw.moveSrcSel E).clsOk.eval σ = 1#1 := by
    rw [hclsES]
    rw [if_pos ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) (σ.mems "mem" (AW.setWidth 12).toNat 32) 0 12).mpr hbitS.symm)]
  have hdecS : (decide ((Handle.decode (σ.mems "mem" (AW.setWidth 12).toNat 32)).cls
      = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32)).cls)) = true :=
    decide_eq_true ((cls_eq_iff_bits (σ.mems "mem" (AW.setWidth 12).toNat 32) (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32)).mpr hbitS)
  by_cases hlvD : σ.regs (Hw.dcapV E (finOfBv (by decide)
        ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 1 = 1#1
      ∧ σ.regs (Hw.dgen E (finOfBv (by decide)
        ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 8 = (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 4 8
      ∧ (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 4 8 ≠ 0
  case neg =>
    -- destination handle stale
    have hlive0D : ¬((Hw.moveDstSel E).live.eval σ = 1#1) :=
      fun hcc => hlvD (hlivDiff.mp hcc)
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.moveDstSel E).live : Expr 1),
          (Resp.err .staleHandle)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))),
          rfl⟩)
      have h2 : ~~~(~~~((Hw.moveDstSel E).live.eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hlive0D] at h2
      exact absurd h2 (by decide))
    have hlcND : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).liveCap
        (Handle.decode (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32)).slot (Handle.decode (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32)).gen = none := by
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_neg hlvD
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.staleHandle.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1)
            from by
          show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
          rw [hliv1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1)
            from by
          show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
          rw [hcls1S]
          decide),
        if_pos (show (Expr.not (Hw.moveDstSel E).live).eval σ = 1#1 from by
          show ~~~((Hw.moveDstSel E).live.eval σ) = 1#1
          rw [bv1_ne_one.mp hlive0D]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcSS', hcekS]
      rw [hdecS]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hlcND]
      rfl
  case pos =>
  -- destination selector passes liveness
  have hliv1D : (Hw.moveDstSel E).live.eval σ = 1#1 := hlivDiff.mpr hlvD
  have hlcSD : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).liveCap
      (Handle.decode (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32)).slot (Handle.decode (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32)).gen
      = some { kind := Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32)
               lineage := if σ.regs (Hw.dcapLinV E (finOfBv (by decide)
                   ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 1 = 1#1
                 then some (finOfBv (by decide)
                   (σ.regs (Hw.dcapLin E (finOfBv (by decide)
                     ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 4))
                 else none } := by
    rw [specLiveCap_bridge, abs_liveCap]
    exact if_pos hlvD
  obtain ⟨ceD, hlcSD', hcekD⟩ :
      ∃ ce : CapEntry, (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).liveCap
        (Handle.decode (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32)).slot (Handle.decode (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32)).gen = some ce
      ∧ ce.kind = Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) := ⟨_, hlcSD, rfl⟩
  have hclsED : (Hw.moveDstSel E).clsOk.eval σ
      = (if (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 12 1
        then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.moveDstSel E).kindW.eval σ).extractLsb' 0 1
        = ((Hw.moveW E 1).eval σ).extractLsb' 12 1
      then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwD, hmw1]
  by_cases hbitD : (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).getLsbD 12 = (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).getLsbD 0
  case neg =>
    -- destination class mismatch
    have hcls0D : ¬((Hw.moveDstSel E).clsOk.eval σ = 1#1) := by
      rw [hclsED]
      intro h
      by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 12 1
      · exact hbitD ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32) 0 12).mp hcx).symm
      · rw [if_neg hcx] at h
        exact absurd h (by decide)
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.moveDstSel E).clsOk : Expr 1),
          (Resp.err .badCap)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_self ..)))))))), rfl⟩)
      have h2 : ~~~(~~~((Hw.moveDstSel E).clsOk.eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hcls0D] at h2
      exact absurd h2 (by decide))
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1)
            from by
          show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
          rw [hliv1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1)
            from by
          show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
          rw [hcls1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).live).eval σ = 1#1)
            from by
          show ¬(~~~((Hw.moveDstSel E).live.eval σ) = 1#1)
          rw [hliv1D]
          decide),
        if_pos (show (Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1 from by
          show ~~~((Hw.moveDstSel E).clsOk.eval σ) = 1#1
          rw [bv1_ne_one.mp hcls0D]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcSS', hcekS]
      rw [hdecS]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hlcSD', hcekD]
      rw [show (decide ((Handle.decode (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32)).cls
          = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32)).cls)) = false from decide_eq_false
        (fun hA => hbitD ((cls_eq_iff_bits (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32) (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32)).mp hA))]
      rfl
  case pos =>
  -- destination class agrees
  have hcls1D : (Hw.moveDstSel E).clsOk.eval σ = 1#1 := by
    rw [hclsED]
    rw [if_pos ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32) 0 12).mpr hbitD.symm)]
  have hdecD : (decide ((Handle.decode (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32)).cls
      = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32)).cls)) = true :=
    decide_eq_true ((cls_eq_iff_bits (σ.mems "mem" (AW.setWidth 12 + 1).toNat 32) (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32)).mpr hbitD)
  have hmemES : (Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ
      = (if (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = 0#1 then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.moveSrcSel E).kindW.eval σ).extractLsb' 0 1
        = (Expr.lit 0).eval σ then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwS]
    rfl
  have hmemED : (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ
      = (if (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = 0#1 then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.moveDstSel E).kindW.eval σ).extractLsb' 0 1
        = (Expr.lit 0).eval σ then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwD]
    rfl
  by_cases hmS : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).getLsbD 0 = false
  case neg =>
    by_cases hmD : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).getLsbD 0 = false
    case pos =>
      -- kind combo: src gate, dst mem
      have hgkS2 : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) = .gate (finOfBv (by decide)
          ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 1 2)) := by
        rw [Hw.decKind, if_pos (by
          cases hb : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).getLsbD 0
          · exact absurd hb hmS
          · rfl)]
      have hkm0S : ¬((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ = 1#1) := by
        rw [hmemES]
        intro h
        by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = 0#1
        · exact hmS ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) 0).mp hcx)
        · rw [if_neg hcx] at h
          exact absurd h (by decide)
      have hmkD2 : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) = .mem ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 1 12)
          ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13) (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 26 3)) :=
        (decKind_mem_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32)).mp hmD
      have hand0 : ¬((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
          (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ = 1#1) := by
        show ¬((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ &&&
          (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ = 1#1)
        rw [bv1_ne_one.mp hkm0S]
        generalize (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ = b
        revert b
        decide
      have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
        have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
          ⟨((Expr.not (Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
              (Hw.kIsMem (Hw.moveDstSel E).kindW)) : Expr 1),
            (Resp.err .badCap)),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))),
            rfl⟩)
        have h2 : ~~~(~~~((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ)) = 1#1 := h1
        rw [bv1_ne_one.mp hand0] at h2
        exact absurd h2 (by decide))
      refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
        hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
      · intro acc
        rw [hladder acc,
          if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
          if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
              (.lit (BitVec.ofNat 12 0)))
              { r := true, w := false, x := false })).eval σ = 1#1) from by
            show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
            rw [hc0]
            decide),
          if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
              (.lit (BitVec.ofNat 12 1)))
              { r := true, w := false, x := false })).eval σ = 1#1) from by
            show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
            rw [hc1]
            decide),
          if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
              (.lit (BitVec.ofNat 12 2)))
              { r := true, w := false, x := false })).eval σ = 1#1) from by
            show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
            rw [hc2]
            decide),
          if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
              (.lit (BitVec.ofNat 12 3)))
              { r := true, w := false, x := false })).eval σ = 1#1) from by
            show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
            rw [hc3]
            decide),
          if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1) from by
            show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
            rw [hliv1S]
            decide),
          if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1) from by
            show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
            rw [hcls1S]
            decide),
          if_neg (show ¬((Expr.not (Hw.moveDstSel E).live).eval σ = 1#1) from by
            show ¬(~~~((Hw.moveDstSel E).live.eval σ) = 1#1)
            rw [hliv1D]
            decide),
          if_neg (show ¬((Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1) from by
            show ¬(~~~((Hw.moveDstSel E).clsOk.eval σ) = 1#1)
            rw [hcls1D]
            decide),
          if_pos (show (Expr.not (Expr.and
              (Hw.kIsMem (Hw.moveSrcSel E).kindW)
              (Hw.kIsMem (Hw.moveDstSel E).kindW))).eval σ = 1#1 from by
            show ~~~((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
              (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ) = 1#1
            rw [bv1_ne_one.mp hand0]
            decide)]
        rfl
      · rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        rw [hmovN]
        simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
          SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
          specM_bind, specM_pure, hrd0, hrd1]
        simp only [hlcSS', hcekS]
        rw [hdecS]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [hlcSD', hcekD]
        rw [hdecD]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [hcekS, hcekD]
        rw [hgkS2, hmkD2]
        rfl
    case neg =>
      -- kind combo: src gate, dst gate
      have hgkS2 : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) = .gate (finOfBv (by decide)
          ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 1 2)) := by
        rw [Hw.decKind, if_pos (by
          cases hb : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).getLsbD 0
          · exact absurd hb hmS
          · rfl)]
      have hkm0S : ¬((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ = 1#1) := by
        rw [hmemES]
        intro h
        by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = 0#1
        · exact hmS ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) 0).mp hcx)
        · rw [if_neg hcx] at h
          exact absurd h (by decide)
      have hgkD2 : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) = .gate (finOfBv (by decide)
          ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 1 2)) := by
        rw [Hw.decKind, if_pos (by
          cases hb : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).getLsbD 0
          · exact absurd hb hmD
          · rfl)]
      have hkm0D : ¬((Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ = 1#1) := by
        rw [hmemED]
        intro h
        by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = 0#1
        · exact hmD ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) 0).mp hcx)
        · rw [if_neg hcx] at h
          exact absurd h (by decide)
      have hand0 : ¬((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
          (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ = 1#1) := by
        show ¬((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ &&&
          (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ = 1#1)
        rw [bv1_ne_one.mp hkm0S]
        generalize (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ = b
        revert b
        decide
      have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
        have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
          ⟨((Expr.not (Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
              (Hw.kIsMem (Hw.moveDstSel E).kindW)) : Expr 1),
            (Resp.err .badCap)),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))),
            rfl⟩)
        have h2 : ~~~(~~~((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ)) = 1#1 := h1
        rw [bv1_ne_one.mp hand0] at h2
        exact absurd h2 (by decide))
      refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
        hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
      · intro acc
        rw [hladder acc,
          if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
          if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
              (.lit (BitVec.ofNat 12 0)))
              { r := true, w := false, x := false })).eval σ = 1#1) from by
            show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
            rw [hc0]
            decide),
          if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
              (.lit (BitVec.ofNat 12 1)))
              { r := true, w := false, x := false })).eval σ = 1#1) from by
            show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
            rw [hc1]
            decide),
          if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
              (.lit (BitVec.ofNat 12 2)))
              { r := true, w := false, x := false })).eval σ = 1#1) from by
            show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
            rw [hc2]
            decide),
          if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
              (.lit (BitVec.ofNat 12 3)))
              { r := true, w := false, x := false })).eval σ = 1#1) from by
            show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
            rw [hc3]
            decide),
          if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1) from by
            show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
            rw [hliv1S]
            decide),
          if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1) from by
            show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
            rw [hcls1S]
            decide),
          if_neg (show ¬((Expr.not (Hw.moveDstSel E).live).eval σ = 1#1) from by
            show ¬(~~~((Hw.moveDstSel E).live.eval σ) = 1#1)
            rw [hliv1D]
            decide),
          if_neg (show ¬((Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1) from by
            show ¬(~~~((Hw.moveDstSel E).clsOk.eval σ) = 1#1)
            rw [hcls1D]
            decide),
          if_pos (show (Expr.not (Expr.and
              (Hw.kIsMem (Hw.moveSrcSel E).kindW)
              (Hw.kIsMem (Hw.moveDstSel E).kindW))).eval σ = 1#1 from by
            show ~~~((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
              (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ) = 1#1
            rw [bv1_ne_one.mp hand0]
            decide)]
        rfl
      · rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        rw [hmovN]
        simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
          SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
          specM_bind, specM_pure, hrd0, hrd1]
        simp only [hlcSS', hcekS]
        rw [hdecS]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [hlcSD', hcekD]
        rw [hdecD]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [hcekS, hcekD]
        rw [hgkS2, hgkD2]
        rfl
  case pos =>
  by_cases hmD : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).getLsbD 0 = false
  case neg =>
    -- kind combo: src mem, dst gate
    have hmkS2 : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) = .mem ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 1 12)
        ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13) (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 26 3)) :=
      (decKind_mem_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32)).mp hmS
    have hgkD2 : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) = .gate (finOfBv (by decide)
        ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 1 2)) := by
      rw [Hw.decKind, if_pos (by
        cases hb : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).getLsbD 0
        · exact absurd hb hmD
        · rfl)]
    have hkm0D : ¬((Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ = 1#1) := by
      rw [hmemED]
      intro h
      by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 0 1 = 0#1
      · exact hmD ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) 0).mp hcx)
      · rw [if_neg hcx] at h
        exact absurd h (by decide)
    have hand0 : ¬((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
        (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ = 1#1) := by
      show ¬((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ &&&
        (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ = 1#1)
      rw [bv1_ne_one.mp hkm0D]
      generalize (Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ = a
      revert a
      decide
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW)) : Expr 1),
          (Resp.err .badCap)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))),
          rfl⟩)
      have h2 : ~~~(~~~((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
          (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hand0] at h2
      exact absurd h2 (by decide))
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
          rw [hliv1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
          rw [hcls1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).live.eval σ) = 1#1)
          rw [hliv1D]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).clsOk.eval σ) = 1#1)
          rw [hcls1D]
          decide),
        if_pos (show (Expr.not (Expr.and
            (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW))).eval σ = 1#1 from by
          show ~~~((Expr.and (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW)).eval σ) = 1#1
          rw [bv1_ne_one.mp hand0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcSS', hcekS]
      rw [hdecS]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hlcSD', hcekD]
      rw [hdecD]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcekS, hcekD]
      rw [hmkS2, hgkD2]
      rfl
  case pos =>
  -- both kinds are memory
  have hmkS2 : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) = .mem ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 1 12)
      ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13) (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 26 3)) :=
    (decKind_mem_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32)).mp hmS
  have hmkD2 : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) = .mem ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 1 12)
      ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13) (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 26 3)) :=
    (decKind_mem_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32)).mp hmD
  have hkm1S : (Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ = 1#1 := by
    rw [hmemES]
    rw [if_pos ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) 0).mpr hmS)]
  have hkm1D : (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ = 1#1 := by
    rw [hmemED]
    rw [if_pos ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) 0).mpr hmD)]
  have hmw2 : (Hw.moveW E 2).eval σ = (σ.mems "mem" (AW.setWidth 12 + 2).toNat 32) := hmwE 2
  have hmw3 : (Hw.moveW E 3).eval σ = (σ.mems "mem" (AW.setWidth 12 + 3).toNat 32) := hmwE 3
  have hrd2 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).read (AW.setWidth 12 + 2) = (σ.mems "mem" (AW.setWidth 12 + 2).toNat 32) := hrd _
  have hrd3 : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).read (AW.setWidth 12 + 3) = (σ.mems "mem" (AW.setWidth 12 + 3).toNat 32) := hrd _
  by_cases hprS : (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 26 3)).r = true
  case neg =>
    -- source lacks read permission
    have hkr0 : ¬((Hw.kR (Hw.moveSrcSel E).kindW).eval σ = 1#1) :=
      fun h => hprS ((kR_eval_iff σ _ (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) hkwS).mp h)
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.kR (Hw.moveSrcSel E).kindW) : Expr 1), (Resp.err .permDenied)), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))), rfl⟩)
      have h2 : ~~~(~~~((Hw.kR (Hw.moveSrcSel E).kindW).eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hkr0] at h2
      exact absurd h2 (by decide))
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.permDenied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
          rw [hliv1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
          rw [hcls1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).live.eval σ) = 1#1)
          rw [hliv1D]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).clsOk.eval σ) = 1#1)
          rw [hcls1D]
          decide),
        if_neg (show ¬((Expr.not (Expr.and
            (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW))).eval σ = 1#1) from by
          show ¬(~~~((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ &&&
            (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ) = 1#1)
          rw [hkm1S, hkm1D]
          decide),
        if_pos (show (Expr.not (Hw.kR
            (Hw.moveSrcSel E).kindW)).eval σ = 1#1 from by
          show ~~~((Hw.kR (Hw.moveSrcSel E).kindW).eval σ) = 1#1
          rw [bv1_ne_one.mp hkr0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcSS', hcekS]
      rw [hdecS]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hlcSD', hcekD]
      rw [hdecD]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcekS, hcekD]
      simp only [hmkS2, hmkD2]
      rw [if_neg hprS]
      rfl
  case pos =>
  have hkr1 : (Hw.kR (Hw.moveSrcSel E).kindW).eval σ = 1#1 :=
    (kR_eval_iff σ _ (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32) hkwS).mpr hprS
  by_cases hpwD : (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 26 3)).w = true
  case neg =>
    -- destination lacks write permission
    have hkw0 : ¬((Hw.kW (Hw.moveDstSel E).kindW).eval σ = 1#1) :=
      fun h => hpwD ((kW_eval_iff σ _ (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) hkwD).mp h)
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.kW (Hw.moveDstSel E).kindW) : Expr 1), (Resp.err .permDenied)), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))), rfl⟩)
      have h2 : ~~~(~~~((Hw.kW (Hw.moveDstSel E).kindW).eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hkw0] at h2
      exact absurd h2 (by decide))
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.permDenied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
          rw [hliv1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
          rw [hcls1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).live.eval σ) = 1#1)
          rw [hliv1D]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).clsOk.eval σ) = 1#1)
          rw [hcls1D]
          decide),
        if_neg (show ¬((Expr.not (Expr.and
            (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW))).eval σ = 1#1) from by
          show ¬(~~~((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ &&&
            (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ) = 1#1)
          rw [hkm1S, hkm1D]
          decide),
        if_neg (show ¬((Expr.not (Hw.kR (Hw.moveSrcSel E).kindW)).eval σ = 1#1) from by
          show ¬(~~~((Hw.kR (Hw.moveSrcSel E).kindW).eval σ) = 1#1)
          rw [hkr1]
          decide),
        if_pos (show (Expr.not (Hw.kW
            (Hw.moveDstSel E).kindW)).eval σ = 1#1 from by
          show ~~~((Hw.kW (Hw.moveDstSel E).kindW).eval σ) = 1#1
          rw [bv1_ne_one.mp hkw0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcSS', hcekS]
      rw [hdecS]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hlcSD', hcekD]
      rw [hdecD]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcekS, hcekD]
      simp only [hmkS2, hmkD2]
      simp only [hprS, reduceIte, specM_bind, specM_pure]
      rw [if_neg hpwD]
      rfl
  case pos =>
  have hkw1 : (Hw.kW (Hw.moveDstSel E).kindW).eval σ = 1#1 :=
    (kW_eval_iff σ _ (σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32) hkwD).mpr hpwD
  by_cases hlen : ((σ.mems "mem" (AW.setWidth 12 + 2).toNat 32).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13).toNat
      ∧ (σ.mems "mem" (AW.setWidth 12 + 2).toNat 32).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)
  case neg =>
    -- word count exceeds a capability's length
    have hor1 : ((Expr.ult (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32)
          (Hw.moveW E 2)).eval σ |||
        (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32)
          (Hw.moveW E 2)).eval σ) = 1#1 := by
      rcases Decidable.not_and_iff_not_or_not.mp hlen with hA | hA
      · have hu : (Expr.ult (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32)
            (Hw.moveW E 2)).eval σ = 1#1 := by
          rw [ultE_eval]
          show ((((Hw.moveSrcSel E).kindW.eval σ).extractLsb' 13 13
            ).setWidth 32).toNat < ((Hw.moveW E 2).eval σ).toNat
          rw [hkwS, hmw2, toNat_setWidth_le (by omega)]
          exact Nat.lt_of_not_le hA
        rw [hu]
        generalize (Expr.ult (.zext (Hw.kLen
          (Hw.moveDstSel E).kindW) 32) (Hw.moveW E 2)).eval σ = b
        revert b
        decide
      · have hu : (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32)
            (Hw.moveW E 2)).eval σ = 1#1 := by
          rw [ultE_eval]
          show ((((Hw.moveDstSel E).kindW.eval σ).extractLsb' 13 13
            ).setWidth 32).toNat < ((Hw.moveW E 2).eval σ).toNat
          rw [hkwD, hmw2, toNat_setWidth_le (by omega)]
          exact Nat.lt_of_not_le hA
        rw [hu]
        generalize (Expr.ult (.zext (Hw.kLen
          (Hw.moveSrcSel E).kindW) 32) (Hw.moveW E 2)).eval σ = a
        revert a
        decide
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.or (Expr.ult (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32) (Hw.moveW E 2)) (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32) (Hw.moveW E 2)) : Expr 1), (Resp.err .outOfRange)), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))), rfl⟩)
      have h2 : ~~~(((Expr.ult (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32) (Hw.moveW E 2)).eval σ ||| (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32) (Hw.moveW E 2)).eval σ)) = 1#1 := h1
      rw [hor1] at h2
      exact absurd h2 (by decide))
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.outOfRange.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
          rw [hliv1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
          rw [hcls1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).live.eval σ) = 1#1)
          rw [hliv1D]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).clsOk.eval σ) = 1#1)
          rw [hcls1D]
          decide),
        if_neg (show ¬((Expr.not (Expr.and
            (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW))).eval σ = 1#1) from by
          show ¬(~~~((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ &&&
            (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ) = 1#1)
          rw [hkm1S, hkm1D]
          decide),
        if_neg (show ¬((Expr.not (Hw.kR (Hw.moveSrcSel E).kindW)).eval σ = 1#1) from by
          show ¬(~~~((Hw.kR (Hw.moveSrcSel E).kindW).eval σ) = 1#1)
          rw [hkr1]
          decide),
        if_neg (show ¬((Expr.not (Hw.kW (Hw.moveDstSel E).kindW)).eval σ = 1#1) from by
          show ¬(~~~((Hw.kW (Hw.moveDstSel E).kindW).eval σ) = 1#1)
          rw [hkw1]
          decide),
        if_pos (show (Expr.or (Expr.ult
            (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32) (Hw.moveW E 2))
            (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32)
              (Hw.moveW E 2))).eval σ = 1#1 from hor1)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcSS', hcekS]
      rw [hdecS]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hlcSD', hcekD]
      rw [hdecD]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcekS, hcekD]
      simp only [hmkS2, hmkD2]
      simp only [hprS, hpwD, reduceIte, specM_bind, specM_pure, hrd2]
      rw [show (decide ((σ.mems "mem" (AW.setWidth 12 + 2).toNat 32).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)
          && decide ((σ.mems "mem" (AW.setWidth 12 + 2).toNat 32).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13).toNat))
          = false from by
        rcases Decidable.not_and_iff_not_or_not.mp hlen with hA | hA
        · rw [decide_eq_false hA]
          generalize decide ((σ.mems "mem" (AW.setWidth 12 + 2).toNat 32).toNat
            ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13).toNat) = b
          revert b
          decide
        · rw [decide_eq_false hA]
          generalize decide ((σ.mems "mem" (AW.setWidth 12 + 2).toNat 32).toNat
            ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13).toNat) = a
          revert a
          decide]
      rfl
  case pos =>
  have hu0S : (Expr.ult (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32)
      (Hw.moveW E 2)).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro h
    have h2 : ((((Hw.moveSrcSel E).kindW.eval σ).extractLsb' 13 13
      ).setWidth 32).toNat < ((Hw.moveW E 2).eval σ).toNat :=
      (ultE_eval _ _ σ).mp h
    rw [hkwS, hmw2, toNat_setWidth_le (by omega)] at h2
    exact absurd hlen.1 (Nat.not_le_of_lt h2)
  have hu0D : (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32)
      (Hw.moveW E 2)).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro h
    have h2 : ((((Hw.moveDstSel E).kindW.eval σ).extractLsb' 13 13
      ).setWidth 32).toNat < ((Hw.moveW E 2).eval σ).toNat :=
      (ultE_eval _ _ σ).mp h
    rw [hkwD, hmw2, toNat_setWidth_le (by omega)] at h2
    exact absurd hlen.2 (Nat.not_le_of_lt h2)
  have hlenB : (decide ((σ.mems "mem" (AW.setWidth 12 + 2).toNat 32).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)
      && decide ((σ.mems "mem" (AW.setWidth 12 + 2).toNat 32).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) ((σ.mems "mem" (AW.setWidth 12 + 1).toNat 32).extractLsb' 0 4))) 32).extractLsb' 13 13).toNat))
      = true := by
    rw [decide_eq_true hlen.1, decide_eq_true hlen.2]
    decide
  by_cases hsaC : (Hw.domCoversE E (Hw.field (Hw.moveW E 3) 0 12)
      { r := false, w := true, x := false }).eval σ = 1#1
  case neg =>
    -- status-word write authority fault
    have hin : Inert σ := Inert.of_move_fail σ hkill E hifexcl (fun hc => by
      have h1 := (andAll_eval σ _).mp hc _ (List.mem_map.mpr
        ⟨((Expr.not (Hw.domCoversE E (Hw.field (Hw.moveW E 3) 0 12) { r := false, w := true, x := false }) : Expr 1), (Resp.fault .memoryAuthority)), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))), rfl⟩)
      have h2 : ~~~(~~~((Hw.domCoversE E (Hw.field (Hw.moveW E 3) 0 12) { r := false, w := true, x := false }).eval σ)) = 1#1 := h1
      rw [bv1_ne_one.mp hsaC] at h2
      exact absurd h2 (by decide))
    have haddrSA : ((Hw.field (Hw.moveW E 3) 0 12).eval σ)
        = (σ.mems "mem" (AW.setWidth 12 + 3).toNat 32).setWidth 12 := by
      show ((Hw.moveW E 3).eval σ).extractLsb' 0 12 = _
      rw [hmw3]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth]
    have hcovFsa : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E ((σ.mems "mem" (AW.setWidth 12 + 3).toNat 32).setWidth 12)
        { r := false, w := true, x := false } = false := by
      rw [spec_covers_bridge]
      rw [← Bool.not_eq_true]
      intro hcv
      exact hsaC ((domCoversE_eval σ E _ _).mpr (by
        rw [haddrSA]
        exact hcv))
    refine square_retire_fault_of m hwf hfit σ hsync hifv hcl hin hswz
      hmapz hunmapz
      (fun ad => by
        rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
        exact refill_pres_mem m σ "mem" ad 32)
      E rfl .memoryAuthority ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.reg 1 "mov_v").eval σ = 1#1) from hbusy),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 0)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc0]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 1)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc1]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 2)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc2]
          decide),
        if_neg (show ¬((Expr.not (Hw.domCoversE E (.add (Hw.moveBase E)
            (.lit (BitVec.ofNat 12 3)))
            { r := true, w := false, x := false })).eval σ = 1#1) from by
          show ¬(~~~((Hw.domCoversE E _ _).eval σ) = 1#1)
          rw [hc3]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).live.eval σ) = 1#1)
          rw [hliv1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveSrcSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveSrcSel E).clsOk.eval σ) = 1#1)
          rw [hcls1S]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).live.eval σ) = 1#1)
          rw [hliv1D]
          decide),
        if_neg (show ¬((Expr.not (Hw.moveDstSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.moveDstSel E).clsOk.eval σ) = 1#1)
          rw [hcls1D]
          decide),
        if_neg (show ¬((Expr.not (Expr.and
            (Hw.kIsMem (Hw.moveSrcSel E).kindW)
            (Hw.kIsMem (Hw.moveDstSel E).kindW))).eval σ = 1#1) from by
          show ¬(~~~((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ &&&
            (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ) = 1#1)
          rw [hkm1S, hkm1D]
          decide),
        if_neg (show ¬((Expr.not (Hw.kR (Hw.moveSrcSel E).kindW)).eval σ = 1#1) from by
          show ¬(~~~((Hw.kR (Hw.moveSrcSel E).kindW).eval σ) = 1#1)
          rw [hkr1]
          decide),
        if_neg (show ¬((Expr.not (Hw.kW (Hw.moveDstSel E).kindW)).eval σ = 1#1) from by
          show ¬(~~~((Hw.kW (Hw.moveDstSel E).kindW).eval σ) = 1#1)
          rw [hkw1]
          decide),
        if_neg (show ¬((Expr.or (Expr.ult
            (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32) (Hw.moveW E 2))
            (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32)
              (Hw.moveW E 2))).eval σ = 1#1) from by
          show ¬(((Expr.ult (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32)
              (Hw.moveW E 2)).eval σ |||
            (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32)
              (Hw.moveW E 2)).eval σ) = 1#1)
          rw [hu0S, hu0D]
          decide),
        if_pos (show (Expr.not (Hw.domCoversE E
            (Hw.field (Hw.moveW E 3) 0 12)
            { r := false, w := true, x := false })).eval σ = 1#1 from by
          show ~~~((Hw.domCoversE E _ _).eval σ) = 1#1
          rw [bv1_ne_one.mp hsaC]
          decide)]
      rfl
    · rw [hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      rw [hmovN]
      simp only [Option.isNone_none, reduceIte, specM_bind, SpecM.get,
        SpecM.require, SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hcovT0, hcovT1, hcovT2, hcovT3, reduceIte,
        specM_bind, specM_pure, hrd0, hrd1]
      simp only [hlcSS', hcekS]
      rw [hdecS]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hlcSD', hcekD]
      rw [hdecD]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcekS, hcekD]
      simp only [hmkS2, hmkD2]
      simp only [hprS, hpwD, reduceIte, specM_bind, specM_pure, hrd2,
        hrd3, hlenB, SpecM.get, SpecM.demand, SpecM.fatal, hcovFsa]
      rfl
  case pos =>
  -- ==== OK: the job installs and the Mover starts ====
  have hsa1 : (Hw.domCoversE E (Hw.field (Hw.moveW E 3) 0 12)
      { r := false, w := true, x := false }).eval σ = 1#1 := hsaC
  have haddrSA : ((Hw.field (Hw.moveW E 3) 0 12).eval σ)
      = (σ.mems "mem" (AW.setWidth 12 + 3).toNat 32).setWidth 12 := by
    show ((Hw.moveW E 3).eval σ).extractLsb' 0 12 = _
    rw [hmw3]
    exact extract0_eq_setWidth _ _
  have hcovTsa : (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).domCovers E ((σ.mems "mem" (AW.setWidth 12 + 3).toNat 32).setWidth 12)
      { r := false, w := true, x := false } = true := by
    rw [spec_covers_bridge]
    exact haddrSA ▸ (domCoversE_eval σ E _ _).mp hsaC
  have hok1 : ((Hw.moveJob E).ok).eval σ = 1#1 := by
    show (Hw.andAll ((Hw.moveChecks E).map
      (fun c => Expr.not c.1))).eval σ = 1#1
    rw [andAll_eval]
    intro e he
    obtain ⟨c, hcmem, rfl⟩ := List.mem_map.mp he
    rcases hcmem with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _
      | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _
      | ⟨_, hnil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · show ~~~(σ.regs "mov_v" 1) = 1#1
      rw [bv1_ne_one.mp hbusy]
      decide
    · show ~~~(~~~((Hw.domCoversE E _ _).eval σ)) = 1#1
      rw [hc0]
      decide
    · show ~~~(~~~((Hw.domCoversE E _ _).eval σ)) = 1#1
      rw [hc1]
      decide
    · show ~~~(~~~((Hw.domCoversE E _ _).eval σ)) = 1#1
      rw [hc2]
      decide
    · show ~~~(~~~((Hw.domCoversE E _ _).eval σ)) = 1#1
      rw [hc3]
      decide
    · show ~~~(~~~((Hw.moveSrcSel E).live.eval σ)) = 1#1
      rw [hliv1S]
      decide
    · show ~~~(~~~((Hw.moveSrcSel E).clsOk.eval σ)) = 1#1
      rw [hcls1S]
      decide
    · show ~~~(~~~((Hw.moveDstSel E).live.eval σ)) = 1#1
      rw [hliv1D]
      decide
    · show ~~~(~~~((Hw.moveDstSel E).clsOk.eval σ)) = 1#1
      rw [hcls1D]
      decide
    · show ~~~(~~~((Hw.kIsMem (Hw.moveSrcSel E).kindW).eval σ &&&
        (Hw.kIsMem (Hw.moveDstSel E).kindW).eval σ)) = 1#1
      rw [hkm1S, hkm1D]
      decide
    · show ~~~(~~~((Hw.kR (Hw.moveSrcSel E).kindW).eval σ)) = 1#1
      rw [hkr1]
      decide
    · show ~~~(~~~((Hw.kW (Hw.moveDstSel E).kindW).eval σ)) = 1#1
      rw [hkw1]
      decide
    · show ~~~((Expr.ult (.zext (Hw.kLen (Hw.moveSrcSel E).kindW) 32)
          (Hw.moveW E 2)).eval σ |||
        (Expr.ult (.zext (Hw.kLen (Hw.moveDstSel E).kindW) 32)
          (Hw.moveW E 2)).eval σ) = 1#1
      rw [hu0S, hu0D]
      decide
    · show ~~~(~~~((Hw.domCoversE E _ _).eval σ)) = 1#1
      rw [hsaC]
      decide
    · exact absurd hnil (List.not_mem_nil)
  have hnj1 : (Hw.newJobSet E).eval σ = 1#1 := by
    show (Hw.andAll [Hw.retiringE, Hw.ifDomIs E, Hw.isMn "move",
      (Hw.moveJob E).ok]).eval σ = 1#1
    rw [andAll_eval]
    intro e he
    rcases he with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, hnil⟩⟩⟩⟩
    · exact hret
    · exact hifsel
    · exact hmovemn
    · exact hok1
    · exact absurd hnil (List.not_mem_nil)
  have hnj0 : ∀ d : DomainId, d ≠ E → (Hw.newJobSet d).eval σ = 0#1 :=
    fun d hd => andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (hifexcl d hd)
  have hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = 0#1 :=
    killedByCore_of_nokill σ hkill
  sorry

