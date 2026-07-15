-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireDrop

/-!
# R-MC retirement: full cap_drop arm

The two error outcomes use the ordinary inert retirement square.  The
successful outcome uses the kill-aware square and the structural, region,
status-memory, and Mover bridges from `RMCRetireDrop`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

private theorem ifv_notin_dropSuccessA (E : DomainId) :
    (("if_v" : String), (1 : Nat)) ∉ (dropSuccessArmA E).regWrites := by
  fin_cases E <;> decide +kernel

theorem square_retire_drop (m : Manifest) (hwfm : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 17#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (17#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (17#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1 := by
    intro d
    by_cases hd : d = E
    · subst d; rw [if_pos rfl]; exact hifsel
    · rw [if_neg hd, bv1_ne_one.mp (hifexcl d hd)]
  have hdmn : (Hw.isMn "cap_drop").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "cap_drop" = 17#6).symm
  have hret := retiringE_one σ hifv hcl
  have hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_revoke" 17#6 hopc (by decide +kernel)
  have hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_call" 17#6 hopc (by decide +kernel)
  have hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_return" 17#6 hopc (by decide +kernel)
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1 := by
    intro d
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 17#6 hopc (by decide +kernel)
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 17#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 17#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d
          (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 17#6 hopc (by decide +kernel))
  have hsel := retireFor_drop_ladder σ E hopc
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ)
      = refillPhase m (Hw.abs σ) := abs_refill m hwfm hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y; rw [← habs1]; rfl
  have hG1 : ∀ g, (refillPhase m (Hw.abs σ)).gates g
      = Hw.absGate ((Hw.refillAct m).run σ σ) g := by
    intro g; rw [← habs1]; rfl
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  set HWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hHWv
  have hSPr : ∀ rs : RegId,
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg rs
        = ((Hw.abs σ).doms E).reg rs := fun rs => specReg_bridge m σ E rs
  have hRD : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
      (operandsOf W).rs1 = HWv := hSPr _
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ))
      = retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hDO : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (match ((SpecM.reg E (operandsOf W).rs1 >>= fun hw =>
          Machines.Lnp64u.Isa.capLive E hw >>= fun x =>
          let (s, g, _) := x
          let ref : CapRef := ⟨E, s, g⟩
          SpecM.get >>= fun τ0 =>
          let τ1 := match τ0.parentOf E s with
            | some p => τ0.reparent ref p
            | none => τ0.orphanChildren ref
          SpecM.set (((τ1.clearSlot E s).sweepRegions).sweepMover) >>=
            fun _ => SpecM.setReg E (operandsOf W).rd 0)
          (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
            (fun ds => { ds with pc := ds.pc + 1 }))) with
        | .ok _ σ' => σ'
        | .err e σ' =>
            σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault fl => haltWith
            { refillPhase m (Hw.abs σ) with inflight := none } E fl) := by
    have hfind : isa.find? (fun d => d.opcode == (17#6 : BitVec 6)) =
        some (Machines.Lnp64u.Isa.system.get ⟨1, by decide⟩) := by rfl
    have hexec :
        (Machines.Lnp64u.Isa.system.get ⟨1, by decide⟩).sem.exec =
          (fun c => do
            let hw ← SpecM.reg c.d c.op.rs1
            let (s, g, _) ← Machines.Lnp64u.Isa.capLive c.d hw
            let ref : CapRef := ⟨c.d, s, g⟩
            let τ0 ← SpecM.get
            let τ1 := match τ0.parentOf c.d s with
              | some p => τ0.reparent ref p
              | none => τ0.orphanChildren ref
            SpecM.set (((τ1.clearSlot c.d s).sweepRegions).sweepMover)
            SpecM.setReg c.d c.op.rd 0) := by rfl
    rw [retire_of_decode_some _ E W _ (hdec.trans hfind), hexec]
    rfl
  have hSval : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (HWv.extractLsb' 0 4)).val =
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := by
    rw [hR1]; rfl
  have hlivE := capSel_live_eval σ E (Hw.readReg E Hw.rs1E) _ hSval
  rw [hR1] at hlivE
  have hnd : ((Hw.opCircs E).map Prod.fst).Nodup := by
    rw [opCircs_fst_all E]
    exact allMns_nodup
  have hq : ∀ p ∈ Hw.opCircs E, p.1 ≠ "cap_drop" →
      (Hw.isMn p.1).eval σ = 0#1 ∨ isLit0 p.2.memEn = true := by
    intro p hp hne
    left
    exact bv1_ne_one.mp (isMn_ne_of_opc σ p.1 17#6 hopc
      ((by decide +kernel : ∀ mn' ∈ allMns, mn' ≠ "cap_drop" →
        (17#6 : BitVec 6) ≠ Hw.opcodeOf mn') p.1
        (by rw [← opCircs_fst_all E]; exact List.mem_map_of_mem hp) hne))
  have hmemdrop : ("cap_drop", Hw.dropCirc E) ∈ Hw.opCircs E :=
    List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hport := retireMem_op_sel σ E "cap_drop" (Hw.dropCirc E)
    hifsel hifexcl hdmn hmemdrop hnd hq
  have hcoremem_of_dropOk_zero (hok0 : (Hw.dropOkE E).eval σ = 0#1) :
      ∀ b : Addr,
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
          b.toNat 32 = σ.mems "mem" b.toNat 32 := by
    intro b
    rw [coreAct_run_retire_eq m σ _ hifv hcl,
      retireAct_run_mems σ _ b.toNat 32]
    show (if (((List.finRange numDomains).foldr
        (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
          let (en_d, ad_d, da_d) := Hw.retireMemFor d
          let g := Expr.and (Hw.ifDomIs d) en_d
          (.or g acc'.1, .mux g ad_d acc'.2.1,
            .mux g da_d acc'.2.2))
        ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
          (.lit 0 : Expr 32))).1).eval σ = 1#1 then _
      else ((Hw.refillAct m).run σ σ)).mems "mem" b.toNat 32 = _
    rw [if_neg (by
      rw [hport.1]
      show ¬((Hw.dropCirc E).memEn.eval σ = 1#1)
      unfold Hw.dropCirc Hw.sweepMem Hw.andAll
      change ¬((Hw.dropOkE E).eval σ &&& _ = 1#1)
      rw [hok0]
      exact (by decide : ∀ b : BitVec 1, ¬(0#1 &&& b = 1#1)) _)]
    rw [refill_pres_mem m σ "mem" b.toNat 32]
  by_cases hlv : σ.regs (Hw.dcapV E
        (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1 ∧
      σ.regs (Hw.dgen E (finOfBv (by decide)
        (HWv.extractLsb' 0 4))) 8 = HWv.extractLsb' 4 8 ∧
      HWv.extractLsb' 4 8 ≠ 0
  case neg =>
    have hlive0 : ¬((Hw.dropSel E).live.eval σ = 1#1) :=
      fun hc => hlv (hlivE.mp hc)
    have hlcN : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom
        E (fun ds => { ds with pc := ds.pc + 1 })).doms E).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = none := by
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_neg hlv
    have hbad : ∀ d : DomainId, d = E → (Hw.dropOkE d).eval σ = 0#1 := by
      intro d hd; subst d
      unfold Hw.dropOkE Hw.okOf Hw.dropChecks Hw.andAll
      change ~~~(~~~((Hw.dropSel E).live.eval σ)) &&&
        ~~~(~~~((Hw.dropSel E).clsOk.eval σ)) = 0#1
      rw [bv1_ne_one.mp hlive0]
      generalize (Hw.dropSel E).clsOk.eval σ = b
      exact (by decide : ∀ b : BitVec 1,
        ~~~(~~~(0#1)) &&& ~~~(~~~b) = 0#1) b
    have hin : Inert σ := Inert.of_failed_drop σ E hret hif hdmn hrev
      hcall hreturn hbad hnew
    have hcoremem := hcoremem_of_dropOk_zero (hbad E rfl)
    refine retire_err_common_mem m hwfm hfit σ hsync hifv hcl hin
      hmapz hunmapz hswz hcoremem E rfl Errno.staleHandle.toWord ?_ ?_
    · intro acc
      rw [hsel acc, if_pos (show (Expr.not (Hw.dropSel E).live).eval σ =
        1#1 from by
          show ~~~((Hw.dropSel E).live.eval σ) = 1#1
          rw [bv1_ne_one.mp hlive0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure, hRD, hlcN]
      rfl
  case pos =>
    have hliv1 : (Hw.dropSel E).live.eval σ = 1#1 := hlivE.mpr hlv
    let S : Slot := finOfBv (by decide) (HWv.extractLsb' 0 4)
    let e : CapEntry :=
      { kind := Hw.decKind (σ.regs (Hw.dcapKind E S) 32)
        lineage := if σ.regs (Hw.dcapLinV E S) 1 = 1#1 then
          some (finOfBv (by decide) (σ.regs (Hw.dcapLin E S) 4))
        else none }
    have hcap : ((Hw.abs σ).doms E).caps S = some e := by
      change (if σ.regs (Hw.dcapV E S) 1 = 1#1 then
        some { kind := Hw.decKind (σ.regs (Hw.dcapKind E S) 32)
               lineage := if σ.regs (Hw.dcapLinV E S) 1 = 1#1 then
                 some (finOfBv (by decide) (σ.regs (Hw.dcapLin E S) 4))
               else none }
        else none) = some e
      rw [if_pos hlv.1]
    have hlcS : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom
        E (fun ds => { ds with pc := ds.pc + 1 })).doms E).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = some e := by
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_pos hlv
    have hkwE : (Hw.dropSel E).kindW.eval σ =
        σ.regs (Hw.dcapKind E S) 32 := by
      exact capSel_kindW_eval σ E (Hw.readReg E Hw.rs1E) S hSval
    have hclsE : (Hw.dropSel E).clsOk.eval σ =
        (if (σ.regs (Hw.dcapKind E S) 32).extractLsb' 0 1 =
            HWv.extractLsb' 12 1 then (1#1 : BitVec 1) else 0#1) := by
      show (if ((Hw.dropSel E).kindW.eval σ).extractLsb' 0 1 =
          ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 12 1
        then (1#1 : BitVec 1) else 0#1) = _
      rw [hkwE, hR1]
    by_cases hbit : HWv.getLsbD 12 =
        (σ.regs (Hw.dcapKind E S) 32).getLsbD 0
    · have hcls1 : (Hw.dropSel E).clsOk.eval σ = 1#1 := by
        rw [hclsE]
        rw [if_pos ((extract1_eq_iff (σ.regs (Hw.dcapKind E S) 32)
          HWv 0 12).mpr hbit.symm)]
      have hdecT : decide ((Handle.decode HWv).cls = e.kind.cls) = true := by
        apply decide_eq_true
        unfold e
        exact (cls_eq_iff_bits HWv (σ.regs (Hw.dcapKind E S) 32)).mpr hbit
      have hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val := by
        show ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4 = _
        rw [hR1]
        exact (bv4_slot_iff _ S).mpr rfl
      have hwfσ : Wf (Hw.abs σ) :=
        (Machines.Lnp64u.wfa_invariant m hwfm (Hw.abs σ) hsr).1
      have hok : ∀ d : DomainId, d = E → (Hw.dropOkE d).eval σ = 1#1 := by
        intro d hd; subst d
        unfold Hw.dropOkE Hw.okOf Hw.dropChecks Hw.andAll
        change ~~~(~~~((Hw.dropSel E).live.eval σ)) &&&
          ~~~(~~~((Hw.dropSel E).clsOk.eval σ)) = 1#1
        rw [hliv1, hcls1]
        decide
      have hkills : ∀ (dm : Expr 2) (sl : Expr 4),
          (Hw.killedByCoreE dm sl).eval σ =
            (Hw.dropKilled E dm sl).eval σ :=
        killedByCoreE_drop_eval σ E hret hif hdmn hrev hcall hreturn hok
      let RD : RegId := (operandsOf W).rd
      have hrd : (Hw.rdE.eval σ).toNat = RD.val := rfl
      let τ0 : MachineState :=
        ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })
      let ref : CapRef := ⟨E, S, HWv.extractLsb' 4 8⟩
      let τs : MachineState :=
        match τ0.parentOf E S with
        | some p => τ0.reparent ref p
        | none => τ0.orphanChildren ref
      let τr : MachineState := (τs.clearSlot E S).sweepRegions
      let τm : MachineState := τr.sweepMover
      let τ2 : MachineState := τm.setDom E
        (fun ds => ds.setReg RD 0)
      have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
        rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure, hRD, hlcS]
        rw [hdecT]
        simp only [reduceIte, specM_bind, specM_pure, SpecM.set,
          SpecM.setReg, SpecM.modify]
        unfold τ2 τm τr τs τ0 ref RD S
        rfl
      have hcoreR : ∀ (rn : String) (w : Nat),
          ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
            ((Act.seq (.write 1 "if_v" (.lit 0))
              (dropSuccessArmA E)).run σ
                ((Hw.refillAct m).run σ σ)).regs rn w := by
        intro rn w
        rw [coreAct_run_retire_eq m σ _ hifv hcl,
          retireAct_run_regs σ _ E rfl rn w, hsel]
        rw [if_neg (show ¬((Expr.not (Hw.dropSel E).live).eval σ = 1#1)
          from by
            show ¬(~~~((Hw.dropSel E).live.eval σ) = 1#1)
            rw [hliv1]
            decide),
          if_neg (show ¬((Expr.not (Hw.dropSel E).clsOk).eval σ = 1#1)
          from by
            show ¬(~~~((Hw.dropSel E).clsOk.eval σ) = 1#1)
            rw [hcls1]
            decide)]
        rfl
      have habsG : ∀ g, Hw.absGate
          ((Act.seq (.write 1 "if_v" (.lit 0))
            (dropSuccessArmA E)).run σ ((Hw.refillAct m).run σ σ)) g =
            τ2.gates g := by
        intro g
        have hquiet : ∀ q ∈ gateReadNames g,
            q ∉ (Act.seq (.write 1 "if_v" (.lit 0))
              (dropSuccessArmA E)).regWrites := by
          clear_value E
          clear * - g E
          native_decide +revert
        have hg := absGate_congr g (fun p hp => frame (hquiet p hp) σ
          ((Hw.refillAct m).run σ σ))
        rw [hg, ← hG1 g]
        unfold τ2 τm τr τs τ0
        split <;>
          simp only [MachineState.setDom, sweepMover_gates, sweepRegions_gates, clearSlot_gates,
            reparent_gates, orphanChildren_gates] <;>
          rfl
      refine square_retire_kill m hwfm hfit σ hsync hifv hcl
        (dropSuccessArmA E) τ2 hcoreR (ifv_notin_dropSuccessA E) hspec
        ?_ habsG ?_ ?_ ?_ ?_
      · let δ0 : MachineState := dropStructSpecArm (Hw.abs σ) E S
        let δτ : MachineState := τs.clearSlot E S
        have href : ref =
            ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩ := by
          have hgen : ((Hw.abs σ).doms E).slotGen S =
              HWv.extractLsb' 4 8 := by
            simpa [Hw.abs, Hw.absDom] using hlv.2.1
          unfold ref
          rw [hgen]
        have hparent : τ0.parentOf E S =
            (Hw.abs σ).parentOf E S := by
          unfold τ0 MachineState.parentOf MachineState.setDom
          simp only [Loom.Fun.update_same, refillPhase_caps,
            refillPhase_lineage]
        have hτs : τs =
            match (Hw.abs σ).parentOf E S with
            | some p => τ0.reparent
                ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩ p
            | none => τ0.orphanChildren
                ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩ := by
          unfold τs
          rw [hparent, href]
        have htables : TablesEq δ0 δτ := by
          intro d
          cases hp : (Hw.abs σ).parentOf E S with
          | none =>
              by_cases hd : d = E
              · subst d
                simp [δ0, dropStructSpecArm, δτ, hτs, hp,
                  τ0, MachineState.orphanChildren, MachineState.clearSlot,
                  MachineState.setDom]
              · simp [δ0, dropStructSpecArm, δτ, hτs, hp,
                  τ0, MachineState.orphanChildren, MachineState.clearSlot,
                  MachineState.setDom, hd]
          | some p =>
              by_cases hd : d = E
              · subst d
                simp [δ0, dropStructSpecArm, δτ, hτs, hp,
                  τ0, MachineState.reparent, MachineState.clearSlot,
                  MachineState.setDom]
              · simp [δ0, dropStructSpecArm, δτ, hτs, hp,
                  τ0, MachineState.reparent, MachineState.clearSlot,
                  MachineState.setDom, hd]
        have hliveδ : ∀ r : CapRef, δτ.liveRef r = δ0.liveRef r := by
          intro r
          unfold MachineState.liveRef DomainState.liveCap
          rw [(htables r.dom).1, (htables r.dom).2.2]
        have hregions0 : ∀ d, (δτ.doms d).regions =
            (δ0.doms d).regions := by
          intro d
          cases hp : (Hw.abs σ).parentOf E S with
          | none =>
              by_cases hd : d = E
              · subst d
                simp [δ0, dropStructSpecArm, δτ, hτs, hp, τ0,
                  MachineState.orphanChildren, MachineState.clearSlot,
                  MachineState.setDom]
              · simp [δ0, dropStructSpecArm, δτ, hτs, hp, τ0,
                  MachineState.orphanChildren, MachineState.clearSlot,
                  MachineState.setDom, hd]
          | some p =>
              by_cases hd : d = E
              · subst d
                simp [δ0, dropStructSpecArm, δτ, hτs, hp, τ0,
                  MachineState.reparent, MachineState.clearSlot,
                  MachineState.setDom]
              · simp [δ0, dropStructSpecArm, δτ, hτs, hp, τ0,
                  MachineState.reparent, MachineState.clearSlot,
                  MachineState.setDom, hd]
        have hregions : ∀ d, ((δτ.sweepRegions).doms d).regions =
            ((δ0.sweepRegions).doms d).regions := by
          intro d
          funext r
          change (match (δτ.doms d).regions r with
            | some rg => if δτ.liveRef rg.backing then some rg else none
            | none => none) =
            (match (δ0.doms d).regions r with
            | some rg => if δ0.liveRef rg.backing then some rg else none
            | none => none)
          rw [congrFun (hregions0 d) r]
          cases hr : (δ0.doms d).regions r with
          | none => rfl
          | some rg =>
              simp only
              rw [hliveδ]
        have hframe : ∀ d,
            (δτ.doms d).regs = (δ0.doms d).regs ∧
            (δτ.doms d).pc = (if d = E then (δ0.doms d).pc + 1
              else (δ0.doms d).pc) ∧
            (δτ.doms d).run = (δ0.doms d).run ∧
            (δτ.doms d).serving = (δ0.doms d).serving ∧
            (δτ.doms d).cause = (δ0.doms d).cause ∧
            (δτ.doms d).budget =
              ((refillPhase m (Hw.abs σ)).doms d).budget ∧
            (δτ.doms d).maxDonation = (δ0.doms d).maxDonation := by
          intro d
          cases hp : (Hw.abs σ).parentOf E S with
          | none =>
              by_cases hd : d = E
              · subst d
                simp [δ0, dropStructSpecArm, δτ, hτs, hp, τ0,
                  MachineState.orphanChildren, MachineState.clearSlot,
                  MachineState.setDom]
                exact refillPhase_maxDonation m (Hw.abs σ) E
              · simp [δ0, dropStructSpecArm, δτ, hτs, hp, τ0,
                  MachineState.orphanChildren, MachineState.clearSlot,
                  MachineState.setDom, hd]
                exact refillPhase_maxDonation m (Hw.abs σ) d
          | some p =>
              by_cases hd : d = E
              · subst d
                simp [δ0, dropStructSpecArm, δτ, hτs, hp, τ0,
                  MachineState.reparent, MachineState.clearSlot,
                  MachineState.setDom]
                exact refillPhase_maxDonation m (Hw.abs σ) E
              · simp [δ0, dropStructSpecArm, δτ, hτs, hp, τ0,
                  MachineState.reparent, MachineState.clearSlot,
                  MachineState.setDom, hd]
                exact refillPhase_maxDonation m (Hw.abs σ) d
        intro c
        unfold dropSuccessArmA
        rw [absDom_dropSuccessA_refill m hwfm hfit σ hsync E S e RD
          hslot hliv1 hcap hwfσ hrd hkills hmapz hunmapz c]
        have hτ2dom : τ2.doms c = ((δτ.sweepRegions).setDom E
            (fun ds => ds.setReg RD 0)).doms c := by
          unfold τ2 τm τr δτ
          by_cases hc : c = E
          · subst c
            rw [setDom_doms_same, setDom_doms_same,
              sweepMover_doms]
          · rw [setDom_doms_ne _ _ _ _ hc,
              setDom_doms_ne _ _ _ _ hc, sweepMover_doms]
        rw [hτ2dom]
        obtain ⟨hregs, hpc, hrun, hserv, hcause, hbud, hmax⟩ := hframe c
        by_cases hc : c = E
        · subst c
          simp only [MachineState.setDom, Loom.Fun.update_same, if_pos]
          apply domainState_ext'
          · funext r
            rw [setReg_regs, setReg_regs]
            change (if RD = 0 then (δ0.doms E).regs r
              else if r = RD then 0 else (δ0.doms E).regs r) =
              (if RD = 0 then (δτ.doms E).regs r
              else if r = RD then 0 else (δτ.doms E).regs r)
            rw [congrFun hregs r]
          · simp only [setReg_pc]
            change (δ0.doms E).pc + 1 = (δτ.doms E).pc
            simpa using hpc.symm
          · simp only [setReg_caps, sweepRegions_caps]
            exact (htables E).1.symm
          · simp only [setReg_slotGen, sweepRegions_slotGen]
            exact (htables E).2.2.symm
          · simp only [setReg_lineage, sweepRegions_lineage]
            exact (htables E).2.1.symm
          · simp only [setReg_regions]
            exact (hregions E).symm
          · simp only [setReg_run, sweepRegions_run]
            exact hrun.symm
          · simp only [setReg_serving, sweepRegions_serving]
            exact hserv.symm
          · simp only [setReg_cause]
            exact hcause.symm
          · simp only [setReg_budget]
            exact hbud.symm
          · simp only [setReg_maxDonation]
            exact hmax.symm
        · simp only [MachineState.setDom,
            Loom.Fun.update_ne _ _ _ _ hc, if_neg hc]
          rw [if_neg hc] at hpc
          apply domainState_ext'
          · change (δ0.doms c).regs = (δτ.doms c).regs
            exact hregs.symm
          · change (δ0.doms c).pc = (δτ.doms c).pc
            exact hpc.symm
          · change (δ0.doms c).caps = (δτ.doms c).caps
            exact (htables c).1.symm
          · change (δ0.doms c).slotGen = (δτ.doms c).slotGen
            exact (htables c).2.2.symm
          · change (δ0.doms c).lineage = (δτ.doms c).lineage
            exact (htables c).2.1.symm
          · exact (hregions c).symm
          · change (δ0.doms c).run = (δτ.doms c).run
            exact hrun.symm
          · change (δ0.doms c).serving = (δτ.doms c).serving
            exact hserv.symm
          · change (δ0.doms c).cause = (δτ.doms c).cause
            exact hcause.symm
          · exact hbud.symm
          · change (δ0.doms c).maxDonation =
              (δτ.doms c).maxDonation
            exact hmax.symm
      · have hliveτ0 : ∀ r : CapRef,
            τ0.liveRef r = (Hw.abs σ).liveRef r := by
          intro r
          unfold τ0 MachineState.liveRef DomainState.liveCap
          by_cases hd : r.dom = E
          · rw [hd]
            simp [MachineState.setDom]
          · simp [MachineState.setDom,
              Loom.Fun.update_ne _ _ _ _ hd]
        have hliveR : ∀ r : CapRef, τr.liveRef r =
            if r.dom = E ∧ r.slot = S then false
            else (Hw.abs σ).liveRef r := by
          intro r
          unfold τr τs
          rw [sweepRegions_liveRef]
          split
          · rw [reparent_clearSlot_liveRef, hliveτ0]
          · rw [orphan_clearSlot_liveRef, hliveτ0]
        have hmoverτ0 : τ0.mover = (Hw.abs σ).mover := by
          unfold τ0
          rfl
        have hmoverR : τr.mover = (Hw.abs σ).mover := by
          unfold τr τs
          rw [sweepRegions_mover]
          split
          · change τ0.mover = (Hw.abs σ).mover
            exact hmoverτ0
          · change τ0.mover = (Hw.abs σ).mover
            exact hmoverτ0
        have href0 : ref =
            ⟨E, S, (τ0.doms E).slotGen S⟩ := by
          have hgen : (τ0.doms E).slotGen S =
              HWv.extractLsb' 4 8 := by
            unfold τ0
            rw [setDom_doms_same, refillPhase_slotGen]
            change σ.regs (Hw.dgen E S) 8 = _
            exact hlv.2.1
          unfold ref
          rw [hgen]
        have hstruct : τs.clearSlot E S =
            dropStructSpecArm τ0 E S := by
          unfold τs dropStructSpecArm
          rw [href0]
          rfl
        have hτ0cap : ∀ d s g,
            (τ0.doms d).liveCap s g =
              ((Hw.abs σ).doms d).liveCap s g := by
          intro d s g
          unfold τ0 DomainState.liveCap
          by_cases hd : d = E
          · subst d
            simp [MachineState.setDom]
          · simp [MachineState.setDom,
              Loom.Fun.update_ne _ _ _ _ hd]
        have hkind : ∀ d s g, ¬(d = E ∧ s = S) →
            Option.map CapEntry.kind ((τ2.doms d).liveCap s g) =
              Option.map CapEntry.kind
                (((Hw.abs σ).doms d).liveCap s g) := by
          intro d s g hout
          have hpost : (τ2.doms d).liveCap s g =
              (((τs.clearSlot E S).doms d).liveCap s g) := by
            unfold τ2 τm τr DomainState.liveCap
            by_cases hd : d = E
            · subst d
              simp [MachineState.setDom]
            · simp [MachineState.setDom,
                Loom.Fun.update_ne _ _ _ _ hd]
          rw [hpost, hstruct]
          exact (dropStructSpecArm_liveKind τ0 E S d s g hout).trans
            (congrArg (Option.map CapEntry.kind) (hτ0cap d s g))
        have hjob : τ2.mover =
            match Hw.absMover σ with
            | none => none
            | some job =>
                if (job.src.dom = E ∧ job.src.slot = S) ∨
                    (job.dst.dom = E ∧ job.dst.slot = S)
                then none else some job := by
          have hsweep := sweepMover_drop_mover (Hw.abs σ) τr E S
            hmoverR hliveR (moverEndpoints_live hwfσ)
          simpa [τ2, τm] using hsweep
        exact absMover_moverAct_drop σ
          ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)) τ2 E S
          hslot hkills hnew hkind hjob
      · have hliveτ0 : ∀ r : CapRef,
            τ0.liveRef r = (Hw.abs σ).liveRef r := by
          intro r
          unfold τ0 MachineState.liveRef DomainState.liveCap
          by_cases hd : r.dom = E
          · rw [hd]
            simp [MachineState.setDom]
          · simp [MachineState.setDom,
              Loom.Fun.update_ne _ _ _ _ hd]
        have hliveC : ∀ r : CapRef, (τs.clearSlot E S).liveRef r =
            if r.dom = E ∧ r.slot = S then false
            else (Hw.abs σ).liveRef r := by
          intro r
          unfold τs
          split
          · rw [reparent_clearSlot_liveRef, hliveτ0]
          · rw [orphan_clearSlot_liveRef, hliveτ0]
        have hliveR : ∀ r : CapRef, τr.liveRef r =
            if r.dom = E ∧ r.slot = S then false
            else (Hw.abs σ).liveRef r := by
          intro r
          unfold τr
          rw [sweepRegions_liveRef, hliveC]
        have hmoverτ0 : τ0.mover = (Hw.abs σ).mover := by
          unfold τ0
          rfl
        have hmoverR : τr.mover = (Hw.abs σ).mover := by
          unfold τr τs
          rw [sweepRegions_mover]
          split
          · change τ0.mover = (Hw.abs σ).mover
            exact hmoverτ0
          · change τ0.mover = (Hw.abs σ).mover
            exact hmoverτ0
        have hregionsτ0 : ∀ c, (τ0.doms c).regions =
            ((Hw.abs σ).doms c).regions := by
          intro c
          unfold τ0
          by_cases hc : c = E
          · subst c
            simp [MachineState.setDom]
          · simp [MachineState.setDom,
              Loom.Fun.update_ne _ _ _ _ hc]
        have hregionsC : ∀ c,
            (((τs.clearSlot E S).doms c).regions) =
              ((Hw.abs σ).doms c).regions := by
          intro c
          unfold τs
          split
          · rw [clearSlot_regions]
            change (τ0.doms c).regions = _
            exact hregionsτ0 c
          · rw [clearSlot_regions, orphanChildren_regions]
            exact hregionsτ0 c
        have hauthR : ∀ (ow : Expr 2) (sa : Expr 12),
            ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
              (List.finRange numRegions).map fun r =>
                Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
                  Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                    ⟨false, true, false⟩])).eval σ = 1#1) ↔
              τr.domCovers (finOfBv (by decide) (ow.eval σ))
                (sa.eval σ) ⟨false, true, false⟩ = true := by
          intro ow sa
          simpa [τr] using sAuth_drop_eval σ E S (τs.clearSlot E S)
            hslot hkills hmapz hunmapz hregionsC hliveC hwfσ ow sa
        have hmemR : ∀ b : Addr, τr.mem b =
            σ.mems "mem" b.toNat 32 := by
          intro b
          unfold τr τs τ0
          split <;> rfl
        have hsweepMem : ∀ b : Addr, τm.mem b =
            match (Hw.abs σ).mover with
            | none => τr.mem b
            | some job =>
                if (job.src.dom = E ∧ job.src.slot = S) ∨
                    (job.dst.dom = E ∧ job.dst.slot = S) then
                  if ({ τr with mover := none } : MachineState).domCovers
                      job.owner job.statusAddr
                      { r := false, w := true, x := false } then
                    if b = job.statusAddr then Errno.staleHandle.toWord
                    else τr.mem b
                  else τr.mem b
                else τr.mem b := by
          intro b
          exact sweepMover_drop_mem (Hw.abs σ) τr E S hmoverR hliveR
            (moverEndpoints_live hwfσ) b
        have hcoreMem : ∀ b : Addr,
            ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems
                "mem" b.toNat 32 = τ2.mem b := by
          intro b
          rw [coreAct_run_retire_eq m σ _ hifv hcl,
            retireAct_run_mems σ _ b.toNat 32]
          have hentry : ∀ (c : DomainId) (r : RegionId),
              ((Hw.andAll [Expr.eq (.reg 2 "mov_owner") (Hw.dLit c),
                .not (Hw.dropKilled E
                  (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
                  (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)),
                Hw.coversE c r (.reg 12 "mov_status")
                  ⟨false, true, false⟩]).eval σ = 1#1) ↔
              ((Hw.andAll [Expr.eq (.reg 2 "mov_owner") (Hw.dLit c),
                Hw.rgnVPostE c r,
                Hw.rgnCoversVal (Hw.rgnValPostE c r)
                  (.reg 12 "mov_status")
                  ⟨false, true, false⟩]).eval σ = 1#1) := by
            intro c r
            have hrv : (Hw.rgnVPostE c r).eval σ =
                σ.regs (Hw.drgnV c r) 1 &&&
                  ~~~((Hw.killedByCoreE
                    (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
                    (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval σ) := by
              show (if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c,
                  Hw.isMn "map", Hw.mapOkE c,
                  .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1 then _
                else if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c,
                  Hw.isMn "unmap", .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1
                then _ else _) = _
              rw [hmapz c r, hunmapz c r]
              rw [if_neg (by decide), if_neg (by decide)]
              rfl
            have hrval : (Hw.rgnValPostE c r).eval σ =
                σ.regs (Hw.drgn c r) 42 := by
              exact rgnValPostE_quiescent σ hmapz c r
            have hcover :
                ((Hw.coversE c r (.reg 12 "mov_status")
                    ⟨false, true, false⟩).eval σ = 1#1) ↔
                (σ.regs (Hw.drgnV c r) 1 = 1#1 ∧
                  (Hw.rgnCoversVal (.reg 42 (Hw.drgn c r))
                    (.reg 12 "mov_status")
                    ⟨false, true, false⟩).eval σ = 1#1) := by
              rw [Hw.coversE, andAll_eval, Hw.rgnCoversVal, andAll_eval]
              simp only [reduceIte, List.cons_append, List.nil_append,
                List.forall_mem_cons, List.not_mem_nil, implies_true,
                False.elim]
              constructor
              · rintro ⟨hv, hp, hlo, hhi⟩
                exact ⟨hv, hp, hlo, hhi⟩
              · rintro ⟨hv, hp, hlo, hhi⟩
                exact ⟨hv, hp, hlo, hhi⟩
            rw [andAll_eval, andAll_eval]
            simp only [List.forall_mem_cons, List.not_mem_nil, implies_true,
              False.elim]
            rw [hcover, hrv, bv1_and_eq_one,
              rgnCoversVal_eval, rgnCoversVal_eval, hrval]
            simp [and_assoc, and_left_comm, and_comm]
            intro _
            rw [notE_eval, ← hkills]
            constructor
            · rintro ⟨hc, hk, hv⟩
              refine ⟨?_, hc, hv⟩
              rw [hk]
              decide
            · rintro ⟨hn, hc, hv⟩
              refine ⟨hc, ?_, hv⟩
              apply bv1_ne_one.mp
              intro hk
              rw [hk] at hn
              exact absurd hn (by decide)
          have hstatusPost :
              ((Hw.statusAuthE (Hw.dropKilled E)).eval σ = 1#1) ↔
              ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
                (List.finRange numRegions).map fun r =>
                  Hw.andAll [Expr.eq (.reg 2 "mov_owner") (Hw.dLit c),
                    Hw.rgnVPostE c r,
                    Hw.rgnCoversVal (Hw.rgnValPostE c r)
                      (.reg 12 "mov_status")
                      ⟨false, true, false⟩])).eval σ = 1#1) := by
            unfold Hw.statusAuthE
            rw [orAll_eval, orAll_eval]
            constructor
            · rintro ⟨e', he', hev⟩
              rw [List.mem_flatMap] at he'
              obtain ⟨c, hc, he'⟩ := he'
              obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he'
              exact ⟨_, List.mem_flatMap.mpr ⟨c, hc,
                List.mem_map.mpr ⟨r, hr, rfl⟩⟩, (hentry c r).mp hev⟩
            · rintro ⟨e', he', hev⟩
              rw [List.mem_flatMap] at he'
              obtain ⟨c, hc, he'⟩ := he'
              obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he'
              exact ⟨_, List.mem_flatMap.mpr ⟨c, hc,
                List.mem_map.mpr ⟨r, hr, rfl⟩⟩, (hentry c r).mpr hev⟩
          simp only [Act.run]
          rw [hport.1]
          change _ = τm.mem b
          rw [hsweepMem b]
          rw [show (Hw.abs σ).mover = Hw.absMover σ from rfl]
          by_cases hv : σ.regs "mov_v" 1 = 1#1
          · let job : MoverJob :=
              { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
                src := Hw.decRef (σ.regs "mov_src" 14)
                dst := Hw.decRef (σ.regs "mov_dst" 14)
                srcCur := σ.regs "mov_srccur" 12
                dstCur := σ.regs "mov_dstcur" 12
                remaining := (σ.regs "mov_rem" 13).toNat
                statusAddr := σ.regs "mov_status" 12 }
            have habs : Hw.absMover σ = some job := absMover_some σ hv
            rw [habs]
            have hauth :
                ((Hw.statusAuthE (Hw.dropKilled E)).eval σ = 1#1) ↔
                τr.domCovers job.owner job.statusAddr
                  ⟨false, true, false⟩ = true := by
              exact hstatusPost.trans (by
                simpa [job] using
                  (hauthR (.reg 2 "mov_owner") (.reg 12 "mov_status")))
            have hen : ((Hw.dropCirc E).memEn.eval σ = 1#1) ↔
                (((job.src.dom = E ∧ job.src.slot = S) ∨
                    (job.dst.dom = E ∧ job.dst.slot = S)) ∧
                  τr.domCovers job.owner job.statusAddr
                    ⟨false, true, false⟩ = true) := by
              have hmovEq :
                  (Hw.movKilledE (Hw.dropKilled E)).eval σ =
                    (Hw.movKilledE (fun dm sl =>
                      Hw.killedByCoreE dm sl)).eval σ := by
                rw [movKilledE_drop_eval σ E hkills]
                unfold Hw.movKilledE
                rfl
              unfold Hw.dropCirc Hw.sweepMem
              rw [andAll_eval]
              simp only [List.forall_mem_cons, List.not_mem_nil,
                implies_true]
              rw [hok E rfl, hmovEq,
                movKilledE_drop_iff σ E S hslot hkills, habs, hauth]
              simp
            by_cases hk : (job.src.dom = E ∧ job.src.slot = S) ∨
                (job.dst.dom = E ∧ job.dst.slot = S)
            · simp only
              rw [if_pos hk]
              by_cases ha : τr.domCovers job.owner job.statusAddr
                  ⟨false, true, false⟩ = true
              · have he : (Hw.dropCirc E).memEn.eval σ = 1#1 :=
                  hen.mpr ⟨hk, ha⟩
                have ha' : ({ τr with mover := none } : MachineState).domCovers
                    job.owner job.statusAddr ⟨false, true, false⟩ = true := ha
                rw [if_pos ha', if_pos he]
                obtain ⟨had, hda⟩ := hport.2 he
                rw [had, hda]
                unfold Hw.dropCirc Hw.sweepMem
                simp only [Act.run, refill_pres_mem m σ "mem" b.toNat 32,
                  hmemR]
                by_cases hb : b = job.statusAddr
                · subst b
                  simp only [MemEnv.set]
                  simp [Expr.eval, job]
                · have hbn : b.toNat ≠ job.statusAddr.toNat :=
                    fun h => hb (BitVec.eq_of_toNat_eq h)
                  simp only [MemEnv.set]
                  rw [if_neg (fun h => hbn h.2),
                    refill_pres_mem m σ "mem" b.toNat 32]
                  rw [if_neg hb]
              · have he : ¬((Hw.dropCirc E).memEn.eval σ = 1#1) :=
                  fun h => ha (hen.mp h).2
                have ha' : ¬(({ τr with mover := none } : MachineState).domCovers
                    job.owner job.statusAddr ⟨false, true, false⟩ = true) := ha
                rw [if_neg ha', if_neg he,
                  refill_pres_mem m σ "mem" b.toNat 32]
                exact (hmemR b).symm
            · simp only
              have he : ¬((Hw.dropCirc E).memEn.eval σ = 1#1) :=
                fun h => hk (hen.mp h).1
              rw [if_neg hk, if_neg he,
                refill_pres_mem m σ "mem" b.toNat 32]
              exact (hmemR b).symm
          · have habs : Hw.absMover σ = none := absMover_none σ hv
            rw [habs]
            simp only
            have he : ¬((Hw.dropCirc E).memEn.eval σ = 1#1) := by
              intro h
              have hm : (Hw.movKilledE (fun dm sl =>
                  Hw.killedByCoreE dm sl)).eval σ = 1#1 := by
                unfold Hw.dropCirc Hw.sweepMem at h
                have hd := (andAll_eval σ _).mp h _
                  (List.mem_cons_of_mem _ (List.mem_cons_self ..))
                exact (by
                  have hEq : (Hw.movKilledE (Hw.dropKilled E)).eval σ =
                      (Hw.movKilledE (fun dm sl =>
                        Hw.killedByCoreE dm sl)).eval σ := by
                    rw [movKilledE_drop_eval σ E hkills]
                    unfold Hw.movKilledE
                    rfl
                  rwa [hEq] at hd)
              simpa [habs] using
                (movKilledE_drop_iff σ E S hslot hkills).mp hm
            rw [if_neg he, refill_pres_mem m σ "mem" b.toNat 32]
            exact (hmemR b).symm
        have href0 : ref =
            ⟨E, S, (τ0.doms E).slotGen S⟩ := by
          have hgen : (τ0.doms E).slotGen S =
              HWv.extractLsb' 4 8 := by
            unfold τ0
            rw [setDom_doms_same, refillPhase_slotGen]
            change σ.regs (Hw.dgen E S) 8 = _
            exact hlv.2.1
          unfold ref
          rw [hgen]
        have hstruct : τs.clearSlot E S =
            dropStructSpecArm τ0 E S := by
          unfold τs dropStructSpecArm
          rw [href0]
          rfl
        have hτ0cap : ∀ d s g,
            (τ0.doms d).liveCap s g =
              ((Hw.abs σ).doms d).liveCap s g := by
          intro d s g
          unfold τ0 DomainState.liveCap
          by_cases hd : d = E
          · subst d
            simp [MachineState.setDom]
          · simp [MachineState.setDom,
              Loom.Fun.update_ne _ _ _ _ hd]
        have hkind : ∀ d s g, ¬(d = E ∧ s = S) →
            Option.map CapEntry.kind ((τ2.doms d).liveCap s g) =
              Option.map CapEntry.kind
                (((Hw.abs σ).doms d).liveCap s g) := by
          intro d s g hout
          have hpost : (τ2.doms d).liveCap s g =
              (((τs.clearSlot E S).doms d).liveCap s g) := by
            unfold τ2 τm τr DomainState.liveCap
            by_cases hd : d = E
            · subst d
              simp [MachineState.setDom]
            · simp [MachineState.setDom,
                Loom.Fun.update_ne _ _ _ _ hd]
          rw [hpost, hstruct]
          exact (dropStructSpecArm_liveKind τ0 E S d s g hout).trans
            (congrArg (Option.map CapEntry.kind) (hτ0cap d s g))
        have hjob : τ2.mover =
            match Hw.absMover σ with
            | none => none
            | some job =>
                if (job.src.dom = E ∧ job.src.slot = S) ∨
                    (job.dst.dom = E ∧ job.dst.slot = S)
                then none else some job := by
          have hsweep := sweepMover_drop_mover (Hw.abs σ) τr E S
            hmoverR hliveR (moverEndpoints_live hwfσ)
          simpa [τ2, τm] using hsweep
        have hregions2 : ∀ d : DomainId,
            (τ2.doms d).regions = (τr.doms d).regions := by
          intro d
          unfold τ2 τm
          by_cases hd : d = E
          · subst d
            rw [setDom_doms_same, setReg_regions, sweepMover_doms]
          · rw [setDom_doms_ne _ _ _ _ hd, sweepMover_doms]
        have hauth2 : ∀ (ow : Expr 2) (sa : Expr 12),
            ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
              (List.finRange numRegions).map fun r =>
                Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
                  Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                    ⟨false, true, false⟩])).eval σ = 1#1) ↔
              τ2.domCovers (finOfBv (by decide) (ow.eval σ))
                (sa.eval σ) ⟨false, true, false⟩ = true := by
          intro ow sa
          rw [hauthR ow sa]
          rw [MachineState.domCovers, MachineState.domCovers]
          simp only [hregions2]
        have hsw2 : ∀ job, Hw.absMover σ = some job →
            ¬((job.src.dom = E ∧ job.src.slot = S) ∨
              (job.dst.dom = E ∧ job.dst.slot = S)) →
            ∀ sc : Expr 12, Expr.eval σ
              (((List.finRange numDomains).foldr
                (fun d acc' =>
                  Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d,
                      Hw.isMn "sw", Hw.domCoversE d
                        (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                        ⟨false, true, false⟩,
                      .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                        0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
                (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
          intro job habs hk sc
          rw [srcWord_quiescent σ hswz sc]
          change σ.mems "mem" (sc.eval σ).toNat 32 =
            τm.mem (sc.eval σ)
          rw [hsweepMem, show (Hw.abs σ).mover = Hw.absMover σ from rfl,
            habs]
          simp only
          rw [if_neg hk, hmemR]
        exact moverAct_mem_drop σ
          ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)) τ2 E S
          hslot hkills hnew hkind hjob hauth2 hcoreMem hsw2
      · rw [← hspec, corePhase_cycle, refillPhase_cycle]
        rfl
      · rw [← hspec, hcore0, Machines.Lnp64u.Wip.retire_inflight]
    · have hcls0 : ¬((Hw.dropSel E).clsOk.eval σ = 1#1) := by
        rw [hclsE]
        intro h
        by_cases hx : (σ.regs (Hw.dcapKind E S) 32).extractLsb' 0 1 =
            HWv.extractLsb' 12 1
        · exact hbit ((extract1_eq_iff (σ.regs (Hw.dcapKind E S) 32)
            HWv 0 12).mp hx).symm
        · rw [if_neg hx] at h
          exact absurd h (by decide)
      have hdecF : decide ((Handle.decode HWv).cls = e.kind.cls) = false := by
        apply decide_eq_false
        intro hc
        apply hbit
        unfold e at hc
        exact (cls_eq_iff_bits HWv (σ.regs (Hw.dcapKind E S) 32)).mp hc
      have hbad : ∀ d : DomainId, d = E → (Hw.dropOkE d).eval σ = 0#1 := by
        intro d hd; subst d
        unfold Hw.dropOkE Hw.okOf Hw.dropChecks Hw.andAll
        change ~~~(~~~((Hw.dropSel E).live.eval σ)) &&&
          ~~~(~~~((Hw.dropSel E).clsOk.eval σ)) = 0#1
        rw [hliv1, bv1_ne_one.mp hcls0]
        decide
      have hin : Inert σ := Inert.of_failed_drop σ E hret hif hdmn hrev
        hcall hreturn hbad hnew
      have hcoremem := hcoremem_of_dropOk_zero (hbad E rfl)
      refine retire_err_common_mem m hwfm hfit σ hsync hifv hcl hin
        hmapz hunmapz hswz hcoremem E rfl Errno.badCap.toWord ?_ ?_
      · intro acc
        rw [hsel acc,
          if_neg (show ¬((Expr.not (Hw.dropSel E).live).eval σ = 1#1)
            from by
              show ¬(~~~((Hw.dropSel E).live.eval σ) = 1#1)
              rw [hliv1]
              decide),
          if_pos (show (Expr.not (Hw.dropSel E).clsOk).eval σ = 1#1
            from by
              show ~~~((Hw.dropSel E).clsOk.eval σ) = 1#1
              rw [bv1_ne_one.mp hcls0]
              decide)]
        rfl
      · rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure, hRD, hlcS]
        rw [hdecF]
        rfl

end Machines.Lnp64u.Theorems.RMC
