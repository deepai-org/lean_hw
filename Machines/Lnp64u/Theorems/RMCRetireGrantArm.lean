-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGrantFrame

/-!
# R-MC retirement: full mem_grant arm

The error/spec ladder and full-state square, specialized from the proved
cap_dup install arm and using the two-domain grant abstraction.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

private theorem ifv_notin_grantX (e : DomainId) :
    (("if_v" : String), (1 : Nat)) ∉
      (Hw.seqAll
        [ Hw.seqAll ((List.finRange numDomains).map fun c =>
            .ite (.eq (Hw.descTgt (Hw.readReg e Hw.rs2E)) (Hw.dLit c))
              (Hw.installA c (Hw.freeSlotIdx c)
                (Hw.narrowKindE (Hw.grantSel e).kindW
                  (Hw.readReg e Hw.rs2E))
                (.lit 1) (Hw.freeCellIdx c)
                (Hw.encRefE (Hw.dLit e) (Hw.grantSel e).slot
                  (Hw.grantSel e).gen))
              .skip),
          Hw.writeReg e Hw.rdE (Hw.muxFin (fun c =>
            Hw.handleE (Hw.freeSlotIdx c)
              (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
            (Hw.descTgt (Hw.readReg e Hw.rs2E))),
          Hw.pcAdvA e ]).regWrites := by
  fin_cases e <;> decide +kernel

theorem square_retire_grant (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 19#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (19#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (19#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hdupmn : (Hw.isMn "mem_grant").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "mem_grant" = 19#6).symm
  have hret := retiringE_one σ hifv hcl
  have hin : Inert σ := Inert.of_benign7 σ (fun mn' hmn' =>
    isMn_ne_of_opc σ mn' 19#6 hopc
      ((by decide +kernel : ∀ mn' ∈ ["cap_drop", "cap_revoke", "gate_call",
        "gate_return", "move"], (19#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn'))
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 19#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 19#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 19#6 hopc (by decide +kernel))
  have hben5 : ∀ mn ∈ memMns, (Hw.isMn mn).eval σ ≠ 1#1 := fun mn hmn =>
    isMn_ne_of_opc σ mn 19#6 hopc
      ((by decide +kernel : ∀ mn ∈ memMns, (19#6 : BitVec 6)
        ≠ Hw.opcodeOf mn) mn hmn)
  have hselC := retireFor_sel_of_opc σ E "mem_grant" 19#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨Hw.ladder E (Hw.grantChecks E) (Hw.seqAll
      [ Hw.seqAll ((List.finRange numDomains).map fun c =>
          .ite (.eq (Hw.descTgt (Hw.readReg E Hw.rs2E)) (Hw.dLit c))
            (Hw.installA c (Hw.freeSlotIdx c)
              (Hw.narrowKindE (Hw.grantSel E).kindW
                (Hw.readReg E Hw.rs2E))
              (.lit 1) (Hw.freeCellIdx c)
              (Hw.encRefE (Hw.dLit E) (Hw.grantSel E).slot
                (Hw.grantSel E).gen))
            .skip),
        Hw.writeReg E Hw.rdE (Hw.muxFin (fun c =>
          Hw.handleE (Hw.freeSlotIdx c)
            (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
          (Hw.descTgt (Hw.readReg E Hw.rs2E))),
        Hw.pcAdvA E ]),
      .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
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
  have hG1 : ∀ g, (refillPhase m (Hw.abs σ)).gates g
      = Hw.absGate ((Hw.refillAct m).run σ σ) g := by
    intro g
    rw [← habs1]
    rfl
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  set HWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hHWv
  set DWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs2 with hDWv
  set T : DomainId := Machines.Lnp64u.Isa.descDom DWv with hTdef
  have htarget : Machines.Lnp64u.Isa.descDom
      ((Hw.readReg E Hw.rs2E).eval σ) = T := by
    rw [hR2]
  have hslotMux : (Hw.muxFin (fun c => Hw.freeSlotV c)
      (Hw.descTgt (Hw.readReg E Hw.rs2E))).eval σ =
        (Hw.freeSlotV T).eval σ := by
    rw [grant_freeSlotV_eval, htarget]
  have hcellMux : (Hw.muxFin (fun c => Hw.freeCellV c)
      (Hw.descTgt (Hw.readReg E Hw.rs2E))).eval σ =
        (Hw.freeCellV T).eval σ := by
    rw [grant_freeCellV_eval, htarget]
  have hSPr : ∀ rs : RegId,
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg rs
        = ((Hw.abs σ).doms E).reg rs := fun rs => specReg_bridge m σ E rs
  have hSval : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (HWv.extractLsb' 0 4)).val
      = (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := by
    rw [hR1]
    rfl
  have hlivE := capSel_live_eval σ E (Hw.readReg E Hw.rs1E) _ hSval
  rw [hR1] at hlivE
  have hkwE : (Hw.grantSel E).kindW.eval σ
      = σ.regs (Hw.dcapKind E (finOfBv (by decide)
          (HWv.extractLsb' 0 4))) 32 :=
    capSel_kindW_eval σ E (Hw.readReg E Hw.rs1E) _ hSval
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ))
      = retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hDO : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (match ((SpecM.reg E (operandsOf W).rs1 >>= fun hw =>
          SpecM.reg E (operandsOf W).rs2 >>= fun dw =>
          Machines.Lnp64u.Isa.capLive E hw >>= fun x =>
          match x with
          | (s, g, e) =>
            match e.kind with
            | .gate _ => SpecM.raise .badCap
            | .mem base len perms =>
                Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
                Machines.Lnp64u.Isa.allocDerived
                  (Machines.Lnp64u.Isa.descDom dw) kind ⟨E, s, g⟩ >>=
                  fun h => SpecM.setReg E (operandsOf W).rd h
            )
          (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))) with
        | .ok _ σ' => σ'
        | .err e σ' =>
            σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault fl => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E fl) := by
    have hfind : isa.find? (fun d => d.opcode == (19#6 : BitVec 6)) =
        some (Machines.Lnp64u.Isa.system.get ⟨3, by decide⟩) := by
      rfl
    have hexec :
        (Machines.Lnp64u.Isa.system.get ⟨3, by decide⟩).sem.exec =
          (fun c => do
            let hw ← SpecM.reg c.d c.op.rs1
            let dw ← SpecM.reg c.d c.op.rs2
            let (s, g, e) ← Machines.Lnp64u.Isa.capLive c.d hw
            match e.kind with
            | .gate _ => SpecM.raise .badCap
            | .mem base len perms => do
              let kind ← Machines.Lnp64u.Isa.narrow base len perms dw
              let h ← Machines.Lnp64u.Isa.allocDerived
                (Machines.Lnp64u.Isa.descDom dw) kind ⟨c.d, s, g⟩
              SpecM.setReg c.d c.op.rd h) := by
      rfl
    rw [retire_of_decode_some _ E W _ (hdec.trans hfind)]
    rw [hexec]
    rfl
  have hladder : ∀ acc : Loom.Hw.St, (Hw.retireFor E).run σ acc
      = (if (Expr.not (Hw.grantSel E).live).eval σ = 1#1 then
          (Hw.respA E (.err .staleHandle)).run σ acc
        else if (Expr.not (Expr.and (Hw.grantSel E).clsOk
            (Hw.kIsMem (Hw.grantSel E).kindW))).eval σ = 1#1 then
          (Hw.respA E (.err .badCap)).run σ acc
        else if (Expr.and (.lit 1)
            (Expr.ult (.zext (Hw.kLen (Hw.grantSel E).kindW) 14)
              (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
                (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1 then
          (Hw.respA E (.err .outOfRange)).run σ acc
        else if (Expr.and (.lit 1) (Expr.not (Expr.ult
            (.add (.zext (Hw.kBase (Hw.grantSel E).kindW) 13)
              (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13))
            (.lit 4096)))).eval σ = 1#1 then
          (Hw.respA E (.err .outOfRange)).run σ acc
        else if (Expr.and (.lit 1) (Hw.orAll
            [.and (Hw.descR (Hw.readReg E Hw.rs2E))
                (.not (Hw.kR (Hw.grantSel E).kindW)),
              .and (Hw.descW (Hw.readReg E Hw.rs2E))
                (.not (Hw.kW (Hw.grantSel E).kindW)),
              .and (Hw.descX (Hw.readReg E Hw.rs2E))
                (.not (Hw.kX (Hw.grantSel E).kindW))])).eval σ = 1#1 then
          (Hw.respA E (.err .permDenied)).run σ acc
        else if (Expr.and (.lit 1)
            (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E))
              (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ = 1#1 then
          (Hw.respA E (.err .permDenied)).run σ acc
        else if (Expr.not (Hw.muxFin (fun c => Hw.freeSlotV c)
            (Hw.descTgt (Hw.readReg E Hw.rs2E)))).eval σ = 1#1 then
          (Hw.respA E (.err .slotOccupied)).run σ acc
        else if (Expr.not (Hw.muxFin (fun c => Hw.freeCellV c)
            (Hw.descTgt (Hw.readReg E Hw.rs2E)))).eval σ = 1#1 then
          (Hw.respA E (.err .noLineage)).run σ acc
        else (Hw.seqAll
          [ Hw.seqAll ((List.finRange numDomains).map fun c =>
              .ite (.eq (Hw.descTgt (Hw.readReg E Hw.rs2E)) (Hw.dLit c))
                (Hw.installA c (Hw.freeSlotIdx c)
                  (Hw.narrowKindE (Hw.grantSel E).kindW
                    (Hw.readReg E Hw.rs2E))
                  (.lit 1) (Hw.freeCellIdx c)
                  (Hw.encRefE (Hw.dLit E) (Hw.grantSel E).slot
                    (Hw.grantSel E).gen))
                .skip),
            Hw.writeReg E Hw.rdE (Hw.muxFin (fun c =>
              Hw.handleE (Hw.freeSlotIdx c)
                (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
              (Hw.descTgt (Hw.readReg E Hw.rs2E))),
            Hw.pcAdvA E ]).run σ acc) := by
    intro acc
    rw [hselC acc]
    rfl
  have hRD : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1 = HWv :=
    hSPr (operandsOf W).rs1
  have hRD2 : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2 = DWv :=
    hSPr (operandsOf W).rs2
  by_cases hlv : σ.regs (Hw.dcapV E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1
      ∧ σ.regs (Hw.dgen E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 8 = HWv.extractLsb' 4 8
      ∧ HWv.extractLsb' 4 8 ≠ 0
  case neg =>
    -- stale handle
    have hlive0 : ¬((Hw.grantSel E).live.eval σ = 1#1) :=
      fun hc => hlv (hlivE.mp hc)
    have hlcN : ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = none := by
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_neg hlv
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.staleHandle.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_pos (show (Expr.not (Hw.grantSel E).live).eval σ = 1#1 from by
          show ~~~((Hw.grantSel E).live.eval σ) = 1#1
          rw [bv1_ne_one.mp hlive0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcN]
      rfl
  case pos =>
  have hliv1 : (Hw.grantSel E).live.eval σ = 1#1 := hlivE.mpr hlv
  have hlcS : ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
      (Handle.decode HWv).slot (Handle.decode HWv).gen
      = some { kind := Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)
               lineage := if σ.regs (Hw.dcapLinV E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1
                 then some (finOfBv (by decide)
                   (σ.regs (Hw.dcapLin E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 4))
                 else none } := by
    rw [specLiveCap_bridge, abs_liveCap]
    exact if_pos hlv
  obtain ⟨ce, hlcS', hcek⟩ :
      ∃ c0 : CapEntry, ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = some c0
      ∧ c0.kind = Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) := ⟨_, hlcS, rfl⟩
  have hclsE2 : (Hw.grantSel E).clsOk.eval σ
      = (if (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 0 1 = HWv.extractLsb' 12 1
        then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.grantSel E).kindW.eval σ).extractLsb' 0 1
        = ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 12 1
      then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwE, hR1]
  by_cases hbit : HWv.getLsbD 12 = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 0
  case neg =>
    -- class mismatch
    have hcls0 : ¬((Hw.grantSel E).clsOk.eval σ = 1#1) := by
      rw [hclsE2]
      intro h
      by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 0 1 = HWv.extractLsb' 12 1
      · exact hbit ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) HWv 0 12).mp hcx).symm
      · rw [if_neg hcx] at h
        exact absurd h (by decide)
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_pos (show (Expr.not (Expr.and (Hw.grantSel E).clsOk
            (Hw.kIsMem (Hw.grantSel E).kindW))).eval σ = 1#1 from by
          show ~~~((Hw.grantSel E).clsOk.eval σ &&&
            (Hw.kIsMem (Hw.grantSel E).kindW).eval σ) = 1#1
          rw [bv1_ne_one.mp hcls0]
          generalize (Hw.kIsMem (Hw.grantSel E).kindW).eval σ = b
          revert b
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [show (decide ((Handle.decode HWv).cls
          = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).cls)) = false from decide_eq_false
        (fun hA => hbit ((cls_eq_iff_bits HWv (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mp hA))]
      rfl
  case pos =>
  have hcls1 : (Hw.grantSel E).clsOk.eval σ = 1#1 := by
    rw [hclsE2]
    rw [if_pos ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) HWv 0 12).mpr hbit.symm)]
  have hdecT : (decide ((Handle.decode HWv).cls
      = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).cls)) = true :=
    decide_eq_true ((cls_eq_iff_bits HWv (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mpr hbit)
  by_cases hmem : (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 0 = false
  case neg =>
    -- A gate parent is rejected by mem_grant's second check.
    have hgatebit :
        (σ.regs (Hw.dcapKind E (finOfBv (by decide)
          (HWv.extractLsb' 0 4))) 32).getLsbD 0 = true := by
      cases h : (σ.regs (Hw.dcapKind E (finOfBv (by decide)
        (HWv.extractLsb' 0 4))) 32).getLsbD 0
      · exact absurd h hmem
      · rfl
    have hgate : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide)
        (HWv.extractLsb' 0 4))) 32) =
        .gate (finOfBv (by decide) ((σ.regs (Hw.dcapKind E
          (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 2)) :=
      (decKind_gate_iff _).mp hgatebit
    have hkm0 : (Hw.kIsMem (Hw.grantSel E).kindW).eval σ = 0#1 := by
      show (if ((Hw.grantSel E).kindW.eval σ).extractLsb' 0 1
          = (Expr.lit 0).eval σ then (1#1 : BitVec 1) else 0#1) = 0#1
      rw [show ((Expr.lit 0 : Expr 1)).eval σ = 0#1 from rfl]
      simp only [hkwE]
      rw [if_neg (fun hx => by
        have hz := (extract1_eq_zero_iff (σ.regs (Hw.dcapKind E
          (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 0).mp hx
        rw [hz] at hgatebit
        exact absurd hgatebit (by decide))]
    have hbad : (Expr.not (Expr.and (Hw.grantSel E).clsOk
        (Hw.kIsMem (Hw.grantSel E).kindW))).eval σ = 1#1 := by
      show ~~~((Hw.grantSel E).clsOk.eval σ &&&
        (Hw.kIsMem (Hw.grantSel E).kindW).eval σ) = 1#1
      rw [hcls1, hkm0]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_pos hbad]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2, hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek, hgate, SpecM.raise]
      rfl
  case pos =>
  -- memory kind: narrowing applies
  have hmk : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) = .mem ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12)
      ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13) (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) :=
    (decKind_mem_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mp hmem
  have hkm1 : (Hw.kIsMem (Hw.grantSel E).kindW).eval σ = 1#1 := by
    show (if ((Hw.grantSel E).kindW.eval σ).extractLsb' 0 1
        = (Expr.lit 0).eval σ then (1#1 : BitVec 1) else 0#1) = 1#1
    rw [show ((Expr.lit 0 : Expr 1)).eval σ = 0#1 from rfl]
    simp only [hkwE]
    rw [if_pos ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 0).mpr hmem)]
  have hbad0 : ¬((Expr.not (Expr.and (Hw.grantSel E).clsOk
      (Hw.kIsMem (Hw.grantSel E).kindW))).eval σ = 1#1) := by
    show ¬(~~~((Hw.grantSel E).clsOk.eval σ &&&
      (Hw.kIsMem (Hw.grantSel E).kindW).eval σ) = 1#1)
    rw [hcls1, hkm1]
    decide
  have hcheck_mem : ∀ p : Expr 1,
      (Expr.and (.lit 1) p).eval σ =
        (Expr.and (Hw.kIsMem (Hw.grantSel E).kindW) p).eval σ := by
    intro p
    show (1#1 &&& p.eval σ) =
      ((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&& p.eval σ)
    rw [hkm1]
  have hklenE : (Hw.kLen (Hw.grantSel E).kindW).eval σ
      = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13 := by
    show ((Hw.grantSel E).kindW.eval σ).extractLsb' 13 13 = _
    rw [hkwE]
  have hkbaseE : (Hw.kBase (Hw.grantSel E).kindW).eval σ
      = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12 := by
    show ((Hw.grantSel E).kindW.eval σ).extractLsb' 1 12 = _
    rw [hkwE]
  have hoffE : (Hw.descOffE (Hw.readReg E Hw.rs2E)).eval σ = DWv.extractLsb' 5 12 := by
    show ((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12 = _
    rw [hR2]
  have hlenE : (Hw.descLenE (Hw.readReg E Hw.rs2E)).eval σ = DWv.extractLsb' 17 13 := by
    show ((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 17 13 = _
    rw [hR2]
  -- range check
  by_cases hr1 : ((DWv.extractLsb' 5 12).toNat
      + (DWv.extractLsb' 17 13).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)
  case neg =>
    -- narrow out of range
    have hc3 : (Expr.and (Hw.kIsMem (Hw.grantSel E).kindW) (Expr.ult (.zext (Hw.kLen (Hw.grantSel E).kindW) 14) (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14) (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1 := by
      show ((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&&
        (Expr.ult (.zext (Hw.kLen (Hw.grantSel E).kindW) 14)
          (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
            (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ) = 1#1
      rw [hkm1]
      rw [(ultE_eval _ _ σ).mpr (by
        show (((Hw.kLen (Hw.grantSel E).kindW).eval σ).setWidth 14).toNat
          < ((((Hw.descOffE (Hw.readReg E Hw.rs2E)).eval σ).setWidth 14)
            + (((Hw.descLenE (Hw.readReg E Hw.rs2E)).eval σ).setWidth 14)).toNat
        rw [hklenE, hoffE, hlenE, toNat_setWidth_le (by omega)]
        rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
          toNat_setWidth_le (by omega)]
        have b1 := (DWv.extractLsb' 5 12).isLt
        have b2 := (DWv.extractLsb' 17 13).isLt
        rw [Nat.mod_eq_of_lt (by omega)]
        omega)]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.outOfRange.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg hbad0,
        if_pos (by rw [hcheck_mem]; exact hc3)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = false from
        decide_eq_false hr1]
      rfl
  case pos =>
  have hc3z : ¬((Expr.and (Hw.kIsMem (Hw.grantSel E).kindW) (Expr.ult (.zext (Hw.kLen (Hw.grantSel E).kindW) 14) (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14) (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&&
      (Expr.ult (.zext (Hw.kLen (Hw.grantSel E).kindW) 14)
        (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
          (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ = 1#1)
    rw [bv1_ne_one.mp (show ¬((Expr.ult
        (.zext (Hw.kLen (Hw.grantSel E).kindW) 14)
        (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
          (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ = 1#1) from by
      intro hc
      have h2 : ((((Hw.grantSel E).kindW.eval σ).extractLsb' 13 13
          ).setWidth 14).toNat
          < (((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
            ).setWidth 14)
            + ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 17 13
              ).setWidth 14)).toNat :=
        (ultE_eval _ _ σ).mp hc
      rw [hkwE, hR2] at h2
      rw [toNat_setWidth_le (by omega), BitVec.toNat_add,
        toNat_setWidth_le (by omega), toNat_setWidth_le (by omega)] at h2
      have b1 := (DWv.extractLsb' 5 12).isLt
      have b2 := (DWv.extractLsb' 17 13).isLt
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      omega)]
    generalize (Hw.kIsMem (Hw.grantSel E).kindW).eval σ = b
    revert b
    decide
  -- one-bit extract as ofBool (for the perm-bit walks)
  have hEx1 : ∀ {n : Nat} (x : BitVec n) (i : Nat),
      x.extractLsb' i 1 = BitVec.ofBool (x.getLsbD i) := by
    intro n x i
    cases h : x.getLsbD i
    · rw [(extract1_eq_zero_iff x i).mpr h]; rfl
    · rw [(extract1_eq_one_iff x i).mpr h]; rfl
  -- no-wrap check
  by_cases hr2 : (((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
      + (DWv.extractLsb' 5 12).toNat < 4096)
  case neg =>
    -- narrowed base out of physical memory
    have hult0 : ¬((Expr.ult (.add (.zext (Hw.kBase (Hw.grantSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ = 1#1) := by
      intro hc
      have h2 : ((((Hw.grantSel E).kindW.eval σ).extractLsb' 1 12
          ).setWidth 13
          + (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
            ).setWidth 13).toNat
          < ((4096 : BitVec 13)).toNat :=
        (ultE_eval _ _ σ).mp hc
      rw [hkwE, hR2] at h2
      rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
        toNat_setWidth_le (by omega)] at h2
      have b1 := ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).isLt
      have b2 := (DWv.extractLsb' 5 12).isLt
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      exact hr2 (by
        have h3 : ((4096 : BitVec 13)).toNat = 4096 := rfl
        omega)
    have hc4 : (Expr.and (Hw.kIsMem (Hw.grantSel E).kindW)
        (Expr.not (Expr.ult (.add (.zext (Hw.kBase (Hw.grantSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)))).eval σ = 1#1 := by
      show ((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&&
        ~~~((Expr.ult (.add (.zext (Hw.kBase (Hw.grantSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ)) = 1#1
      rw [hkm1, bv1_ne_one.mp hult0]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.outOfRange.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg hbad0,
        if_neg (by rw [hcheck_mem]; exact hc3z),
        if_pos (by rw [hcheck_mem]; exact hc4)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = false from decide_eq_false hr2]
      rfl
  case pos =>
  have hult1 : (Expr.ult (.add (.zext (Hw.kBase (Hw.grantSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ = 1#1 := by
    rw [ultE_eval]
    show ((((Hw.grantSel E).kindW.eval σ).extractLsb' 1 12).setWidth 13
      + (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
        ).setWidth 13).toNat < ((4096 : BitVec 13)).toNat
    rw [hkwE, hR2]
    rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
      toNat_setWidth_le (by omega)]
    have b1 := ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).isLt
    have b2 := (DWv.extractLsb' 5 12).isLt
    rw [Nat.mod_eq_of_lt (by omega)]
    show _ < (4096 : BitVec 13).toNat
    have h3 : ((4096 : BitVec 13)).toNat = 4096 := rfl
    omega
  have hc4z : ¬((Expr.and (Hw.kIsMem (Hw.grantSel E).kindW)
      (Expr.not (Expr.ult (.add (.zext (Hw.kBase (Hw.grantSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&&
      ~~~((Expr.ult (.add (.zext (Hw.kBase (Hw.grantSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ) = 1#1)
    rw [hult1]
    generalize (Hw.kIsMem (Hw.grantSel E).kindW).eval σ = b
    revert b
    decide
  -- permission checks
  have hpermsOr : ((Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.grantSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.grantSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.grantSel E).kindW))]).eval σ = 1#1)
      ↔ ¬((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) = true) := by
    show ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 2 1 &&&
        ~~~(((Hw.grantSel E).kindW.eval σ).extractLsb' 26 1)) |||
      ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 3 1 &&&
        ~~~(((Hw.grantSel E).kindW.eval σ).extractLsb' 27 1)) |||
       (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 4 1 &&&
        ~~~(((Hw.grantSel E).kindW.eval σ).extractLsb' 28 1)))) = 1#1 ↔ _
    rw [hkwE, hR2]
    rw [show (Machines.Lnp64u.Isa.descPerms DWv)
        = ⟨DWv.getLsbD 2, DWv.getLsbD 3, DWv.getLsbD 4⟩ from rfl]
    rw [show (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))
        = ⟨(σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 26, (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 27, (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 28⟩ from by
      show (⟨((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 0,
        ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 1,
        ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 2⟩ : Perms) = _
      simp [BitVec.getLsbD_extractLsb']]
    rw [hEx1 DWv 2, hEx1 DWv 3, hEx1 DWv 4,
      hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 26, hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 27, hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 28]
    cases DWv.getLsbD 2 <;> cases DWv.getLsbD 3 <;> cases DWv.getLsbD 4 <;>
      cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 26 <;> cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 27 <;>
      cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 28 <;> simp [Perms.le]
  by_cases hr3 : ((Machines.Lnp64u.Isa.descPerms DWv).le
      (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) = true)
  case neg =>
    -- permission escalation
    have hc5 : (Expr.and (Hw.kIsMem (Hw.grantSel E).kindW) (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.grantSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.grantSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.grantSel E).kindW))])).eval σ
        = 1#1 := by
      show ((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&&
        (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.grantSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.grantSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.grantSel E).kindW))]).eval σ) = 1#1
      rw [hkm1, hpermsOr.mpr hr3]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.permDenied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg hbad0,
        if_neg (by rw [hcheck_mem]; exact hc3z),
        if_neg (by rw [hcheck_mem]; exact hc4z),
        if_pos (by rw [hcheck_mem]; exact hc5)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = false from by
        cases h : ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)))
        · rfl
        · exact absurd h hr3]
      rfl
  case pos =>
  have hc5z : ¬((Expr.and (Hw.kIsMem (Hw.grantSel E).kindW)
      (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.grantSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.grantSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.grantSel E).kindW))])).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&&
      (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.grantSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.grantSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.grantSel E).kindW))]).eval σ = 1#1)
    rw [bv1_ne_one.mp (fun hc => (hpermsOr.mp hc) hr3)]
    generalize (Hw.kIsMem (Hw.grantSel E).kindW).eval σ = b
    revert b
    decide
  -- W^X check
  have hwxOr : ((Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ = 1#1)
      ↔ ¬((Machines.Lnp64u.Isa.descPerms DWv).wx = true) := by
    show ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 3 1) &&&
      (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 4 1)) = 1#1 ↔ _
    rw [hR2]
    rw [show (Machines.Lnp64u.Isa.descPerms DWv)
        = ⟨DWv.getLsbD 2, DWv.getLsbD 3, DWv.getLsbD 4⟩ from rfl]
    rw [hEx1 DWv 3, hEx1 DWv 4]
    cases DWv.getLsbD 3 <;> cases DWv.getLsbD 4 <;> simp [Perms.wx]
  by_cases hr4 : ((Machines.Lnp64u.Isa.descPerms DWv).wx = true)
  case neg =>
    -- W^X violation
    have hc6 : (Expr.and (Hw.kIsMem (Hw.grantSel E).kindW) (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ
        = 1#1 := by
      show ((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&&
        (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ) = 1#1
      rw [hkm1, hwxOr.mpr hr4]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.permDenied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg hbad0,
        if_neg (by rw [hcheck_mem]; exact hc3z),
        if_neg (by rw [hcheck_mem]; exact hc4z),
        if_neg (by rw [hcheck_mem]; exact hc5z),
        if_pos (by rw [hcheck_mem]; exact hc6)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = false from by
        cases h : ((Machines.Lnp64u.Isa.descPerms DWv).wx)
        · rfl
        · exact absurd h hr4]
      rfl
  case pos =>
  have hc6z : ¬((Expr.and (Hw.kIsMem (Hw.grantSel E).kindW)
      (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.grantSel E).kindW).eval σ &&&
      (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ = 1#1)
    rw [bv1_ne_one.mp (fun hc => absurd hr4 (fun h4 =>
      (hwxOr.mp hc) h4))]
    generalize (Hw.kIsMem (Hw.grantSel E).kindW).eval σ = b
    revert b
    decide
  -- Free-resource bridges for the descriptor-selected target domain.
  have hcapsB : ∀ s : Slot,
      (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 }))).doms T).caps s =
        ((Hw.abs σ).doms T).caps s := fun s => by
    unfold MachineState.setDom
    dsimp only
    by_cases hTE : T = E
    · rw [hTE, Loom.Fun.update_same]
      exact congrFun (refillPhase_caps m (Hw.abs σ) E) s
    · rw [Loom.Fun.update_ne _ _ _ _ hTE]
      exact congrFun (refillPhase_caps m (Hw.abs σ) T) s
  have hgenB : ∀ s : Slot,
      (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 }))).doms T).slotGen s =
        ((Hw.abs σ).doms T).slotGen s := fun s => by
    unfold MachineState.setDom
    dsimp only
    by_cases hTE : T = E
    · rw [hTE, Loom.Fun.update_same]
      exact congrFun (refillPhase_slotGen m (Hw.abs σ) E) s
    · rw [Loom.Fun.update_ne _ _ _ _ hTE]
      exact congrFun (refillPhase_slotGen m (Hw.abs σ) T) s
  have hlinB : ∀ l : LineageId,
      (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 }))).doms T).lineage l =
        ((Hw.abs σ).doms T).lineage l := fun l => by
    unfold MachineState.setDom
    dsimp only
    by_cases hTE : T = E
    · rw [hTE, Loom.Fun.update_same]
      exact congrFun (refillPhase_lineage m (Hw.abs σ) E) l
    · rw [Loom.Fun.update_ne _ _ _ _ hTE]
      exact congrFun (refillPhase_lineage m (Hw.abs σ) T) l
  have hfsB :
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 }))).freeSlot T =
        (Hw.abs σ).freeSlot T :=
    freeSlot_congr _ _ T hcapsB hgenB
  have hfcB :
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 }))).freeCell T =
        (Hw.abs σ).freeCell T :=
    freeCell_congr _ _ T hlinB
  cases hfs : (Hw.abs σ).freeSlot T with
  | none =>
    -- no free slot
    have hfsv0 : ¬((Hw.freeSlotV T).eval σ = 1#1) := fun hc => by
      have h2 := (freeSlotV_eval σ T).mp hc
      rw [hfs] at h2
      exact absurd h2 (by decide)
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.slotOccupied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg hbad0,
        if_neg (by rw [hcheck_mem]; exact hc3z),
        if_neg (by rw [hcheck_mem]; exact hc4z),
        if_neg (by rw [hcheck_mem]; exact hc5z),
        if_neg (by rw [hcheck_mem]; exact hc6z),
        if_pos (show (Expr.not (Hw.muxFin (fun c => Hw.freeSlotV c)
            (Hw.descTgt (Hw.readReg E Hw.rs2E)))).eval σ = 1#1 from by
          show ~~~((Hw.muxFin (fun c => Hw.freeSlotV c)
            (Hw.descTgt (Hw.readReg E Hw.rs2E))).eval σ) = 1#1
          rw [hslotMux, bv1_ne_one.mp hfsv0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = true from hr4]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [Machines.Lnp64u.Isa.allocDerived, SpecM.get, specM_bind,
        SpecM.raise, specM_pure]
      rw [hfsB.trans hfs]
      rfl
  | some NS =>
    have hfsv1 : (Hw.freeSlotV T).eval σ = 1#1 :=
      (freeSlotV_eval σ T).mpr (by rw [hfs]; rfl)
    cases hfc : (Hw.abs σ).freeCell T with
    | none =>
      -- no free lineage cell
      have hfcv0 : ¬((Hw.freeCellV T).eval σ = 1#1) := fun hc => by
        have h2 := (freeCellV_eval σ T).mp hc
        rw [hfc] at h2
        exact absurd h2 (by decide)
      refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
        hswz hben5 E rfl Errno.noLineage.toWord ?_ ?_
      · intro acc
        rw [hladder acc,
          if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1) from by
            show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
            rw [hliv1]
            decide),
        if_neg hbad0,
          if_neg (by rw [hcheck_mem]; exact hc3z),
          if_neg (by rw [hcheck_mem]; exact hc4z),
          if_neg (by rw [hcheck_mem]; exact hc5z),
          if_neg (by rw [hcheck_mem]; exact hc6z),
          if_neg (show ¬((Expr.not (Hw.muxFin (fun c => Hw.freeSlotV c)
              (Hw.descTgt (Hw.readReg E Hw.rs2E)))).eval σ = 1#1) from by
            show ¬(~~~((Hw.muxFin (fun c => Hw.freeSlotV c)
              (Hw.descTgt (Hw.readReg E Hw.rs2E))).eval σ) = 1#1)
            rw [hslotMux, hfsv1]
            decide),
          if_pos (show (Expr.not (Hw.muxFin (fun c => Hw.freeCellV c)
              (Hw.descTgt (Hw.readReg E Hw.rs2E)))).eval σ = 1#1 from by
            show ~~~((Hw.muxFin (fun c => Hw.freeCellV c)
              (Hw.descTgt (Hw.readReg E Hw.rs2E))).eval σ) = 1#1
            rw [hcellMux, bv1_ne_one.mp hfcv0]
            decide)]
        rfl
      · rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        simp only [hRD, hRD2]
        simp only [hlcS', hcek]
        rw [hdecT]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [hcek]
        simp only [hmk]
        simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
          SpecM.raise, specM_pure]
        rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
            + (Machines.Lnp64u.Isa.descLen DWv).toNat
            ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
          decide_eq_true hr1]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
            + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
            = true from decide_eq_true hr2]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
            (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = true from hr4]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [Machines.Lnp64u.Isa.allocDerived, SpecM.get, specM_bind,
          SpecM.raise, specM_pure]
        rw [hfsB.trans hfs]
        simp only [specM_bind, specM_pure]
        rw [hfcB.trans hfc]
        rfl
    | some NL =>
      -- install (mem kind)
      have hsidx : (Hw.freeSlotIdx T).eval σ = BitVec.ofNat 4 NS.val :=
        freeSlotIdx_eval σ T NS hfs
      have hlidx : (Hw.freeCellIdx T).eval σ = BitVec.ofNat 4 NL.val :=
        freeCellIdx_eval σ T NL hfc
      let S : Slot := finOfBv (by decide) (HWv.extractLsb' 0 4)
      let K : CapKind := .mem
        ((σ.regs (Hw.dcapKind E S) 32).extractLsb' 1 12 +
          Machines.Lnp64u.Isa.descOff DWv)
        (Machines.Lnp64u.Isa.descLen DWv)
        (Machines.Lnp64u.Isa.descPerms DWv)
      let P : CapRef := ⟨E, S, HWv.extractLsb' 4 8⟩
      let τ0 : MachineState :=
        ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })
      let G : Gen := (τ0.doms T).slotGen NS
      let V : BitVec 32 := Handle.encode ⟨NS, G, .mem⟩
      let τi : MachineState := (τ0.installDerived T NS NL K P).1
      let τ2 : MachineState := τi.setDom E
        (fun ds => ds.setReg (operandsOf W).rd V)
      have hkind : (Hw.narrowKindE (Hw.grantSel E).kindW
          (Hw.readReg E Hw.rs2E)).eval σ = Hw.encKind K := by
        rw [narrowKindE_pack, hkwE, hR2]
      have hparent : (Hw.encRefE (Hw.dLit E) (Hw.grantSel E).slot
          (Hw.grantSel E).gen).eval σ = Hw.encRef P := by
        simpa only [Hw.grantSel, hR1] using
          (encRefE_sel_eval σ E (Hw.readReg E Hw.rs1E))
      have hgenT : (Hw.genOfE T (Hw.freeSlotIdx T)).eval σ = G := by
        rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots)]
        have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
            ((Hw.freeSlotIdx T).eval σ) = NS := by
          rw [hsidx]
          exact finOfBv_ofNat4 (by decide) NS
        rw [hfin]
        unfold G τ0
        rw [hgenB NS]
        rfl
      have hval : (Hw.muxFin (fun c =>
          Hw.handleE (Hw.freeSlotIdx c)
            (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
          (Hw.descTgt (Hw.readReg E Hw.rs2E))).eval σ = V := by
        rw [grant_handle_mux_eval, htarget]
        rw [handleE_pack σ _ _ _ .mem (by rfl), hsidx, hgenT]
        show Handle.encode
          ⟨finOfBv (by decide) (BitVec.ofNat 4 NS.val), G, .mem⟩ = V
        rw [finOfBv_ofNat4]
      have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
        rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        simp only [hRD, hRD2, hlcS', hcek]
        rw [hdecT]
        simp only [reduceIte, specM_bind, specM_pure, hcek, hmk]
        simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
          SpecM.raise, specM_pure]
        rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
            + (Machines.Lnp64u.Isa.descLen DWv).toNat
            ≤ ((σ.regs (Hw.dcapKind E S) 32).extractLsb' 13 13).toNat))
            = true from decide_eq_true hr1]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show (decide (((σ.regs (Hw.dcapKind E S) 32).extractLsb'
            1 12).toNat + (Machines.Lnp64u.Isa.descOff DWv).toNat
            < memWords)) = true from decide_eq_true hr2]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
            (Hw.decPerms ((σ.regs (Hw.dcapKind E S) 32).extractLsb' 26 3)))
            = true from hr3]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show (Machines.Lnp64u.Isa.descPerms DWv).wx = true from hr4]
        simp only [reduceIte, specM_bind, specM_pure,
          Machines.Lnp64u.Isa.allocDerived, SpecM.get, SpecM.set,
          SpecM.modify, SpecM.raise]
        rw [hfsB.trans hfs]
        simp only [specM_bind, specM_pure]
        rw [hfcB.trans hfc]
        simp only [SpecM.set, SpecM.setReg, SpecM.modify, specM_bind,
          specM_pure]
        unfold τ2 τi V G K P S
        rfl
      let X : Act := Hw.seqAll
        [ Hw.seqAll ((List.finRange numDomains).map fun c =>
            .ite (.eq (Hw.descTgt (Hw.readReg E Hw.rs2E)) (Hw.dLit c))
              (Hw.installA c (Hw.freeSlotIdx c)
                (Hw.narrowKindE (Hw.grantSel E).kindW
                  (Hw.readReg E Hw.rs2E))
                (.lit 1) (Hw.freeCellIdx c)
                (Hw.encRefE (Hw.dLit E) (Hw.grantSel E).slot
                  (Hw.grantSel E).gen))
              .skip),
          Hw.writeReg E Hw.rdE (Hw.muxFin (fun c =>
            Hw.handleE (Hw.freeSlotIdx c)
              (Hw.genOfE c (Hw.freeSlotIdx c)) (.lit 0))
            (Hw.descTgt (Hw.readReg E Hw.rs2E))),
          Hw.pcAdvA E ]
      have hcoreR : ∀ (rn : String) (w : Nat),
          ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
            ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
              ((Hw.refillAct m).run σ σ)).regs rn w := by
        intro rn w
        rw [coreAct_run_retire_eq m σ _ hifv hcl,
          retireAct_run_regs σ _ E rfl rn w, hladder]
        rw [if_neg (show ¬((Expr.not (Hw.grantSel E).live).eval σ = 1#1)
            from by show ¬(~~~((Hw.grantSel E).live.eval σ) = 1#1)
                    rw [hliv1]; decide),
          if_neg hbad0,
          if_neg (by rw [hcheck_mem]; exact hc3z),
          if_neg (by rw [hcheck_mem]; exact hc4z),
          if_neg (by rw [hcheck_mem]; exact hc5z),
          if_neg (by rw [hcheck_mem]; exact hc6z),
          if_neg (show ¬((Expr.not (Hw.muxFin (fun c => Hw.freeSlotV c)
              (Hw.descTgt (Hw.readReg E Hw.rs2E)))).eval σ = 1#1)
            from by show ¬(~~~((Hw.muxFin (fun c => Hw.freeSlotV c)
                      (Hw.descTgt (Hw.readReg E Hw.rs2E))).eval σ) = 1#1)
                    rw [hslotMux, hfsv1]; decide),
          if_neg (show ¬((Expr.not (Hw.muxFin (fun c => Hw.freeCellV c)
              (Hw.descTgt (Hw.readReg E Hw.rs2E)))).eval σ = 1#1)
            from by
              have hfcv1 : (Hw.freeCellV T).eval σ = 1#1 :=
                (freeCellV_eval σ T).mpr (by rw [hfc]; rfl)
              show ¬(~~~((Hw.muxFin (fun c => Hw.freeCellV c)
                (Hw.descTgt (Hw.readReg E Hw.rs2E))).eval σ) = 1#1)
              rw [hcellMux, hfcv1]
              decide)]
        rfl
      have hgrant :
          (grantFull E).run σ ((Hw.refillAct m).run σ σ) =
            (grantExplicit E T NS NL).run σ
              ((Hw.refillAct m).run σ σ) := by
        rw [grantFull_run_selected, htarget,
          grantChosen_run_explicit σ _ E T NS NL hsidx hlidx]
      have hpc : σ.regs (Hw.dpc E) 12 =
          ((Hw.refillAct m).run σ σ).regs (Hw.dpc E) 12 := by
        have hpcAll : ∀ d : DomainId,
            ((Hw.refillAct m).run σ σ).regs (Hw.dpc d) 12 =
              σ.regs (Hw.dpc d) 12 := by
          intro d
          exact refill_pres m σ (by fin_cases d <;> decide +kernel)
        exact (hpcAll E).symm
      have habsD : ∀ x,
          Hw.absDom ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
            ((Hw.refillAct m).run σ σ)) x = τ2.doms x := by
        intro x
        change Hw.absDom ((grantFull E).run σ
          ((Hw.refillAct m).run σ σ)) x = τ2.doms x
        rw [hgrant]
        by_cases hxE : x = E
        · subst x
          by_cases hET : E = T
          ·
            have hlidxE : (Hw.freeCellIdx E).eval σ = NL := by
                simpa only [← hET] using hlidx
            have hs := absDom_grantExplicit_same σ
                ((Hw.refillAct m).run σ σ) E NS NL K P
                (operandsOf W).rd V hlidxE hkind hparent rfl hval hpc
            rw [show (grantExplicit E T NS NL).run σ
                ((Hw.refillAct m).run σ σ) =
                (grantExplicit E E NS NL).run σ
                  ((Hw.refillAct m).run σ σ) by
              simpa only [← hET]]
            rw [hs, ← hL1 E]
            unfold τ2 τi τ0 MachineState.installDerived MachineState.setDom
            dsimp only
            simp only [← hET, Loom.Fun.update_same]
          ·
            have he := absDom_grantExplicit_owner_ne σ
              ((Hw.refillAct m).run σ σ) E T hET NS NL
              (operandsOf W).rd V rfl hval hpc
            rw [he, ← hL1 E]
            unfold τ2 τi τ0 MachineState.installDerived MachineState.setDom
            dsimp only
            rw [Loom.Fun.update_same,
              Loom.Fun.update_ne _ _ _ _ hET,
              Loom.Fun.update_same]
        · by_cases hxT : x = T
          · subst x
            have hTE : T ≠ E := fun h => hxE h
            have ht := absDom_grantExplicit_target_ne σ
              ((Hw.refillAct m).run σ σ) E T hTE.symm NS NL K P
              hlidx hkind hparent
            rw [ht, ← hL1 T]
            unfold τ2 τi τ0 MachineState.installDerived
              MachineState.setDom
            dsimp only
            rw [Loom.Fun.update_ne _ _ _ _ hTE,
              Loom.Fun.update_same,
              Loom.Fun.update_ne _ _ _ _ hTE]
          · rw [absDom_grantExplicit_other σ
              ((Hw.refillAct m).run σ σ) E T x hxE hxT NS NL,
              ← hL1 x]
            unfold τ2 τi τ0 MachineState.installDerived
              MachineState.setDom
            dsimp only
            rw [Loom.Fun.update_ne _ _ _ _ hxE,
              Loom.Fun.update_ne _ _ _ _ hxT,
              Loom.Fun.update_ne _ _ _ _ hxE]
      have habsG : ∀ g,
          Hw.absGate ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
            ((Hw.refillAct m).run σ σ)) g = τ2.gates g := by
        intro g
        change Hw.absGate ((grantFull E).run σ
          ((Hw.refillAct m).run σ σ)) g = τ2.gates g
        rw [hgrant, absGate_grantExplicit, ← hG1 g]
        rfl
      have hjob : τ2.mover = Hw.absMover σ := by
        show (refillPhase m (Hw.abs σ)).mover = Hw.absMover σ
        rw [refillPhase_mover]
        rfl
      have hτ0caps : ∀ (d : DomainId) (s : Slot),
          (τ0.doms d).caps s = ((Hw.abs σ).doms d).caps s := by
        intro d s
        unfold τ0 MachineState.setDom
        dsimp only
        by_cases hd : d = E
        · subst d
          rw [Loom.Fun.update_same]
          exact congrFun (refillPhase_caps m (Hw.abs σ) E) s
        · rw [Loom.Fun.update_ne _ _ _ _ hd]
          exact congrFun (refillPhase_caps m (Hw.abs σ) d) s
      have hτ0gen : ∀ (d : DomainId) (s : Slot),
          (τ0.doms d).slotGen s = ((Hw.abs σ).doms d).slotGen s := by
        intro d s
        unfold τ0 MachineState.setDom
        dsimp only
        by_cases hd : d = E
        · subst d
          rw [Loom.Fun.update_same]
          exact congrFun (refillPhase_slotGen m (Hw.abs σ) E) s
        · rw [Loom.Fun.update_ne _ _ _ _ hd]
          exact congrFun (refillPhase_slotGen m (Hw.abs σ) d) s
      have hfree0 : (τ0.doms T).caps NS = none := by
        rw [hτ0caps T NS]
        exact freeSlot_caps_none (Hw.abs σ) T hfs
      have hwcaps : ∀ (r : CapRef),
          (∃ ce, ((Hw.abs σ).doms r.dom).liveCap r.slot r.gen = some ce) →
          (τ2.doms r.dom).caps r.slot =
            ((Hw.abs σ).doms r.dom).caps r.slot := by
        intro r hlive
        have hlive0 : ∃ ce, (τ0.doms r.dom).liveCap r.slot r.gen = some ce := by
          obtain ⟨ce, hce⟩ := hlive
          refine ⟨ce, ?_⟩
          unfold DomainState.liveCap
          rw [hτ0caps r.dom r.slot, hτ0gen r.dom r.slot]
          exact hce
        have hi := installDerived_caps_at_live τ0 T NS NL K P r
          hfree0 hlive0
        show ((τi.setDom E (fun ds => ds.setReg (operandsOf W).rd V)).doms
            r.dom).caps r.slot = _
        rw [show ((τi.setDom E
            (fun ds => ds.setReg (operandsOf W).rd V)).doms r.dom).caps
              r.slot = (τi.doms r.dom).caps r.slot from by
          unfold MachineState.setDom
          dsimp only
          by_cases hd : r.dom = E
          · rw [hd, Loom.Fun.update_same, setReg_caps]
          · rw [Loom.Fun.update_ne _ _ _ _ hd]]
        exact hi.trans (hτ0caps r.dom r.slot)
      have hwgen : ∀ (r : CapRef),
          (τ2.doms r.dom).slotGen r.slot =
            ((Hw.abs σ).doms r.dom).slotGen r.slot := by
        intro r
        show ((τi.setDom E (fun ds => ds.setReg (operandsOf W).rd V)).doms
            r.dom).slotGen r.slot = _
        rw [show ((τi.setDom E
            (fun ds => ds.setReg (operandsOf W).rd V)).doms r.dom).slotGen
              r.slot = (τi.doms r.dom).slotGen r.slot from by
          unfold MachineState.setDom
          dsimp only
          by_cases hd : r.dom = E
          · rw [hd, Loom.Fun.update_same, setReg_slotGen]
          · rw [Loom.Fun.update_ne _ _ _ _ hd]]
        rw [show (τi.doms r.dom).slotGen r.slot =
            (τ0.doms r.dom).slotGen r.slot from
          installDerived_slotGen τ0 T NS NL K P r.dom r.slot]
        exact hτ0gen r.dom r.slot
      have hτ0regions : ∀ d : DomainId,
          (τ0.doms d).regions = ((Hw.abs σ).doms d).regions := by
        intro d
        unfold τ0 MachineState.setDom
        dsimp only
        by_cases hd : d = E
        · subst d
          rw [Loom.Fun.update_same]
          exact refillPhase_regions m (Hw.abs σ) E
        · rw [Loom.Fun.update_ne _ _ _ _ hd]
          exact refillPhase_regions m (Hw.abs σ) d
      have hτiregions : ∀ d : DomainId,
          (τi.doms d).regions = (τ0.doms d).regions := by
        intro d
        unfold τi MachineState.installDerived MachineState.setDom
        dsimp only
        by_cases hd : d = T
        · subst d
          rw [Loom.Fun.update_same]
        · rw [Loom.Fun.update_ne _ _ _ _ hd]
      have hτ2regions : ∀ d : DomainId,
          (τ2.doms d).regions = ((Hw.abs σ).doms d).regions := by
        intro d
        unfold τ2 MachineState.setDom
        dsimp only
        by_cases hd : d = E
        · subst d
          rw [Loom.Fun.update_same, setReg_regions, hτiregions,
            hτ0regions]
        · rw [Loom.Fun.update_ne _ _ _ _ hd, hτiregions,
            hτ0regions]
      have hauthτ2 : ∀ (ow : Expr 2) (sa : Expr 12),
          ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
            (List.finRange numRegions).map fun r =>
              Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
                Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                  ⟨false, true, false⟩])).eval σ = 1#1) ↔
            τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
              ⟨false, true, false⟩ = true := by
        intro ow sa
        rw [sAuth_quiescent_eval σ hin.killed hmapz hunmapz ow sa]
        rw [MachineState.domCovers, MachineState.domCovers]
        simp only [hτ2regions]
      have hmemτ2 : ∀ b : Addr,
          ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems
            "mem" b.toNat 32 = τ2.mem b := by
        intro b
        rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
        rw [refill_pres_mem m σ "mem" b.toNat 32]
        rfl
      have hswτ2 : ∀ sc : Expr 12, Expr.eval σ
          (((List.finRange numDomains).foldr
            (fun d acc' =>
              Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d,
                  Hw.isMn "sw", Hw.domCoversE d
                    (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                    ⟨false, true, false⟩,
                  .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                    0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
            (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
        intro sc
        rw [srcWord_quiescent σ hswz sc]
        rfl
      refine square_retire_install m hwf hfit σ hsync hifv hcl hin X τ2
        hcoreR ?_ hspec habsD habsG hjob ?_ ?_ ?_ ?_ hauthτ2 hmemτ2
        hswτ2 ?_ ?_
      · unfold X
        exact ifv_notin_grantX E
      · intro hv
        exact hwcaps _ (watched_live_of_reachable m σ hsr hv).1
      · intro _
        exact hwgen _
      · intro hv
        exact hwcaps _ (watched_live_of_reachable m σ hsr hv).2
      · intro _
        exact hwgen _
      · rfl
      · rfl


end Machines.Lnp64u.Theorems.RMC
