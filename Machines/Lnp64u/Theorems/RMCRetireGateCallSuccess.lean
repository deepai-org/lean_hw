-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCallArm
import Machines.Lnp64u.Theorems.RMCRetireGateSquare
import Machines.Lnp64u.Theorems.RMCRetireGateShared

/-!
# R-MC retirement: successful gate_call arms

Successful `gate_call` retirement, split at the optional argument transfer.
The null branch establishes the complete activation/callee/caller cycle with
an empty structural kill footprint; the non-null branch reuses the shared
`transferA` abstraction.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

private theorem ifv_notin_callSuccess (d : DomainId) :
    ("if_v", 1) ∉ (callSuccessA d).regWrites := by
  fin_cases d <;> decide +kernel

/-- A null argument selects the identity arm of the optional hardware
transfer, independently of the accumulator supplied by retirement. -/
theorem callTransferA_run_zero (σ acc : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argW d).eval σ = 0#32) :
    (callTransferA d).run σ acc = acc := by
  have hnz : (Hw.argNZ d).eval σ ≠ 1#1 := by
    intro h
    exact (argNZ_eval_iff σ d).mp h hz
  simp [callTransferA, Act.run, bv1_ne_one.mp hnz]

/-- A non-null argument selects the shared structural transfer action. -/
theorem callTransferA_run_nonzero (σ acc : Loom.Hw.St) (d : DomainId)
    (hnz : (Hw.argW d).eval σ ≠ 0#32) :
    (callTransferA d).run σ acc =
      (Hw.transferA d (Hw.callCal d) (Hw.argSel d)).run σ acc := by
  have hnzE : (Hw.argNZ d).eval σ = 1#1 :=
    (argNZ_eval_iff σ d).mpr hnz
  simp [callTransferA, Act.run, hnzE]

/-- A successful call with a null argument cannot invalidate a Mover
endpoint, so its auxiliary status-memory port is disabled. -/
theorem callCirc_memEn_zero_arg (σ : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argW d).eval σ = 0#32) :
    (Hw.callCirc d).memEn.eval σ = 0#1 := by
  have hnz : (Hw.argNZ d).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro h
    exact (argNZ_eval_iff σ d).mp h hz
  have hk : (Hw.movKilledE (Hw.callKilled d)).eval σ = 0#1 := by
    unfold Hw.movKilledE Hw.callKilled Hw.andAll
    simp only [Expr.eval]
    rw [hnz]
    exact (by decide : ∀ a b c : BitVec 1,
      a &&& ((0#1 &&& b) ||| (0#1 &&& c)) = 0#1) _ _ _
  unfold Hw.callCirc Hw.sweepMem Hw.andAll
  change (Hw.callOkE d).eval σ &&&
    ((Hw.movKilledE (Hw.callKilled d)).eval σ &&&
      (Hw.statusAuthE (Hw.callKilled d)).eval σ) = 0#1
  rw [hk]
  exact (by decide : ∀ a b : BitVec 1, a &&& (0#1 &&& b) = 0#1) _ _

/-- Consequently, the core phase of a null-argument call preserves memory,
including when all call checks pass. -/
theorem coreAct_mem_gateCall_zero_arg (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hz : (Hw.argW E).eval σ = 0#32) (b : Addr) :
    ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
      b.toNat 32 = σ.mems "mem" b.toNat 32 := by
  have hport := retireMem_gateCall_sel σ E hifsel hifexcl hopc
  have hmen : (Hw.callCirc E).memEn.eval σ = 0#1 :=
    callCirc_memEn_zero_arg σ E hz
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
  rw [if_neg (by rw [hport.1, hmen]; decide)]
  exact refill_pres_mem m σ "mem" b.toNat 32

/-- Successful non-null gate-call memory commit, factored through the shared
sweeping-operation bridge.  The caller supplies the post-structural region
authority and the exact target-memory shape; opcode selection and the
call-specific endpoint guard are discharged here. -/
theorem coreAct_mem_gateCall_success_nonzero (m : Manifest)
    (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (base target : MachineState)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hslot : (Hw.argSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.argNZ E).eval σ = 1#1)
    (hok : (Hw.callOkE E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.callKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hauthPost : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
        base.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true)
    (hbase : ∀ b : Addr, base.mem b = σ.mems "mem" b.toNat 32)
    (htarget : ∀ b : Addr, target.mem b =
      match Hw.absMover σ with
      | none => base.mem b
      | some job =>
          if (job.src.dom = E ∧ job.src.slot = S) ∨
              (job.dst.dom = E ∧ job.dst.slot = S) then
            if base.domCovers job.owner job.statusAddr
                { r := false, w := true, x := false } then
              if b = job.statusAddr then Errno.staleHandle.toWord
              else base.mem b
            else base.mem b
          else base.mem b)
    (b : Addr) :
    ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
      b.toNat 32 = target.mem b := by
  have hport := retireMem_gateCall_sel σ E hifsel hifexcl hopc
  apply coreAct_mem_sweep_success m σ (Hw.callOkE E) (Hw.callKilled E)
    (Hw.callCirc E) E S base target hifv hcl hport
  · rfl
  · rfl
  · rfl
  · exact hok
  · exact movKilledE_call_nonzero_iff σ E S hslot hnz
  · intro job hjob
    have hstatus := statusAuthE_post_eval σ (Hw.callKilled E) hkills
      hmapz hunmapz
    have hv : σ.regs "mov_v" 1 = 1#1 := by
      by_contra hn
      rw [absMover_none σ hn] at hjob
      contradiction
    have hcanon := Option.some.inj ((absMover_some σ hv).symm.trans hjob)
    subst job
    exact hstatus.trans (by
      simpa using hauthPost (.reg 2 "mov_owner") (.reg 12 "mov_status"))
  · exact hbase
  · exact htarget

/-- Although the call itself succeeds, a null argument gives it an empty
structural kill footprint, so the ordinary inert Mover assembly applies. -/
theorem Inert.of_successful_call_zero (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ = 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1)
    (hok : ∀ d : DomainId, d = E → (Hw.callOkE d).eval σ = 1#1)
    (hz : (Hw.argNZ E).eval σ = 0#1)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1) : Inert σ where
  killed := by
    intro dm sl
    rw [killedByCoreE_call_eval σ E hret hif hdrop hrev hcall hreturn
      hok dm sl]
    exact callKilled_zero_eval σ E hz dm sl
  newJob := hnew



/-- Status-authority bridge specialized to a structural transfer from the
retirement base. -/
theorem sAuth_call_retire_transfer (m : Manifest) (σ : Loom.Hw.St)
    (E T : DomainId) (S NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (hslot : (Hw.argSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.argNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.callKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hfree : ((Hw.abs σ).doms T).caps NS = none)
    (hwf : Wf (Hw.abs σ)) (ow : Expr 2) (sa : Expr 12) :
    ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
      (transferStructural
        { refillPhase m (Hw.abs σ) with inflight := none }
        T NS kind moved oldRef newRef E S).domCovers
          (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true := by
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let τc := ((installTransferred base T NS kind moved).reparent oldRef newRef)
    |>.clearSlot E S
  have hregions : ∀ c : DomainId,
      (τc.doms c).regions = ((Hw.abs σ).doms c).regions := by
    intro c
    by_cases hcT : c = T
    · subst c
      by_cases hTE : T = E <;>
        simp [τc, base, installTransferred, MachineState.reparent,
          MachineState.clearSlot, MachineState.setDom, Loom.Fun.update,
          retireBase_regions, hTE]
    · by_cases hcE : c = E
      · subst c
        simp [τc, base, installTransferred, MachineState.reparent,
          MachineState.clearSlot, MachineState.setDom, Loom.Fun.update,
          retireBase_regions, hcT]
      · simp [τc, base, installTransferred, MachineState.reparent,
          MachineState.clearSlot, MachineState.setDom, Loom.Fun.update,
          retireBase_regions, hcT, hcE]
  have hbacking : ∀ c r rg, ((Hw.abs σ).doms c).regions r = some rg →
      τc.liveRef rg.backing =
        if rg.backing.dom = E ∧ rg.backing.slot = S then false
        else (Hw.abs σ).liveRef rg.backing := by
    intro c r rg hrg
    have hlive := regionBacking_live hwf hrg
    have h := transferStructural_retire_liveRef m σ T NS kind moved
      oldRef newRef E S rg.backing hfree hlive
    simpa [transferStructural, τc, base, sweepRegions_liveRef, hlive] using h
  have h := sAuth_call_backings_eval σ E S τc hslot hnz hkills hmapz
    hunmapz hregions hbacking hwf ow sa
  simpa [transferStructural, τc, base] using h


/-- Full-cycle assembly for a successful non-null call after the semantic
branch has identified the transferred source slot and post-core state. -/
theorem square_retire_gateCall_payload (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId) (S : Slot) (X : Act) (τ2 : MachineState)
    (hslot : (Hw.argSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.argNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.callKilled E dm sl).eval σ)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w)
    (hXifv : ("if_v", 1) ∉ X.regWrites)
    (hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2)
    (habsD : ∀ x, Hw.absDom
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) x = τ2.doms x)
    (habsG : ∀ g, Hw.absGate
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) g = τ2.gates g)
    (hkindS : ∀ job, Hw.absMover σ = some job →
      ¬(job.src.dom = E ∧ job.src.slot = S) →
      Option.map CapEntry.kind
          ((τ2.doms job.src.dom).liveCap job.src.slot job.src.gen) =
        Option.map CapEntry.kind
          (((Hw.abs σ).doms job.src.dom).liveCap job.src.slot job.src.gen))
    (hkindD : ∀ job, Hw.absMover σ = some job →
      ¬(job.dst.dom = E ∧ job.dst.slot = S) →
      Option.map CapEntry.kind
          ((τ2.doms job.dst.dom).liveCap job.dst.slot job.dst.gen) =
        Option.map CapEntry.kind
          (((Hw.abs σ).doms job.dst.dom).liveCap job.dst.slot job.dst.gen))
    (hjob : τ2.mover =
      match Hw.absMover σ with
      | none => none
      | some job =>
          if (job.src.dom = E ∧ job.src.slot = S) ∨
              (job.dst.dom = E ∧ job.dst.slot = S)
          then none else some job)
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
    (hswτ2 : ∀ job, Hw.absMover σ = some job →
      ¬((job.src.dom = E ∧ job.src.slot = S) ∨
        (job.dst.dom = E ∧ job.dst.slot = S)) →
      ∀ sc : Expr 12, Expr.eval σ
        (((List.finRange numDomains).foldr
          (fun d acc' =>
            Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                Hw.domCoversE d
                  (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                  ⟨false, true, false⟩,
                .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                  0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
          (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ))
    (hcyc : τ2.cycle = σ.regs "cycle" 32)
    (hτ2if : τ2.inflight = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  apply square_retire_gate_payload m σ X τ2 hcoreR hXifv hspec habsD habsG
  · exact absMover_moverAct_call σ
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)) τ2 E S hslot hnz
      hkills hnew hkindS hkindD hjob
  · intro a
    exact moverAct_mem_call σ
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)) τ2 E S hslot hnz
      hkills hnew hkindS hkindD hjob hauthτ2 hmemτ2 hswτ2 a
  · exact hcyc
  · exact hτ2if

/-- The specification enters the call body after advancing the caller PC,
whereas the hardware successful payload performs that advance itself.  Refill
does not change any value captured by the activation record, so the two pure
successful-call transformers coincide. -/
theorem callAbstractSuccess_refill_pc (m : Manifest) (σ : Loom.Hw.St)
    (d cal : DomainId) (g : GateId) (rd : RegId)
    (argHandle : Loom.Word32) (depth : Nat) (hne : d ≠ cal) :
    let base : MachineState :=
      { refillPhase m (Hw.abs σ) with inflight := none }
    let prefixed := base.setDom d (fun ds => { ds with pc := ds.pc + 1 })
    callAbstractSuccessAt prefixed prefixed d cal g rd argHandle depth
        (prefixed.doms d).pc =
      callAbstractSuccess (Hw.abs σ) base d cal g rd argHandle depth := by
  dsimp only
  unfold callAbstractSuccess callAbstractSuccessAt
  apply machineState_ext' <;> try rfl
  · funext x
    by_cases hxd : x = d
    · subst x
      simp [MachineState.setDom, Loom.Fun.update]
    · by_cases hxc : x = cal
      · subst x
        have hcald : cal ≠ d := hxd
        simp [MachineState.setDom, Loom.Fun.update, hcald,
          refillPhase_serving]
      · simp [MachineState.setDom, Loom.Fun.update, hxd, hxc]
  · funext h
    by_cases hh : h = g
    · subst h
      have hcald : cal ≠ d := Ne.symm hne
      simp [MachineState.setDom, Loom.Fun.update, hcald,
        refillPhase_gates,
        refillPhase_serving, refillPhase_dmaxdon]
    · simp [MachineState.setDom, hh, refillPhase_gates]

/-- Domain and gate faces of a successful call agree across the complete
structural-transfer prefix.  The specification performs its PC increment
before transfer and its Mover sweep before the call tail; hardware performs
the structural transfer first and advances PC in the tail.  Neither ordering
difference is visible on domains or gates. -/
theorem callAbstractSuccess_transfer_faces (m : Manifest) (σ : Loom.Hw.St)
    (d cal : DomainId) (g : GateId) (rd : RegId)
    (argHandle : Loom.Word32) (depth : Nat) (hne : d ≠ cal)
    (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (S : Slot) :
    let base : MachineState :=
      { refillPhase m (Hw.abs σ) with inflight := none }
    let prefixed := base.setDom d (fun ds => { ds with pc := ds.pc + 1 })
    let hwStruct :=
      transferStructural base cal NS kind moved oldRef newRef d S
    let specStruct :=
      (transferStructural prefixed cal NS kind moved oldRef newRef d S).sweepMover
    let specCall := callAbstractSuccessAt prefixed specStruct d cal g rd
      argHandle depth (specStruct.doms d).pc
    let hwCall := callAbstractSuccess (Hw.abs σ) hwStruct d cal g rd
      argHandle depth
    (∀ x, specCall.doms x = hwCall.doms x) ∧
      (∀ h, specCall.gates h = hwCall.gates h) := by
  dsimp only
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let hwStruct :=
    transferStructural base cal NS kind moved oldRef newRef d S
  have hcomm : transferStructural
        (base.setDom d fun ds => { ds with pc := ds.pc + 1 })
        cal NS kind moved oldRef newRef d S =
      hwStruct.setDom d (fun ds => { ds with pc := ds.pc + 1 }) := by
    simpa [hwStruct] using transferStructural_setPc base d cal NS kind moved
      oldRef newRef S hne
  constructor
  · intro x
    rw [hcomm]
    unfold callAbstractSuccess callAbstractSuccessAt
    by_cases hxd : x = d
    · subst x
      simp [MachineState.setDom, Loom.Fun.update, hne, base, hwStruct,
        transferStructural, installTransferred]
    · by_cases hxc : x = cal
      · subst x
        have hcald : cal ≠ d := hxd
        simp [MachineState.setDom, Loom.Fun.update, hne, hcald,
          base, hwStruct, transferStructural, installTransferred,
          refillPhase_gates]
      · simp [MachineState.setDom, Loom.Fun.update, hxd, hxc,
          base, hwStruct, transferStructural, installTransferred]
  · intro h
    rw [hcomm]
    unfold callAbstractSuccess callAbstractSuccessAt
    by_cases hh : h = g
    · subst h
      have hcald : cal ≠ d := Ne.symm hne
      simp [MachineState.setDom, Loom.Fun.update, hcald,
        base, hwStruct, transferStructural, installTransferred,
        refillPhase_gates, refillPhase_regs, refillPhase_pc,
        refillPhase_serving, refillPhase_maxDonation]
    · simp [MachineState.setDom, Loom.Fun.update, hh,
        base, hwStruct, transferStructural, installTransferred,
        refillPhase_gates]

/-- Whole-state strengthening of `callAbstractSuccess_transfer_faces` when
the normalized hardware-side base includes the specification's Mover sweep.
This is the canonical successful non-null call state used by the final
retirement square. -/
theorem callAbstractSuccess_transfer_state (m : Manifest) (σ : Loom.Hw.St)
    (d cal : DomainId) (g : GateId) (rd : RegId)
    (argHandle : Loom.Word32) (depth : Nat) (hne : d ≠ cal)
    (NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (S : Slot) :
    let base : MachineState :=
      { refillPhase m (Hw.abs σ) with inflight := none }
    let prefixed := base.setDom d (fun ds => { ds with pc := ds.pc + 1 })
    let hwStruct :=
      transferStructural base cal NS kind moved oldRef newRef d S
    let specStruct :=
      (transferStructural prefixed cal NS kind moved oldRef newRef d S).sweepMover
    callAbstractSuccessAt prefixed specStruct d cal g rd argHandle depth
        (specStruct.doms d).pc =
      callAbstractSuccess (Hw.abs σ) hwStruct.sweepMover d cal g rd
        argHandle depth := by
  dsimp only
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let hwStruct :=
    transferStructural base cal NS kind moved oldRef newRef d S
  have hcomm : transferStructural
        (base.setDom d fun ds => { ds with pc := ds.pc + 1 })
        cal NS kind moved oldRef newRef d S =
      hwStruct.setDom d (fun ds => { ds with pc := ds.pc + 1 }) := by
    simpa [hwStruct] using transferStructural_setPc base d cal NS kind moved
      oldRef newRef S hne
  rw [hcomm, sweepMover_setPc]
  unfold callAbstractSuccess callAbstractSuccessAt
  apply machineState_ext'
  · rfl
  · rfl
  · funext x
    by_cases hxd : x = d
    · subst x
      simp [MachineState.setDom, Loom.Fun.update, hne, base, hwStruct,
        transferStructural, installTransferred]
    · by_cases hxc : x = cal
      · subst x
        have hcald : cal ≠ d := hxd
        simp [MachineState.setDom, Loom.Fun.update, hne, hcald,
          base, hwStruct, transferStructural, installTransferred,
          refillPhase_gates]
      · simp [MachineState.setDom, Loom.Fun.update, hxd, hxc,
          base, hwStruct, transferStructural, installTransferred]
  · funext h
    by_cases hh : h = g
    · subst h
      have hcald : cal ≠ d := Ne.symm hne
      simp [MachineState.setDom, Loom.Fun.update, hcald,
        base, hwStruct, transferStructural, installTransferred,
        refillPhase_gates, refillPhase_regs, refillPhase_pc,
        refillPhase_serving, refillPhase_maxDonation]
    · simp [MachineState.setDom, Loom.Fun.update, hh,
        base, hwStruct, transferStructural, installTransferred,
        refillPhase_gates]
  · rfl
  · rfl

/-- The call control-state tail frames all capability structure and regions
already produced by the optional transfer. -/
theorem callAbstractSuccess_structural_frames (source base : MachineState)
    (d cal : DomainId) (g : GateId) (rd : RegId)
    (argHandle : Loom.Word32) (depth : Nat) :
    (∀ x, ((callAbstractSuccess source base d cal g rd argHandle depth).doms
        x).caps = (base.doms x).caps) ∧
    (∀ x, ((callAbstractSuccess source base d cal g rd argHandle depth).doms
        x).slotGen = (base.doms x).slotGen) ∧
    (∀ x, ((callAbstractSuccess source base d cal g rd argHandle depth).doms
        x).regions = (base.doms x).regions) ∧
    (callAbstractSuccess source base d cal g rd argHandle depth).mover =
      base.mover ∧
    (callAbstractSuccess source base d cal g rd argHandle depth).mem =
      base.mem := by
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = cal <;>
      simp_all [callAbstractSuccess, callAbstractSuccessAt]
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = cal <;>
      simp_all [callAbstractSuccess, callAbstractSuccessAt]
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = cal <;>
      simp_all [callAbstractSuccess, callAbstractSuccessAt]
  · exact ⟨rfl, rfl⟩

/-- Once the common gate-call checks have selected a ready callee, a null
argument reduces the specification body directly to the successful pure
transformer. -/
theorem gateCallExec_success_zero_of_ready (σ : Loom.Hw.St)
    (τ : MachineState) (d : DomainId) (c : Ctx)
    (hready : CallReady σ τ d c)
    (harg : (τ.doms c.d).reg c.op.rs2 = 0) :
    ∃ g : GateId, ∃ cal : DomainId,
      cal ≠ c.d ∧
      finOfBv (by decide : 2 ^ 2 = numGates)
          ((Hw.callGid d).eval σ) = g ∧
      finOfBv (by decide : 2 ^ 2 = numDomains)
          ((Hw.callCal d).eval σ) = cal ∧
      Machines.Lnp64u.Isa.Wip.gateCallExec c τ =
        .ok () (callAbstractSuccessAt τ τ c.d cal g c.op.rd 0
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ) (τ.doms c.d).pc) := by
  obtain ⟨S, G, e, g, cal, hlive, hkind, hact, hcal, hne, hrun,
      hserv, hdepth, hgid, hcalSel⟩ := hready
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ.doms c.d).reg c.op.rs2) τ = .ok 0 τ := by
    rw [harg]
    exact transferByHandle_eq_zero τ c.d cal
  refine ⟨g, cal, hne, hgid, hcalSel, ?_⟩
  exact gateCallExec_eq_selected c τ τ S G e g cal 0 hlive hkind hact
    hcal hne hrun hserv hdepth htransfer rfl rfl rfl rfl rfl

/-- Once the common call checks have selected a ready callee, any successful
argument transfer reduces `gateCallExec` to the same pure call transformer.
This statement is deliberately independent of the root/derived transfer
split so both allocation branches share the call-control proof. -/
theorem gateCallExec_success_of_ready (σ : Loom.Hw.St)
    (τ τ' : MachineState) (d : DomainId) (c : Ctx)
    (hready : CallReady σ τ d c) (argHandle resultHandle : Loom.Word32)
    (harg : (τ.doms c.d).reg c.op.rs2 = argHandle)
    (htransfer : Machines.Lnp64u.Isa.transferByHandle c.d
      (finOfBv (by decide : 2 ^ 2 = numDomains)
        ((Hw.callCal d).eval σ)) argHandle τ = .ok resultHandle τ')
    (hdonation : (τ'.doms c.d).maxDonation =
      (τ.doms c.d).maxDonation) :
    ∃ g : GateId, ∃ cal : DomainId,
      cal ≠ c.d ∧
      finOfBv (by decide : 2 ^ 2 = numGates)
          ((Hw.callGid d).eval σ) = g ∧
      finOfBv (by decide : 2 ^ 2 = numDomains)
          ((Hw.callCal d).eval σ) = cal ∧
      Machines.Lnp64u.Isa.Wip.gateCallExec c τ =
        .ok () (callAbstractSuccessAt τ τ' c.d cal g c.op.rd
          resultHandle (Machines.Lnp64u.Isa.Wip.gateDepth c τ)
          (τ'.doms c.d).pc) := by
  obtain ⟨S, G, e, g, cal, hlive, hkind, hact, hcal, hne, hrun,
      hserv, hdepth, hgid, hcalSel⟩ := hready
  have htransfer' : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ.doms c.d).reg c.op.rs2) τ = .ok resultHandle τ' := by
    rw [harg, ← hcalSel]
    exact htransfer
  have hcalm := transferByHandle_calm c.d cal
    ((τ.doms c.d).reg c.op.rs2) τ resultHandle τ' htransfer'
  have hframe := Machines.Lnp64u.Isa.Wip.transferByHandle_frame c.d cal
    ((τ.doms c.d).reg c.op.rs2) τ resultHandle τ' htransfer'
  refine ⟨g, cal, hne, hgid, hcalSel, ?_⟩
  exact gateCallExec_eq_selected c τ τ' S G e g cal resultHandle
    hlive hkind hact hcal hne hrun hserv hdepth htransfer'
    hframe.2.2.1 (hcalm cal).1 (hcalm cal).2.1 (hframe.2.1 cal)
    hdonation

/-- Complete successful null-argument arm.  This is the first successful
leaf of the gate-call check tree and the full-cycle template for the
structural-transfer branches. -/
theorem square_retire_gateCall_success_zero (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ ≠ 1#1)
    (hnotServing : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hdepthPass : (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hargZero : (Hw.argW
      (finOfBv (by decide) (σ.regs "if_dom" 2))).eval σ = 0#32) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let c : Ctx :=
    { d := E, pc := (base.doms E).pc, op := operandsOf W }
  let τ0 : MachineState :=
    base.setDom E (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire base E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  have hreg1 : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hreg2 : (τ0.doms E).reg (operandsOf W).rs2 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    specReg_bridge m σ E _
  have hword1 : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg1, hR1]
  have hword2 : (τ0.doms c.d).reg c.op.rs2 =
      (Hw.argW E).eval σ := by
    simp only [c, Hw.argW]
    rw [hreg2, hR2]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword1 hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  have hcallee := callCallee_of_pass σ τ0 E c rfl hgates hp
    (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunBridge : ∀ x : DomainId,
      (τ0.doms x).run = ((Hw.abs σ).doms x).run := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, base, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, base, MachineState.setDom, Loom.Fun.update, hx]
  have hservBridge : ∀ x : DomainId,
      (τ0.doms x).serving = ((Hw.abs σ).doms x).serving := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, base, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, base, MachineState.setDom, Loom.Fun.update, hx]
  have hwfAbs : Wf (Hw.abs σ) :=
    (Machines.Lnp64u.wfa_invariant m hwf (Hw.abs σ) hsr).1
  have hready := callReady_of_pass σ τ0 E c rfl hwfAbs hrc hrunBridge
    hservBridge hgates hcallee (by simpa [E] using hrunning)
      (by simpa [E] using hnotServing) (by simpa [E] using hdepthPass)
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal, hne,
      hrun, hserv, hdepth, hgid, hcalSel⟩ := hready
  have hselPass :
      (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 ∧
      (Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))).eval σ ≠ 1#1 := by
    constructor
    · show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
      rw [show (Hw.callSel E).live.eval σ = 1#1 from by
        simpa [E] using hlive]
      decide
    · simpa [E] using hprimary
  have hstatePass := callStateChecks_pass σ c g cal hwfAbs (hrc cal)
    hgid hcalSel (by simpa [hgates] using hact) (by simpa [c] using hne)
    (by simpa [hrunBridge] using hrun)
    (by simpa [hservBridge] using hserv)
    (by
      have heq : Machines.Lnp64u.Isa.Wip.gateDepth c τ0 =
          Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) := by
        unfold Machines.Lnp64u.Isa.Wip.gateDepth
        rw [hservBridge c.d, hgates]
      simpa [heq] using hdepth)
  have hargPass := callArgumentChecks_zero σ E (by simpa [E] using hargZero)
  have hok : (Hw.callOkE E).eval σ = 1#1 :=
    callOkE_of_passes σ E hselPass hstatePass hargPass.1
      hargPass.2.1 hargPass.2.2
  have hargSpec : (τ0.doms c.d).reg c.op.rs2 = 0 := by
    rw [hword2]
    simpa [E] using hargZero
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ0.doms c.d).reg c.op.rs2) τ0 = .ok 0 τ0 := by
    rw [hargSpec]
    exact transferByHandle_eq_zero τ0 c.d cal
  have hexec : Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 =
      .ok () (callAbstractSuccessAt τ0 τ0 c.d cal g c.op.rd 0
        (Machines.Lnp64u.Isa.Wip.gateDepth c τ0) (τ0.doms c.d).pc) :=
    gateCallExec_eq_selected c τ0 τ0 S G e g cal 0 hcapLive hkind hact
      hcal hne hrun hserv hdepth htransfer rfl rfl rfl rfl rfl
  have hdepthEq : ((Hw.callDepth E).eval σ).toNat =
      Machines.Lnp64u.Isa.Wip.gateDepth c τ0 := by
    rw [show ((Hw.callDepth E).eval σ).toNat =
      Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) from by
        simpa [c] using callDepth_eval σ c hwfAbs]
    unfold Machines.Lnp64u.Isa.Wip.gateDepth
    rw [hservBridge c.d, hgates]
  let τ2 := callAbstractSuccess (Hw.abs σ) base E cal g
    (operandsOf W).rd 0 ((Hw.callDepth E).eval σ).toNat
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
    rw [hcore0, retire_gateCall_exec _ E W hdec]
    change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err er τ' => τ'.setDom E
          (fun ds => ds.setReg (operandsOf W).rd er.toWord)
      | .fault f => haltWith base E f) = τ2
    rw [hexec]
    rw [← hdepthEq]
    simpa [c, τ0, base, τ2] using
      (callAbstractSuccess_refill_pc m σ E cal g (operandsOf W).rd 0
        ((Hw.callDepth E).eval σ).toNat (by simpa [c] using hne.symm))
  let acc0 := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  have habsBase : Hw.abs acc0 = base := by
    exact abs_refill_clearInflight m hwf hfit σ hsync
  have habsCall : Hw.abs ((callSuccessA E).run σ acc0) = τ2 := by
    rw [abs_callSuccessA σ acc0 E cal g (by simpa [c] using hne.symm)
      hcalSel hgid]
    rw [callTransferA_run_zero σ acc0 E (by simpa [E] using hargZero),
      habsBase, callArgHandle_eval_zero σ E (by simpa [E] using hargZero)]
    rfl
  have hret := retiringE_one σ hifv hcl
  have hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1 := by
    intro d
    by_cases hd : d = E
    · subst d; simpa using hifsel
    · rw [if_neg hd, bv1_ne_one.mp (hifexcl d hd)]
  have hmn : (Hw.isMn "gate_call").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_call" = 22#6).symm
  have hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_drop" 22#6 hopc (by decide +kernel)
  have hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_revoke" 22#6 hopc (by decide +kernel)
  have hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_return" 22#6 hopc (by decide +kernel)
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1 := by
    intro d
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 22#6 hopc (by decide +kernel)
  have hin : Inert σ := Inert.of_successful_call_zero σ E hret hif hdrop
    hrev hmn hreturn (fun d hd => by simpa [hd] using hok)
      (by
        apply bv1_ne_one.mp
        intro hnz
        exact (argNZ_eval_iff σ E).mp hnz (by simpa [E] using hargZero))
      hnew
  have hmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "map", Hw.mapOkE x,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 22#6 hopc (by decide +kernel))
  have hunmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 22#6 hopc (by decide +kernel))
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
      (isMn_ne_of_opc σ "sw" 22#6 hopc (by decide +kernel))
  let X := callSuccessA E
  have hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w := by
    intro rn w
    rw [coreAct_run_retire_eq m σ _ hifv hcl,
      retireAct_run_regs σ _ E rfl rn w,
      retireFor_gateCall_success σ _ E hopc hok]
    rfl
  have hframes := callAbstractSuccess_structural_frames (Hw.abs σ) base E
    cal g (operandsOf W).rd 0 ((Hw.callDepth E).eval σ).toNat
  have hcaps : ∀ x, (τ2.doms x).caps = ((Hw.abs σ).doms x).caps := by
    intro x
    rw [show (τ2.doms x).caps = (base.doms x).caps from hframes.1 x]
    exact refillPhase_caps m (Hw.abs σ) x
  have hgens : ∀ x, (τ2.doms x).slotGen =
      ((Hw.abs σ).doms x).slotGen := by
    intro x
    rw [show (τ2.doms x).slotGen = (base.doms x).slotGen from
      hframes.2.1 x]
    exact refillPhase_slotGen m (Hw.abs σ) x
  have hregions : ∀ x, (τ2.doms x).regions =
      ((Hw.abs σ).doms x).regions := by
    intro x
    rw [show (τ2.doms x).regions = (base.doms x).regions from
      hframes.2.2.1 x]
    exact refillPhase_regions m (Hw.abs σ) x
  have hjob : τ2.mover = Hw.absMover σ := by
    rw [show τ2.mover = base.mover from hframes.2.2.2.1]
    exact refillPhase_mover m (Hw.abs σ)
  have hauth : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun x =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit x), Hw.rgnVPostE x r,
            Hw.rgnCoversVal (Hw.rgnValPostE x r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true := by
    intro ow sa
    rw [sAuth_quiescent_eval σ hin.killed hmapz hunmapz ow sa]
    simp only [MachineState.domCovers, hregions]
  have hmem : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = τ2.mem b := by
    intro b
    rw [coreAct_mem_gateCall_zero_arg m σ E hifv hcl hifsel hifexcl
      hopc (by simpa [E] using hargZero) b]
    change (Hw.abs σ).mem b = τ2.mem b
    rw [show τ2.mem = base.mem from hframes.2.2.2.2]
    rfl
  have hsw : ∀ sc : Expr 12, Expr.eval σ
      (((List.finRange numDomains).foldr
        (fun d acc' =>
          Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
              Hw.domCoversE d
                (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                ⟨false, true, false⟩,
              .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
        (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
    intro sc
    rw [srcWord_quiescent σ hswz sc]
    change (Hw.abs σ).mem (sc.eval σ) = τ2.mem (sc.eval σ)
    rw [show τ2.mem = base.mem from hframes.2.2.2.2]
    rfl
  refine square_retire_install m hwf hfit σ hsync hifv hcl hin X τ2
    hcoreR ?_ hspec ?_ ?_ hjob ?_ ?_ ?_ ?_ hauth hmem hsw ?_ ?_
  · unfold X
    exact ifv_notin_callSuccess E
  · intro x
    change Hw.absDom ((callSuccessA E).run σ acc0) x = τ2.doms x
    exact congrFun (congrArg MachineState.doms habsCall) x
  · intro gate
    change Hw.absGate ((callSuccessA E).run σ acc0) gate = τ2.gates gate
    exact congrFun (congrArg MachineState.gates habsCall) gate
  · intro _
    exact congrFun (hcaps _) _
  · intro _
    exact congrFun (hgens _) _
  · intro _
    exact congrFun (hcaps _) _
  · intro _
    exact congrFun (hgens _) _
  · rfl
  · rfl

/-- Complete successful non-null argument arm.  The passing placement check
selects either a root transfer or a derived transfer; both branches are
normalized through the shared whole-state `transferA` abstraction. -/
theorem square_retire_gateCall_success_nonzero (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hlive : (Hw.callSel
      (finOfBv (by decide) (σ.regs "if_dom" 2))).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and
      (Hw.callSel (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk
      (Expr.not (Hw.kIsMem
        (Hw.callSel (finOfBv (by decide)
          (σ.regs "if_dom" 2))).kindW)))).eval σ ≠ 1#1)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hnotSelf : (Expr.eq
      (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.dLit (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun d => .reg 2 (Hw.drun d))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2))))
      (.lit 0)).eval σ ≠ 1#1)
    (hnotServing : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
      (Hw.callCal (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hdepthPass : (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth (finOfBv (by decide)
        (σ.regs "if_dom" 2)))).eval σ ≠ 1#1)
    (hargNonzero : (Hw.argW
      (finOfBv (by decide) (σ.regs "if_dom" 2))).eval σ ≠ 0#32)
    (hargLive : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.argSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).live)).eval σ ≠ 1#1)
    (hargClass : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.argSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk)).eval σ ≠ 1#1)
    (hnotBlocked : (Expr.and
      (Hw.argNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.transferBlocked
        (finOfBv (by decide) (σ.regs "if_dom" 2))
        (Hw.callCal (finOfBv (by decide) (σ.regs "if_dom" 2)))
        (Hw.argSel
          (finOfBv (by decide) (σ.regs "if_dom" 2))))).eval σ ≠ 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let c : Ctx :=
    { d := E, pc := (base.doms E).pc, op := operandsOf W }
  let τ0 : MachineState :=
    base.setDom E (fun ds => { ds with pc := ds.pc + 1 })
  have hop : Machines.Lnp64u.sig.opcodeOf W = (22#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire base E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  have hreg1 : (τ0.doms E).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E _
  have hreg2 : (τ0.doms E).reg (operandsOf W).rs2 =
      ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    specReg_bridge m σ E _
  have hword1 : (τ0.doms c.d).reg c.op.rs1 =
      (Hw.readReg E Hw.rs1E).eval σ := by
    simp only [c]
    rw [hreg1, hR1]
  have hword2 : (τ0.doms c.d).reg c.op.rs2 =
      (Hw.argW E).eval σ := by
    simp only [c, Hw.argW]
    rw [hreg2, hR2]
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  have hp := callPrimary_of_pass σ τ0 E c rfl hword1 hbridge hkc
    (by simpa [E] using hlive) (by simpa [E] using hprimary)
  have hgates : τ0.gates = (Hw.abs σ).gates := by
    change (refillPhase m (Hw.abs σ)).gates = (Hw.abs σ).gates
    exact refillPhase_gates m (Hw.abs σ)
  have hcallee := callCallee_of_pass σ τ0 E c rfl hgates hp
    (by simpa [E] using hidle) (by simpa [E] using hnotSelf)
  have hrunBridge : ∀ x : DomainId,
      (τ0.doms x).run = ((Hw.abs σ).doms x).run := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, base, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, base, MachineState.setDom, Loom.Fun.update, hx]
  have hservBridge : ∀ x : DomainId,
      (τ0.doms x).serving = ((Hw.abs σ).doms x).serving := by
    intro x
    by_cases hx : x = E
    · subst x
      simp [τ0, base, MachineState.setDom, Loom.Fun.update]
    · simp [τ0, base, MachineState.setDom, Loom.Fun.update, hx]
  have hwfAbs : Wf (Hw.abs σ) :=
    (Machines.Lnp64u.wfa_invariant m hwf (Hw.abs σ) hsr).1
  have hready := callReady_of_pass σ τ0 E c rfl hwfAbs hrc hrunBridge
    hservBridge hgates hcallee (by simpa [E] using hrunning)
      (by simpa [E] using hnotServing) (by simpa [E] using hdepthPass)
  obtain ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal, hne,
      hrun, hserv, hdepth, hgid, hcalSel⟩ := hready
  have hreadyFull : CallReady σ τ0 E c :=
    ⟨S, G, e, g, cal, hcapLive, hkind, hact, hcal, hne, hrun, hserv,
      hdepth, hgid, hcalSel⟩
  have hnz : (Hw.argW E).eval σ ≠ 0#32 := by
    simpa [E] using hargNonzero
  have hnzE : (Hw.argNZ E).eval σ = 1#1 :=
    (argNZ_eval_iff σ E).mpr hnz
  have hargLive1 : (Hw.argSel E).live.eval σ = 1#1 := by
    exact (by decide : ∀ a b : BitVec 1,
      a = 1#1 → a &&& ~~~b ≠ 1#1 → b = 1#1)
      ((Hw.argNZ E).eval σ) ((Hw.argSel E).live.eval σ) hnzE
      (by simpa [E] using hargLive)
  have hargCls1 : (Hw.argSel E).clsOk.eval σ = 1#1 := by
    exact (by decide : ∀ a b : BitVec 1,
      a = 1#1 → a &&& ~~~b ≠ 1#1 → b = 1#1)
      ((Hw.argNZ E).eval σ) ((Hw.argSel E).clsOk.eval σ) hnzE
      (by simpa [E] using hargClass)
  obtain ⟨ae, alive, acap⟩ := capSel_entry_of_live σ τ0 E
    (Hw.argW E) hbridge (by simpa [Hw.argSel] using hargLive1)
  let AS : Slot := (Handle.decode ((Hw.argW E).eval σ)).slot
  let AG : Gen := (Handle.decode ((Hw.argW E).eval σ)).gen
  have aslotNat : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.argW E).eval σ).extractLsb' 0 4)).val =
      (((Hw.argW E).eval σ).extractLsb' 0 4).toNat := rfl
  have aclsIff := capSel_clsOk_iff_some σ E (Hw.argW E)
    (finOfBv (by decide) (((Hw.argW E).eval σ).extractLsb' 0 4))
    ae hkc aslotNat acap
  have acls : (Handle.decode ((Hw.argW E).eval σ)).cls = ae.kind.cls :=
    aclsIff.mp (by simpa [Hw.argSel] using hargCls1)
  have aslotE : (Hw.argSel E).slot.eval σ =
      BitVec.ofNat 4 AS.val := by
    exact (bv4_slot_iff _ AS).mpr rfl
  have hsource : (τ0.doms E).caps AS = some ae := by
    change (τ0.doms E).liveCap AS AG = some ae at alive
    unfold DomainState.liveCap at alive
    cases hc : (τ0.doms E).caps AS with
    | none => simp [hc] at alive
    | some ae' =>
        rw [hc] at alive
        change (if (decide ((τ0.doms E).slotGen AS = AG) && AG != 0) = true
          then some ae' else none) = some ae at alive
        by_cases hg : (decide ((τ0.doms E).slotGen AS = AG) && AG != 0) = true
        · rw [if_pos hg] at alive
          have heq : ae' = ae := Option.some.inj alive
          rw [← heq]
        · rw [if_neg hg] at alive
          contradiction
  have hgenSource : (τ0.doms E).slotGen AS = AG := by
    have h := alive
    change (τ0.doms E).liveCap AS AG = some ae at h
    unfold DomainState.liveCap at h
    rw [hsource] at h
    change (if (decide ((τ0.doms E).slotGen AS = AG) && AG != 0) = true
      then some ae else none) = some ae at h
    by_cases hg : (decide ((τ0.doms E).slotGen AS = AG) && AG != 0) = true
    · have hp : (τ0.doms E).slotGen AS = AG ∧ AG ≠ 0 := by
        simpa using hg
      exact hp.1
    · rw [if_neg hg] at h
      contradiction
  have hgenSourceAbs : ((Hw.abs σ).doms E).slotGen AS = AG := by
    simpa [τ0, base, MachineState.setDom, Loom.Fun.update] using hgenSource
  have hkw : (Hw.argSel E).kindW.eval σ = Hw.encKind ae.kind :=
    capSel_kind_of_some σ E (Hw.argW E) AS ae hkc (by rfl) acap
  have hold : Hw.decRef
      ((Hw.encRefE (Hw.dLit E) (Hw.argSel E).slot
        (Hw.argSel E).gen).eval σ) =
      ⟨E, AS, ((Hw.abs σ).doms E).slotGen AS⟩ := by
    apply encRefE_decoded_selected σ E (Hw.argSel E).slot
      (Hw.argSel E).gen AS (((Hw.abs σ).doms E).slotGen AS) aslotE
    simpa [AG] using hgenSourceAbs.symm
  have hdecode : Handle.decode ((Hw.argW E).eval σ) =
      ⟨AS, AG, ae.kind.cls⟩ := by
    cases hd : Handle.decode ((Hw.argW E).eval σ) with
    | mk slot gen cls =>
        simp only [AS, AG, hd] at acls ⊢
        cases acls
        rfl
  have hcapLiveArg : Machines.Lnp64u.Isa.capLive E ((Hw.argW E).eval σ) τ0 =
      .ok (AS, AG, ae) τ0 :=
    capLive_eq_selected τ0 E ((Hw.argW E).eval σ) AS AG ae hdecode alive
  have hlineage : ∀ L : LineageId,
      (τ0.doms E).lineage L = ((Hw.abs σ).doms E).lineage L := by
    intro L
    simp [τ0, base, MachineState.setDom, Loom.Fun.update]
  have hcalNE : cal ≠ E := by simpa [c] using hne
  have hfreeSlot : τ0.freeSlot cal = (Hw.abs σ).freeSlot cal := by
    unfold MachineState.freeSlot
    simp [τ0, base, MachineState.setDom, Loom.Fun.update, hcalNE]
  have hfreeCell : τ0.freeCell cal = (Hw.abs σ).freeCell cal := by
    unfold MachineState.freeCell
    simp [τ0, base, MachineState.setDom, Loom.Fun.update, hcalNE]
  have htransferPass :
      (Hw.transferBlocked E (Hw.callCal E) (Hw.argSel E)).eval σ ≠ 1#1 := by
    intro hb
    apply hnotBlocked
    change (Hw.argNZ E).eval σ &&&
      (Hw.transferBlocked E (Hw.callCal E) (Hw.argSel E)).eval σ = 1#1
    rw [hnzE, hb]
    decide
  have hselPass :
      (Expr.not (Hw.callSel E).live).eval σ ≠ 1#1 ∧
      (Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))).eval σ ≠ 1#1 := by
    constructor
    · show ¬(~~~((Hw.callSel E).live.eval σ) = 1#1)
      rw [show (Hw.callSel E).live.eval σ = 1#1 from by
        simpa [E] using hlive]
      decide
    · simpa [E] using hprimary
  have hstatePass := callStateChecks_pass σ c g cal hwfAbs (hrc cal)
    hgid hcalSel (by simpa [hgates] using hact) (by simpa [c] using hne)
    (by simpa [hrunBridge] using hrun)
    (by simpa [hservBridge] using hserv)
    (by
      have heq : Machines.Lnp64u.Isa.Wip.gateDepth c τ0 =
          Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) := by
        unfold Machines.Lnp64u.Isa.Wip.gateDepth
        rw [hservBridge c.d, hgates]
      simpa [heq] using hdepth)
  have hok : (Hw.callOkE E).eval σ = 1#1 :=
    callOkE_of_passes σ E hselPass hstatePass
      (by simpa [E] using hargLive) (by simpa [E] using hargClass)
      (by simpa [E] using hnotBlocked)
  have hret := retiringE_one σ hifv hcl
  have hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1 := by
    intro d
    by_cases hd : d = E
    · subst d; simpa using hifsel
    · rw [if_neg hd, bv1_ne_one.mp (hifexcl d hd)]
  have hmn : (Hw.isMn "gate_call").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_call" = 22#6).symm
  have hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_drop" 22#6 hopc (by decide +kernel)
  have hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_revoke" 22#6 hopc (by decide +kernel)
  have hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_return" 22#6 hopc (by decide +kernel)
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1 := by
    intro d
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 22#6 hopc (by decide +kernel)
  have hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.callKilled E dm sl).eval σ :=
    killedByCoreE_call_eval σ E hret hif hdrop hrev hmn hreturn
      (fun d hd => by simpa [hd] using hok)
  have hmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "map", Hw.mapOkE x,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 22#6 hopc (by decide +kernel))
  have hunmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 22#6 hopc (by decide +kernel))
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
      (isMn_ne_of_opc σ "sw" 22#6 hopc (by decide +kernel))
  let acc0 := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  let X := callSuccessA E
  have hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w := by
    intro rn w
    rw [coreAct_run_retire_eq m σ _ hifv hcl,
      retireAct_run_regs σ _ E rfl rn w,
      retireFor_gateCall_success σ _ E hopc hok]
    rfl
  rcases transferCap_selected_of_pass σ τ0 E cal (Hw.callCal E)
      (Hw.argW E) AS ae hcalSel aslotE acap hsource hlineage
      hfreeSlot hfreeCell hwfAbs htransferPass with hroot | hderived
  · obtain ⟨NS, hlin, hNS, hlinV, htransferCap⟩ := hroot
    let oldRef : CapRef :=
      ⟨E, AS, ((Hw.abs σ).doms E).slotGen AS⟩
    let newRef : CapRef :=
      ⟨cal, NS, ((Hw.abs σ).doms cal).slotGen NS⟩
    let hwStruct := transferStructural base cal NS ae.kind none
      oldRef newRef E AS
    let specStruct := (transferStructural τ0 cal NS ae.kind none
      oldRef newRef E AS).sweepMover
    have htransferCap' : τ0.transferCap E AS cal =
        some (specStruct, newRef) := by
      simpa [specStruct, oldRef, newRef, τ0, base,
        MachineState.setDom, Loom.Fun.update, hcalNE,
        refillPhase_slotGen] using htransferCap
    have htransferBy : Machines.Lnp64u.Isa.transferByHandle E cal
        ((Hw.argW E).eval σ) τ0 =
        .ok (Handle.encode ⟨newRef.slot, newRef.gen, ae.kind.cls⟩)
          specStruct :=
      transferByHandle_eq_selected τ0 specStruct E cal
        ((Hw.argW E).eval σ) AS AG ae newRef hnz hcapLiveArg htransferCap'
    have hsidx : (Hw.freeSlotIdx cal).eval σ =
        BitVec.ofNat 4 NS.val := freeSlotIdx_eval σ cal NS hNS
    have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
        ((Hw.freeSlotIdx cal).eval σ) = NS :=
      (bv4_slot_iff _ NS).mp hsidx
    have hgenNew : (Hw.genOfE cal (Hw.freeSlotIdx cal)).eval σ =
        ((Hw.abs σ).doms cal).slotGen NS := by
      rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
      rfl
    have hclsbit : (Hw.field (Hw.argSel E).kindW 0 1).eval σ =
        if ae.kind.cls = .gate then 1#1 else 0#1 := by
      show ((Hw.argSel E).kindW.eval σ).extractLsb' 0 1 = _
      rw [hkw]
      cases ae.kind <;>
        simp only [CapKind.cls, Hw.encKind, if_false, if_true] <;>
        apply BitVec.eq_of_getLsbD_eq <;>
        intro i hi <;> interval_cases i <;> simp
    have hargHandle : (callArgHandle E).eval σ =
        Handle.encode ⟨newRef.slot, newRef.gen, ae.kind.cls⟩ := by
      rw [callArgHandle_eval_nonzero σ E ae.kind.cls hnz hclsbit]
      dsimp only
      rw [hcalSel, hsidx, hgenNew]
      simp only [newRef]
      rw [finOfBv_ofNat4]
    have hdonation : (specStruct.doms E).maxDonation =
        (τ0.doms E).maxDonation := by
      dsimp only [specStruct]
      rw [sweepMover_doms]
      simp [specStruct, transferStructural, installTransferred,
        MachineState.reparent, MachineState.clearSlot,
        MachineState.sweepRegions, MachineState.sweepMover,
        MachineState.setDom, Loom.Fun.update, hcalNE.symm]
    obtain ⟨g', cal', hne', hgid', hcalSel', hexec⟩ :=
      gateCallExec_success_of_ready σ τ0 specStruct E c hreadyFull
        ((Hw.argW E).eval σ)
        (Handle.encode ⟨newRef.slot, newRef.gen, ae.kind.cls⟩)
        hword2 (by simpa [c, hcalSel, hargHandle] using htransferBy) hdonation
    have hgg : g' = g := hgid'.symm.trans hgid
    have hcc : cal' = cal := hcalSel'.symm.trans hcalSel
    subst g'; subst cal'
    let τ2 := callAbstractSuccessAt τ0 specStruct E cal g
      (operandsOf W).rd ((callArgHandle E).eval σ)
      (Machines.Lnp64u.Isa.Wip.gateDepth c τ0) (specStruct.doms E).pc
    have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
      rw [hcore0, retire_gateCall_exec _ E W hdec]
      change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
        | .ok _ τ' => τ'
        | .err er τ' => τ'.setDom E
            (fun ds => ds.setReg (operandsOf W).rd er.toWord)
        | .fault f => haltWith base E f) = τ2
      rw [hexec]
      rw [show c.d = E from rfl, hcalSel, hgid]
      simpa [τ2, c, hargHandle]
    have hdepthEq : ((Hw.callDepth E).eval σ).toNat =
        Machines.Lnp64u.Isa.Wip.gateDepth c τ0 := by
      rw [show ((Hw.callDepth E).eval σ).toNat =
        Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) from by
          simpa [c] using callDepth_eval σ c hwfAbs]
      unfold Machines.Lnp64u.Isa.Wip.gateDepth
      rw [hservBridge c.d, hgates]
    have habsTransfer : Hw.abs
        ((Hw.transferA E (Hw.callCal E) (Hw.argSel E)).run σ acc0) =
        hwStruct := by
      simpa [acc0, hwStruct, oldRef, newRef, base] using
        (abs_transferA_none_retireAcc m hwf hfit σ hsync E cal
          (Hw.callCal E) (Hw.argSel E) AS NS ae hcalSel aslotE acap hNS
          hlin hlinV hkw hold hwfAbs)
    have habsCall : Hw.abs ((callSuccessA E).run σ acc0) =
        callAbstractSuccess (Hw.abs σ) hwStruct E cal g
          (operandsOf W).rd ((callArgHandle E).eval σ)
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ0) := by
      rw [abs_callSuccessA σ acc0 E cal g hcalNE.symm
        hcalSel hgid]
      rw [callTransferA_run_nonzero σ acc0 E hnz, habsTransfer]
      rw [hdepthEq]
      rfl
    have hfaces := callAbstractSuccess_transfer_faces m σ E cal g
      (operandsOf W).rd ((callArgHandle E).eval σ)
      (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)
      hcalNE.symm NS ae.kind none oldRef newRef AS
    have hstate : τ2 = callAbstractSuccess (Hw.abs σ)
        hwStruct.sweepMover E cal g (operandsOf W).rd
        ((callArgHandle E).eval σ)
        (Machines.Lnp64u.Isa.Wip.gateDepth c τ0) := by
      simpa [τ2, specStruct, hwStruct, base, τ0] using
        (callAbstractSuccess_transfer_state m σ E cal g
          (operandsOf W).rd ((callArgHandle E).eval σ)
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)
          hcalNE.symm NS ae.kind none oldRef newRef AS)
    have hframes := callAbstractSuccess_structural_frames (Hw.abs σ)
      hwStruct.sweepMover E cal g (operandsOf W).rd
      ((callArgHandle E).eval σ)
      (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)
    have hfreeCap : ((Hw.abs σ).doms cal).caps NS = none :=
      freeSlot_caps_none (Hw.abs σ) cal hNS
    have hkindS : ∀ job, Hw.absMover σ = some job →
        ¬(job.src.dom = E ∧ job.src.slot = AS) →
        Option.map CapEntry.kind
            ((τ2.doms job.src.dom).liveCap job.src.slot job.src.gen) =
          Option.map CapEntry.kind
            (((Hw.abs σ).doms job.src.dom).liveCap job.src.slot job.src.gen) := by
      intro job hjob hout
      rw [hstate]
      unfold DomainState.liveCap
      rw [hframes.1 job.src.dom, hframes.2.1 job.src.dom, sweepMover_doms]
      exact transferStructural_retire_liveKind m σ cal NS ae.kind none
        oldRef newRef E AS job.src hfreeCap
        (moverEndpoints_live hwfAbs job hjob).1 hout
    have hkindD : ∀ job, Hw.absMover σ = some job →
        ¬(job.dst.dom = E ∧ job.dst.slot = AS) →
        Option.map CapEntry.kind
            ((τ2.doms job.dst.dom).liveCap job.dst.slot job.dst.gen) =
          Option.map CapEntry.kind
            (((Hw.abs σ).doms job.dst.dom).liveCap job.dst.slot job.dst.gen) := by
      intro job hjob hout
      rw [hstate]
      unfold DomainState.liveCap
      rw [hframes.1 job.dst.dom, hframes.2.1 job.dst.dom, sweepMover_doms]
      exact transferStructural_retire_liveKind m σ cal NS ae.kind none
        oldRef newRef E AS job.dst hfreeCap
        (moverEndpoints_live hwfAbs job hjob).2 hout
    have hjob : τ2.mover =
        match Hw.absMover σ with
        | none => none
        | some job =>
            if (job.src.dom = E ∧ job.src.slot = AS) ∨
                (job.dst.dom = E ∧ job.dst.slot = AS)
            then none else some job := by
      rw [hstate, hframes.2.2.2.1]
      exact transferStructural_retire_sweepMover_mover m σ cal NS ae.kind
        none oldRef newRef E AS hfreeCap hwfAbs
    have hauth : ∀ (ow : Expr 2) (sa : Expr 12),
        ((Hw.orAll ((List.finRange numDomains).flatMap fun x =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit x), Hw.rgnVPostE x r,
              Hw.rgnCoversVal (Hw.rgnValPostE x r) sa
                ⟨false, true, false⟩])).eval σ = 1#1) ↔
          τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
            ⟨false, true, false⟩ = true := by
      intro ow sa
      rw [hstate]
      unfold MachineState.domCovers
      rw [hframes.2.2.1, sweepMover_doms]
      exact sAuth_call_retire_transfer m σ E cal AS NS ae.kind none
        oldRef newRef aslotE hnzE hkills hmapz hunmapz hfreeCap hwfAbs ow sa
    have hmem : ∀ b : Addr,
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
          b.toNat 32 = τ2.mem b := by
      intro b
      apply coreAct_mem_gateCall_success_nonzero m σ E AS hwStruct τ2
        hifv hcl hifsel hifexcl hopc aslotE hnzE hok hkills hmapz hunmapz
        (sAuth_call_retire_transfer m σ E cal AS NS ae.kind none oldRef
          newRef aslotE hnzE hkills hmapz hunmapz hfreeCap hwfAbs) ?_ ?_ b
      · intro a
        change base.mem a = σ.mems "mem" a.toNat 32
        exact retireBase_mem m σ a
      · intro a
        rw [hstate, hframes.2.2.2.2]
        exact transferStructural_retire_sweepMover_mem m σ cal NS ae.kind
          none oldRef newRef E AS hfreeCap hwfAbs a
    have hsw : ∀ job, Hw.absMover σ = some job →
        ¬((job.src.dom = E ∧ job.src.slot = AS) ∨
          (job.dst.dom = E ∧ job.dst.slot = AS)) →
        ∀ sc : Expr 12, Expr.eval σ
          (((List.finRange numDomains).foldr
            (fun d acc' =>
              Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                  Hw.domCoversE d
                    (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                    ⟨false, true, false⟩,
                  .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                    0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
            (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
      intro job hjob hsurv sc
      rw [srcWord_quiescent σ hswz sc, hstate, hframes.2.2.2.2]
      rw [transferStructural_retire_sweepMover_mem m σ cal NS ae.kind
        none oldRef newRef E AS hfreeCap hwfAbs (sc.eval σ), hjob]
      simp [hsurv]
    refine square_retire_gateCall_payload m σ E AS X τ2 aslotE hnzE
      hkills hnew hcoreR ?_ hspec ?_ ?_ hkindS hkindD hjob hauth hmem hsw
      ?_ ?_
    · unfold X
      exact ifv_notin_callSuccess E
    · intro x
      change Hw.absDom ((callSuccessA E).run σ acc0) x = τ2.doms x
      rw [show Hw.absDom ((callSuccessA E).run σ acc0) x =
        (callAbstractSuccess (Hw.abs σ) hwStruct E cal g
          (operandsOf W).rd ((callArgHandle E).eval σ)
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)).doms x from
            congrFun (congrArg MachineState.doms habsCall) x]
      simpa [τ2, specStruct, hwStruct, τ0, base] using (hfaces.1 x).symm
    · intro gate
      change Hw.absGate ((callSuccessA E).run σ acc0) gate = τ2.gates gate
      rw [show Hw.absGate ((callSuccessA E).run σ acc0) gate =
        (callAbstractSuccess (Hw.abs σ) hwStruct E cal g
          (operandsOf W).rd ((callArgHandle E).eval σ)
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)).gates gate from
            congrFun (congrArg MachineState.gates habsCall) gate]
      simpa [τ2, specStruct, hwStruct, τ0, base] using (hfaces.2 gate).symm
    · rw [← hspec, corePhase_cycle, refillPhase_cycle]
      rfl
    · rw [hstate]
      change hwStruct.sweepMover.inflight = none
      rw [sweepMover_inflight]
      simp [hwStruct, transferStructural, installTransferred, base]
  · obtain ⟨L, cell, NS, NL, hlin, hcell, hNS, hNL, hlinV,
      hlinIdx, htransferCap⟩ := hderived
    let oldRef : CapRef :=
      ⟨E, AS, ((Hw.abs σ).doms E).slotGen AS⟩
    let newRef : CapRef :=
      ⟨cal, NS, ((Hw.abs σ).doms cal).slotGen NS⟩
    let hwStruct := transferStructural base cal NS ae.kind (some (NL, cell.parent))
      oldRef newRef E AS
    let specStruct := (transferStructural τ0 cal NS ae.kind (some (NL, cell.parent))
      oldRef newRef E AS).sweepMover
    have htransferCap' : τ0.transferCap E AS cal =
        some (specStruct, newRef) := by
      simpa [specStruct, oldRef, newRef, τ0, base,
        MachineState.setDom, Loom.Fun.update, hcalNE,
        refillPhase_slotGen] using htransferCap
    have htransferBy : Machines.Lnp64u.Isa.transferByHandle E cal
        ((Hw.argW E).eval σ) τ0 =
        .ok (Handle.encode ⟨newRef.slot, newRef.gen, ae.kind.cls⟩)
          specStruct :=
      transferByHandle_eq_selected τ0 specStruct E cal
        ((Hw.argW E).eval σ) AS AG ae newRef hnz hcapLiveArg htransferCap'
    have hsidx : (Hw.freeSlotIdx cal).eval σ =
        BitVec.ofNat 4 NS.val := freeSlotIdx_eval σ cal NS hNS
    have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
        ((Hw.freeSlotIdx cal).eval σ) = NS :=
      (bv4_slot_iff _ NS).mp hsidx
    have hgenNew : (Hw.genOfE cal (Hw.freeSlotIdx cal)).eval σ =
        ((Hw.abs σ).doms cal).slotGen NS := by
      rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
      rfl
    have hclsbit : (Hw.field (Hw.argSel E).kindW 0 1).eval σ =
        if ae.kind.cls = .gate then 1#1 else 0#1 := by
      show ((Hw.argSel E).kindW.eval σ).extractLsb' 0 1 = _
      rw [hkw]
      cases ae.kind <;>
        simp only [CapKind.cls, Hw.encKind, if_false, if_true] <;>
        apply BitVec.eq_of_getLsbD_eq <;>
        intro i hi <;> interval_cases i <;> simp
    have hargHandle : (callArgHandle E).eval σ =
        Handle.encode ⟨newRef.slot, newRef.gen, ae.kind.cls⟩ := by
      rw [callArgHandle_eval_nonzero σ E ae.kind.cls hnz hclsbit]
      dsimp only
      rw [hcalSel, hsidx, hgenNew]
      simp only [newRef]
      rw [finOfBv_ofNat4]
    have hdonation : (specStruct.doms E).maxDonation =
        (τ0.doms E).maxDonation := by
      dsimp only [specStruct]
      rw [sweepMover_doms]
      simp [specStruct, transferStructural, installTransferred,
        MachineState.reparent, MachineState.clearSlot,
        MachineState.sweepRegions, MachineState.sweepMover,
        MachineState.setDom, Loom.Fun.update, hcalNE.symm]
    obtain ⟨g', cal', hne', hgid', hcalSel', hexec⟩ :=
      gateCallExec_success_of_ready σ τ0 specStruct E c hreadyFull
        ((Hw.argW E).eval σ)
        (Handle.encode ⟨newRef.slot, newRef.gen, ae.kind.cls⟩)
        hword2 (by simpa [c, hcalSel, hargHandle] using htransferBy) hdonation
    have hgg : g' = g := hgid'.symm.trans hgid
    have hcc : cal' = cal := hcalSel'.symm.trans hcalSel
    subst g'; subst cal'
    let τ2 := callAbstractSuccessAt τ0 specStruct E cal g
      (operandsOf W).rd ((callArgHandle E).eval σ)
      (Machines.Lnp64u.Isa.Wip.gateDepth c τ0) (specStruct.doms E).pc
    have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
      rw [hcore0, retire_gateCall_exec _ E W hdec]
      change (match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
        | .ok _ τ' => τ'
        | .err er τ' => τ'.setDom E
            (fun ds => ds.setReg (operandsOf W).rd er.toWord)
        | .fault f => haltWith base E f) = τ2
      rw [hexec]
      rw [show c.d = E from rfl, hcalSel, hgid]
      simpa [τ2, c, hargHandle]
    have hdepthEq : ((Hw.callDepth E).eval σ).toNat =
        Machines.Lnp64u.Isa.Wip.gateDepth c τ0 := by
      rw [show ((Hw.callDepth E).eval σ).toNat =
        Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) from by
          simpa [c] using callDepth_eval σ c hwfAbs]
      unfold Machines.Lnp64u.Isa.Wip.gateDepth
      rw [hservBridge c.d, hgates]
    have habsTransfer : Hw.abs
        ((Hw.transferA E (Hw.callCal E) (Hw.argSel E)).run σ acc0) =
        hwStruct := by
      simpa [acc0, hwStruct, oldRef, newRef, base] using
        (abs_transferA_some_retireAcc m hwf hfit σ hsync E cal
          (Hw.callCal E) (Hw.argSel E) AS NS ae L cell NL hcalSel aslotE
          acap hNS hlin hcell hNL hlinV hlinIdx hkw hold hwfAbs)
    have habsCall : Hw.abs ((callSuccessA E).run σ acc0) =
        callAbstractSuccess (Hw.abs σ) hwStruct E cal g
          (operandsOf W).rd ((callArgHandle E).eval σ)
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ0) := by
      rw [abs_callSuccessA σ acc0 E cal g hcalNE.symm
        hcalSel hgid]
      rw [callTransferA_run_nonzero σ acc0 E hnz, habsTransfer]
      rw [hdepthEq]
      rfl
    have hfaces := callAbstractSuccess_transfer_faces m σ E cal g
      (operandsOf W).rd ((callArgHandle E).eval σ)
      (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)
      hcalNE.symm NS ae.kind (some (NL, cell.parent)) oldRef newRef AS
    have hstate : τ2 = callAbstractSuccess (Hw.abs σ)
        hwStruct.sweepMover E cal g (operandsOf W).rd
        ((callArgHandle E).eval σ)
        (Machines.Lnp64u.Isa.Wip.gateDepth c τ0) := by
      simpa [τ2, specStruct, hwStruct, base, τ0] using
        (callAbstractSuccess_transfer_state m σ E cal g
          (operandsOf W).rd ((callArgHandle E).eval σ)
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)
          hcalNE.symm NS ae.kind (some (NL, cell.parent)) oldRef newRef AS)
    have hframes := callAbstractSuccess_structural_frames (Hw.abs σ)
      hwStruct.sweepMover E cal g (operandsOf W).rd
      ((callArgHandle E).eval σ)
      (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)
    have hfreeCap : ((Hw.abs σ).doms cal).caps NS = none :=
      freeSlot_caps_none (Hw.abs σ) cal hNS
    have hkindS : ∀ job, Hw.absMover σ = some job →
        ¬(job.src.dom = E ∧ job.src.slot = AS) →
        Option.map CapEntry.kind
            ((τ2.doms job.src.dom).liveCap job.src.slot job.src.gen) =
          Option.map CapEntry.kind
            (((Hw.abs σ).doms job.src.dom).liveCap job.src.slot job.src.gen) := by
      intro job hjob hout
      rw [hstate]
      unfold DomainState.liveCap
      rw [hframes.1 job.src.dom, hframes.2.1 job.src.dom, sweepMover_doms]
      exact transferStructural_retire_liveKind m σ cal NS ae.kind (some (NL, cell.parent))
        oldRef newRef E AS job.src hfreeCap
        (moverEndpoints_live hwfAbs job hjob).1 hout
    have hkindD : ∀ job, Hw.absMover σ = some job →
        ¬(job.dst.dom = E ∧ job.dst.slot = AS) →
        Option.map CapEntry.kind
            ((τ2.doms job.dst.dom).liveCap job.dst.slot job.dst.gen) =
          Option.map CapEntry.kind
            (((Hw.abs σ).doms job.dst.dom).liveCap job.dst.slot job.dst.gen) := by
      intro job hjob hout
      rw [hstate]
      unfold DomainState.liveCap
      rw [hframes.1 job.dst.dom, hframes.2.1 job.dst.dom, sweepMover_doms]
      exact transferStructural_retire_liveKind m σ cal NS ae.kind (some (NL, cell.parent))
        oldRef newRef E AS job.dst hfreeCap
        (moverEndpoints_live hwfAbs job hjob).2 hout
    have hjob : τ2.mover =
        match Hw.absMover σ with
        | none => none
        | some job =>
            if (job.src.dom = E ∧ job.src.slot = AS) ∨
                (job.dst.dom = E ∧ job.dst.slot = AS)
            then none else some job := by
      rw [hstate, hframes.2.2.2.1]
      exact transferStructural_retire_sweepMover_mover m σ cal NS ae.kind
        (some (NL, cell.parent)) oldRef newRef E AS hfreeCap hwfAbs
    have hauth : ∀ (ow : Expr 2) (sa : Expr 12),
        ((Hw.orAll ((List.finRange numDomains).flatMap fun x =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit x), Hw.rgnVPostE x r,
              Hw.rgnCoversVal (Hw.rgnValPostE x r) sa
                ⟨false, true, false⟩])).eval σ = 1#1) ↔
          τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
            ⟨false, true, false⟩ = true := by
      intro ow sa
      rw [hstate]
      unfold MachineState.domCovers
      rw [hframes.2.2.1, sweepMover_doms]
      exact sAuth_call_retire_transfer m σ E cal AS NS ae.kind (some (NL, cell.parent))
        oldRef newRef aslotE hnzE hkills hmapz hunmapz hfreeCap hwfAbs ow sa
    have hmem : ∀ b : Addr,
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
          b.toNat 32 = τ2.mem b := by
      intro b
      apply coreAct_mem_gateCall_success_nonzero m σ E AS hwStruct τ2
        hifv hcl hifsel hifexcl hopc aslotE hnzE hok hkills hmapz hunmapz
        (sAuth_call_retire_transfer m σ E cal AS NS ae.kind (some (NL, cell.parent)) oldRef
          newRef aslotE hnzE hkills hmapz hunmapz hfreeCap hwfAbs) ?_ ?_ b
      · intro a
        change base.mem a = σ.mems "mem" a.toNat 32
        exact retireBase_mem m σ a
      · intro a
        rw [hstate, hframes.2.2.2.2]
        exact transferStructural_retire_sweepMover_mem m σ cal NS ae.kind
          (some (NL, cell.parent)) oldRef newRef E AS hfreeCap hwfAbs a
    have hsw : ∀ job, Hw.absMover σ = some job →
        ¬((job.src.dom = E ∧ job.src.slot = AS) ∨
          (job.dst.dom = E ∧ job.dst.slot = AS)) →
        ∀ sc : Expr 12, Expr.eval σ
          (((List.finRange numDomains).foldr
            (fun d acc' =>
              Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                  Hw.domCoversE d
                    (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                    ⟨false, true, false⟩,
                  .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX)
                    0 12) sc]) (Hw.readReg d Hw.rs2E) acc')
            (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
      intro job hjob hsurv sc
      rw [srcWord_quiescent σ hswz sc, hstate, hframes.2.2.2.2]
      rw [transferStructural_retire_sweepMover_mem m σ cal NS ae.kind
        (some (NL, cell.parent)) oldRef newRef E AS hfreeCap hwfAbs (sc.eval σ), hjob]
      simp [hsurv]
    refine square_retire_gateCall_payload m σ E AS X τ2 aslotE hnzE
      hkills hnew hcoreR ?_ hspec ?_ ?_ hkindS hkindD hjob hauth hmem hsw
      ?_ ?_
    · unfold X
      exact ifv_notin_callSuccess E
    · intro x
      change Hw.absDom ((callSuccessA E).run σ acc0) x = τ2.doms x
      rw [show Hw.absDom ((callSuccessA E).run σ acc0) x =
        (callAbstractSuccess (Hw.abs σ) hwStruct E cal g
          (operandsOf W).rd ((callArgHandle E).eval σ)
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)).doms x from
            congrFun (congrArg MachineState.doms habsCall) x]
      simpa [τ2, specStruct, hwStruct, τ0, base] using (hfaces.1 x).symm
    · intro gate
      change Hw.absGate ((callSuccessA E).run σ acc0) gate = τ2.gates gate
      rw [show Hw.absGate ((callSuccessA E).run σ acc0) gate =
        (callAbstractSuccess (Hw.abs σ) hwStruct E cal g
          (operandsOf W).rd ((callArgHandle E).eval σ)
          (Machines.Lnp64u.Isa.Wip.gateDepth c τ0)).gates gate from
            congrFun (congrArg MachineState.gates habsCall) gate]
      simpa [τ2, specStruct, hwStruct, τ0, base] using (hfaces.2 gate).symm
    · rw [← hspec, corePhase_cycle, refillPhase_cycle]
      rfl
    · rw [hstate]
      change hwStruct.sweepMover.inflight = none
      rw [sweepMover_inflight]
      simp [hwStruct, transferStructural, installTransferred, base]

/-- Complete `gate_call` retirement arm, dispatching the ten hardware checks
in ladder order and then splitting the successful optional transfer into its
null and non-null cases. -/
theorem square_retire_gateCall (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  let E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2)
  by_cases hlive : (Hw.callSel E).live.eval σ = 1#1
  · by_cases hprimary : (Expr.not (Expr.and (Hw.callSel E).clsOk
        (Expr.not (Hw.kIsMem (Hw.callSel E).kindW)))).eval σ = 1#1
    · exact square_retire_gateCall_badPrimary m hwf hfit σ hsync hz hkc
        hifv hcl hopc hlive hprimary
    · by_cases hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
          (Hw.callGid E)).eval σ = 1#1
      · exact square_retire_gateCall_active m hwf hfit σ hsync hz hkc
          hifv hcl hopc hlive hprimary hidle
      · by_cases hself : (Expr.eq (Hw.callCal E) (Hw.dLit E)).eval σ = 1#1
        · exact square_retire_gateCall_self m hwf hfit σ hsync hz hkc
            hifv hcl hopc hlive hprimary hidle hself
        · by_cases hrunning : (Hw.neqE
              (Hw.muxFin (fun d => .reg 2 (Hw.drun d)) (Hw.callCal E))
              (.lit 0)).eval σ = 1#1
          · exact square_retire_gateCall_notRunning m hwf hfit σ hsync hrc
              hz hkc hifv hcl hopc hlive hprimary hidle hself hrunning
          · by_cases hserving : (Hw.muxFin (fun d => .reg 1 (Hw.dsrvV d))
                (Hw.callCal E)).eval σ = 1#1
            · exact square_retire_gateCall_serving m hwf hfit σ hsync hrc
                hz hkc hifv hcl hopc hlive hprimary hidle hself hrunning
                hserving
            · by_cases hdepth : (Expr.ult
                  (.lit (BitVec.ofNat 3 maxChainDepth))
                  (Hw.callDepth E)).eval σ = 1#1
              · exact square_retire_gateCall_depthOverflow m hwf hfit σ
                  hsync hrc hz hkc hsr hifv hcl hopc hlive hprimary hidle
                  hself hrunning hserving hdepth
              · by_cases hargLive : (Expr.and (Hw.argNZ E)
                    (Expr.not (Hw.argSel E).live)).eval σ = 1#1
                · exact square_retire_gateCall_argStale m hwf hfit σ hsync
                    hrc hz hkc hsr hifv hcl hopc hlive hprimary hidle hself
                    hrunning hserving hdepth hargLive
                · by_cases hargClass : (Expr.and (Hw.argNZ E)
                      (Expr.not (Hw.argSel E).clsOk)).eval σ = 1#1
                  · exact square_retire_gateCall_argBadClass m hwf hfit σ
                      hsync hrc hz hkc hsr hifv hcl hopc hlive hprimary hidle
                      hself hrunning hserving hdepth hargLive hargClass
                  · by_cases hblocked : (Expr.and (Hw.argNZ E)
                        (Hw.transferBlocked E (Hw.callCal E)
                          (Hw.argSel E))).eval σ = 1#1
                    · exact square_retire_gateCall_argBlocked m hwf hfit σ
                        hsync hrc hz hkc hsr hifv hcl hopc hlive hprimary
                        hidle hself hrunning hserving hdepth hargLive hargClass
                        hblocked
                    · by_cases hzero : (Hw.argW E).eval σ = 0#32
                      · exact square_retire_gateCall_success_zero m hwf hfit σ
                          hsync hrc hz hkc hsr hifv hcl hopc hlive hprimary
                          hidle hself hrunning hserving hdepth hzero
                      · exact square_retire_gateCall_success_nonzero m hwf hfit
                          σ hsync hrc hz hkc hsr hifv hcl hopc hlive hprimary
                          hidle hself hrunning hserving hdepth hzero hargLive
                          hargClass hblocked
  · exact square_retire_gateCall_stale m hwf hfit σ hsync hz hifv hcl
      hopc hlive


end Machines.Lnp64u.Theorems.RMC
