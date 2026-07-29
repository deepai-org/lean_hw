-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateReturnSuccess
import Machines.Lnp64u.Theorems.RMCRetireGateSquare
import Machines.Lnp64u.Theorems.RMCRetireGateCallSuccess

/-!
# R-MC retirement: successful gate_return arms

Full-cycle assembly for the null and non-null successful return paths.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

private theorem ifv_notin_gateReturnSuccess (d : DomainId) :
    ("if_v", 1) ∉ (gateReturnSuccessA d).regWrites := by
  fin_cases d <;> decide +kernel

/-- A null reply handle disables the return sweep-memory port. -/
theorem retCirc_memEn_zero_reply (σ : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.retW d).eval σ = 0#32) :
    (Hw.retCirc d).memEn.eval σ = 0#1 := by
  have hnz : (Hw.retNZ d).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro h
    exact (retNZ_eval_iff σ d).mp h hz
  have hk : (Hw.movKilledE (Hw.retKilled d)).eval σ = 0#1 := by
    unfold Hw.movKilledE Hw.retKilled Hw.andAll
    simp only [Expr.eval]
    rw [hnz]
    exact (by decide : ∀ a b c : BitVec 1,
      a &&& ((0#1 &&& b) ||| (0#1 &&& c)) = 0#1) _ _ _
  unfold Hw.retCirc Hw.sweepMem Hw.andAll
  change (Hw.retOkE d).eval σ &&&
    ((Hw.movKilledE (Hw.retKilled d)).eval σ &&&
      (Hw.statusAuthE (Hw.retKilled d)).eval σ) = 0#1
  rw [hk]
  exact (by decide : ∀ a b : BitVec 1, a &&& (0#1 &&& b) = 0#1) _ _

/-- The full core phase preserves memory on a successful null reply. -/
theorem coreAct_mem_gateReturn_zero_reply (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hz : (Hw.retW E).eval σ = 0#32) (ad : Nat) :
    ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
      ad 32 = σ.mems "mem" ad 32 := by
  have hport := retireMem_gateReturn_sel σ E hifsel hifexcl hopc
  have hmen := retCirc_memEn_zero_reply σ E hz
  rw [coreAct_run_retire_eq m σ _ hifv hcl,
      retireAct_run_mems σ _ ad 32]
  show (if (((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1,
          .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
        (.lit 0 : Expr 32))).1).eval σ = 1#1 then _
    else ((Hw.refillAct m).run σ σ)).mems "mem" ad 32 = _
  rw [if_neg (by rw [hport.1, hmen]; decide)]
  exact refill_pres_mem m σ "mem" ad 32

/-- With a non-null reply, the return kill predicate is exactly the retiring
domain and selected reply slot. -/
theorem retKilled_nonzero_eval (σ : Loom.Hw.St) (d : DomainId)
    (hnz : (Hw.retNZ d).eval σ = 1#1) (dm : Expr 2) (sl : Expr 4) :
    (Hw.retKilled d dm sl).eval σ =
      (Expr.and (.eq dm (Hw.dLit d))
        (.eq sl (Hw.retSel d).slot)).eval σ := by
  unfold Hw.retKilled Hw.andAll
  change (Hw.retNZ d).eval σ &&&
      ((Expr.eq dm (Hw.dLit d)).eval σ &&&
        (Expr.eq sl (Hw.retSel d).slot).eval σ) = _
  rw [hnz]
  exact (by decide : ∀ a b : BitVec 1,
    1#1 &&& (a &&& b) = a &&& b) _ _

/-- The return Mover guard recognizes precisely an endpoint in the selected
non-null reply slot. -/
theorem movKilledE_return_nonzero_iff (σ : Loom.Hw.St) (d : DomainId)
    (S : Slot)
    (hslot : (Hw.retSel d).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.retNZ d).eval σ = 1#1) :
    ((Hw.movKilledE (Hw.retKilled d)).eval σ = 1#1) ↔
      match Hw.absMover σ with
      | none => False
      | some job =>
          (job.src.dom = d ∧ job.src.slot = S) ∨
          (job.dst.dom = d ∧ job.dst.slot = S) := by
  have heval : (Hw.movKilledE (Hw.retKilled d)).eval σ =
      σ.regs "mov_v" 1 &&&
        ((Expr.and (.eq Hw.movSrcDom (Hw.dLit d))
            (.eq Hw.movSrcSlot (Hw.retSel d).slot)).eval σ |||
         (Expr.and (.eq Hw.movDstDom (Hw.dLit d))
            (.eq Hw.movDstSlot (Hw.retSel d).slot)).eval σ) := by
    unfold Hw.movKilledE
    change σ.regs "mov_v" 1 &&&
        ((Hw.retKilled d Hw.movSrcDom Hw.movSrcSlot).eval σ |||
         (Hw.retKilled d Hw.movDstDom Hw.movDstSlot).eval σ) = _
    rw [retKilled_nonzero_eval σ d hnz,
      retKilled_nonzero_eval σ d hnz]
  rw [heval]
  by_cases hv : σ.regs "mov_v" 1 = 1#1
  · rw [absMover_some σ hv, bv1_and_eq_one, bv1_or_eq_one]
    simp only [Hw.movSrcDom, Hw.movSrcSlot, Hw.movDstDom, Hw.movDstSlot]
    rw [slotKilled_ref_eval σ d (Hw.retSel d).slot S hslot
        (.reg 14 "mov_src"),
      slotKilled_ref_eval σ d (Hw.retSel d).slot S hslot
        (.reg 14 "mov_dst")]
    simp [hv]
    rfl
  · have hv0 : σ.regs "mov_v" 1 = 0#1 := bv1_ne_one.mp hv
    simp [absMover_none σ hv, hv0]

/-- A non-null return reply is the recipient-relative handle selected by the
shared transfer machinery. -/
theorem gateReturnReplyE_eval_nonzero (σ : Loom.Hw.St) (d : DomainId)
    (cls : CapClass) (hnz : (Hw.retNZ d).eval σ = 1#1)
    (hcls : (Hw.field (Hw.retSel d).kindW 0 1).eval σ =
      if cls = .gate then 1#1 else 0#1) :
    (gateReturnReplyE d).eval σ =
      let caller : DomainId := finOfBv (by decide) ((Hw.retCl d).eval σ)
      Handle.encode
        ⟨finOfBv (by decide) ((Hw.freeSlotIdx caller).eval σ),
          (Hw.genOfE caller (Hw.freeSlotIdx caller)).eval σ, cls⟩ := by
  simp only [gateReturnReplyE, Expr.eval]
  rw [hnz, if_pos rfl]
  exact transferHandleAt_eval σ (Hw.retCl d) (Hw.retSel d) cls hcls

/-- The five concrete return checks all pass under the successful-arm
hypotheses. -/
theorem retOkE_of_passes (σ : Loom.Hw.St) (d : DomainId) (gid : GateId)
    (act : Activation)
    (hserv : ((Hw.abs σ).doms d).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hstale : (Expr.and (Hw.retNZ d) (.not (Hw.retSel d).live)).eval σ ≠ 1#1)
    (hclass : (Expr.and (Hw.retNZ d) (.not (Hw.retSel d).clsOk)).eval σ ≠ 1#1)
    (hblocked : (Expr.and (Hw.retNZ d)
      (Hw.transferBlocked d (Hw.retCl d) (Hw.retSel d))).eval σ ≠ 1#1) :
    (Hw.retOkE d).eval σ = 1#1 := by
  apply (okOf_eval_iff σ (Hw.retChecks d)).mpr
  have hgid := retGid_eval_selected σ d gid hserv
  have hservV : σ.regs (Hw.dsrvV d) 1 = 1#1 := by
    change (if σ.regs (Hw.dsrvV d) 1 = 1#1 then some _ else none) =
      some gid at hserv
    by_contra hv
    rw [if_neg hv] at hserv
    contradiction
  have hactV : σ.regs (Hw.gactV gid) 1 = 1#1 := by
    change (if σ.regs (Hw.gactV gid) 1 = 1#1 then some _ else none) =
      some act at hact
    by_contra hv
    rw [if_neg hv] at hact
    contradiction
  intro x hx
  simp only [Hw.retChecks, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx | hx | hx
  · subst x
    simp [Expr.eval, hservV]
  · subst x
    have hactive : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.retGid d)).eval σ = 1#1 := by
      rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
      exact hactV
    simp [Expr.eval, hactive]
  · simpa [hx] using hstale
  · simpa [hx] using hclass
  · simpa [hx] using hblocked

/-- Successful non-null return memory commit, specialized from the shared
sweeping-operation bridge. -/
theorem coreAct_mem_gateReturn_success_nonzero (m : Manifest)
    (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (base target : MachineState)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hslot : (Hw.retSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.retNZ E).eval σ = 1#1)
    (hok : (Hw.retOkE E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled E dm sl).eval σ)
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
  have hport := retireMem_gateReturn_sel σ E hifsel hifexcl hopc
  apply coreAct_mem_sweep_success m σ (Hw.retOkE E) (Hw.retKilled E)
    (Hw.retCirc E) E S base target hifv hcl hport
  · rfl
  · rfl
  · rfl
  · exact hok
  · exact movKilledE_return_nonzero_iff σ E S hslot hnz
  · intro job hjob
    have hstatus := statusAuthE_post_eval σ (Hw.retKilled E) hkills
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

/-- Successful non-null return specialization of the shared one-source-slot
Mover-state bridge. -/
theorem absMover_moverAct_return (σ acc : Loom.Hw.St) (τ : MachineState)
    (E : DomainId) (S : Slot)
    (hslot : (Hw.retSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.retNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled E dm sl).eval σ)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hkindS : ∀ job, Hw.absMover σ = some job →
      ¬(job.src.dom = E ∧ job.src.slot = S) →
      Option.map CapEntry.kind
          ((τ.doms job.src.dom).liveCap job.src.slot job.src.gen) =
        Option.map CapEntry.kind
          (((Hw.abs σ).doms job.src.dom).liveCap job.src.slot job.src.gen))
    (hkindD : ∀ job, Hw.absMover σ = some job →
      ¬(job.dst.dom = E ∧ job.dst.slot = S) →
      Option.map CapEntry.kind
          ((τ.doms job.dst.dom).liveCap job.dst.slot job.dst.gen) =
        Option.map CapEntry.kind
          (((Hw.abs σ).doms job.dst.dom).liveCap job.dst.slot job.dst.gen))
    (hjob : τ.mover =
      match Hw.absMover σ with
      | none => none
      | some job =>
          if (job.src.dom = E ∧ job.src.slot = S) ∨
              (job.dst.dom = E ∧ job.dst.slot = S)
          then none else some job) :
    Hw.absMover (Hw.moverAct.run σ acc) = (moverPhase τ).mover := by
  apply absMover_moverAct_transfer σ acc τ E (Hw.retSel E).slot S hslot
  · intro dm sl
    rw [hkills]
    exact retKilled_nonzero_eval σ E hnz dm sl
  · exact hnew
  · exact hkindS
  · exact hkindD
  · exact hjob

/-- Successful non-null return specialization of the shared one-source-slot
Mover-memory bridge. -/
theorem moverAct_mem_return (σ acc : Loom.Hw.St) (τ : MachineState)
    (E : DomainId) (S : Slot)
    (hslot : (Hw.retSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.retNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled E dm sl).eval σ)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hkindS : ∀ job, Hw.absMover σ = some job →
      ¬(job.src.dom = E ∧ job.src.slot = S) →
      Option.map CapEntry.kind
          ((τ.doms job.src.dom).liveCap job.src.slot job.src.gen) =
        Option.map CapEntry.kind
          (((Hw.abs σ).doms job.src.dom).liveCap job.src.slot job.src.gen))
    (hkindD : ∀ job, Hw.absMover σ = some job →
      ¬(job.dst.dom = E ∧ job.dst.slot = S) →
      Option.map CapEntry.kind
          ((τ.doms job.dst.dom).liveCap job.dst.slot job.dst.gen) =
        Option.map CapEntry.kind
          (((Hw.abs σ).doms job.dst.dom).liveCap job.dst.slot job.dst.gen))
    (hjob : τ.mover =
      match Hw.absMover σ with
      | none => none
      | some job =>
          if (job.src.dom = E ∧ job.src.slot = S) ∨
              (job.dst.dom = E ∧ job.dst.slot = S)
          then none else some job)
    (hauthτ : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
              Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true)
    (hmemτ : ∀ b : Addr, acc.mems "mem" b.toNat 32 = τ.mem b)
    (hswτ : ∀ job, Hw.absMover σ = some job →
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
          (.memRead 32 "mem" sc))) = τ.mem (sc.eval σ))
    (a : Addr) :
    (Hw.moverAct.run σ acc).mems "mem" a.toNat 32 =
      (moverPhase τ).mem a := by
  apply moverAct_mem_transfer σ acc τ E (Hw.retSel E).slot S hslot
  · intro dm sl
    rw [hkills]
    exact retKilled_nonzero_eval σ E hnz dm sl
  · exact hnew
  · exact hkindS
  · exact hkindD
  · exact hjob
  · exact hauthτ
  · exact hmemτ
  · exact hswτ

/-- Full-cycle assembly for a successful non-null return once its semantic
branch and post-transfer faces have been identified. -/
theorem square_retire_gateReturn_payload (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId) (S : Slot) (X : Act) (τ2 : MachineState)
    (hslot : (Hw.retSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.retNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled E dm sl).eval σ)
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
    (hauth : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
              Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true)
    (hmem : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = τ2.mem b)
    (hsw : ∀ job, Hw.absMover σ = some job →
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
  · exact absMover_moverAct_return σ _ τ2 E S hslot hnz hkills hnew
      hkindS hkindD hjob
  · intro a
    exact moverAct_mem_return σ _ τ2 E S hslot hnz hkills hnew
      hkindS hkindD hjob hauth hmem hsw a
  · exact hcyc
  · exact hτ2if

/-- Return-specific status-authority bridge over an arbitrary structural
transfer prefix. -/
theorem sAuth_return_backings_eval (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (τ : MachineState)
    (hslot : (Hw.retSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.retNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hregions : ∀ c : DomainId,
      (τ.doms c).regions = ((Hw.abs σ).doms c).regions)
    (hbacking : ∀ c r rg, ((Hw.abs σ).doms c).regions r = some rg →
      τ.liveRef rg.backing =
        if rg.backing.dom = E ∧ rg.backing.slot = S then false
        else (Hw.abs σ).liveRef rg.backing)
    (hwf : Wf (Hw.abs σ)) (ow : Expr 2) (sa : Expr 12) :
    ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
      τ.sweepRegions.domCovers (finOfBv (by decide) (ow.eval σ))
        (sa.eval σ) ⟨false, true, false⟩ = true := by
  apply sAuth_region_eq_eval σ τ.sweepRegions hmapz
  intro c r
  exact sweepRegions_transfer_region_eq_backings σ E (Hw.retSel E).slot S
    τ hslot (fun dm sl => by
      rw [hkills]
      exact retKilled_nonzero_eval σ E hnz dm sl)
    hmapz hunmapz hregions hbacking hwf c r

/-- Status authority for a return transfer from the post-refill retirement
base. -/
theorem sAuth_return_retire_transfer (m : Manifest) (σ : Loom.Hw.St)
    (E T : DomainId) (S NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (hslot : (Hw.retSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.retNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled E dm sl).eval σ)
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
  have h := sAuth_return_backings_eval σ E S τc hslot hnz hkills
    hmapz hunmapz hregions hbacking hwf ow sa
  simpa [transferStructural, τc, base] using h

/-- A structural return transfer commutes with the eager retirement PC
increment: the successful return tail restores the callee PC and resumes the
distinct caller, so the prefixed and hardware-base forms coincide. -/
theorem returnAbstractSuccess_transfer_state (m : Manifest)
    (σ : Loom.Hw.St) (d : DomainId) (gid : GateId) (act : Activation)
    (reply : Loom.Word32) (hne : d ≠ act.caller) (NS : Slot)
    (kind : CapKind) (moved : Option (LineageId × CapRef))
    (oldRef newRef : CapRef) (S : Slot) :
    let base : MachineState :=
      { refillPhase m (Hw.abs σ) with inflight := none }
    let prefixed := base.setDom d fun ds => { ds with pc := ds.pc + 1 }
    let hwStruct := transferStructural base act.caller NS kind moved
      oldRef newRef d S
    let specStruct := (transferStructural prefixed act.caller NS kind moved
      oldRef newRef d S).sweepMover
    returnAbstractSuccess specStruct d gid act reply =
      returnAbstractSuccess hwStruct.sweepMover d gid act reply := by
  dsimp only
  let base : MachineState :=
    { refillPhase m (Hw.abs σ) with inflight := none }
  let hwStruct := transferStructural base act.caller NS kind moved
    oldRef newRef d S
  have hcomm : transferStructural
        (base.setDom d fun ds => { ds with pc := ds.pc + 1 })
        act.caller NS kind moved oldRef newRef d S =
      hwStruct.setDom d (fun ds => { ds with pc := ds.pc + 1 }) := by
    simpa [hwStruct] using transferStructural_setPc base d act.caller NS
      kind moved oldRef newRef S hne
  rw [hcomm, sweepMover_setPc]
  exact returnAbstractSuccess_setPc hwStruct.sweepMover d gid act reply hne

private def gateReturnTransferBase (m : Manifest) (σ : Loom.Hw.St) :
    MachineState :=
  { refillPhase m (Hw.abs σ) with inflight := none }

private def gateReturnPrefixed (m : Manifest) (σ : Loom.Hw.St)
    (d : DomainId) : MachineState :=
  (gateReturnTransferBase m σ).setDom d fun ds => { ds with pc := ds.pc + 1 }

private def gateReturnHwStruct (m : Manifest) (σ : Loom.Hw.St)
    (d : DomainId) (act : Activation) (S NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef) :
    MachineState :=
  transferStructural (gateReturnTransferBase m σ) act.caller NS kind moved
    oldRef newRef d S

private def gateReturnSpecStruct (m : Manifest) (σ : Loom.Hw.St)
    (d : DomainId) (act : Activation) (S NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef) :
    MachineState :=
  (transferStructural (gateReturnPrefixed m σ d) act.caller NS kind moved
    oldRef newRef d S).sweepMover

private def gateReturnTransferPost (m : Manifest) (σ : Loom.Hw.St)
    (d : DomainId) (gid : GateId) (act : Activation) (reply : Loom.Word32)
    (S NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef) :
    MachineState :=
  returnAbstractSuccess
    (gateReturnHwStruct m σ d act S NS kind moved oldRef newRef).sweepMover
    d gid act reply

private theorem returnAbstractSuccess_sweepMover_doms (τ : MachineState)
    (d : DomainId) (gid : GateId) (act : Activation) (reply : Loom.Word32)
    (x : DomainId) :
    (returnAbstractSuccess τ d gid act reply).doms x =
      (returnAbstractSuccess τ.sweepMover d gid act reply).doms x := by
  simp [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update]

private theorem returnAbstractSuccess_sweepMover_gates (τ : MachineState)
    (d : DomainId) (gid : GateId) (act : Activation) (reply : Loom.Word32)
    (g : GateId) :
    (returnAbstractSuccess τ d gid act reply).gates g =
      (returnAbstractSuccess τ.sweepMover d gid act reply).gates g := by
  simp [returnAbstractSuccess, MachineState.setDom]

/-- Specification normalization shared by the root and derived successful
return transfers. -/
private theorem gateReturn_success_transfer_spec (m : Manifest)
    (σ : Loom.Hw.St) (d : DomainId) (gid : GateId) (act : Activation)
    (reply : Loom.Word32) (S NS : Slot) (kind : CapKind)
    (moved : Option (LineageId × CapRef)) (oldRef newRef : CapRef)
    (hz0 : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hd : d = finOfBv (by decide) (σ.regs "if_dom" 2))
    (hserv : ((Hw.abs σ).doms d).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hne : d ≠ act.caller)
    (htransfer : Machines.Lnp64u.Isa.transferByHandle d act.caller
      ((Hw.retW d).eval σ) (gateReturnPrefixed m σ d) =
        .ok reply (gateReturnSpecStruct m σ d act S NS kind moved
          oldRef newRef)) :
    corePhase m (refillPhase m (Hw.abs σ)) =
      gateReturnTransferPost m σ d gid act reply S NS kind moved
        oldRef newRef := by
  let W := σ.regs "if_word" 32
  let base := gateReturnTransferBase m σ
  let τ0 := gateReturnPrefixed m σ d
  let c : Ctx := { d := d, pc := (base.doms d).pc, op := operandsOf W }
  have hop : Machines.Lnp64u.sig.opcodeOf W = (23#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun op => op.opcode == (23#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := d, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [W, hd] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire base d W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
    rfl
  have hR : (Hw.retW d).eval σ =
      ((Hw.abs σ).doms d).reg (operandsOf W).rs1 :=
    retW_eval σ hz0 d (operandsOf W).rs1 rfl
  have hreg : (τ0.doms d).reg (operandsOf W).rs1 =
      ((Hw.abs σ).doms d).reg (operandsOf W).rs1 :=
    specReg_bridge m σ d _
  have hword : (τ0.doms c.d).reg c.op.rs1 = (Hw.retW d).eval σ := by
    simp only [c]
    rw [hreg, hR]
  have hserv0 : (τ0.doms c.d).serving = some gid := by
    simp [τ0, gateReturnPrefixed, gateReturnTransferBase, c, MachineState.setDom,
      Loom.Fun.update, refillPhase_serving, hserv]
  have hact0 : (τ0.gates gid).act = some act := by
    simp [τ0, gateReturnPrefixed, gateReturnTransferBase, MachineState.setDom,
      refillPhase_gates, hact]
  have hexec : Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 =
      .ok () (returnAbstractSuccess
        (gateReturnSpecStruct m σ d act S NS kind moved oldRef newRef)
        d gid act reply) := by
    exact gateReturnExec_success c τ0 _ gid act reply hserv0 hact0
      (by simpa [c, hword] using htransfer)
  rw [hcore0, retire_gateReturn_exec base d W hdec]
  change (match Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 with
    | .ok _ τ' => τ'
    | .err er τ' => τ'.setDom d
        (fun ds => ds.setReg (operandsOf W).rd er.toWord)
    | .fault f => haltWith base d f) =
      gateReturnTransferPost m σ d gid act reply S NS kind moved
        oldRef newRef
  rw [hexec]
  simpa [gateReturnSpecStruct, gateReturnPrefixed, gateReturnTransferPost,
    gateReturnHwStruct, gateReturnTransferBase, τ0, base] using
      returnAbstractSuccess_transfer_state m σ d gid act reply hne NS kind
        moved oldRef newRef S

/-- Common full-cycle proof for root and derived successful return transfers. -/
private theorem square_retire_gateReturn_success_transfer
    (m : Manifest) (σ : Loom.Hw.St) (d : DomainId) (gid : GateId)
    (act : Activation) (reply : Loom.Word32) (S NS : Slot)
    (kind : CapKind) (moved : Option (LineageId × CapRef))
    (oldRef newRef : CapRef)
    (hz0 : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (hd : d = finOfBv (by decide) (σ.regs "if_dom" 2))
    (hifsel : (Hw.ifDomIs d).eval σ = 1#1)
    (hifexcl : ∀ x : DomainId, x ≠ d → (Hw.ifDomIs x).eval σ ≠ 1#1)
    (hserv : ((Hw.abs σ).doms d).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hne : d ≠ act.caller)
    (hslot : (Hw.retSel d).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.retNZ d).eval σ = 1#1)
    (hok : (Hw.retOkE d).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled d dm sl).eval σ)
    (hnew : ∀ x : DomainId, (Hw.newJobSet x).eval σ = 0#1)
    (hmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "map", Hw.mapOkE x,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hswz : ∀ (x : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "sw",
        Hw.domCoversE x
          (Hw.field (.add (Hw.readReg x Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg x Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1)
    (hwfAbs : Wf (Hw.abs σ))
    (hfree : ((Hw.abs σ).doms act.caller).caps NS = none)
    (htransfer : Machines.Lnp64u.Isa.transferByHandle d act.caller
      ((Hw.retW d).eval σ) (gateReturnPrefixed m σ d) =
        .ok reply (gateReturnSpecStruct m σ d act S NS kind moved
          oldRef newRef))
    (habsTransfer :
      let acc0 := (Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)
      Hw.abs ((Hw.transferA d (Hw.retCl d) (Hw.retSel d)).run σ acc0) =
        gateReturnHwStruct m σ d act S NS kind moved oldRef newRef)
    (hreply : (gateReturnReplyE d).eval σ = reply) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  let acc0 := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  let X := gateReturnSuccessA d
  let hwStruct := gateReturnHwStruct m σ d act S NS kind moved oldRef newRef
  let τ2 := gateReturnTransferPost m σ d gid act reply S NS kind moved
    oldRef newRef
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
    exact gateReturn_success_transfer_spec m σ d gid act reply S NS kind
      moved oldRef newRef hz0 hifv hcl hopc hd hserv hact hne htransfer
  have hgid := retGid_eval_selected σ d gid hserv
  have hcaller := retCl_eval_selected σ d gid act hserv hact
  have habsRet : Hw.abs ((gateReturnSuccessA d).run σ acc0) =
      returnAbstractSuccess hwStruct d gid act reply := by
    rw [abs_gateReturnSuccessA σ acc0 d gid act reply hne hgid hcaller hact
      hreply]
    rw [gateReturnTransferA_run_nonzero σ acc0 d hnz, habsTransfer]
  have hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w := by
    intro rn w
    have hdval : d.val = (σ.regs "if_dom" 2).toNat := by
      rw [hd]
      rfl
    rw [coreAct_run_retire_eq m σ _ hifv hcl,
      retireAct_run_regs σ _ d hdval rn w,
      retireFor_gateReturn_success σ _ d hopc hok]
    rfl
  have hframes := returnAbstractSuccess_structural_frames
    hwStruct.sweepMover d gid act reply
  have habsD : ∀ x, Hw.absDom
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) x = τ2.doms x := by
    intro x
    change Hw.absDom ((gateReturnSuccessA d).run σ acc0) x = τ2.doms x
    rw [show Hw.absDom ((gateReturnSuccessA d).run σ acc0) x =
      (returnAbstractSuccess hwStruct d gid act reply).doms x from
        congrFun (congrArg MachineState.doms habsRet) x]
    change (returnAbstractSuccess hwStruct d gid act reply).doms x =
      (returnAbstractSuccess hwStruct.sweepMover d gid act reply).doms x
    exact returnAbstractSuccess_sweepMover_doms hwStruct d gid act reply x
  have habsG : ∀ g, Hw.absGate
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) g = τ2.gates g := by
    intro g
    change Hw.absGate ((gateReturnSuccessA d).run σ acc0) g = τ2.gates g
    rw [show Hw.absGate ((gateReturnSuccessA d).run σ acc0) g =
      (returnAbstractSuccess hwStruct d gid act reply).gates g from
        congrFun (congrArg MachineState.gates habsRet) g]
    change (returnAbstractSuccess hwStruct d gid act reply).gates g =
      (returnAbstractSuccess hwStruct.sweepMover d gid act reply).gates g
    exact returnAbstractSuccess_sweepMover_gates hwStruct d gid act reply g
  have hkindS : ∀ job, Hw.absMover σ = some job →
      ¬(job.src.dom = d ∧ job.src.slot = S) →
      Option.map CapEntry.kind
          ((τ2.doms job.src.dom).liveCap job.src.slot job.src.gen) =
        Option.map CapEntry.kind
          (((Hw.abs σ).doms job.src.dom).liveCap job.src.slot job.src.gen) := by
    intro job hjob hout
    unfold DomainState.liveCap
    rw [show (τ2.doms job.src.dom).caps =
        (hwStruct.sweepMover.doms job.src.dom).caps from hframes.1 _,
      show (τ2.doms job.src.dom).slotGen =
        (hwStruct.sweepMover.doms job.src.dom).slotGen from hframes.2.1 _,
      sweepMover_doms]
    exact transferStructural_retire_liveKind m σ act.caller NS kind moved
      oldRef newRef d S job.src hfree
      (moverEndpoints_live hwfAbs job hjob).1 hout
  have hkindD : ∀ job, Hw.absMover σ = some job →
      ¬(job.dst.dom = d ∧ job.dst.slot = S) →
      Option.map CapEntry.kind
          ((τ2.doms job.dst.dom).liveCap job.dst.slot job.dst.gen) =
        Option.map CapEntry.kind
          (((Hw.abs σ).doms job.dst.dom).liveCap job.dst.slot job.dst.gen) := by
    intro job hjob hout
    unfold DomainState.liveCap
    rw [show (τ2.doms job.dst.dom).caps =
        (hwStruct.sweepMover.doms job.dst.dom).caps from hframes.1 _,
      show (τ2.doms job.dst.dom).slotGen =
        (hwStruct.sweepMover.doms job.dst.dom).slotGen from hframes.2.1 _,
      sweepMover_doms]
    exact transferStructural_retire_liveKind m σ act.caller NS kind moved
      oldRef newRef d S job.dst hfree
      (moverEndpoints_live hwfAbs job hjob).2 hout
  have hjob : τ2.mover =
      match Hw.absMover σ with
      | none => none
      | some job =>
          if (job.src.dom = d ∧ job.src.slot = S) ∨
              (job.dst.dom = d ∧ job.dst.slot = S)
          then none else some job := by
    rw [show τ2.mover = hwStruct.sweepMover.mover from hframes.2.2.2.2.1]
    exact transferStructural_retire_sweepMover_mover m σ act.caller NS kind
      moved oldRef newRef d S hfree hwfAbs
  have hauth : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun x =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit x), Hw.rgnVPostE x r,
            Hw.rgnCoversVal (Hw.rgnValPostE x r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true := by
    intro ow sa
    unfold MachineState.domCovers
    rw [show (τ2.doms _).regions = (hwStruct.sweepMover.doms _).regions
      from hframes.2.2.2.1 _, sweepMover_doms]
    exact sAuth_return_retire_transfer m σ d act.caller S NS kind moved
      oldRef newRef hslot hnz hkills hmapz hunmapz hfree hwfAbs ow sa
  have hmem : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = τ2.mem b := by
    intro b
    apply coreAct_mem_gateReturn_success_nonzero m σ d S hwStruct τ2
      hifv hcl hifsel hifexcl hopc hslot hnz hok hkills hmapz hunmapz
      (sAuth_return_retire_transfer m σ d act.caller S NS kind moved oldRef
        newRef hslot hnz hkills hmapz hunmapz hfree hwfAbs) ?_ ?_ b
    · intro a
      change (gateReturnHwStruct m σ d act S NS kind moved oldRef newRef).mem a =
        σ.mems "mem" a.toNat 32
      exact retireBase_mem m σ a
    · intro a
      rw [show τ2.mem = hwStruct.sweepMover.mem from hframes.2.2.2.2.2]
      exact transferStructural_retire_sweepMover_mem m σ act.caller NS kind
        moved oldRef newRef d S hfree hwfAbs a
  have hsw : ∀ job, Hw.absMover σ = some job →
      ¬((job.src.dom = d ∧ job.src.slot = S) ∨
        (job.dst.dom = d ∧ job.dst.slot = S)) →
      ∀ sc : Expr 12, Expr.eval σ
        (((List.finRange numDomains).foldr
          (fun x acc' =>
            Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "sw",
                Hw.domCoversE x
                  (Hw.field (.add (Hw.readReg x Hw.rs1E) Hw.immX) 0 12)
                  ⟨false, true, false⟩,
                .eq (Hw.field (.add (Hw.readReg x Hw.rs1E) Hw.immX)
                  0 12) sc]) (Hw.readReg x Hw.rs2E) acc')
          (.memRead 32 "mem" sc))) = τ2.mem (sc.eval σ) := by
    intro job hjob' hsurv sc
    rw [srcWord_quiescent σ hswz sc,
      show τ2.mem = hwStruct.sweepMover.mem from hframes.2.2.2.2.2]
    change σ.mems "mem" (sc.eval σ).toNat 32 =
      (transferStructural
        { refillPhase m (Hw.abs σ) with inflight := none }
        act.caller NS kind moved oldRef newRef d S).sweepMover.mem (sc.eval σ)
    rw [transferStructural_retire_sweepMover_mem m σ act.caller NS kind
      moved oldRef newRef d S hfree hwfAbs (sc.eval σ), hjob']
    simp [hsurv]
  apply square_retire_gateReturn_payload m σ d S X τ2 hslot hnz hkills
    hnew hcoreR
  · unfold X
    exact ifv_notin_gateReturnSuccess d
  · exact hspec
  · exact habsD
  · exact habsG
  · exact hkindS
  · exact hkindD
  · exact hjob
  · exact hauth
  · exact hmem
  · exact hsw
  · rw [← hspec, corePhase_cycle, refillPhase_cycle]
    rfl
  · change (returnAbstractSuccess hwStruct.sweepMover d gid act reply).inflight =
      none
    simp [returnAbstractSuccess, MachineState.setDom, hwStruct,
      gateReturnHwStruct, transferStructural, installTransferred,
      gateReturnTransferBase]

/-- A successful null reply has no core kill footprint. -/
theorem Inert.of_successful_gateReturn_zero (σ : Loom.Hw.St)
    (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ = 1#1)
    (hok : ∀ d : DomainId, d = E → (Hw.retOkE d).eval σ = 1#1)
    (hz : (Hw.retNZ E).eval σ = 0#1)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1) : Inert σ where
  killed := by
    intro dm sl
    rw [killedByCoreE_gateReturn_eval σ E hret hif hdrop hrev hcall
      hreturn hok]
    unfold Hw.retKilled Hw.andAll
    simp only [Expr.eval]
    rw [hz]
    exact (by decide : ∀ x : BitVec 1, 0#1 &&& x = 0#1) _
  newJob := hnew

private theorem square_retire_gate_payload_abs (m : Manifest)
    (σ : Loom.Hw.St) (X : Act) (τ2 : MachineState)
    (hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w)
    (hXifv : ("if_v", 1) ∉ X.regWrites)
    (hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2)
    (habs : Hw.abs
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) = τ2)
    (hmover : Hw.absMover
      (Hw.moverAct.run σ
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))) =
      (moverPhase τ2).mover)
    (hmem : ∀ a : Addr,
      (Hw.moverAct.run σ
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))).mems "mem"
          a.toNat 32 = (moverPhase τ2).mem a)
    (hcyc : τ2.cycle = σ.regs "cycle" 32)
    (hτ2if : τ2.inflight = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  exact square_retire_gate_payload m σ X τ2 hcoreR hXifv hspec
    (fun x => congrFun (congrArg MachineState.doms habs) x)
    (fun g => congrFun (congrArg MachineState.gates habs) g)
    hmover hmem hcyc hτ2if

private def gateReturnIssuer (σ : Loom.Hw.St) : DomainId :=
  finOfBv (by decide) (σ.regs "if_dom" 2)

private def gateReturnBase (m : Manifest) (σ : Loom.Hw.St) : MachineState :=
  { refillPhase m (Hw.abs σ) with inflight := none }

private def gateReturnZeroPost (m : Manifest) (σ : Loom.Hw.St)
    (gid : GateId) (act : Activation) : MachineState :=
  returnAbstractSuccess (gateReturnBase m σ) (gateReturnIssuer σ) gid act 0

private theorem gateReturnIssuer_ne_caller (m : Manifest) (hwf : m.WF)
    (σ : Loom.Hw.St) (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1) (gid : GateId) (act : Activation)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    gateReturnIssuer σ ≠ act.caller := by
  simpa [gateReturnIssuer] using
    gateReturnIssuer_ne_caller_of_reachable m hwf σ hsr hifv gid act hact

private theorem gateReturn_zero_spec (m : Manifest) (hwf : m.WF)
    (σ : Loom.Hw.St) (hsr : (machine m).Reachable (Hw.abs σ))
    (hz0 : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (gid : GateId) (act : Activation)
    (hserv : ((Hw.abs σ).doms (gateReturnIssuer σ)).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hzero : (Hw.retW (gateReturnIssuer σ)).eval σ = 0#32) :
    corePhase m (refillPhase m (Hw.abs σ)) =
      gateReturnZeroPost m σ gid act := by
  let W := σ.regs "if_word" 32
  let E := gateReturnIssuer σ
  let base := gateReturnBase m σ
  let c : Ctx := { d := E, pc := (base.doms E).pc, op := operandsOf W }
  let τ0 := base.setDom E fun ds => { ds with pc := ds.pc + 1 }
  have hop : Machines.Lnp64u.sig.opcodeOf W = (23#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (23#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    simpa [E, W, gateReturnIssuer] using absInflight_some σ hifv
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ)) =
      retire base E W := by
    rw [corePhase_retire m _ _ hfl
      (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
    rfl
  have hserv0 : (τ0.doms c.d).serving = some gid := by
    simp [τ0, c, base, gateReturnBase, MachineState.setDom,
      Loom.Fun.update, refillPhase_serving, hserv, E]
  have hact0 : (τ0.gates gid).act = some act := by
    simp [τ0, base, gateReturnBase, MachineState.setDom,
      refillPhase_gates, hact]
  have htransfer : Machines.Lnp64u.Isa.transferByHandle c.d act.caller
      ((τ0.doms c.d).reg c.op.rs1) τ0 = .ok 0 τ0 := by
    have hw : (τ0.doms c.d).reg c.op.rs1 = 0#32 := by
      have hR : (Hw.retW E).eval σ =
          ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
        retW_eval σ hz0 E (operandsOf W).rs1 rfl
      have hreg : (τ0.doms E).reg (operandsOf W).rs1 =
          ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
        specReg_bridge m σ E _
      simp only [c]
      rw [hreg, ← hR]
      simpa [E] using hzero
    rw [hw]
    exact transferByHandle_eq_zero τ0 c.d act.caller
  have hexec : Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 =
      .ok () (returnAbstractSuccess τ0 c.d gid act 0) :=
    gateReturnExec_success c τ0 τ0 gid act 0 hserv0 hact0 htransfer
  have hne : E ≠ act.caller := by
    simpa [E] using gateReturnIssuer_ne_caller m hwf σ hsr hifv gid act hact
  rw [hcore0, retire_gateReturn_exec base E W hdec]
  change (match Machines.Lnp64u.Isa.Wip.gateReturnExec c τ0 with
    | .ok _ τ' => τ'
    | .err er τ' => τ'.setDom E
        (fun ds => ds.setReg (operandsOf W).rd er.toWord)
    | .fault f => haltWith base E f) = gateReturnZeroPost m σ gid act
  rw [hexec]
  simpa [c, τ0, gateReturnZeroPost, gateReturnBase, base, E] using
    returnAbstractSuccess_setPc base E gid act 0 hne

/-- Complete successful null-reply return. -/
theorem square_retire_gateReturn_success_zero (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz0 : R0Zero σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (gid : GateId) (act : Activation)
    (hserv : ((Hw.abs σ).doms
      (finOfBv (by decide) (σ.regs "if_dom" 2))).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hok : (Hw.retOkE
      (finOfBv (by decide) (σ.regs "if_dom" 2))).eval σ = 1#1)
    (hzero : (Hw.retW
      (finOfBv (by decide) (σ.regs "if_dom" 2))).eval σ = 0#32) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  let E := gateReturnIssuer σ
  let base := gateReturnBase m σ
  let τ2 := gateReturnZeroPost m σ gid act
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hne : E ≠ act.caller := by
    simpa [E, gateReturnIssuer] using
      gateReturnIssuer_ne_caller m hwf σ hsr hifv gid act
        hact
  have hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2 := by
    simpa [τ2] using gateReturn_zero_spec m hwf σ hsr hz0 hifv hcl hopc
      gid act (by simpa [gateReturnIssuer] using hserv) hact
      (by simpa [gateReturnIssuer] using hzero)
  have hgid := retGid_eval_selected σ E gid (by simpa [E] using hserv)
  have hcaller := retCl_eval_selected σ E gid act
    (by simpa [E] using hserv) hact
  have hnz0 : (Hw.retNZ E).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro hnz
    exact (retNZ_eval_iff σ E).mp hnz (by simpa [E] using hzero)
  have hreply : (gateReturnReplyE E).eval σ = 0#32 := by
    simp [gateReturnReplyE, Expr.eval, hnz0]
  let acc0 := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  have habsBase : Hw.abs acc0 = base :=
    abs_refill_clearInflight m hwf hfit σ hsync
  have habsRet : Hw.abs ((gateReturnSuccessA E).run σ acc0) = τ2 := by
    rw [abs_gateReturnSuccessA σ acc0 E gid act 0 hne hgid hcaller hact
      hreply]
    rw [gateReturnTransferA_run_zero σ acc0 E hnz0, habsBase]
    rfl
  have hret := retiringE_one σ hifv hcl
  have hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1 := by
    intro d
    by_cases hd : d = E
    · subst d; simpa using hifsel
    · rw [if_neg hd, bv1_ne_one.mp (hifexcl d hd)]
  have hmn : (Hw.isMn "gate_return").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_return" = 23#6).symm
  have hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_drop" 23#6 hopc (by decide +kernel)
  have hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "cap_revoke" 23#6 hopc (by decide +kernel)
  have hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1 :=
    isMn_ne_of_opc σ "gate_call" 23#6 hopc (by decide +kernel)
  have hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1 := by
    intro d
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 23#6 hopc (by decide +kernel)
  have hin : Inert σ := Inert.of_successful_gateReturn_zero σ E hret hif
    hdrop hrev hcall hmn (fun d hd => by simpa [hd, E] using hok) hnz0 hnew
  have hmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "map", Hw.mapOkE x,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 23#6 hopc (by decide +kernel))
  have hunmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 23#6 hopc (by decide +kernel))
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
      (isMn_ne_of_opc σ "sw" 23#6 hopc (by decide +kernel))
  let X := gateReturnSuccessA E
  have hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w := by
    intro rn w
    rw [coreAct_run_retire_eq m σ _ hifv hcl,
      retireAct_run_regs σ _ E rfl rn w,
      retireFor_gateReturn_success σ _ E hopc (by simpa [E] using hok)]
    rfl
  have hframes := returnAbstractSuccess_structural_frames base E gid act 0
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
      hframes.2.2.2.1 x]
    exact refillPhase_regions m (Hw.abs σ) x
  have hjob : τ2.mover = Hw.absMover σ := by
    rw [show τ2.mover = base.mover from hframes.2.2.2.2.1]
    exact refillPhase_mover m (Hw.abs σ)
  have hcoreMem : ∀ ad,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem" ad 32 =
        σ.mems "mem" ad 32 := by
    intro ad
    exact coreAct_mem_gateReturn_zero_reply m σ E hifv hcl hifsel hifexcl
      hopc (by simpa [E] using hzero) ad
  have hτmem : ∀ b : Addr, τ2.mem b = σ.mems "mem" b.toNat 32 := by
    intro b
    rw [show τ2.mem = base.mem from hframes.2.2.2.2.2]
    rfl
  have hmover : Hw.absMover
      (Hw.moverAct.run σ
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))) =
      (moverPhase τ2).mover :=
    absMover_moverAct_quiescent σ _ τ2 hin hcaps hgens hjob
  have hmoverMem : ∀ a : Addr,
      (Hw.moverAct.run σ
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))).mems "mem"
          a.toNat 32 = (moverPhase τ2).mem a := by
    intro a
    exact moverAct_mem_quiescent σ _ τ2 hin hcaps hgens hregions hjob
      hswz hmapz hunmapz hcoreMem hτmem a
  have habsPayload : Hw.abs
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) = τ2 := by
    change Hw.abs ((gateReturnSuccessA E).run σ acc0) = τ2
    exact habsRet
  apply square_retire_gate_payload_abs m σ X τ2 hcoreR
  · unfold X
    exact ifv_notin_gateReturnSuccess E
  · exact hspec
  · exact habsPayload
  · exact hmover
  · exact hmoverMem
  · rfl
  · rfl

/-- Complete successful non-null return. The placement check exposes either a
root or derived structural transfer; both instantiate the common cycle proof
above. -/
theorem square_retire_gateReturn_success_nonzero (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz0 : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6)
    (gid : GateId) (act : Activation)
    (hserv : ((Hw.abs σ).doms
      (finOfBv (by decide) (σ.regs "if_dom" 2))).serving = some gid)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hnonzero : (Hw.retW
      (finOfBv (by decide) (σ.regs "if_dom" 2))).eval σ ≠ 0#32)
    (hstale : (Expr.and
      (Hw.retNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.retSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).live)).eval σ ≠ 1#1)
    (hclass : (Expr.and
      (Hw.retNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Expr.not (Hw.retSel
        (finOfBv (by decide) (σ.regs "if_dom" 2))).clsOk)).eval σ ≠ 1#1)
    (hblocked : (Expr.and
      (Hw.retNZ (finOfBv (by decide) (σ.regs "if_dom" 2)))
      (Hw.transferBlocked
        (finOfBv (by decide) (σ.regs "if_dom" 2))
        (Hw.retCl (finOfBv (by decide) (σ.regs "if_dom" 2)))
        (Hw.retSel
          (finOfBv (by decide) (σ.regs "if_dom" 2))))).eval σ ≠ 1#1) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hE
  let base := gateReturnTransferBase m σ
  let τ0 := gateReturnPrefixed m σ E
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hne : E ≠ act.caller := by
    simpa [E] using gateReturnIssuer_ne_caller_of_reachable
      m hwf σ hsr hifv gid act hact
  have hnz : (Hw.retNZ E).eval σ = 1#1 :=
    (retNZ_eval_iff σ E).mpr (by simpa [E] using hnonzero)
  have hlive : (Hw.retSel E).live.eval σ = 1#1 := by
    exact (by decide : ∀ a b : BitVec 1,
      a = 1#1 → a &&& ~~~b ≠ 1#1 → b = 1#1)
      ((Hw.retNZ E).eval σ) ((Hw.retSel E).live.eval σ) hnz
      (by simpa [E] using hstale)
  have hcls1 : (Hw.retSel E).clsOk.eval σ = 1#1 := by
    exact (by decide : ∀ a b : BitVec 1,
      a = 1#1 → a &&& ~~~b ≠ 1#1 → b = 1#1)
      ((Hw.retNZ E).eval σ) ((Hw.retSel E).clsOk.eval σ) hnz
      (by simpa [E] using hclass)
  have hok : (Hw.retOkE E).eval σ = 1#1 :=
    retOkE_of_passes σ E gid act (by simpa [E] using hserv) hact
      (by simpa [E] using hstale) (by simpa [E] using hclass)
      (by simpa [E] using hblocked)
  have hbridge : ∀ (S : Slot) (G : Gen),
      (τ0.doms E).liveCap S G = ((Hw.abs σ).doms E).liveCap S G := by
    intro S G
    exact specLiveCap_bridge m σ E S G
  obtain ⟨e, alive, acap⟩ := capSel_entry_of_live σ τ0 E
    (Hw.retW E) hbridge (by simpa [Hw.retSel] using hlive)
  let S : Slot := (Handle.decode ((Hw.retW E).eval σ)).slot
  let G : Gen := (Handle.decode ((Hw.retW E).eval σ)).gen
  have hclsIff := capSel_clsOk_iff_some σ E (Hw.retW E)
    (finOfBv (by decide) (((Hw.retW E).eval σ).extractLsb' 0 4)) e hkc
    (show (finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.retW E).eval σ).extractLsb' 0 4)).val =
      (((Hw.retW E).eval σ).extractLsb' 0 4).toNat from rfl) acap
  have hcls : (Handle.decode ((Hw.retW E).eval σ)).cls = e.kind.cls :=
    hclsIff.mp (by simpa [Hw.retSel] using hcls1)
  have hslot : (Hw.retSel E).slot.eval σ = BitVec.ofNat 4 S.val := by
    exact (bv4_slot_iff _ S).mpr rfl
  have hsource : (τ0.doms E).caps S = some e := by
    change (τ0.doms E).liveCap S G = some e at alive
    unfold DomainState.liveCap at alive
    cases hc : (τ0.doms E).caps S with
    | none => simp [hc] at alive
    | some e' =>
        rw [hc] at alive
        change (if (decide ((τ0.doms E).slotGen S = G) && G != 0) = true
          then some e' else none) = some e at alive
        by_cases hg : (decide ((τ0.doms E).slotGen S = G) && G != 0) = true
        · rw [if_pos hg] at alive
          exact Option.some.inj alive ▸ rfl
        · rw [if_neg hg] at alive
          contradiction
  have hgen : (τ0.doms E).slotGen S = G := by
    change (τ0.doms E).liveCap S G = some e at alive
    unfold DomainState.liveCap at alive
    rw [hsource] at alive
    change (if (decide ((τ0.doms E).slotGen S = G) && G != 0) = true
      then some e else none) = some e at alive
    by_cases hg : (decide ((τ0.doms E).slotGen S = G) && G != 0) = true
    · simpa using (show (τ0.doms E).slotGen S = G ∧ G ≠ 0 from by
        simpa using hg).1
    · rw [if_neg hg] at alive
      contradiction
  have hgenAbs : ((Hw.abs σ).doms E).slotGen S = G := by
    simpa [τ0, gateReturnPrefixed, gateReturnTransferBase,
      MachineState.setDom, Loom.Fun.update] using hgen
  have hkind : (Hw.retSel E).kindW.eval σ = Hw.encKind e.kind :=
    capSel_kind_of_some σ E (Hw.retW E) S e hkc (by rfl) acap
  have hold : Hw.decRef
      ((Hw.encRefE (Hw.dLit E) (Hw.retSel E).slot
        (Hw.retSel E).gen).eval σ) =
      ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩ := by
    apply encRefE_decoded_selected σ E (Hw.retSel E).slot
      (Hw.retSel E).gen S (((Hw.abs σ).doms E).slotGen S) hslot
    simpa [G] using hgenAbs.symm
  have hdecode : Handle.decode ((Hw.retW E).eval σ) =
      ⟨S, G, e.kind.cls⟩ := by
    cases hd : Handle.decode ((Hw.retW E).eval σ) with
    | mk slot gen cls =>
        simp only [S, G, hd] at hcls ⊢
        cases hcls
        rfl
  have hcapLive : Machines.Lnp64u.Isa.capLive E ((Hw.retW E).eval σ) τ0 =
      .ok (S, G, e) τ0 :=
    capLive_eq_selected τ0 E ((Hw.retW E).eval σ) S G e hdecode alive
  have hlineage : ∀ L : LineageId,
      (τ0.doms E).lineage L = ((Hw.abs σ).doms E).lineage L := by
    intro L
    simp [τ0, gateReturnPrefixed, gateReturnTransferBase,
      MachineState.setDom, Loom.Fun.update]
  have hfreeSlot : τ0.freeSlot act.caller =
      (Hw.abs σ).freeSlot act.caller := by
    unfold MachineState.freeSlot
    simp [τ0, gateReturnPrefixed, gateReturnTransferBase,
      MachineState.setDom, Loom.Fun.update, hne.symm]
  have hfreeCell : τ0.freeCell act.caller =
      (Hw.abs σ).freeCell act.caller := by
    unfold MachineState.freeCell
    simp [τ0, gateReturnPrefixed, gateReturnTransferBase,
      MachineState.setDom, Loom.Fun.update, hne.symm]
  have hwfAbs : Wf (Hw.abs σ) := reachable_wf m hwf _ hsr
  have hto := retCl_eval_selected σ E gid act
    (by simpa [E] using hserv) hact
  have hpass : (Hw.transferBlocked E (Hw.retCl E) (Hw.retSel E)).eval σ ≠
      1#1 := by
    intro hb
    apply hblocked
    change (Hw.retNZ E).eval σ &&&
      (Hw.transferBlocked E (Hw.retCl E) (Hw.retSel E)).eval σ = 1#1
    rw [hnz, hb]
    decide
  have hret := retiringE_one σ hifv hcl
  have hif : ∀ x : DomainId, (Hw.ifDomIs x).eval σ =
      if x = E then 1#1 else 0#1 := by
    intro x
    by_cases hx : x = E
    · subst x; simpa using hifsel
    · rw [if_neg hx, bv1_ne_one.mp (hifexcl x hx)]
  have hmn : (Hw.isMn "gate_return").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_return" = 23#6).symm
  have hdrop := isMn_ne_of_opc σ "cap_drop" 23#6 hopc (by decide +kernel)
  have hrev := isMn_ne_of_opc σ "cap_revoke" 23#6 hopc (by decide +kernel)
  have hcall := isMn_ne_of_opc σ "gate_call" 23#6 hopc (by decide +kernel)
  have hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.retKilled E dm sl).eval σ :=
    killedByCoreE_gateReturn_eval σ E hret hif hdrop hrev hcall hmn
      (fun x hx => by simpa [hx] using hok)
  have hnew : ∀ x : DomainId, (Hw.newJobSet x).eval σ = 0#1 := by
    intro x
    apply andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    exact isMn_ne_of_opc σ "move" 23#6 hopc (by decide +kernel)
  have hmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "map", Hw.mapOkE x,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 23#6 hopc (by decide +kernel))
  have hunmapz : ∀ (x : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun x r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 23#6 hopc (by decide +kernel))
  have hswz : ∀ (x : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs x, Hw.isMn "sw",
        Hw.domCoversE x
          (Hw.field (.add (Hw.readReg x Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg x Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun x sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 23#6 hopc (by decide +kernel))
  let acc0 := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  rcases transferCap_selected_of_pass σ τ0 E act.caller (Hw.retCl E)
      (Hw.retW E) S e hto hslot acap hsource hlineage hfreeSlot hfreeCell
      hwfAbs hpass with hroot | hderived
  · obtain ⟨NS, hlin, hNS, hlinV, htransferCap⟩ := hroot
    let oldRef : CapRef := ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩
    let newRef : CapRef :=
      ⟨act.caller, NS, ((Hw.abs σ).doms act.caller).slotGen NS⟩
    let reply := Handle.encode ⟨newRef.slot, newRef.gen, e.kind.cls⟩
    have htransferCap' : τ0.transferCap E S act.caller =
        some (gateReturnSpecStruct m σ E act S NS e.kind none oldRef newRef,
          newRef) := by
      simpa [gateReturnSpecStruct, gateReturnPrefixed, oldRef, newRef, τ0,
        gateReturnTransferBase, MachineState.setDom, Loom.Fun.update, hne.symm,
        refillPhase_slotGen] using htransferCap
    have htransfer : Machines.Lnp64u.Isa.transferByHandle E act.caller
        ((Hw.retW E).eval σ) τ0 =
        .ok reply (gateReturnSpecStruct m σ E act S NS e.kind none
          oldRef newRef) :=
      transferByHandle_eq_selected τ0 _ E act.caller ((Hw.retW E).eval σ)
        S G e newRef (by simpa [E] using hnonzero) hcapLive htransferCap'
    have habsTransfer : Hw.abs
        ((Hw.transferA E (Hw.retCl E) (Hw.retSel E)).run σ acc0) =
        gateReturnHwStruct m σ E act S NS e.kind none oldRef newRef := by
      simpa [acc0, gateReturnHwStruct, oldRef, newRef,
        gateReturnTransferBase] using
        (abs_transferA_none_retireAcc m hwf hfit σ hsync E act.caller
          (Hw.retCl E) (Hw.retSel E) S NS e hto hslot acap hNS hlin hlinV
          hkind hold hwfAbs)
    have hsidx := freeSlotIdx_eval σ act.caller NS hNS
    have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
        ((Hw.freeSlotIdx act.caller).eval σ) = NS :=
      (bv4_slot_iff _ NS).mp hsidx
    have hgenNew : (Hw.genOfE act.caller
        (Hw.freeSlotIdx act.caller)).eval σ =
        ((Hw.abs σ).doms act.caller).slotGen NS := by
      rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
      rfl
    have hclsbit : (Hw.field (Hw.retSel E).kindW 0 1).eval σ =
        if e.kind.cls = .gate then 1#1 else 0#1 := by
      show ((Hw.retSel E).kindW.eval σ).extractLsb' 0 1 = _
      rw [hkind]
      cases e.kind <;> simp only [CapKind.cls, Hw.encKind, if_false,
        if_true] <;> apply BitVec.eq_of_getLsbD_eq <;>
        intro i hi <;> interval_cases i <;> simp
    have hreply : (gateReturnReplyE E).eval σ = reply := by
      rw [gateReturnReplyE_eval_nonzero σ E e.kind.cls hnz hclsbit]
      dsimp only [reply]
      rw [hto, hsidx, hgenNew]
      simp only [newRef]
      rw [finOfBv_ofNat4]
    exact square_retire_gateReturn_success_transfer m σ E gid act reply S NS
      e.kind none oldRef newRef hz0 hifv hcl hopc rfl hifsel hifexcl
      (by simpa [E] using hserv) hact hne hslot hnz hok hkills hnew hmapz
      hunmapz hswz hwfAbs (freeSlot_caps_none (Hw.abs σ) act.caller hNS)
      htransfer (by simpa [acc0] using habsTransfer) hreply
  · obtain ⟨L, cell, NS, NL, hlin, hcell, hNS, hNL, hlinV, hlinIdx,
      htransferCap⟩ := hderived
    let moved : Option (LineageId × CapRef) := some (NL, cell.parent)
    let oldRef : CapRef := ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩
    let newRef : CapRef :=
      ⟨act.caller, NS, ((Hw.abs σ).doms act.caller).slotGen NS⟩
    let reply := Handle.encode ⟨newRef.slot, newRef.gen, e.kind.cls⟩
    have htransferCap' : τ0.transferCap E S act.caller =
        some (gateReturnSpecStruct m σ E act S NS e.kind moved oldRef newRef,
          newRef) := by
      simpa [gateReturnSpecStruct, gateReturnPrefixed, moved, oldRef, newRef,
        τ0, gateReturnTransferBase, MachineState.setDom, Loom.Fun.update,
        hne.symm,
        refillPhase_slotGen] using htransferCap
    have htransfer : Machines.Lnp64u.Isa.transferByHandle E act.caller
        ((Hw.retW E).eval σ) τ0 =
        .ok reply (gateReturnSpecStruct m σ E act S NS e.kind moved
          oldRef newRef) :=
      transferByHandle_eq_selected τ0 _ E act.caller ((Hw.retW E).eval σ)
        S G e newRef (by simpa [E] using hnonzero) hcapLive htransferCap'
    have habsTransfer : Hw.abs
        ((Hw.transferA E (Hw.retCl E) (Hw.retSel E)).run σ acc0) =
        gateReturnHwStruct m σ E act S NS e.kind moved oldRef newRef := by
      simpa [acc0, gateReturnHwStruct, moved, oldRef, newRef,
        gateReturnTransferBase] using
        (abs_transferA_some_retireAcc m hwf hfit σ hsync E act.caller
          (Hw.retCl E) (Hw.retSel E) S NS e L cell NL hto hslot acap hNS
          hlin hcell hNL hlinV hlinIdx hkind hold hwfAbs)
    have hsidx := freeSlotIdx_eval σ act.caller NS hNS
    have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
        ((Hw.freeSlotIdx act.caller).eval σ) = NS :=
      (bv4_slot_iff _ NS).mp hsidx
    have hgenNew : (Hw.genOfE act.caller
        (Hw.freeSlotIdx act.caller)).eval σ =
        ((Hw.abs σ).doms act.caller).slotGen NS := by
      rw [Hw.genOfE, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
      rfl
    have hclsbit : (Hw.field (Hw.retSel E).kindW 0 1).eval σ =
        if e.kind.cls = .gate then 1#1 else 0#1 := by
      show ((Hw.retSel E).kindW.eval σ).extractLsb' 0 1 = _
      rw [hkind]
      cases e.kind <;> simp only [CapKind.cls, Hw.encKind, if_false,
        if_true] <;> apply BitVec.eq_of_getLsbD_eq <;>
        intro i hi <;> interval_cases i <;> simp
    have hreply : (gateReturnReplyE E).eval σ = reply := by
      rw [gateReturnReplyE_eval_nonzero σ E e.kind.cls hnz hclsbit]
      dsimp only [reply]
      rw [hto, hsidx, hgenNew]
      simp only [newRef]
      rw [finOfBv_ofNat4]
    exact square_retire_gateReturn_success_transfer m σ E gid act reply S NS
      e.kind moved oldRef newRef hz0 hifv hcl hopc rfl hifsel hifexcl
      (by simpa [E] using hserv) hact hne hslot hnz hok hkills hnew hmapz
      hunmapz hswz hwfAbs (freeSlot_caps_none (Hw.abs σ) act.caller hNS)
      htransfer (by simpa [acc0] using habsTransfer) hreply

end Machines.Lnp64u.Theorems.RMC
