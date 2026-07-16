-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateReturnSuccess
import Machines.Lnp64u.Theorems.RMCRetireGateSquare

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

end Machines.Lnp64u.Theorems.RMC
