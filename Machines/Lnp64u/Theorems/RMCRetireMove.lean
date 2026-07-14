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
  sorry


end Machines.Lnp64u.Theorems.RMC
