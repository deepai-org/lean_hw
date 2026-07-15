-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRgn

/-!
# R-MC support: the `map` retirement arm

`map` caches a live memory capability's authority in a region register:
two errno outcomes (stale handle, bad cap — class mismatch or gate
kind) and the region-write outcome, whose packed value decodes to the
spec's cached `Region` through the kind-canon clause (`mapVal_pack`).
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 25600000
set_option maxRecDepth 400000

/-! ## Bit-level class/kind bridges -/

theorem extract1_eq_iff {n m : Nat} (a : BitVec n) (b : BitVec m)
    (i j : Nat) :
    (a.extractLsb' i 1 = b.extractLsb' j 1) ↔ (a.getLsbD i = b.getLsbD j) := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec 1 => v.getLsbD 0) h
    simpa [BitVec.getLsbD_extractLsb'] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k
    simpa [BitVec.getLsbD_extractLsb'] using h

theorem extract1_eq_zero_iff {n : Nat} (a : BitVec n) (i : Nat) :
    (a.extractLsb' i 1 = 0#1) ↔ (a.getLsbD i = false) := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec 1 => v.getLsbD 0) h
    simpa [BitVec.getLsbD_extractLsb'] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k
    simpa [BitVec.getLsbD_extractLsb'] using h

/-- Class agreement between a handle word and a kind word is the
tag-bit test. -/
theorem cls_eq_iff_bits (hw kw : BitVec 32) :
    ((Handle.decode hw).cls = (Hw.decKind kw).cls)
      ↔ (hw.getLsbD 12 = kw.getLsbD 0) := by
  rw [show (Handle.decode hw).cls
    = (if hw.getLsbD 12 then CapClass.gate else CapClass.mem) from rfl]
  rw [Hw.decKind]
  cases h1 : hw.getLsbD 12 <;> cases h2 : kw.getLsbD 0 <;>
    simp [CapKind.cls]

/-- The memory-kind test is the tag bit. -/
theorem decKind_mem_iff (kw : BitVec 32) :
    (kw.getLsbD 0 = false) ↔
      Hw.decKind kw = .mem (kw.extractLsb' 1 12) (kw.extractLsb' 13 13)
        (Hw.decPerms (kw.extractLsb' 26 3)) := by
  rw [Hw.decKind]
  cases h : kw.getLsbD 0 <;> simp

/-! ## The shared errno-outcome assembly for `map` -/

set_option maxHeartbeats 25600000 in
/-- Both `map` errno outcomes retire as `pc += 1; rd := errno` with the
Mover fully quiescent (`mapOkE` is off, so even the fired-`map`
composites collapse). -/
theorem retire_err_common_mem (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hin : Inert σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1)
    (hcoremem : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = σ.mems "mem" b.toNat 32)
    (E : DomainId) (hE : E.val = (σ.regs "if_dom" 2).toNat)
    (errw : Loom.Word32)
    (hcoreX : ∀ acc, (Hw.retireFor E).run σ acc
      = (Act.seq (Hw.pcAdvA E) (Hw.writeReg E Hw.rdE (.lit errw))).run σ acc)
    (hspecE : corePhase m (refillPhase m (Hw.abs σ))
      = (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).setDom E
          (fun ds => ds.setReg (operandsOf (σ.regs "if_word" 32)).rd errw)) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y
    rw [← habs1]
    rfl
  set W := σ.regs "if_word" 32 with hW
  have hτ2E : ((({ refillPhase m (Hw.abs σ) with inflight := none
      }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).setDom E
      (fun ds => ds.setReg (operandsOf W).rd errw)).doms E
      = ({ (refillPhase m (Hw.abs σ)).doms E with
          pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 }).setReg
          (operandsOf W).rd errw := by
    rw [setDom_setDom]
    show (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E = _
    rw [Loom.Fun.update_same]
  have hτ2x : ∀ x, x ≠ E → ((({ refillPhase m (Hw.abs σ) with inflight :=
      none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).setDom E
      (fun ds => ds.setReg (operandsOf W).rd errw)).doms x
      = (refillPhase m (Hw.abs σ)).doms x := by
    intro x hx
    rw [setDom_setDom]
    show (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x = _
    rw [Loom.Fun.update_ne _ _ _ _ hx]
  refine square_retire_store m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
    (Act.seq (Hw.pcAdvA E) (Hw.writeReg E Hw.rdE (.lit errw))) _
    (fun rn w => by
      rw [coreAct_run_retire_eq m σ _ hifv hcl,
        retireAct_run_regs σ _ E hE rn w, hcoreX]
      rfl)
    (by
      intro hm
      rcases List.mem_cons.mp (show (("if_v" : String), (1 : Nat)) ∈
          (Hw.dpc E, (12 : Nat)) :: (Hw.writeReg E Hw.rdE
            (Expr.lit errw)).regWrites from hm) with h | h
      · exact absurd (congrArg Prod.snd h) (show ¬((1 : Nat) = 12) by decide)
      · exact absurd h ((by decide +kernel : ∀ e : DomainId,
          (("if_v" : String), (1 : Nat))
            ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) E)
    )
    hspecE
    (fun x => by
      by_cases hx : x = E
      · subst hx
        rw [hτ2E]
        have hq : ∀ q ∈ domQuietNames x,
            ((Act.seq (.write 1 "if_v" (.lit 0))
              (Act.seq (Hw.pcAdvA x) (Hw.writeReg x Hw.rdE
                (.lit errw)))).run σ ((Hw.refillAct m).run σ σ)).regs
              q.1 q.2 = ((Hw.refillAct m).run σ σ).regs q.1 q.2 := by
          intro q hq'
          refine frame ?_ σ _
          intro hm
          rcases List.mem_cons.mp (show q ∈ ("if_v", (1 : Nat)) ::
              ((Hw.dpc x, (12 : Nat)) :: (Hw.writeReg x Hw.rdE
                (Expr.lit errw)).regWrites) from hm) with h | h
          · exact absurd (h ▸ hq' : _)
              (fun hmem => (quiet_notin_dom x x q hq')
                (h ▸ List.mem_cons_self ..))
          · rcases List.mem_cons.mp h with h' | h'
            · exact (quiet_notin_dom x x q hq')
                (h' ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (List.mem_cons_self ..)))))))))
            · exact (quiet_notin_dom x x q hq')
                ((by decide +kernel : ∀ (e : DomainId)
                    (q' : String × Nat),
                    q' ∈ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites →
                    q' ∈ ("if_v", 1) :: domWrites e) x q h')
        rw [absDom_regpc x hq, hL1 x]
        apply domainState_ext'
        · funext r
          show ((Hw.writeReg x Hw.rdE (.lit errw)).run σ
            ((Hw.pcAdvA x).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ)))).regs (Hw.dreg x r) 32 = _
          rw [setReg_regs]
          have hbase : ∀ (rr : RegId),
              ((Hw.pcAdvA x).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ))).regs (Hw.dreg x rr) 32
              = ((Hw.refillAct m).run σ σ).regs (Hw.dreg x rr) 32 := by
            intro rr
            rw [frame (fun hm => absurd
              (congrArg Prod.snd (List.mem_singleton.mp hm))
              (show ¬((32 : Nat) = 12) by decide)) σ _]
            exact frame (fun hm => absurd
              (congrArg Prod.snd (List.mem_singleton.mp hm))
              (show ¬((32 : Nat) = 1) by decide)) σ _
          by_cases h0 : (operandsOf W).rd = (0 : Fin numRegs)
          · rw [if_pos h0]
            rw [writeReg_run_of_zero σ _ x Hw.rdE _ (by
              rw [show ((Hw.rdE.eval σ)).toNat
                = ((operandsOf W).rd : Fin numRegs).val from rfl, h0]
              rfl)]
            rw [hbase r]
            rfl
          · rw [if_neg h0]
            rw [writeReg_run_of_nz σ _ x Hw.rdE _ (operandsOf W).rd rfl
              (fun hc => h0 (Fin.ext hc))]
            show (RegEnv.set _ (Hw.dreg x (operandsOf W).rd) _)
              (Hw.dreg x r) 32 = _
            simp only [RegEnv.set]
            by_cases hr : r = (operandsOf W).rd
            · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial]
              rfl
            · rw [if_neg (fun hc => hr (dreg_inj x r (operandsOf W).rd hc)),
                if_neg hr]
              rw [hbase r]
              rfl
        · show ((Hw.writeReg x Hw.rdE (.lit errw)).run σ
            ((Hw.pcAdvA x).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ)))).regs (Hw.dpc x) 12 = _
          rw [setReg_pc]
          rw [frame (show ((Hw.dpc x : String), (12 : Nat))
              ∉ (Hw.writeReg x Hw.rdE (Expr.lit errw)).regWrites from
            (by decide +kernel : ∀ e : DomainId,
              ((Hw.dpc e : String), (12 : Nat))
                ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) x) σ _]
          rw [show ((Hw.pcAdvA x).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ))).regs (Hw.dpc x) 12
            = σ.regs (Hw.dpc x) 12 + 1 from by
            show (RegEnv.set _ (Hw.dpc x)
              ((Expr.add (Hw.rPc x) (.lit 1)).eval σ)) (Hw.dpc x) 12 = _
            simp [RegEnv.set, Expr.eval, Hw.rPc]]
          show σ.regs (Hw.dpc x) 12 + 1
            = ((Hw.refillAct m).run σ σ).regs (Hw.dpc x) 12 + 1
          rw [refill_pres m σ ((by decide +kernel : ∀ e : DomainId,
            ((Hw.dpc e : String), (12 : Nat)) ∉
            ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
              ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
              ("d3_budget", 32), ("d3_rctr", 32)] :
              List (String × Nat))) x)]
        · rw [setReg_caps]
        · rw [setReg_slotGen]
        · rw [setReg_lineage]
        · rw [setReg_regions]
        · rw [setReg_run]
        · rw [setReg_serving]
        · rw [setReg_cause]
        · rw [setReg_budget]
        · rw [setReg_maxDonation]
      · rw [hτ2x x hx, hL1 x]
        refine absDom_congr x (fun p hp => frame ?_ σ _)
        intro hm
        rcases List.mem_cons.mp (show p ∈ ("if_v", (1 : Nat)) ::
            ((Hw.dpc E, (12 : Nat)) :: (Hw.writeReg E Hw.rdE
              (Expr.lit errw)).regWrites) from hm) with h | h
        · exact (read_notin_dom_ne x E hx p hp)
            (h ▸ List.mem_cons_self ..)
        · rcases List.mem_cons.mp h with h' | h'
          · exact (read_notin_dom_ne x E hx p hp)
              (h' ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_self ..)))))))))
          · exact (read_notin_dom_ne x E hx p hp)
              ((by decide +kernel : ∀ (e : DomainId) (q' : String × Nat),
                q' ∈ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites →
                q' ∈ ("if_v", 1) :: domWrites e) E p h')
    )
    (fun g => by
      refine (absGate_congr g (fun p hp => frame ?_ σ _)).trans ?_
      · intro hm
        rcases List.mem_cons.mp (show p ∈ ("if_v", (1 : Nat)) ::
            ((Hw.dpc E, (12 : Nat)) :: (Hw.writeReg E Hw.rdE
              (Expr.lit errw)).regWrites) from hm) with h | h
        · exact (gate_notin_dom g E p hp) (h ▸ List.mem_cons_self ..)
        · rcases List.mem_cons.mp h with h' | h'
          · exact (gate_notin_dom g E p hp)
              (h' ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_self ..)))))))))
          · exact (gate_notin_dom g E p hp)
              ((by decide +kernel : ∀ (e : DomainId) (q' : String × Nat),
                q' ∈ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites →
                q' ∈ ("if_v", 1) :: domWrites e) E p h')
      · rw [← habs1]
        rfl)
    (fun x => by
      by_cases hx : x = E
      · subst hx
        rw [hτ2E, setReg_caps]
        show ((refillPhase m (Hw.abs σ)).doms x).caps = _
        rw [refillPhase_caps]
      · rw [hτ2x x hx, refillPhase_caps])
    (fun x => by
      by_cases hx : x = E
      · subst hx
        rw [hτ2E, setReg_slotGen]
        show ((refillPhase m (Hw.abs σ)).doms x).slotGen = _
        rw [refillPhase_slotGen]
      · rw [hτ2x x hx, refillPhase_slotGen])
    (fun x => by
      by_cases hx : x = E
      · subst hx
        rw [hτ2E, setReg_regions]
        show ((refillPhase m (Hw.abs σ)).doms x).regions = _
        rw [refillPhase_regions]
      · rw [hτ2x x hx, refillPhase_regions])
    (by
      show (refillPhase m (Hw.abs σ)).mover = _
      rw [refillPhase_mover]
      rfl)
    hcoremem
    (fun sc => by
      rw [srcWord_quiescent σ hswz sc]
      rfl)
    (by
      show (refillPhase m (Hw.abs σ)).cycle = _
      rfl)
    rfl

set_option maxHeartbeats 25600000 in
/-- Backwards-compatible errno wrapper for mnemonics whose memory-capable
circuits are not selected. -/
theorem map_err_common (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hin : Inert σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1)
    (hben5 : ∀ mn ∈ memMns, (Hw.isMn mn).eval σ ≠ 1#1)
    (E : DomainId) (hE : E.val = (σ.regs "if_dom" 2).toNat)
    (errw : Loom.Word32)
    (hcoreX : ∀ acc, (Hw.retireFor E).run σ acc
      = (Act.seq (Hw.pcAdvA E) (Hw.writeReg E Hw.rdE (.lit errw))).run σ acc)
    (hspecE : corePhase m (refillPhase m (Hw.abs σ))
      = (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).setDom E
          (fun ds => ds.setReg (operandsOf (σ.regs "if_word" 32)).rd errw)) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  apply retire_err_common_mem m hwf hfit σ hsync hifv hcl hin hmapz
    hunmapz hswz
  · intro b
    rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
    rw [refill_pres_mem m σ "mem" b.toNat 32]
  · exact hE
  · exact hcoreX
  · exact hspecE

/-! ## The `map` ok-path write set and value bridge -/

/-- The ok-path payload with the latch clear in front. -/
def mapFull (e : DomainId) : Act :=
  .seq (.write 1 "if_v" (.lit 0))
    (Hw.seqAll
      (((List.finRange numRegions).map fun r =>
        .ite (.eq Hw.riE (Hw.rLit r))
          (.seq (.write 1 (Hw.drgnV e r) (.lit 1))
                (.write 42 (Hw.drgn e r) (Hw.mapValE e))) .skip)
      ++ [Hw.writeReg e Hw.rdE (.lit 0), Hw.pcAdvA e]))

private theorem mapFull_writes (e : DomainId) :
    (mapFull e).regWrites
      = [("if_v", 1), (Hw.drgnV e 0, 1), (Hw.drgn e 0, 42),
         (Hw.drgnV e 1, 1), (Hw.drgn e 1, 42),
         (Hw.drgnV e 2, 1), (Hw.drgn e 2, 42),
         (Hw.drgnV e 3, 1), (Hw.drgn e 3, 42),
         (Hw.dreg e 1, 32), (Hw.dreg e 2, 32), (Hw.dreg e 3, 32),
         (Hw.dreg e 4, 32), (Hw.dreg e 5, 32), (Hw.dreg e 6, 32),
         (Hw.dreg e 7, 32), (Hw.dpc e, 12)] := rfl

private theorem quietRg_notin_map (x e : DomainId) :
    ∀ q ∈ domQuietNamesRg x, q ∉ (mapFull e).regWrites := by
  rw [mapFull_writes]
  fin_cases x <;> fin_cases e <;> decide +kernel

private theorem read_notin_map_ne (x e : DomainId) (hne : x ≠ e) :
    ∀ q ∈ domReadNames x, q ∉ (mapFull e).regWrites := by
  rw [mapFull_writes]
  fin_cases x <;> fin_cases e <;>
    first
      | exact absurd rfl hne
      | decide +kernel

private theorem gate_notin_map (g : GateId) (e : DomainId) :
    ∀ q ∈ gateReadNames g, q ∉ (mapFull e).regWrites := by
  rw [mapFull_writes]
  fin_cases g <;> fin_cases e <;> decide +kernel

private theorem ifv_notin_mapX (e : DomainId) :
    (("if_v" : String), (1 : Nat)) ∉
      (Hw.seqAll
        (((List.finRange numRegions).map fun r =>
          Act.ite (.eq Hw.riE (Hw.rLit r))
            (.seq (.write 1 (Hw.drgnV e r) (.lit 1))
                  (.write 42 (Hw.drgn e r) (Hw.mapValE e))) .skip)
        ++ [Hw.writeReg e Hw.rdE (Expr.lit 0), Hw.pcAdvA e])).regWrites := by
  have h : (Hw.seqAll
      (((List.finRange numRegions).map fun r =>
        Act.ite (.eq Hw.riE (Hw.rLit r))
          (.seq (.write 1 (Hw.drgnV e r) (.lit 1))
                (.write 42 (Hw.drgn e r) (Hw.mapValE e))) .skip)
      ++ [Hw.writeReg e Hw.rdE (Expr.lit 0), Hw.pcAdvA e])).regWrites
      = (mapFull e).regWrites.tail := rfl
  rw [h, mapFull_writes]
  fin_cases e <;> decide +kernel

set_option maxHeartbeats 51200000 in
set_option maxRecDepth 1000000 in
/-- The `map` arm: opcode 20. -/
theorem square_retire_map (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hkc : KindCanon σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 20#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (20#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (20#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hmapmn : (Hw.isMn "map").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "map" = 20#6).symm
  have hret := retiringE_one σ hifv hcl
  have hin : Inert σ := Inert.of_benign7 σ (fun mn' hmn' =>
    isMn_ne_of_opc σ mn' 20#6 hopc
      ((by decide +kernel : ∀ mn' ∈ ["cap_drop", "cap_revoke", "gate_call",
        "gate_return", "move"], (20#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn'))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 20#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 20#6 hopc (by decide +kernel))
  have hben5 : ∀ mn ∈ memMns, (Hw.isMn mn).eval σ ≠ 1#1 := fun mn hmn =>
    isMn_ne_of_opc σ mn 20#6 hopc
      ((by decide +kernel : ∀ mn ∈ memMns, (20#6 : BitVec 6)
        ≠ Hw.opcodeOf mn) mn hmn)
  have hselC := retireFor_sel_of_opc σ E "map" 20#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨Hw.ladder E (Hw.mapChecks E) (Hw.seqAll
      (((List.finRange numRegions).map fun r =>
        .ite (.eq Hw.riE (Hw.rLit r))
          (.seq (.write 1 (Hw.drgnV E r) (.lit 1))
                (.write 42 (Hw.drgn E r) (Hw.mapValE E))) .skip)
      ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E])),
      .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))))
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  set HWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hHWv
  set S : Slot := finOfBv (by decide) (HWv.extractLsb' 0 4) with hSdef
  set G : Gen := HWv.extractLsb' 4 8 with hGdef
  set KW := σ.regs (Hw.dcapKind E S) 32 with hKWdef
  have hSval : S.val
      = (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := by
    rw [hR1]
    rfl
  have hlivE := capSel_live_eval σ E (Hw.readReg E Hw.rs1E) S hSval
  have hkwE : (Hw.capSel E (Hw.readReg E Hw.rs1E)).kindW.eval σ = KW :=
    capSel_kindW_eval σ E (Hw.readReg E Hw.rs1E) S hSval
  have hSPr : ∀ rs : RegId,
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg rs
        = ((Hw.abs σ).doms E).reg rs := fun rs => specReg_bridge m σ E rs
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ))
      = retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hDO : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (match ((SpecM.reg E (operandsOf W).rs1 >>= fun hw =>
          Machines.Lnp64u.Isa.capLive E hw >>= fun x =>
          match x with
          | (sl, g, e) =>
            match e.kind with
            | .gate _ => SpecM.raise .badCap
            | .mem base len perms =>
                SpecM.updDom E (fun ds => { ds with regions := Loom.Fun.update ds.regions (mapRI (operandsOf W)) (some (mapRgn E sl g base len perms)) }) >>= fun _ =>
                SpecM.setReg E (operandsOf W).rd 0)
          (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))) with
        | .ok _ σ' => σ'
        | .err e σ' =>
            σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault fl => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E fl) := by
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl
  have hRD : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1 = HWv :=
    hSPr (operandsOf W).rs1
  have hLCb : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).liveCap (Handle.decode HWv).slot
      (Handle.decode HWv).gen
      = ((Hw.abs σ).doms E).liveCap (Handle.decode HWv).slot
        (Handle.decode HWv).gen :=
    specLiveCap_bridge m σ E _ _
  have hlive1iff : ((Hw.capSel E (Hw.readReg E Hw.rs1E)).live.eval σ = 1#1)
      ↔ (σ.regs (Hw.dcapV E S) 1 = 1#1
        ∧ σ.regs (Hw.dgen E S) 8 = G ∧ G ≠ 0) := by
    rw [hR1] at hlivE
    exact hlivE
  have hclsE : (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk.eval σ
      = (if KW.extractLsb' 0 1 = HWv.extractLsb' 12 1
        then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.capSel E (Hw.readReg E Hw.rs1E)).kindW.eval σ).extractLsb' 0 1
        = ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 12 1
      then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwE, hR1]
  have hclsOkiff : ((Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk.eval σ = 1#1)
      ↔ (HWv.getLsbD 12 = KW.getLsbD 0) := by
    rw [hclsE]
    constructor
    · intro h
      by_cases hc : KW.extractLsb' 0 1 = HWv.extractLsb' 12 1
      · exact ((extract1_eq_iff KW HWv 0 12).mp hc).symm
      · rw [if_neg hc] at h
        exact absurd h (by decide)
    · intro h
      rw [if_pos ((extract1_eq_iff KW HWv 0 12).mpr h.symm)]
  have hmemE : (Hw.kIsMem
      (Hw.capSel E (Hw.readReg E Hw.rs1E)).kindW).eval σ
      = (if KW.extractLsb' 0 1 = 0#1 then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.capSel E (Hw.readReg E Hw.rs1E)).kindW.eval σ).extractLsb' 0 1
        = 0#1 then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwE]
  have hmemiff : ((Hw.kIsMem
      (Hw.capSel E (Hw.readReg E Hw.rs1E)).kindW).eval σ = 1#1)
      ↔ (KW.getLsbD 0 = false) := by
    rw [hmemE]
    constructor
    · intro h
      by_cases hc : KW.extractLsb' 0 1 = 0#1
      · exact (extract1_eq_zero_iff KW 0).mp hc
      · rw [if_neg hc] at h
        exact absurd h (by decide)
    · intro h
      rw [if_pos ((extract1_eq_zero_iff KW 0).mpr h)]
  by_cases hlv : σ.regs (Hw.dcapV E S) 1 = 1#1
      ∧ σ.regs (Hw.dgen E S) 8 = G ∧ G ≠ 0
  case neg =>
    -- stale handle
    have hlive0 : ¬((Hw.capSel E (Hw.readReg E Hw.rs1E)).live.eval σ = 1#1)
      := fun hc => hlv (hlive1iff.mp hc)
    have hlcN : ((({ refillPhase m (Hw.abs σ) with inflight := none
        }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen
        = none := by
      rw [hLCb, abs_liveCap]
      exact if_neg hlv
    have hmapok0 : (Hw.mapOkE E).eval σ = 0#1 := by
      show ~~~(~~~((Hw.capSel E (Hw.readReg E Hw.rs1E)).live.eval σ)) &&&
        ~~~(~~~((Expr.and (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
          (Hw.kIsMem (Hw.capSel E
            (Hw.readReg E Hw.rs1E)).kindW)).eval σ)) = 0#1
      rw [bv1_ne_one.mp hlive0]
      exact (by decide : ∀ b : BitVec 1,
        ~~~(~~~(0#1 : BitVec 1)) &&& ~~~(~~~b) = 0#1) _
    refine map_err_common m hwf hfit σ hsync hifv hcl hin
      (fun c r => by
        by_cases hcd : c = E
        · subst hcd
          exact andAll_zero_of_mem σ
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
            (by rw [hmapok0]; decide)
        · exact andAll_zero_of_mem σ
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            (hifexcl c hcd))
      hunmapz hswz hben5 E rfl Errno.staleHandle.toWord
      (fun acc => by
        rw [hselC acc]
        show (if (Expr.not
            (Hw.capSel E (Hw.readReg E Hw.rs1E)).live).eval σ = 1#1
          then (Hw.respA E (.err .staleHandle)).run σ acc else _) = _
        rw [if_pos (by
          show ~~~((Hw.capSel E (Hw.readReg E Hw.rs1E)).live.eval σ) = 1#1
          rw [bv1_ne_one.mp hlive0]
          decide)]
        rfl)
      (by
        rw [hcore0, hDO]
        simp only [specM_bind, SpecM.reg, Machines.Lnp64u.Isa.capLive,
          SpecM.get, SpecM.require, SpecM.raise, SpecM.updDom, SpecM.setReg,
          SpecM.modify, specM_pure]
        rw [hRD, hlcN]
        rfl)
  case pos =>
    have hlive1 : (Hw.capSel E (Hw.readReg E Hw.rs1E)).live.eval σ = 1#1 :=
      hlive1iff.mpr hlv
    have hlcS : ((({ refillPhase m (Hw.abs σ) with inflight := none
        }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen
        = some { kind := Hw.decKind KW
                 lineage :=
                   if σ.regs (Hw.dcapLinV E S) 1 = 1#1 then
                     some (finOfBv (by decide) (σ.regs (Hw.dcapLin E S) 4))
                   else none } := by
      rw [hLCb, abs_liveCap]
      exact if_pos hlv
    by_cases hbit : HWv.getLsbD 12 = KW.getLsbD 0 ∧ KW.getLsbD 0 = false
    case neg =>
      -- bad cap: class mismatch or gate kind
      have hc2 : (Expr.not (Expr.and
          (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
          (Hw.kIsMem (Hw.capSel E
            (Hw.readReg E Hw.rs1E)).kindW))).eval σ = 1#1 := by
        show ~~~((Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk.eval σ &&&
          (Hw.kIsMem (Hw.capSel E
            (Hw.readReg E Hw.rs1E)).kindW).eval σ) = 1#1
        by_cases hA : HWv.getLsbD 12 = KW.getLsbD 0
        · by_cases hB : KW.getLsbD 0 = false
          · exact absurd ⟨hA, hB⟩ hbit
          · rw [bv1_ne_one.mp (fun hc => hB (hmemiff.mp hc))]
            exact (by decide : ∀ b : BitVec 1,
              ~~~(b &&& (0#1 : BitVec 1)) = 1#1) _
        · rw [bv1_ne_one.mp (fun hc => hA (hclsOkiff.mp hc))]
          exact (by decide : ∀ b : BitVec 1,
            ~~~((0#1 : BitVec 1) &&& b) = 1#1) _
      have hmapok0 : (Hw.mapOkE E).eval σ = 0#1 := by
        show ~~~(~~~((Hw.capSel E (Hw.readReg E Hw.rs1E)).live.eval σ)) &&&
          ~~~(~~~((Expr.and (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
            (Hw.kIsMem (Hw.capSel E
              (Hw.readReg E Hw.rs1E)).kindW)).eval σ)) = 0#1
        have h2 : ((Expr.and (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
            (Hw.kIsMem (Hw.capSel E
              (Hw.readReg E Hw.rs1E)).kindW)).eval σ) = 0#1 :=
          (by decide : ∀ b : BitVec 1, ~~~b = 1#1 → b = 0#1) _ hc2
        rw [h2, hlive1]
        decide
      refine map_err_common m hwf hfit σ hsync hifv hcl hin
        (fun c r => by
          by_cases hcd : c = E
          · subst hcd
            exact andAll_zero_of_mem σ
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
              (by rw [hmapok0]; decide)
          · exact andAll_zero_of_mem σ
              (List.mem_cons_of_mem _ (List.mem_cons_self ..))
              (hifexcl c hcd))
        hunmapz hswz hben5 E rfl Errno.badCap.toWord
        (fun acc => by
          rw [hselC acc]
          show (if (Expr.not
              (Hw.capSel E (Hw.readReg E Hw.rs1E)).live).eval σ = 1#1
            then (Hw.respA E (.err .staleHandle)).run σ acc
            else (if (Expr.not (Expr.and
                (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
                (Hw.kIsMem (Hw.capSel E
                  (Hw.readReg E Hw.rs1E)).kindW))).eval σ = 1#1
              then (Hw.respA E (.err .badCap)).run σ acc else _)) = _
          rw [if_neg (by
            show ¬(~~~((Hw.capSel E
              (Hw.readReg E Hw.rs1E)).live.eval σ) = 1#1)
            rw [hlive1]
            decide)]
          rw [if_pos hc2]
          rfl)
        (by
          rw [hcore0, hDO]
          simp only [specM_bind, SpecM.reg, Machines.Lnp64u.Isa.capLive,
            SpecM.get, SpecM.require, SpecM.raise, SpecM.updDom,
            SpecM.setReg, SpecM.modify, specM_pure]
          obtain ⟨ce, hlcS', hcek⟩ :
              ∃ ce : CapEntry,
                ((({ refillPhase m (Hw.abs σ) with inflight := none
                  }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms
                  E).liveCap (Handle.decode HWv).slot (Handle.decode HWv).gen
                  = some ce
                ∧ ce.kind = Hw.decKind KW := ⟨_, hlcS, rfl⟩
          rw [hRD, hlcS']
          simp only [hcek]
          by_cases hA : (Handle.decode HWv).cls
              = (Hw.decKind KW).cls
          · rw [show (decide ((Handle.decode HWv).cls
                = (Hw.decKind KW).cls)) = true from decide_eq_true hA]
            have hbits := (cls_eq_iff_bits HWv KW).mp hA
            have hgt : KW.getLsbD 0 = true := by
              cases hB : KW.getLsbD 0
              · exact absurd ⟨hbits, hB⟩ hbit
              · rfl
            have hgk : Hw.decKind KW = .gate (finOfBv (by decide)
                (KW.extractLsb' 1 2)) := by
              rw [Hw.decKind, if_pos hgt]
            simp only [reduceIte, specM_bind, specM_pure]
            rw [hcek, hgk]
            rfl
          · rw [show (decide ((Handle.decode HWv).cls
                = (Hw.decKind KW).cls)) = false from decide_eq_false hA]
            rfl)
    case pos =>
      -- the OK path: the region installs
      have habs1 : Hw.abs ((Hw.refillAct m).run σ σ)
          = refillPhase m (Hw.abs σ) := abs_refill m hwf hfit σ hsync
      have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
          = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
        intro y
        rw [← habs1]
        rfl
      have hclsq : (Handle.decode HWv).cls = (Hw.decKind KW).cls :=
        (cls_eq_iff_bits HWv KW).mpr hbit.1
      have hmk : Hw.decKind KW = .mem (KW.extractLsb' 1 12)
          (KW.extractLsb' 13 13) (Hw.decPerms (KW.extractLsb' 26 3)) :=
        (decKind_mem_iff KW).mp hbit.2
      have hclsOk1 : (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk.eval σ
          = 1#1 := hclsOkiff.mpr hbit.1
      have hmem1 : (Hw.kIsMem
          (Hw.capSel E (Hw.readReg E Hw.rs1E)).kindW).eval σ = 1#1 :=
        hmemiff.mpr hbit.2
      have hand2 : (Expr.and (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
          (Hw.kIsMem (Hw.capSel E
            (Hw.readReg E Hw.rs1E)).kindW)).eval σ = 1#1 := by
        show ((Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk.eval σ &&&
          (Hw.kIsMem (Hw.capSel E
            (Hw.readReg E Hw.rs1E)).kindW).eval σ) = 1#1
        rw [hclsOk1, hmem1]
        decide
      have hok : (Hw.mapOkE E).eval σ = 1#1 := by
        show ~~~(~~~((Hw.capSel E (Hw.readReg E Hw.rs1E)).live.eval σ)) &&&
          ~~~(~~~((Expr.and (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
            (Hw.kIsMem (Hw.capSel E
              (Hw.readReg E Hw.rs1E)).kindW)).eval σ)) = 1#1
        rw [hlive1, hand2]
        decide
      set RIfin : RegionId := finOfBv (by decide)
        (((operandsOf W).imm).extractLsb' 0 2) with hRIdef
      have hri : Hw.riE.eval σ = BitVec.ofNat 2 RIfin.val := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt
          (show RIfin.val < 2 ^ 2 from RIfin.isLt)).symm
      -- the packed-value bridges
      have hKWc : KW = Hw.encKind (.mem (KW.extractLsb' 1 12)
          (KW.extractLsb' 13 13) (Hw.decPerms (KW.extractLsb' 26 3))) := by
        have h := (hkc E S).symm
        rw [hmk] at h
        exact h
      have hE4 : E.val < 4 := E.isLt
      have hrf : (Hw.encRefE (Hw.dLit E)
          (Hw.capSel E (Hw.readReg E Hw.rs1E)).slot
          (Hw.capSel E (Hw.readReg E Hw.rs1E)).gen).eval σ
          = Hw.encRef ⟨E, S, G⟩ := by
        show (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 4 8).setWidth 14 |||
          (((((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).setWidth 14
              <<< (8#14).toNat) |||
            (((BitVec.ofNat 2 E.val).setWidth 14) <<< (12#14).toNat)) = _
        rw [hR1]
        show G.setWidth 14 ||| ((HWv.extractLsb' 0 4).setWidth 14 <<< 8 |||
          (BitVec.ofNat 2 E.val).setWidth 14 <<< 12)
          = G.setWidth 14 ||| (BitVec.ofNat 14 S.val <<< 8) |||
            (BitVec.ofNat 14 E.val <<< 12)
        have hSv : BitVec.ofNat 14 S.val
            = (HWv.extractLsb' 0 4).setWidth 14 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
          show S.val % 2 ^ 14 = (HWv.extractLsb' 0 4).toNat % 2 ^ 14
          rfl
        have hEv : BitVec.ofNat 14 E.val
            = (BitVec.ofNat 2 E.val).setWidth 14 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega : E.val < 2 ^ 2)]
        rw [hSv, hEv, BitVec.or_assoc]
      have hMVe : (Hw.mapValE E).eval σ
          = ((KW.extractLsb' 26 3).setWidth 42 |||
            (((KW.extractLsb' 13 13).setWidth 42 <<< 3) |||
              (((KW.extractLsb' 1 12).setWidth 42 <<< 16) |||
                ((Hw.encRef ⟨E, S, G⟩).setWidth 42 <<< 28)))) := by
        show ((((Hw.capSel E
              (Hw.readReg E Hw.rs1E)).kindW.eval σ).extractLsb' 26 3
            ).setWidth 42 |||
          ((((Hw.capSel E
              (Hw.readReg E Hw.rs1E)).kindW.eval σ).extractLsb' 13 13
            ).setWidth 42 <<< (3#42).toNat |||
            ((((Hw.capSel E
                (Hw.readReg E Hw.rs1E)).kindW.eval σ).extractLsb' 1 12
              ).setWidth 42 <<< (16#42).toNat |||
              (((Hw.encRefE (Hw.dLit E)
                  (Hw.capSel E (Hw.readReg E Hw.rs1E)).slot
                  (Hw.capSel E (Hw.readReg E Hw.rs1E)).gen).eval σ
                ).setWidth 42 <<< (28#42).toNat)))) = _
        rw [hkwE, hrf]
        rfl
      have hMV : Hw.decRegion ((Hw.mapValE E).eval σ)
          = mapRgn E (Handle.decode HWv).slot (Handle.decode HWv).gen
              (KW.extractLsb' 1 12) (KW.extractLsb' 13 13)
              (Hw.decPerms (KW.extractLsb' 26 3)) := by
        rw [hMVe]
        rw [show ((KW.extractLsb' 26 3).setWidth 42 |||
            (((KW.extractLsb' 13 13).setWidth 42 <<< 3) |||
              (((KW.extractLsb' 1 12).setWidth 42 <<< 16) |||
                ((Hw.encRef ⟨E, S, G⟩).setWidth 42 <<< 28))))
          = (((Hw.encKind (.mem (KW.extractLsb' 1 12) (KW.extractLsb' 13 13)
              (Hw.decPerms (KW.extractLsb' 26 3)))).extractLsb' 26 3
            ).setWidth 42 |||
            ((((Hw.encKind (.mem (KW.extractLsb' 1 12) (KW.extractLsb' 13 13)
                (Hw.decPerms (KW.extractLsb' 26 3)))).extractLsb' 13 13
              ).setWidth 42 <<< 3) |||
              ((((Hw.encKind (.mem (KW.extractLsb' 1 12)
                  (KW.extractLsb' 13 13)
                  (Hw.decPerms (KW.extractLsb' 26 3)))).extractLsb' 1 12
                ).setWidth 42 <<< 16) |||
                ((Hw.encRef ⟨E, S, G⟩).setWidth 42 <<< 28)))) from by
          rw [← hKWc]]
        rw [mapVal_pack, decRef_encRef, decRegion_encRegion]
        rfl
      -- the spec side
      obtain ⟨ce, hlcS', hcek⟩ :
          ∃ ce : CapEntry,
            ((({ refillPhase m (Hw.abs σ) with inflight := none
              }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms
              E).liveCap (Handle.decode HWv).slot (Handle.decode HWv).gen
              = some ce
            ∧ ce.kind = Hw.decKind KW := ⟨_, hlcS, rfl⟩
      have hspec : corePhase m (refillPhase m (Hw.abs σ))
          = ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
              (fun ds => ({ { ds with pc := ds.pc + 1 } with
                regions := Loom.Fun.update
                  ({ ds with pc := ds.pc + 1 }).regions
                  (mapRI (operandsOf W))
                  (some (mapRgn E (Handle.decode HWv).slot
                    (Handle.decode HWv).gen (KW.extractLsb' 1 12)
                    (KW.extractLsb' 13 13)
                    (Hw.decPerms (KW.extractLsb' 26 3)))) }).setReg
                (operandsOf W).rd 0) := by
        have h1 : corePhase m (refillPhase m (Hw.abs σ))
            = (((({ refillPhase m (Hw.abs σ) with inflight := none
                }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).setDom E
                (fun ds => { ds with regions := Loom.Fun.update ds.regions (mapRI (operandsOf W)) (some (mapRgn E (Handle.decode HWv).slot (Handle.decode HWv).gen (KW.extractLsb' 1 12) (KW.extractLsb' 13 13) (Hw.decPerms (KW.extractLsb' 26 3)))) })).setDom E
                (fun ds => ds.setReg (operandsOf W).rd 0)) := by
          rw [hcore0, hDO]
          simp only [specM_bind, SpecM.reg, Machines.Lnp64u.Isa.capLive,
            SpecM.get, SpecM.require, SpecM.raise, SpecM.updDom,
            SpecM.setReg, SpecM.modify, specM_pure]
          rw [hRD, hlcS']
          simp only [hcek]
          rw [show (decide ((Handle.decode HWv).cls
              = (Hw.decKind KW).cls)) = true from decide_eq_true hclsq]
          simp only [reduceIte, specM_bind, specM_pure]
          rw [hcek, hmk]
          rfl
        rw [h1, setDom_setDom, setDom_setDom]
      -- HW faces of the region file
      have hrgnV : ∀ r : RegionId,
          ((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.drgnV E r) 1
          = if r = RIfin then 1#1 else σ.regs (Hw.drgnV E r) 1 := by
        intro r
        show ((Hw.seqAll (((List.finRange numRegions).map fun r' =>
            Act.ite (.eq Hw.riE (Hw.rLit r'))
              (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                    (.write 42 (Hw.drgn E r') (Hw.mapValE E))) .skip)
          ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E])).run σ
            ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ))).regs (Hw.drgnV E r) 1 = _
        rw [seqAll_append_run]
        rw [show ((Hw.seqAll [Hw.writeReg E Hw.rdE (.lit 0),
            Hw.pcAdvA E]).run σ
            ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
              Act.ite (.eq Hw.riE (Hw.rLit r'))
                (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                      (.write 42 (Hw.drgn E r') (Hw.mapValE E))) .skip)).run
              σ ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ)))).regs (Hw.drgnV E r) 1
          = ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
              Act.ite (.eq Hw.riE (Hw.rLit r'))
                (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                      (.write 42 (Hw.drgn E r') (Hw.mapValE E))) .skip)).run
              σ ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ))).regs (Hw.drgnV E r) 1 from by
          show ((Hw.pcAdvA E).run σ
            ((Hw.writeReg E Hw.rdE (Expr.lit 0)).run σ _)).regs
            (Hw.drgnV E r) 1 = _
          rw [frame (show (Hw.drgnV E r, 1) ∉ (Hw.pcAdvA E).regWrites from by
            intro hm
            exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
              (show ¬((1 : Nat) = 12) by decide)) σ _]
          rw [frame ((by decide +kernel : ∀ (e : DomainId) (r' : RegionId),
            ((Hw.drgnV e r' : String), (1 : Nat))
              ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) E r) σ _]]
        rw [seqAll_ite_run_unique σ _
          (fun r' : RegionId => Expr.eq Hw.riE (Hw.rLit r'))
          (fun r' : RegionId => Act.seq
            (.write 1 (Hw.drgnV E r') (.lit 1))
            (.write 42 (Hw.drgn E r') (Hw.mapValE E))) RIfin
          (by
            show (Expr.eq Hw.riE (Hw.rLit RIfin)).eval σ = 1#1
            rw [eqE_eval, hri]
            rfl)
          (fun j hj => by
            intro hc0
            have hc : (Expr.eq Hw.riE (Hw.rLit j)).eval σ = 1#1 := hc0
            rw [eqE_eval, hri] at hc
            apply hj
            apply Fin.ext
            have : (BitVec.ofNat 2 RIfin.val).toNat
                = (BitVec.ofNat 2 j.val).toNat := by rw [hc]; rfl
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (show j.val < 2 ^ 2 from j.isLt),
              Nat.mod_eq_of_lt (show RIfin.val < 2 ^ 2 from RIfin.isLt)]
              at this
            omega)
          _ (List.mem_finRange RIfin) (List.nodup_finRange _)]
        show (RegEnv.set (RegEnv.set _ (Hw.drgnV E RIfin)
            ((Expr.lit 1).eval σ)) (Hw.drgn E RIfin)
            ((Hw.mapValE E).eval σ)) (Hw.drgnV E r) 1 = _
        simp only [RegEnv.set]
        rw [if_neg ((by decide +kernel : ∀ (e : DomainId) (r1 r2 : RegionId),
          ¬(Hw.drgnV e r1 = Hw.drgn e r2)) E r RIfin)]
        by_cases hr : r = RIfin
        · rw [if_pos (by rw [hr]), if_pos hr]
          rfl
        · rw [if_neg (fun hc => hr (drgnV_inj E r RIfin hc)), if_neg hr]
          rw [frame (fun hm => absurd
            (congrArg Prod.fst (List.mem_singleton.mp hm))
            ((by decide +kernel : ∀ (e : DomainId) (r' : RegionId),
              ¬(Hw.drgnV e r' = "if_v")) E r)) σ _]
          exact refill_pres m σ (drgnV_notin_refill E r)
      have hrgn42 : ∀ r : RegionId,
          ((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.drgn E r) 42
          = if r = RIfin then (Hw.mapValE E).eval σ
            else σ.regs (Hw.drgn E r) 42 := by
        intro r
        show ((Hw.seqAll (((List.finRange numRegions).map fun r' =>
            Act.ite (.eq Hw.riE (Hw.rLit r'))
              (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                    (.write 42 (Hw.drgn E r') (Hw.mapValE E))) .skip)
          ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E])).run σ
            ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ))).regs (Hw.drgn E r) 42 = _
        rw [seqAll_append_run]
        rw [show ((Hw.seqAll [Hw.writeReg E Hw.rdE (.lit 0),
            Hw.pcAdvA E]).run σ
            ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
              Act.ite (.eq Hw.riE (Hw.rLit r'))
                (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                      (.write 42 (Hw.drgn E r') (Hw.mapValE E))) .skip)).run
              σ ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ)))).regs (Hw.drgn E r) 42
          = ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
              Act.ite (.eq Hw.riE (Hw.rLit r'))
                (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                      (.write 42 (Hw.drgn E r') (Hw.mapValE E))) .skip)).run
              σ ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ))).regs (Hw.drgn E r) 42 from by
          show ((Hw.pcAdvA E).run σ
            ((Hw.writeReg E Hw.rdE (Expr.lit 0)).run σ _)).regs
            (Hw.drgn E r) 42 = _
          rw [frame (show (Hw.drgn E r, 42) ∉ (Hw.pcAdvA E).regWrites from by
            intro hm
            exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
              (show ¬((42 : Nat) = 12) by decide)) σ _]
          rw [frame ((by decide +kernel : ∀ (e : DomainId) (r' : RegionId),
            ((Hw.drgn e r' : String), (42 : Nat))
              ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) E r) σ _]]
        rw [seqAll_ite_run_unique σ _
          (fun r' : RegionId => Expr.eq Hw.riE (Hw.rLit r'))
          (fun r' : RegionId => Act.seq
            (.write 1 (Hw.drgnV E r') (.lit 1))
            (.write 42 (Hw.drgn E r') (Hw.mapValE E))) RIfin
          (by
            show (Expr.eq Hw.riE (Hw.rLit RIfin)).eval σ = 1#1
            rw [eqE_eval, hri]
            rfl)
          (fun j hj => by
            intro hc0
            have hc : (Expr.eq Hw.riE (Hw.rLit j)).eval σ = 1#1 := hc0
            rw [eqE_eval, hri] at hc
            apply hj
            apply Fin.ext
            have : (BitVec.ofNat 2 RIfin.val).toNat
                = (BitVec.ofNat 2 j.val).toNat := by rw [hc]; rfl
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (show j.val < 2 ^ 2 from j.isLt),
              Nat.mod_eq_of_lt (show RIfin.val < 2 ^ 2 from RIfin.isLt)]
              at this
            omega)
          _ (List.mem_finRange RIfin) (List.nodup_finRange _)]
        show (RegEnv.set (RegEnv.set _ (Hw.drgnV E RIfin)
            ((Expr.lit 1).eval σ)) (Hw.drgn E RIfin)
            ((Hw.mapValE E).eval σ)) (Hw.drgn E r) 42 = _
        simp only [RegEnv.set]
        by_cases hr : r = RIfin
        · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial]
        · rw [if_neg (fun hc => hr
            ((by decide +kernel : ∀ (e : DomainId) (r1 r2 : RegionId),
              Hw.drgn e r1 = Hw.drgn e r2 → r1 = r2) E r RIfin hc))]
          rw [if_neg ((by decide +kernel :
            ∀ (e : DomainId) (r1 r2 : RegionId),
              ¬(Hw.drgn e r1 = Hw.drgnV e r2)) E r RIfin), if_neg hr]
          rw [frame (fun hm => absurd
            (congrArg Prod.fst (List.mem_singleton.mp hm))
            ((by decide +kernel : ∀ (e : DomainId) (r' : RegionId),
              ¬(Hw.drgn e r' = "if_v")) E r)) σ _]
          exact refill_pres m σ (drgn_notin_refill' E r)
      have hcoreX : ∀ acc, (Hw.retireFor E).run σ acc
          = (Hw.seqAll (((List.finRange numRegions).map fun r =>
              .ite (.eq Hw.riE (Hw.rLit r))
                (.seq (.write 1 (Hw.drgnV E r) (.lit 1))
                      (.write 42 (Hw.drgn E r) (Hw.mapValE E))) .skip)
            ++ [Hw.writeReg E Hw.rdE (.lit 0),
                Hw.pcAdvA E])).run σ acc := by
        intro acc
        rw [hselC acc]
        show (if (Expr.not
            (Hw.capSel E (Hw.readReg E Hw.rs1E)).live).eval σ = 1#1
          then (Hw.respA E (.err .staleHandle)).run σ acc
          else (if (Expr.not (Expr.and
              (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
              (Hw.kIsMem (Hw.capSel E
                (Hw.readReg E Hw.rs1E)).kindW))).eval σ = 1#1
            then (Hw.respA E (.err .badCap)).run σ acc
            else _)) = _
        rw [if_neg (by
          show ¬(~~~((Hw.capSel E
            (Hw.readReg E Hw.rs1E)).live.eval σ) = 1#1)
          rw [hlive1]
          decide)]
        rw [if_neg (by
          show ¬(~~~((Expr.and (Hw.capSel E (Hw.readReg E Hw.rs1E)).clsOk
            (Hw.kIsMem (Hw.capSel E
              (Hw.readReg E Hw.rs1E)).kindW)).eval σ) = 1#1)
          rw [hand2]
          decide)]
        rfl
      have hτ2doms : ∀ x, (({ refillPhase m (Hw.abs σ) with inflight := none
          }).setDom E (fun ds => ({ { ds with pc := ds.pc + 1 } with
            regions := Loom.Fun.update
              ({ ds with pc := ds.pc + 1 }).regions (mapRI (operandsOf W))
              (some (mapRgn E (Handle.decode HWv).slot
                (Handle.decode HWv).gen (KW.extractLsb' 1 12)
                (KW.extractLsb' 13 13)
                (Hw.decPerms (KW.extractLsb' 26 3)))) }).setReg
            (operandsOf W).rd 0)).doms x
          = if x = E
            then ({ { (refillPhase m (Hw.abs σ)).doms E with
                pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 } with
                regions := Loom.Fun.update
                  ((refillPhase m (Hw.abs σ)).doms E).regions
                  (mapRI (operandsOf W))
                  (some (mapRgn E (Handle.decode HWv).slot
                    (Handle.decode HWv).gen (KW.extractLsb' 1 12)
                    (KW.extractLsb' 13 13)
                    (Hw.decPerms (KW.extractLsb' 26 3)))) }).setReg
                (operandsOf W).rd 0
            else (refillPhase m (Hw.abs σ)).doms x := by
        intro x
        show (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x = _
        by_cases hx : x = E
        · subst hx
          rw [Loom.Fun.update_same, if_pos rfl]
        · rw [Loom.Fun.update_ne _ _ _ _ hx, if_neg hx]
      refine square_retire_rgnop m hwf hfit σ hsync hifv hcl hin
        (Hw.seqAll (((List.finRange numRegions).map fun r =>
            .ite (.eq Hw.riE (Hw.rLit r))
              (.seq (.write 1 (Hw.drgnV E r) (.lit 1))
                    (.write 42 (Hw.drgn E r) (Hw.mapValE E))) .skip)
          ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E])) _
        (fun rn w => by
          rw [coreAct_run_retire_eq m σ _ hifv hcl,
            retireAct_run_regs σ _ E rfl rn w, hcoreX]
          rfl)
        (ifv_notin_mapX E)
        hspec ?_ ?_ ?_ ?_ ?_ (fun ow sa => ?_) ?_ ?_ ?_ ?_
      · -- absDom faces
        intro x
        rw [hτ2doms x]
        by_cases hx : x = E
        · rw [if_pos hx]
          subst hx
          show Hw.absDom ((mapFull E).run σ ((Hw.refillAct m).run σ σ)) E = _
          have hq : ∀ q ∈ domQuietNamesRg E,
              ((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs q.1 q.2
                = ((Hw.refillAct m).run σ σ).regs q.1 q.2 :=
            fun q hq' => frame (quietRg_notin_map E E q hq') σ _
          rw [absDom_regpcrgn E hq]
          rw [show (refillPhase m (Hw.abs σ)).doms E
            = Hw.absDom ((Hw.refillAct m).run σ σ) E from hL1 E]
          apply domainState_ext'
          · funext r
            show ((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
              (Hw.dreg E r) 32 = _
            rw [show ((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
                (Hw.dreg E r) 32
                = ((Hw.writeReg E Hw.rdE (.lit 0)).run σ
                    ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
                      Act.ite (.eq Hw.riE (Hw.rLit r'))
                        (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                              (.write 42 (Hw.drgn E r') (Hw.mapValE E)))
                        .skip)).run σ
                      ((Act.write 1 "if_v" (.lit 0)).run σ
                        ((Hw.refillAct m).run σ σ)))).regs
                    (Hw.dreg E r) 32 from by
              show ((Hw.seqAll (((List.finRange numRegions).map fun r' =>
                  Act.ite (.eq Hw.riE (Hw.rLit r'))
                    (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                          (.write 42 (Hw.drgn E r') (Hw.mapValE E))) .skip)
                ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E])).run σ
                  ((Act.write 1 "if_v" (.lit 0)).run σ
                    ((Hw.refillAct m).run σ σ))).regs (Hw.dreg E r) 32 = _
              rw [seqAll_append_run]
              show ((Hw.pcAdvA E).run σ
                ((Hw.writeReg E Hw.rdE (Expr.lit 0)).run σ _)).regs
                (Hw.dreg E r) 32 = _
              rw [frame (show (Hw.dreg E r, 32)
                  ∉ (Hw.pcAdvA E).regWrites from by
                intro hm
                exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
                  (show ¬((32 : Nat) = 12) by decide)) σ _]]
            show _ = (({ { Hw.absDom ((Hw.refillAct m).run σ σ) E with
                pc := (Hw.absDom ((Hw.refillAct m).run σ σ) E).pc + 1 } with
                regions := Loom.Fun.update
                  ({ Hw.absDom ((Hw.refillAct m).run σ σ) E with
                    pc := (Hw.absDom ((Hw.refillAct m).run σ σ) E).pc + 1
                    }).regions (mapRI (operandsOf W))
                  (some (mapRgn E (Handle.decode HWv).slot
                    (Handle.decode HWv).gen (KW.extractLsb' 1 12)
                    (KW.extractLsb' 13 13)
                    (Hw.decPerms (KW.extractLsb' 26 3)))) }).setReg
                (operandsOf W).rd 0).regs r
            rw [setReg_regs]
            have hitefr :
                ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
                  Act.ite (.eq Hw.riE (Hw.rLit r'))
                    (.seq (.write 1 (Hw.drgnV E r') (.lit 1))
                          (.write 42 (Hw.drgn E r') (Hw.mapValE E)))
                    .skip)).run σ
                  ((Act.write 1 "if_v" (.lit 0)).run σ
                    ((Hw.refillAct m).run σ σ))).regs (Hw.dreg E r) 32
                = ((Act.write 1 "if_v" (.lit 0)).run σ
                    ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32 := by
              rw [seqAll_ite_run_unique σ _
                (fun r' : RegionId => Expr.eq Hw.riE (Hw.rLit r'))
                (fun r' : RegionId => Act.seq
                  (.write 1 (Hw.drgnV E r') (.lit 1))
                  (.write 42 (Hw.drgn E r') (Hw.mapValE E))) RIfin
                (by
                  show (Expr.eq Hw.riE (Hw.rLit RIfin)).eval σ = 1#1
                  rw [eqE_eval, hri]
                  rfl)
                (fun j hj => by
                  intro hc0
                  have hc : (Expr.eq Hw.riE (Hw.rLit j)).eval σ = 1#1 := hc0
                  rw [eqE_eval, hri] at hc
                  apply hj
                  apply Fin.ext
                  have : (BitVec.ofNat 2 RIfin.val).toNat
                      = (BitVec.ofNat 2 j.val).toNat := by rw [hc]; rfl
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (show j.val < 2 ^ 2 from j.isLt),
                    Nat.mod_eq_of_lt
                      (show RIfin.val < 2 ^ 2 from RIfin.isLt)] at this
                  omega)
                _ (List.mem_finRange RIfin) (List.nodup_finRange _)]
              show (RegEnv.set (RegEnv.set _ (Hw.drgnV E RIfin)
                  ((Expr.lit 1).eval σ)) (Hw.drgn E RIfin)
                  ((Hw.mapValE E).eval σ)) (Hw.dreg E r) 32 = _
              simp only [RegEnv.set]
              rw [if_neg ((by decide +kernel :
                ∀ (e : DomainId) (r1 : RegId) (r2 : RegionId),
                  ¬(Hw.dreg e r1 = Hw.drgn e r2)) E r RIfin)]
              rw [if_neg ((by decide +kernel :
                ∀ (e : DomainId) (r1 : RegId) (r2 : RegionId),
                  ¬(Hw.dreg e r1 = Hw.drgnV e r2)) E r RIfin)]
            have hifvframe :
                ((Act.write 1 "if_v" (.lit 0)).run σ
                  ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32
                = ((Hw.refillAct m).run σ σ).regs (Hw.dreg E r) 32 :=
              frame (fun hm => absurd
                (congrArg Prod.snd (List.mem_singleton.mp hm))
                (show ¬((32 : Nat) = 1) by decide)) σ _
            by_cases h0 : (operandsOf W).rd = (0 : Fin numRegs)
            · rw [if_pos h0]
              rw [writeReg_run_of_zero σ _ E Hw.rdE _ (by
                rw [show ((Hw.rdE.eval σ)).toNat
                  = ((operandsOf W).rd : Fin numRegs).val from rfl, h0]
                rfl)]
              rw [hitefr, hifvframe]
              rfl
            · rw [if_neg h0]
              rw [writeReg_run_of_nz σ _ E Hw.rdE _ (operandsOf W).rd rfl
                (fun hc => h0 (Fin.ext hc))]
              show (RegEnv.set _ (Hw.dreg E (operandsOf W).rd) _)
                (Hw.dreg E r) 32 = _
              simp only [RegEnv.set]
              by_cases hr : r = (operandsOf W).rd
              · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial]
                rfl
              · rw [if_neg (fun hc => hr (dreg_inj E r (operandsOf W).rd hc)),
                  if_neg hr]
                rw [hitefr, hifvframe]
                rfl
          · show ((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
              (Hw.dpc E) 12 = _
            rw [show ((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
                (Hw.dpc E) 12 = σ.regs (Hw.dpc E) 12 + 1 from by
              show (RegEnv.set _ (Hw.dpc E)
                ((Expr.add (Hw.rPc E) (.lit 1)).eval σ)) (Hw.dpc E) 12 = _
              simp [RegEnv.set, Expr.eval, Hw.rPc]]
            rw [setReg_pc]
            show σ.regs (Hw.dpc E) 12 + 1
              = ((Hw.refillAct m).run σ σ).regs (Hw.dpc E) 12 + 1
            rw [refill_pres m σ ((by decide +kernel : ∀ e : DomainId,
              ((Hw.dpc e : String), (12 : Nat)) ∉
              ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
                ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
                ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat)))
              E)]
          · rw [setReg_caps]
          · rw [setReg_slotGen]
          · rw [setReg_lineage]
          · -- the region file
            funext r
            rw [setReg_regions]
            show (if ((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
                (Hw.drgnV E r) 1 = 1
              then some (Hw.decRegion
                (((mapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
                  (Hw.drgn E r) 42))
              else none)
              = Loom.Fun.update
                  (Hw.absDom ((Hw.refillAct m).run σ σ) E).regions
                  (mapRI (operandsOf W))
                  (some (mapRgn E (Handle.decode HWv).slot
                    (Handle.decode HWv).gen (KW.extractLsb' 1 12)
                    (KW.extractLsb' 13 13)
                    (Hw.decPerms (KW.extractLsb' 26 3)))) r
            rw [hrgnV r, hrgn42 r]
            unfold Loom.Fun.update
            by_cases hr : r = RIfin
            · rw [if_pos hr, if_pos hr,
                if_pos (show r = mapRI (operandsOf W) from hr),
                if_pos (show (1#1 : BitVec 1) = 1 from rfl), hMV]
            · rw [if_neg hr, if_neg hr,
                if_neg (show ¬(r = mapRI (operandsOf W)) from hr)]
              show (if σ.regs (Hw.drgnV E r) 1 = 1 then _ else none) = _
              rw [show (Hw.absDom ((Hw.refillAct m).run σ σ) E).regions r
                = (if ((Hw.refillAct m).run σ σ).regs (Hw.drgnV E r) 1 = 1
                  then some (Hw.decRegion
                    (((Hw.refillAct m).run σ σ).regs (Hw.drgn E r) 42))
                  else none) from rfl]
              rw [refill_pres m σ (drgnV_notin_refill E r),
                refill_pres m σ (drgn_notin_refill' E r)]
          · rw [setReg_run]
          · rw [setReg_serving]
          · rw [setReg_cause]
          · rw [setReg_budget]
          · rw [setReg_maxDonation]
        · rw [if_neg hx]
          show Hw.absDom ((mapFull E).run σ ((Hw.refillAct m).run σ σ)) x = _
          rw [hL1 x]
          exact absDom_congr x (fun p hp =>
            frame (read_notin_map_ne x E hx p hp) σ _)
      · -- gates
        intro g
        show Hw.absGate ((mapFull E).run σ ((Hw.refillAct m).run σ σ)) g = _
        rw [absGate_congr g (fun p hp =>
          frame (gate_notin_map g E p hp) σ _)]
        rw [← habs1]
        rfl
      · intro x
        rw [hτ2doms x]
        by_cases hx : x = E
        · rw [if_pos hx, setReg_caps]
          show ((refillPhase m (Hw.abs σ)).doms E).caps = _
          rw [refillPhase_caps, hx]
        · rw [if_neg hx, refillPhase_caps]
      · intro x
        rw [hτ2doms x]
        by_cases hx : x = E
        · rw [if_pos hx, setReg_slotGen]
          show ((refillPhase m (Hw.abs σ)).doms E).slotGen = _
          rw [refillPhase_slotGen, hx]
        · rw [if_neg hx, refillPhase_slotGen]
      · show (refillPhase m (Hw.abs σ)).mover = _
        rw [refillPhase_mover]
        rfl
      · -- the fired-map status authority
        refine sAuth_map_eval σ E hin hret hifsel hifexcl hmapmn hok hunmapz
          RIfin hri _ ?_ ow sa
        intro c r
        rw [hτ2doms c]
        by_cases hc : c = E
        · subst hc
          rw [if_pos rfl, setReg_regions]
          show Loom.Fun.update ((refillPhase m (Hw.abs σ)).doms E).regions
            (mapRI (operandsOf W))
            (some (mapRgn E (Handle.decode HWv).slot
              (Handle.decode HWv).gen (KW.extractLsb' 1 12)
              (KW.extractLsb' 13 13)
              (Hw.decPerms (KW.extractLsb' 26 3)))) r = _
          unfold Loom.Fun.update
          by_cases hr : r = RIfin
          · rw [if_pos (show r = mapRI (operandsOf W) from hr),
              if_pos (⟨rfl, hr⟩ : E = E ∧ r = RIfin), hMV]
          · rw [if_neg (show ¬(r = mapRI (operandsOf W)) from hr),
              if_neg (fun hcr => hr hcr.2)]
            rw [refillPhase_regions]
        · rw [if_neg hc, if_neg (fun hcr => hc hcr.1), refillPhase_regions]
      · -- memory: no store
        intro b
        rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
        rw [refill_pres_mem m σ "mem" b.toNat 32]
        rfl
      · -- forwarding quiescent
        intro sc
        rw [srcWord_quiescent σ hswz sc]
        rfl
      · show (refillPhase m (Hw.abs σ)).cycle = _
        rfl
      · rfl



end Machines.Lnp64u.Theorems.RMC


