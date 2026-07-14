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

private theorem extract1_eq_iff {n m : Nat} (a : BitVec n) (b : BitVec m)
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

private theorem extract1_eq_zero_iff {n : Nat} (a : BitVec n) (i : Nat) :
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
private theorem cls_eq_iff_bits (hw kw : BitVec 32) :
    ((Handle.decode hw).cls = (Hw.decKind kw).cls)
      ↔ (hw.getLsbD 12 = kw.getLsbD 0) := by
  rw [show (Handle.decode hw).cls
    = (if hw.getLsbD 12 then CapClass.gate else CapClass.mem) from rfl]
  rw [Hw.decKind]
  cases h1 : hw.getLsbD 12 <;> cases h2 : kw.getLsbD 0 <;>
    simp [CapKind.cls]

/-- The memory-kind test is the tag bit. -/
private theorem decKind_mem_iff (kw : BitVec 32) :
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
private theorem map_err_common (m : Manifest) (hwf : m.WF) (hfit : Fits m)
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
    (fun b => by
      rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
      rw [refill_pres_mem m σ "mem" b.toNat 32]
      rfl)
    (fun sc => by
      rw [srcWord_quiescent σ hswz sc]
      rfl)
    (by
      show (refillPhase m (Hw.abs σ)).cycle = _
      rfl)
    rfl

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

end Machines.Lnp64u.Theorems.RMC


