-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireBranch

/-!
# R-MC support: the `sw` retirement arm

The first Mover-interacting op: an authorized `sw` commits its store on
memory port 0 and the Mover's same-cycle forwarding mux (`swHit`) serves
the stored word when the job's source cursor aliases the store address —
exactly the spec's `moverPhase` reading the post-core memory. The
unauthorized case is a plain retiring fault.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 12800000
set_option maxRecDepth 400000

/-- The `sw` effective address expression (domain `e`'s operands). -/
def swAddrE (e : DomainId) : Expr 12 :=
  Hw.field (.add (Hw.readReg e Hw.rs1E) Hw.immX) 0 12

/-- The `sw` op circuit (as declared in `baseCircs`). -/
def swC (e : DomainId) : Hw.OpCirc :=
  { act := .ite (Hw.domCoversE e (swAddrE e) ⟨false, true, false⟩)
      (Hw.pcAdvA e) (Hw.haltFault e .memoryAuthority)
    memEn := Hw.domCoversE e (swAddrE e) ⟨false, true, false⟩
    memAddr := swAddrE e
    memData := Hw.readReg e Hw.rs2E }

/-- A retiring cycle turns `retiringE` on. -/
theorem retiringE_one (σ : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2) :
    Hw.retiringE.eval σ = 1#1 := by
  show σ.regs "if_v" 1 &&&
    (if (σ.regs "if_cl" 8).ult ((Expr.lit (2 : BitVec 8)).eval σ)
      then (1#1 : BitVec 1) else 0#1) = 1#1
  rw [hifv, if_pos (show (σ.regs "if_cl" 8).ult
      ((Expr.lit (2 : BitVec 8)).eval σ) = true from
    decide_eq_true (show (σ.regs "if_cl" 8).toNat
      < ((Expr.lit (2 : BitVec 8)).eval σ).toNat from hcl))]
  decide

private theorem bv1_one_and'' (x : BitVec 1) : 1#1 &&& x = x := by
  revert x; decide

/-- The forwarding fold skips non-owning domains down to the memory
read. -/
private theorem swFold_skip (σ : Loom.Hw.St) (E : DomainId)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1) :
    ∀ (l : List DomainId) (sc : Expr 12), (∀ d ∈ l, d ≠ E) →
      Expr.eval σ
        ((l.foldr
          (fun d acc' =>
            Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                Hw.domCoversE d
                  (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                  ⟨false, true, false⟩,
                .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
              (Hw.readReg d Hw.rs2E) acc')
          (.memRead 32 "mem" sc)))
        = σ.mems "mem" ((sc.eval σ)).toNat 32
  | [], _, _ => rfl
  | d :: t, sc, hne => by
      show (if (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
          Hw.domCoversE d
            (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
            ⟨false, true, false⟩,
          .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
            sc]).eval σ = 1#1
        then (Hw.readReg d Hw.rs2E).eval σ else _) = _
      rw [if_neg (by
        rw [andAll_zero_of_mem σ
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          (hifexcl d (hne d (List.mem_cons_self ..)))]
        decide)]
      exact swFold_skip σ E hifexcl t sc
        (fun d' hd' => hne d' (List.mem_cons_of_mem _ hd'))

/-- The forwarding fold on a retiring, authorized `sw`: the stored word
when the cursor aliases the store address, the memory read otherwise. -/
private theorem swFold_store (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hswsel : (Hw.isMn "sw").eval σ = 1#1)
    (hcov : (Hw.domCoversE E
      (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)
      ⟨false, true, false⟩).eval σ = 1#1) :
    ∀ (l : List DomainId) (sc : Expr 12), E ∈ l → l.Nodup →
      Expr.eval σ
        ((l.foldr
          (fun d acc' =>
            Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                Hw.domCoversE d
                  (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                  ⟨false, true, false⟩,
                .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
              (Hw.readReg d Hw.rs2E) acc')
          (.memRead 32 "mem" sc)))
        = if (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ
            = sc.eval σ
          then (Hw.readReg E Hw.rs2E).eval σ
          else σ.mems "mem" ((sc.eval σ)).toNat 32
  | [], _, hmem, _ => absurd hmem (List.not_mem_nil)
  | d :: t, sc, hmem, hnd => by
      rw [List.nodup_cons] at hnd
      by_cases hd : d = E
      · subst hd
        have hchain : (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
            Hw.domCoversE d
              (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
              ⟨false, true, false⟩,
            .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
              sc]).eval σ
            = (Expr.eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                sc).eval σ := by
          show Hw.retiringE.eval σ &&& ((Hw.ifDomIs d).eval σ &&&
            ((Hw.isMn "sw").eval σ &&&
              ((Hw.domCoversE d
                (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                ⟨false, true, false⟩).eval σ &&&
                (Expr.eq (Hw.field
                  (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc).eval σ)))
            = _
          rw [hret, hifsel, hswsel, hcov, bv1_one_and'', bv1_one_and'',
            bv1_one_and'', bv1_one_and'']
        show (if (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
            Hw.domCoversE d
              (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
              ⟨false, true, false⟩,
            .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
              sc]).eval σ = 1#1
          then (Hw.readReg d Hw.rs2E).eval σ else _) = _
        by_cases heq : (Hw.field
          (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12).eval σ = sc.eval σ
        · rw [if_pos (by
            rw [hchain, eqE_eval]
            exact heq), if_pos heq]
        · rw [if_neg (by
            rw [hchain, eqE_eval]
            exact heq), if_neg heq]
          have htne : ∀ d' ∈ t, d' ≠ d := fun d' hd' hc => hnd.1 (hc ▸ hd')
          exact swFold_skip σ d hifexcl t sc htne
      · show (if (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
            Hw.domCoversE d
              (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
              ⟨false, true, false⟩,
            .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
              sc]).eval σ = 1#1
          then (Hw.readReg d Hw.rs2E).eval σ else _) = _
        rw [if_neg (by
          rw [andAll_zero_of_mem σ
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            (hifexcl d hd)]
          decide)]
        have hmem' : E ∈ t := by
          rcases List.mem_cons.mp hmem with heq | h
          · exact absurd heq.symm hd
          · exact h
        exact swFold_store σ E hret hifsel hifexcl hswsel hcov t sc hmem'
          hnd.2

set_option maxHeartbeats 25600000 in
/-- The `sw` arm: opcode 10 — authorized store commits on port 0 (with
Mover same-cycle forwarding); missing authority faults. -/
theorem square_retire_sw (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 10#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (10#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (10#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hswsel : (Hw.isMn "sw").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "sw" = 10#6).symm
  have hret := retiringE_one σ hifv hcl
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  have haddr : (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ
      = effAddr (((Hw.abs σ).doms E).reg (operandsOf W).rs1)
          (operandsOf W).imm := by
    show ((Hw.readReg E Hw.rs1E).eval σ + Hw.immX.eval σ).extractLsb' 0 12 = _
    rw [hR1]
    rfl
  have hselC := retireFor_sel_of_opc σ E "sw" 10#6 hopc
    (by decide +kernel) (by decide +kernel) (swC E)
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))))))))))
  have hnd : ((Hw.opCircs E).map Prod.fst).Nodup := by
    rw [opCircs_fst_all E]
    exact allMns_nodup
  have hq : ∀ p ∈ Hw.opCircs E, p.1 ≠ "sw" →
      (Hw.isMn p.1).eval σ = 0#1 ∨ isLit0 p.2.memEn = true := by
    intro p hp hne
    have hmi := List.all_eq_true.mp (memInert_opCircs E) p hp
    rcases (Bool.or_eq_true _ _).mp hmi with h | h
    · left
      exact bv1_ne_one.mp (isMn_ne_of_opc σ p.1 10#6 hopc
        ((by decide +kernel : ∀ mn' ∈ allMns, mn' ≠ "sw" →
          (10#6 : BitVec 6) ≠ Hw.opcodeOf mn') p.1
          (by
            rw [← opCircs_fst_all E]
            exact List.mem_map_of_mem hp) hne))
    · right
      exact h
  have hmemsw : ("sw", swC E) ∈ Hw.opCircs E :=
    List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))))))))))
  have hswcomm := retireMem_sw_sel σ E (swC E) hifsel hifexcl hswsel hmemsw
    hnd hq
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have hin : Inert σ := Inert.of_benign7 σ (fun mn' hmn' =>
    isMn_ne_of_opc σ mn' 10#6 hopc
      ((by decide +kernel : ∀ mn' ∈ ["cap_drop", "cap_revoke", "gate_call",
        "gate_return", "move", "map", "unmap"], (10#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn'))
  have hspecA : ∀ rs : RegId,
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg rs
        = ((Hw.abs σ).doms E).reg rs :=
    fun rs => specReg_bridge m σ E rs
  have hred : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (if (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).domCovers E (effAddr (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ⟨false, true, false⟩ = true
         then (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).write (effAddr (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E)).reg (operandsOf W).rs2)
         else haltWith { refillPhase m (Hw.abs σ) with inflight := none } E
           .memoryAuthority) := by
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    show (match ((SpecM.reg E (operandsOf W).rs1 >>= fun a =>
        SpecM.reg E (operandsOf W).rs2 >>= fun v =>
        SpecM.store E (effAddr a (operandsOf W).imm) v)
        (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 }))) with
      | .ok _ σ' => σ'
      | .err e σ' =>
          σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
      | .fault fl =>
          haltWith { refillPhase m (Hw.abs σ) with inflight := none } E fl)
        = _
    simp only [specM_bind, SpecM.reg, SpecM.store, SpecM.get, SpecM.demand,
      SpecM.set, specM_pure]
    by_cases hc : (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).domCovers E (effAddr (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ⟨false, true, false⟩ = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      rfl
  by_cases hcov : (Hw.domCoversE E
      (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)
      ⟨false, true, false⟩).eval σ = 1#1
  · -- authorized store
    have hcovS : (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).domCovers E (effAddr (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ⟨false, true, false⟩ = true := by
      rw [hspecA, spec_covers_bridge]
      have := (domCoversE_eval σ E
        (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)
        ⟨false, true, false⟩).mp hcov
      rwa [haddr] at this
    refine square_retire_store m hwf hfit σ hsync hifv hcl hin
      (fun c r => andAll_zero_of_mem σ
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..)))
        (isMn_ne_of_opc σ "map" 10#6 hopc (by decide +kernel)))
      (fun c r => andAll_zero_of_mem σ
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..)))
        (isMn_ne_of_opc σ "unmap" 10#6 hopc (by decide +kernel)))
      (Hw.pcAdvA E)
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).write (effAddr (((Hw.abs σ).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) (((Hw.abs σ).doms E).reg (operandsOf W).rs2))
      (fun rn w => by
        rw [coreAct_run_retire_eq m σ _ hifv hcl,
          retireAct_run_regs σ _ E rfl rn w, hselC]
        show ((if (Hw.domCoversE E
            (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)
            ⟨false, true, false⟩).eval σ = 1#1
          then (Hw.pcAdvA E).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
            ((Hw.refillAct m).run σ σ))
          else (Hw.haltFault E .memoryAuthority).run σ
            ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ)))).regs rn w = _
        rw [if_pos hcov]
        rfl)
      (fun hm => absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
        (show ¬((1 : Nat) = 12) by decide))
      (by
        rw [corePhase_retire m _ _ hfl
          (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
        show retire { refillPhase m (Hw.abs σ) with inflight := none }
          (finOfBv (by decide) (σ.regs "if_dom" 2)) W = _
        rw [← hEdef, hred, if_pos hcovS, hspecA, hspecA])
      (fun x => by
        show Hw.absDom ((Act.seq (.write 1 "if_v" (.lit 0))
          (Hw.pcAdvA E)).run σ ((Hw.refillAct m).run σ σ)) x = _
        rw [absDom_pcadv m hwf hfit σ hsync E x]
        rfl)
      (fun g => by
        show Hw.absGate ((Act.seq (.write 1 "if_v" (.lit 0))
          (Hw.pcAdvA E)).run σ ((Hw.refillAct m).run σ σ)) g = _
        rw [absGate_pcadv m hwf hfit σ hsync E g]
        rfl)
      (fun x => by
        show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x).caps
          = _
        by_cases hx : x = E
        · subst hx
          rw [Loom.Fun.update_same]
          show ((refillPhase m (Hw.abs σ)).doms E).caps = _
          rw [refillPhase_caps]
        · rw [Loom.Fun.update_ne _ _ _ _ hx, refillPhase_caps])
      (fun x => by
        show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _)
          x).slotGen = _
        by_cases hx : x = E
        · subst hx
          rw [Loom.Fun.update_same]
          show ((refillPhase m (Hw.abs σ)).doms E).slotGen = _
          rw [refillPhase_slotGen]
        · rw [Loom.Fun.update_ne _ _ _ _ hx, refillPhase_slotGen])
      (fun x => by
        show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _)
          x).regions = _
        by_cases hx : x = E
        · subst hx
          rw [Loom.Fun.update_same]
          show ((refillPhase m (Hw.abs σ)).doms E).regions = _
          rw [refillPhase_regions]
        · rw [Loom.Fun.update_ne _ _ _ _ hx, refillPhase_regions])
      (by
        show (refillPhase m (Hw.abs σ)).mover = _
        rw [refillPhase_mover]
        rfl)
      (fun b => by
        rw [coreAct_run_retire_eq m σ _ hifv hcl,
          retireAct_run_mems σ _ b.toNat 32]
        show (if (((List.finRange numDomains).foldr
            (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
              let (en_d, ad_d, da_d) := Hw.retireMemFor d
              let g := Expr.and (Hw.ifDomIs d) en_d
              (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
            ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
              (.lit 0 : Expr 32))).1).eval σ = 1#1
          then (Act.memWrite 12 32 "mem" 0
            ((List.finRange numDomains).foldr
              (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
                let (en_d, ad_d, da_d) := Hw.retireMemFor d
                let g := Expr.and (Hw.ifDomIs d) en_d
                (.or g acc'.1, .mux g ad_d acc'.2.1,
                  .mux g da_d acc'.2.2))
              ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
                (.lit 0 : Expr 32))).2.1
            ((List.finRange numDomains).foldr
              (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
                let (en_d, ad_d, da_d) := Hw.retireMemFor d
                let g := Expr.and (Hw.ifDomIs d) en_d
                (.or g acc'.1, .mux g ad_d acc'.2.1,
                  .mux g da_d acc'.2.2))
              ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
                (.lit 0 : Expr 32))).2.2).run σ ((Hw.refillAct m).run σ σ)
          else ((Hw.refillAct m).run σ σ)).mems "mem" b.toNat 32 = _
        rw [if_pos (by rw [hswcomm.1]; exact hcov)]
        show (MemEnv.set ((Hw.refillAct m).run σ σ).mems "mem"
          ((((List.finRange numDomains).foldr
            (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
              let (en_d, ad_d, da_d) := Hw.retireMemFor d
              let g := Expr.and (Hw.ifDomIs d) en_d
              (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
            ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
              (.lit 0 : Expr 32))).2.1).eval σ).toNat
          ((((List.finRange numDomains).foldr
            (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
              let (en_d, ad_d, da_d) := Hw.retireMemFor d
              let g := Expr.and (Hw.ifDomIs d) en_d
              (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
            ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
              (.lit 0 : Expr 32))).2.2).eval σ)) "mem" b.toNat 32 = _
        rw [(hswcomm.2 hcov).1, (hswcomm.2 hcov).2]
        show (if ("mem" = "mem" ∧ b.toNat
            = (((swC E).memAddr).eval σ).toNat)
          then (if h : (32 : Nat) = 32
            then h ▸ ((swC E).memData).eval σ
            else ((Hw.refillAct m).run σ σ).mems "mem" b.toNat 32)
          else ((Hw.refillAct m).run σ σ).mems "mem" b.toNat 32) = _
        show _ = Loom.Fun.update
          (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
            (fun ds => { ds with pc := ds.pc + 1 })).mem
          (effAddr (((Hw.abs σ).doms E).reg (operandsOf W).rs1)
            (operandsOf W).imm)
          (((Hw.abs σ).doms E).reg (operandsOf W).rs2) b
        unfold Loom.Fun.update
        by_cases hb : b = (Hw.field
            (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ
        · rw [if_pos ⟨rfl, by rw [hb]; rfl⟩, dif_pos rfl,
            if_pos (by rw [hb, haddr])]
          show (Hw.readReg E Hw.rs2E).eval σ = _
          rw [hR2]
        · rw [if_neg (fun hc => hb (BitVec.eq_of_toNat_eq hc.2)),
            if_neg (fun hc => hb (by rw [hc, ← haddr]))]
          rw [refill_pres_mem m σ "mem" b.toNat 32]
          rfl)
      (fun sc => by
        rw [swFold_store σ E hret hifsel hifexcl hswsel hcov
          (List.finRange numDomains) sc (List.mem_finRange E)
          (List.nodup_finRange _)]
        show _ = Loom.Fun.update
          (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
            (fun ds => { ds with pc := ds.pc + 1 })).mem
          (effAddr (((Hw.abs σ).doms E).reg (operandsOf W).rs1)
            (operandsOf W).imm)
          (((Hw.abs σ).doms E).reg (operandsOf W).rs2) (sc.eval σ)
        unfold Loom.Fun.update
        by_cases heq : (Hw.field
            (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ = sc.eval σ
        · rw [if_pos heq, if_pos (by rw [← heq, haddr])]
          exact hR2
        · rw [if_neg heq, if_neg (fun hc => heq (by rw [haddr, ← hc]))]
          rfl)
      (by
        show (refillPhase m (Hw.abs σ)).cycle = _
        rfl)
      rfl
  · -- authority fault
    have hcovS : ¬((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).domCovers E (effAddr (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ⟨false, true, false⟩ = true) := by
      rw [hspecA, spec_covers_bridge]
      intro hc
      apply hcov
      rw [show ((Hw.domCoversE E
        (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)
        ⟨false, true, false⟩).eval σ = 1#1) ↔ _ from domCoversE_eval σ E _ _]
      rwa [haddr]
    refine square_retire_fault_of m hwf hfit σ hsync hifv hcl hin
      (fun d sc => by
        by_cases hd : d = E
        · subst hd
          exact andAll_zero_of_mem σ
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
            hcov
        · exact andAll_zero_of_mem σ
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            (hifexcl d hd))
      (fun c r => andAll_zero_of_mem σ
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..)))
        (isMn_ne_of_opc σ "map" 10#6 hopc (by decide +kernel)))
      (fun c r => andAll_zero_of_mem σ
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..)))
        (isMn_ne_of_opc σ "unmap" 10#6 hopc (by decide +kernel)))
      (fun ad => by
        rw [coreAct_run_retire_eq m σ _ hifv hcl,
          retireAct_run_mems σ _ ad 32]
        show (if (((List.finRange numDomains).foldr
            (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
              let (en_d, ad_d, da_d) := Hw.retireMemFor d
              let g := Expr.and (Hw.ifDomIs d) en_d
              (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
            ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
              (.lit 0 : Expr 32))).1).eval σ = 1#1
          then _ else ((Hw.refillAct m).run σ σ)).mems "mem" ad 32 = _
        rw [if_neg (by rw [hswcomm.1]; exact hcov)]
        exact refill_pres_mem m σ "mem" ad 32)
      E rfl .memoryAuthority
      (fun acc => by
        rw [hselC acc]
        show (if (Hw.domCoversE E
            (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)
            ⟨false, true, false⟩).eval σ = 1#1 then _ else _) = _
        rw [if_neg hcov])
      (by rw [hred, if_neg hcovS])

end Machines.Lnp64u.Theorems.RMC

