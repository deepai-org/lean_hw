-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireAlu

/-!
# R-MC support: the branch retirement arms

`beq`/`blt` retire as a `pc`-mux: taken writes the branch target, not
taken falls through to `pc + 1`. Both cases instantiate
`square_retire_domShape` — the arm case-splits on the (bridged) test.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 6400000
set_option maxRecDepth 200000

/-- Two same-domain `setDom`s compose. -/
theorem setDom_setDom (σ' : MachineState) (d : DomainId)
    (f g : DomainState → DomainState) :
    (σ'.setDom d f).setDom d g = σ'.setDom d (fun ds => g (f ds)) := by
  show ({ σ' with doms := _ } : MachineState) = { σ' with doms := _ }
  congr 1
  funext x
  show Loom.Fun.update (Loom.Fun.update σ'.doms d (f (σ'.doms d))) d
    (g ((Loom.Fun.update σ'.doms d (f (σ'.doms d))) d)) x
    = Loom.Fun.update σ'.doms d (g (f (σ'.doms d))) x
  rw [Loom.Fun.update_same]
  unfold Loom.Fun.update
  split <;> rfl

/-- Shared dispatch-selection bundle: the retiring op's circuit runs. -/
theorem retireFor_sel_of_opc (σ : Loom.Hw.St) (E : DomainId) (mn : String)
    (k : BitVec 6)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = k)
    (hkmn : Hw.opcodeOf mn = k)
    (hexk : ∀ mn' ∈ allMns, mn' ≠ mn → k ≠ Hw.opcodeOf mn')
    (c : Hw.OpCirc) (hmem : (mn, c) ∈ Hw.opCircs E) :
    ∀ acc, (Hw.retireFor E).run σ acc = c.act.run σ acc := by
  intro acc
  refine retireFor_run_sel σ acc E mn c hmem ?_ ?_ ?_
  · rw [isMn_eval, hopc]
    exact hkmn.symm
  · intro p hp hne
    have hmns : p.1 ∈ allMns := by
      rw [← opCircs_fst_all E]
      exact List.mem_map_of_mem hp
    exact isMn_ne_of_opc σ p.1 k hopc (hexk p.1 hmns hne)
  · exact huniq_of_nodup (by rw [opCircs_fst_all E]; exact allMns_nodup) hmem

/-- Frame: a width-32 file read passes the latch clear and a `pc` write. -/
private theorem dreg_frame_pcw (σ σ1 : Loom.Hw.St) (E : DomainId)
    (tgt : Expr 12) (r : RegId) :
    ((Act.seq (.write 1 "if_v" (.lit 0))
      (Act.write 12 (Hw.dpc E) tgt)).run σ σ1).regs (Hw.dreg E r) 32
      = σ1.regs (Hw.dreg E r) 32 := by
  refine frame ?_ σ σ1
  intro hm
  rcases List.mem_cons.mp (show (Hw.dreg E r, (32 : Nat)) ∈
      ("if_v", (1 : Nat)) :: [(Hw.dpc E, (12 : Nat))] from hm) with h | h
  · exact absurd (congrArg Prod.snd h) (show ¬((32 : Nat) = 1) by decide)
  · exact absurd (congrArg Prod.snd (List.mem_singleton.mp h))
      (show ¬((32 : Nat) = 12) by decide)

/-- The written `pc` value after the latch clear and a `pc` write. -/
private theorem dpc_write_val (σ σ1 : Loom.Hw.St) (E : DomainId)
    (tgt : Expr 12) :
    ((Act.seq (.write 1 "if_v" (.lit 0))
      (Act.write 12 (Hw.dpc E) tgt)).run σ σ1).regs (Hw.dpc E) 12
      = tgt.eval σ := by
  show (RegEnv.set _ (Hw.dpc E) (tgt.eval σ)) (Hw.dpc E) 12 = _
  simp [RegEnv.set]

/-- The branch-target footprint sits inside the domain writes. -/
private theorem pcw_sub (E : DomainId) (tgt : Expr 12) :
    ∀ q ∈ (Act.write 12 (Hw.dpc E) tgt).regWrites, q ∈ domWrites E := by
  intro q hq
  rcases List.mem_singleton.mp
    (show q ∈ [(Hw.dpc E, (12 : Nat))] from hq) with rfl
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))

/-- The fall-through footprint. -/
private theorem pcadv_sub (E : DomainId) :
    ∀ q ∈ (Hw.pcAdvA E).regWrites, q ∈ domWrites E := by
  intro q hq
  rcases List.mem_singleton.mp
    (show q ∈ [(Hw.dpc E, (12 : Nat))] from hq) with rfl
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))

private theorem dreg_frame_pcadv (σ σ1 : Loom.Hw.St) (E : DomainId)
    (r : RegId) :
    ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA E)).run σ σ1).regs
      (Hw.dreg E r) 32 = σ1.regs (Hw.dreg E r) 32 := by
  refine frame ?_ σ σ1
  intro hm
  rcases List.mem_cons.mp (show (Hw.dreg E r, (32 : Nat)) ∈
      ("if_v", (1 : Nat)) :: [(Hw.dpc E, (12 : Nat))] from hm) with h | h
  · exact absurd (congrArg Prod.snd h) (show ¬((32 : Nat) = 1) by decide)
  · exact absurd (congrArg Prod.snd (List.mem_singleton.mp h))
      (show ¬((32 : Nat) = 12) by decide)

private theorem dpc_pcadv_val (σ σ1 : Loom.Hw.St) (E : DomainId) :
    ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA E)).run σ σ1).regs
      (Hw.dpc E) 12 = σ.regs (Hw.dpc E) 12 + 1 := by
  show (RegEnv.set _ (Hw.dpc E)
    ((Expr.add (Hw.rPc E) (.lit 1)).eval σ)) (Hw.dpc E) 12 = _
  simp [RegEnv.set, Expr.eval, Hw.rPc]

/-- The spec's fall-through `pc` against the abstraction. -/
private theorem dsf_pcadv_pc (m : Manifest) (σ : Loom.Hw.St) (E : DomainId) :
    ((fun ds : DomainState => { ds with pc := ds.pc + 1 })
      (Hw.absDom ((Hw.refillAct m).run σ σ) E)).pc
      = σ.regs (Hw.dpc E) 12 + 1 := by
  show ((Hw.refillAct m).run σ σ).regs (Hw.dpc E) 12 + 1 = _
  rw [refill_pres m σ (by
    intro hm
    fin_cases E <;> revert hm <;> decide +kernel)]

/-- The pre-advance `pc` the spec's branch target quotes. -/
private theorem tau1_pc (m : Manifest) (σ : Loom.Hw.St) (E : DomainId) :
    (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc
      = σ.regs (Hw.dpc E) 12 := by
  show ((refillPhase m (Hw.abs σ)).doms E).pc = _
  rw [refillPhase_dpc]
  rfl



/-- The `beq` arm: opcode 11. -/
theorem square_retire_beq (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 11#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (11#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (11#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  have hselC := retireFor_sel_of_opc σ E "beq" 11#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨.ite (Expr.eq (Hw.readReg E Hw.rs1E) (Hw.readReg E Hw.rs2E))
      (.write 12 (Hw.dpc E) (.add (Hw.rPc E) (Hw.field Hw.immX 0 12)))
      (Hw.pcAdvA E), .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  by_cases htest : ((((Hw.abs σ).doms E).reg (operandsOf W).rs1) == (((Hw.abs σ).doms E).reg (operandsOf W).rs2)) = true
  · -- taken
    have hb : (((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) == ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2)) = true := by
      rw [specReg_bridge, specReg_bridge]
      exact htest
    have hcond : ((Expr.eq (Hw.readReg E Hw.rs1E)
        (Hw.readReg E Hw.rs2E)).eval σ) = 1#1 := by
      rw [eqE_eval, hR1, hR2]
      exact beq_iff_eq.mp htest
    have hred : retire { refillPhase m (Hw.abs σ) with inflight := none } E W = ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).setDom E (fun ds => { ds with pc := branchTarget (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc (operandsOf W).imm }) := by
      rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
      show (match (if (((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) == ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2)) = true then SpecM.updDom E (fun ds => { ds with pc := branchTarget (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc (operandsOf W).imm }) else (pure () : SpecM Unit)) (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })) with
        | .ok _ σ' => σ'
        | .err e σ' => σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault f => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
      rw [hb, if_pos rfl]
      rfl
    refine square_retire_domShape m hwf hfit σ hsync hifv hcl 11#6 hopc
      (by decide +kernel) E rfl
      (.write 12 (Hw.dpc E) (.add (Hw.rPc E) (Hw.field Hw.immX 0 12)))
      (pcw_sub E _)
      (fun acc => by
        rw [hselC acc]
        show (if (Expr.eq (Hw.readReg E Hw.rs1E)
          (Hw.readReg E Hw.rs2E)).eval σ = 1#1 then _ else _) = _
        rw [if_pos hcond])
      (fun ds => { ds with pc := branchTarget (σ.regs (Hw.dpc E) 12) (operandsOf W).imm })
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)
      ?_ ?_ ?_
    · intro r
      rw [dreg_frame_pcw]
      rfl
    · rw [dpc_write_val]
      rfl
    · rw [hred, setDom_setDom, tau1_pc m σ E]
  · -- not taken
    have hb : (((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) == ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2)) = false := by
      rw [specReg_bridge, specReg_bridge]
      exact Bool.eq_false_iff.mpr htest
    have hcond : ¬((Expr.eq (Hw.readReg E Hw.rs1E)
        (Hw.readReg E Hw.rs2E)).eval σ) = 1#1 := by
      rw [eqE_eval, hR1, hR2]
      exact fun hc => htest (beq_iff_eq.mpr hc)
    have hred : retire { refillPhase m (Hw.abs σ) with inflight := none } E W = (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })) := by
      rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
      show (match (if (((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) == ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2)) = true then SpecM.updDom E (fun ds => { ds with pc := branchTarget (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc (operandsOf W).imm }) else (pure () : SpecM Unit)) (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })) with
        | .ok _ σ' => σ'
        | .err e σ' => σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault f => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
      rw [hb]
      rw [if_neg (by decide : ¬((false : Bool) = true))]
    refine square_retire_domShape m hwf hfit σ hsync hifv hcl 11#6 hopc
      (by decide +kernel) E rfl
      (Hw.pcAdvA E)
      (pcadv_sub E)
      (fun acc => by
        rw [hselC acc]
        show (if (Expr.eq (Hw.readReg E Hw.rs1E)
          (Hw.readReg E Hw.rs2E)).eval σ = 1#1 then _ else _) = _
        rw [if_neg hcond])
      (fun ds => { ds with pc := ds.pc + 1 })
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)
      ?_ ?_ ?_
    · intro r
      rw [dreg_frame_pcadv]
      rfl
    · rw [dpc_pcadv_val]
      exact (dsf_pcadv_pc m σ E).symm
    · exact hred

/-- The `blt` arm: opcode 12. -/
theorem square_retire_blt (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 12#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (12#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (12#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  have hselC := retireFor_sel_of_opc σ E "blt" 12#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨.ite (Expr.slt (Hw.readReg E Hw.rs1E) (Hw.readReg E Hw.rs2E))
      (.write 12 (Hw.dpc E) (.add (Hw.rPc E) (Hw.field Hw.immX 0 12)))
      (Hw.pcAdvA E), .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  by_cases htest : (BitVec.slt (((Hw.abs σ).doms E).reg (operandsOf W).rs1) (((Hw.abs σ).doms E).reg (operandsOf W).rs2)) = true
  · -- taken
    have hb : (BitVec.slt ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2)) = true := by
      rw [specReg_bridge, specReg_bridge]
      exact htest
    have hcond : ((Expr.slt (Hw.readReg E Hw.rs1E)
        (Hw.readReg E Hw.rs2E)).eval σ) = 1#1 := by
      show (if ((Hw.readReg E Hw.rs1E).eval σ).slt ((Hw.readReg E Hw.rs2E).eval σ)
          then (1#1 : BitVec 1) else 0#1) = 1#1
      rw [hR1, hR2, if_pos htest]
    have hred : retire { refillPhase m (Hw.abs σ) with inflight := none } E W = ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).setDom E (fun ds => { ds with pc := branchTarget (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc (operandsOf W).imm }) := by
      rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
      show (match (if (BitVec.slt ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2)) = true then SpecM.updDom E (fun ds => { ds with pc := branchTarget (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc (operandsOf W).imm }) else (pure () : SpecM Unit)) (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })) with
        | .ok _ σ' => σ'
        | .err e σ' => σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault f => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
      rw [hb, if_pos rfl]
      rfl
    refine square_retire_domShape m hwf hfit σ hsync hifv hcl 12#6 hopc
      (by decide +kernel) E rfl
      (.write 12 (Hw.dpc E) (.add (Hw.rPc E) (Hw.field Hw.immX 0 12)))
      (pcw_sub E _)
      (fun acc => by
        rw [hselC acc]
        show (if (Expr.slt (Hw.readReg E Hw.rs1E)
          (Hw.readReg E Hw.rs2E)).eval σ = 1#1 then _ else _) = _
        rw [if_pos hcond])
      (fun ds => { ds with pc := branchTarget (σ.regs (Hw.dpc E) 12) (operandsOf W).imm })
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)
      ?_ ?_ ?_
    · intro r
      rw [dreg_frame_pcw]
      rfl
    · rw [dpc_write_val]
      rfl
    · rw [hred, setDom_setDom, tau1_pc m σ E]
  · -- not taken
    have hb : (BitVec.slt ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2)) = false := by
      rw [specReg_bridge, specReg_bridge]
      exact Bool.eq_false_iff.mpr htest
    have hcond : ¬((Expr.slt (Hw.readReg E Hw.rs1E)
        (Hw.readReg E Hw.rs2E)).eval σ) = 1#1 := by
      show ¬((if ((Hw.readReg E Hw.rs1E).eval σ).slt ((Hw.readReg E Hw.rs2E).eval σ)
          then (1#1 : BitVec 1) else 0#1) = 1#1)
      rw [hR1, hR2, if_neg (fun hc => htest hc)]
      decide
    have hred : retire { refillPhase m (Hw.abs σ) with inflight := none } E W = (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })) := by
      rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
      show (match (if (BitVec.slt ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2)) = true then SpecM.updDom E (fun ds => { ds with pc := branchTarget (({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc (operandsOf W).imm }) else (pure () : SpecM Unit)) (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })) with
        | .ok _ σ' => σ'
        | .err e σ' => σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault f => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E f) = _
      rw [hb]
      rw [if_neg (by decide : ¬((false : Bool) = true))]
    refine square_retire_domShape m hwf hfit σ hsync hifv hcl 12#6 hopc
      (by decide +kernel) E rfl
      (Hw.pcAdvA E)
      (pcadv_sub E)
      (fun acc => by
        rw [hselC acc]
        show (if (Expr.slt (Hw.readReg E Hw.rs1E)
          (Hw.readReg E Hw.rs2E)).eval σ = 1#1 then _ else _) = _
        rw [if_neg hcond])
      (fun ds => { ds with pc := ds.pc + 1 })
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)
      ?_ ?_ ?_
    · intro r
      rw [dreg_frame_pcadv]
      rfl
    · rw [dpc_pcadv_val]
      exact (dsf_pcadv_pc m σ E).symm
    · exact hred

end Machines.Lnp64u.Theorems.RMC
