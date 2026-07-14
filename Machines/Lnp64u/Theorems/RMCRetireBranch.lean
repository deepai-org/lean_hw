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

/-- The `jalr` arm: opcode 13 — link `rd := pc + 1`, jump
`pc := (rs1 + sext imm) mod 4096`. -/
theorem square_retire_jalr (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 13#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (13#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (13#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  have hselC := retireFor_sel_of_opc σ E "jalr" 13#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨.seq (Hw.writeReg E Hw.rdE (.zext (.add (Hw.rPc E) (.lit 1)) 32))
      (.write 12 (Hw.dpc E)
        (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)),
      .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))))))))))))))
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hred : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).setDom E (fun ds => ds.setReg (operandsOf W).rd (((({ refillPhase m (Hw.abs σ) with inflight := none }).doms E).pc + 1).setWidth 32))).setDom E (fun ds => { ds with pc := effAddr (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg (operandsOf W).rs1) (operandsOf W).imm })) := by
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl
  refine square_retire_domShape m hwf hfit σ hsync hifv hcl 13#6 hopc
    (by decide +kernel) E rfl
    (.seq (Hw.writeReg E Hw.rdE (.zext (.add (Hw.rPc E) (.lit 1)) 32))
      (.write 12 (Hw.dpc E)
        (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)))
    (fun q hq => hq)
    hselC
    (fun ds => { ({ ds with pc := ds.pc + 1 }).setReg (operandsOf W).rd ((σ.regs (Hw.dpc E) 12 + 1).setWidth 32) with pc := effAddr (((Hw.abs σ).doms E).reg (operandsOf W).rs1) (operandsOf W).imm })
    (fun ds => setReg_caps _ _ _)
    (fun ds => setReg_slotGen _ _ _)
    (fun ds => setReg_lineage _ _ _)
    (fun ds => setReg_regions _ _ _)
    (fun ds => setReg_run _ _ _)
    (fun ds => setReg_serving _ _ _)
    (fun ds => setReg_cause _ _ _)
    (fun ds => setReg_budget _ _ _)
    (fun ds => setReg_maxDonation _ _ _)
    ?_ ?_ ?_
  · -- the register file: link write through the jump write
    intro r
    rw [show ((Act.seq (.write 1 "if_v" (.lit 0))
        (Act.seq (Hw.writeReg E Hw.rdE (.zext (.add (Hw.rPc E) (.lit 1)) 32))
          (Act.write 12 (Hw.dpc E)
            (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)))).run σ
          ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32
        = ((Hw.writeReg E Hw.rdE (.zext (.add (Hw.rPc E) (.lit 1)) 32)).run σ
            ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ))).regs (Hw.dreg E r) 32 from
      frame (show (Hw.dreg E r, 32) ∉ (Act.write 12 (Hw.dpc E)
          (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12)).regWrites
        from by
        intro hm
        exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
          (show ¬((32 : Nat) = 12) by decide)) σ _]
    show _ = (({ Hw.absDom ((Hw.refillAct m).run σ σ) E with
        pc := (Hw.absDom ((Hw.refillAct m).run σ σ) E).pc + 1 }).setReg
        (operandsOf W).rd ((σ.regs (Hw.dpc E) 12 + 1).setWidth 32)).regs r
    rw [setReg_regs]
    have hifvframe :
        ((Act.write 1 "if_v" (.lit 0)).run σ
          ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32
          = ((Hw.refillAct m).run σ σ).regs (Hw.dreg E r) 32 :=
      frame (by
        intro hm
        exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
          (show ¬((32 : Nat) = 1) by decide)) σ _
    by_cases h0 : (operandsOf W).rd = (0 : Fin numRegs)
    · rw [if_pos h0]
      rw [writeReg_run_of_zero σ _ E Hw.rdE _ (by
        rw [show ((Hw.rdE.eval σ)).toNat = ((operandsOf W).rd : Fin numRegs).val
          from rfl, h0]
        rfl)]
      rw [hifvframe]
      rfl
    · rw [if_neg h0]
      rw [writeReg_run_of_nz σ _ E Hw.rdE _ (operandsOf W).rd rfl
        (fun hc => h0 (Fin.ext hc))]
      show (RegEnv.set _ (Hw.dreg E (operandsOf W).rd) _) (Hw.dreg E r) 32 = _
      simp only [RegEnv.set]
      by_cases hr : r = (operandsOf W).rd
      · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial]
        rfl
      · rw [if_neg (fun hc => hr (dreg_inj E r (operandsOf W).rd hc)),
          if_neg hr]
        rw [hifvframe]
        rfl
  · -- pc: the jump target
    show (RegEnv.set _ (Hw.dpc E)
      ((Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ))
      (Hw.dpc E) 12 = _
    rw [show (RegEnv.set ((Hw.writeReg E Hw.rdE
        (.zext (.add (Hw.rPc E) (.lit 1)) 32)).run σ
          ((Act.write 1 "if_v" (.lit 0)).run σ
            ((Hw.refillAct m).run σ σ))).regs (Hw.dpc E)
        ((Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ))
        (Hw.dpc E) 12
      = (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ from by
      simp [RegEnv.set]]
    show ((Hw.readReg E Hw.rs1E).eval σ + Hw.immX.eval σ).extractLsb' 0 12 = _
    rw [hR1]
    rfl
  · -- spec: fold the three setDoms and σ-quote the reads
    rw [hred, setDom_setDom, setDom_setDom, specReg_bridge, tau1_pc m σ E]

/-! ## The `halt` arm

Voluntary halt retires as `pc += 1; haltAct` against the spec's
`haltDom` — the halt bridge (`abs_haltAct`) supplies the dom/gate faces
on top of the pc-advance correspondence below. -/

/-- `absDom` after latch-clear + pc-advance is the spec's advanced
state. -/
theorem absDom_pcadv (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (E : DomainId) : ∀ x,
    Hw.absDom ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA E)).run σ
        ((Hw.refillAct m).run σ σ)) x
      = ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).doms) x := by
  intro x
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y
    rw [← habs1]
    rfl
  have hfullsub : ∀ q ∈ (Act.seq (.write 1 "if_v" (.lit 0))
      (Hw.pcAdvA E)).regWrites, q ∈ ("if_v", 1) :: domWrites E := by
    intro q hq
    rcases List.mem_cons.mp (show q ∈ ("if_v", (1 : Nat)) ::
        [(Hw.dpc E, (12 : Nat))] from hq) with rfl | h
    · exact List.mem_cons_self ..
    · rcases List.mem_singleton.mp h with rfl
      exact List.mem_cons_of_mem _ (pcadv_sub E _
        (List.mem_singleton.mpr rfl))
  by_cases hx : x = E
  · subst hx
    show _ = (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms x
      { (refillPhase m (Hw.abs σ)).doms x with
        pc := ((refillPhase m (Hw.abs σ)).doms x).pc + 1 }) x
    rw [Loom.Fun.update_same]
    have hq : ∀ q ∈ domQuietNames x,
        ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA x)).run σ
          ((Hw.refillAct m).run σ σ)).regs q.1 q.2
          = ((Hw.refillAct m).run σ σ).regs q.1 q.2 :=
      fun q hq' => frame (fun hm =>
        absurd (hfullsub q hm) (quiet_notin_dom x x q hq')) σ _
    rw [absDom_regpc x hq]
    rw [hL1 x]
    apply domainState_ext'
    · funext r
      show ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA x)).run σ
        ((Hw.refillAct m).run σ σ)).regs (Hw.dreg x r) 32 = _
      rw [dreg_frame_pcadv]
      rfl
    · show ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA x)).run σ
        ((Hw.refillAct m).run σ σ)).regs (Hw.dpc x) 12 = _
      rw [dpc_pcadv_val]
      show _ = (Hw.absDom ((Hw.refillAct m).run σ σ) x).pc + 1
      rw [show (Hw.absDom ((Hw.refillAct m).run σ σ) x).pc
          = σ.regs (Hw.dpc x) 12 from by
        show ((Hw.refillAct m).run σ σ).regs (Hw.dpc x) 12 = _
        exact refill_pres m σ (by
          intro hm
          fin_cases x <;> revert hm <;> decide +kernel)]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · show _ = (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x
    rw [Loom.Fun.update_ne _ _ _ _ hx, hL1 x]
    exact absDom_congr x (fun p hp => frame (fun hm =>
      absurd (hfullsub p hm) (read_notin_dom_ne x E hx p hp)) σ _)

/-- `absGate` after latch-clear + pc-advance is unchanged. -/
theorem absGate_pcadv (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (E : DomainId) : ∀ g,
    Hw.absGate ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA E)).run σ
        ((Hw.refillAct m).run σ σ)) g
      = (refillPhase m (Hw.abs σ)).gates g := by
  intro g
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  have hfullsub : ∀ q ∈ (Act.seq (.write 1 "if_v" (.lit 0))
      (Hw.pcAdvA E)).regWrites, q ∈ ("if_v", 1) :: domWrites E := by
    intro q hq
    rcases List.mem_cons.mp (show q ∈ ("if_v", (1 : Nat)) ::
        [(Hw.dpc E, (12 : Nat))] from hq) with rfl | h
    · exact List.mem_cons_self ..
    · rcases List.mem_singleton.mp h with rfl
      exact List.mem_cons_of_mem _ (pcadv_sub E _
        (List.mem_singleton.mpr rfl))
  rw [absGate_congr g (fun p hp => frame (fun hm =>
    absurd (hfullsub p hm) (gate_notin_dom g E p hp)) σ _)]
  rw [← habs1]
  rfl

/-- Reads the halt bridge takes from the pre-cycle state pass through the
latch clear, the pc advance, and the refill. -/
private theorem acc_read_pres (m : Manifest) (σ : Loom.Hw.St) (E : DomainId)
    (rn : String) (w : Nat)
    (h1 : ¬(rn, w) = (("if_v" : String), (1 : Nat)))
    (h2 : ¬w = 12)
    (h3 : (rn, w) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) :
    ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA E)).run σ
      ((Hw.refillAct m).run σ σ)).regs rn w = σ.regs rn w := by
  rw [frame (show (rn, w) ∉ (Act.seq (.write 1 "if_v" (.lit 0))
      (Hw.pcAdvA E)).regWrites from by
    intro hm
    rcases List.mem_cons.mp (show (rn, w) ∈ ("if_v", (1 : Nat)) ::
        [(Hw.dpc E, (12 : Nat))] from hm) with h | h
    · exact h1 h
    · exact h2 (congrArg Prod.snd (List.mem_singleton.mp h))) σ _]
  exact refill_pres m σ h3

/-- The `halt` arm: opcode 26 — voluntary terminal halt (T6 unwind if
serving). -/
theorem square_retire_halt (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 26#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (26#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (26#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  have hselC := retireFor_sel_of_opc σ E "halt" 26#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨.seq (Hw.pcAdvA E) (Hw.haltAct E 0), .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))))))))))
  have hben : ∀ mn' ∈ moverMns, (Hw.isMn mn').eval σ ≠ 1#1 :=
    fun mn' hmn' => isMn_ne_of_opc σ mn' 26#6 hopc
      ((by decide +kernel : ∀ mn' ∈ moverMns, (26#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn')
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have hspec : corePhase m (refillPhase m (Hw.abs σ))
      = (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).haltDom E 0 := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
    show retire { refillPhase m (Hw.abs σ) with inflight := none }
      (finOfBv (by decide) (σ.regs "if_dom" 2)) W = _
    rw [← hEdef]
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl
  -- the halt bridge on top of the pc-advance correspondence
  obtain ⟨hHD, hHG⟩ := abs_haltAct σ
    ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA E)).run σ
      ((Hw.refillAct m).run σ σ))
    (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 }))
    E 0
    (absDom_pcadv m hwf hfit σ hsync E)
    (fun g => by
      rw [absGate_pcadv m hwf hfit σ hsync E g]
      rfl)
    ((acc_read_pres m σ E (Hw.dsrvV E) 1
      ((by decide +kernel : ∀ e : DomainId,
        ¬((Hw.dsrvV e, (1 : Nat)) = (("if_v" : String), (1 : Nat)))) E)
      (by decide)
      ((by decide +kernel : ∀ e : DomainId, ((Hw.dsrvV e : String), (1 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) E)).symm)
    ((acc_read_pres m σ E (Hw.dsrv E) 2
      (fun hc => absurd (congrArg Prod.snd hc)
        (show ¬((2 : Nat) = 1) by decide))
      (by decide)
      ((by decide +kernel : ∀ e : DomainId, ((Hw.dsrv e : String), (2 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) E)).symm)
    (fun g => (acc_read_pres m σ E (Hw.gactV g) 1
      ((by decide +kernel : ∀ g' : GateId,
        ¬((Hw.gactV g', (1 : Nat)) = (("if_v" : String), (1 : Nat)))) g)
      (by decide)
      ((by decide +kernel : ∀ g' : GateId, ((Hw.gactV g' : String), (1 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) g)).symm)
    (fun g => (acc_read_pres m σ E (Hw.gcaller g) 2
      (fun hc => absurd (congrArg Prod.snd hc)
        (show ¬((2 : Nat) = 1) by decide))
      (by decide)
      ((by decide +kernel : ∀ g' : GateId, ((Hw.gcaller g' : String), (2 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) g)).symm)
    (fun g => (acc_read_pres m σ E (Hw.gcallerRd g) 3
      (fun hc => absurd (congrArg Prod.snd hc)
        (show ¬((3 : Nat) = 1) by decide))
      (by decide)
      ((by decide +kernel : ∀ g' : GateId,
        ((Hw.gcallerRd g' : String), (3 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) g)).symm)
  refine square_retire_benign m hwf hfit σ hsync hifv hcl hben
    (.seq (Hw.pcAdvA E) (Hw.haltAct E 0)) _
    (fun rn w => by
      rw [coreAct_run_retire_eq m σ _ hifv hcl,
        retireAct_run_regs σ _ E rfl rn w, hselC]
      rfl)
    ((by decide +kernel : ∀ e : DomainId, (("if_v" : String), (1 : Nat))
      ∉ (Act.seq (Hw.pcAdvA e) (Hw.haltAct e 0)).regWrites) E)
    hspec
    (fun x => by
      rw [show ((Act.seq (.write 1 "if_v" (.lit 0))
          (.seq (Hw.pcAdvA E) (Hw.haltAct E 0))).run σ
            ((Hw.refillAct m).run σ σ))
          = (Hw.haltAct E 0).run σ
            ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA E)).run σ
              ((Hw.refillAct m).run σ σ)) from rfl]
      exact hHD x)
    (fun g => by
      rw [show ((Act.seq (.write 1 "if_v" (.lit 0))
          (.seq (Hw.pcAdvA E) (Hw.haltAct E 0))).run σ
            ((Hw.refillAct m).run σ σ))
          = (Hw.haltAct E 0).run σ
            ((Act.seq (.write 1 "if_v" (.lit 0)) (Hw.pcAdvA E)).run σ
              ((Hw.refillAct m).run σ σ)) from rfl]
      exact hHG g)
    (fun x => by
      rw [haltDom_caps']
      by_cases hx : x = E
      · subst hx
        show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E).caps
          = _
        rw [Loom.Fun.update_same]
        show ((refillPhase m (Hw.abs σ)).doms E).caps = _
        rw [refillPhase_caps]
      · show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x).caps
          = _
        rw [Loom.Fun.update_ne _ _ _ _ hx, refillPhase_caps])
    (fun x => by
      rw [haltDom_slotGen']
      by_cases hx : x = E
      · subst hx
        show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E).slotGen
          = _
        rw [Loom.Fun.update_same]
        show ((refillPhase m (Hw.abs σ)).doms E).slotGen = _
        rw [refillPhase_slotGen]
      · show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x).slotGen
          = _
        rw [Loom.Fun.update_ne _ _ _ _ hx, refillPhase_slotGen])
    (fun x => by
      rw [haltDom_regions']
      by_cases hx : x = E
      · subst hx
        show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E).regions
          = _
        rw [Loom.Fun.update_same]
        show ((refillPhase m (Hw.abs σ)).doms E).regions = _
        rw [refillPhase_regions]
      · show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x).regions
          = _
        rw [Loom.Fun.update_ne _ _ _ _ hx, refillPhase_regions])
    (by
      rw [haltDom_mover']
      show (refillPhase m (Hw.abs σ)).mover = _
      rw [refillPhase_mover]
      rfl)
    (fun b => by
      have h := congrFun (haltDom_mem'
        (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })) E 0) b
      rw [h]
      rfl)
    (by
      rw [haltDom_cycle]
      rfl)
    (by
      rw [haltDom_inflight]
      rfl)

end Machines.Lnp64u.Theorems.RMC
