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

end Machines.Lnp64u.Theorems.RMC
