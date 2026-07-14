-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireAlu
import Machines.Lnp64u.Logic.ExecWf

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

/-! ## The retiring-fault glue

A retiring op that faults (`lw` without authority, the unreachable
decode-failure fallback) runs `haltFault` with the `pc` *not* advanced —
the spec's `haltWith` on the pre-advance state. -/

private theorem ifv_notin_domReads : ∀ (x : DomainId),
    ∀ q ∈ domReadNames x, ¬q = (("if_v" : String), (1 : Nat)) := by
  decide +kernel

private theorem ifv_notin_gateReads : ∀ (g : GateId),
    ∀ q ∈ gateReadNames g, ¬q = (("if_v" : String), (1 : Nat)) := by
  decide +kernel

/-- `absDom` after just the latch clear is the pre-advance spec state. -/
theorem absDom_ifv (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP) : ∀ x,
    Hw.absDom ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)) x
      = ({ refillPhase m (Hw.abs σ) with inflight := none }).doms x := by
  intro x
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  rw [absDom_congr x (fun p hp => frame (fun hm =>
    absurd (List.mem_singleton.mp hm) (ifv_notin_domReads x p hp)) σ _)]
  rw [← habs1]
  rfl

/-- `absGate` after just the latch clear is unchanged. -/
theorem absGate_ifv (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP) : ∀ g,
    Hw.absGate ((Act.write 1 "if_v" (.lit 0)).run σ
        ((Hw.refillAct m).run σ σ)) g
      = ({ refillPhase m (Hw.abs σ) with inflight := none }).gates g := by
  intro g
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  rw [absGate_congr g (fun p hp => frame (fun hm =>
    absurd (List.mem_singleton.mp hm) (ifv_notin_gateReads g p hp)) σ _)]
  rw [← habs1]
  rfl

/-- Reads the halt bridge takes pass through the latch clear and the
refill. -/
private theorem acc_read_pres' (m : Manifest) (σ : Loom.Hw.St)
    (rn : String) (w : Nat)
    (h1 : ¬(rn, w) = (("if_v" : String), (1 : Nat)))
    (h3 : (rn, w) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) :
    ((Act.write 1 "if_v" (.lit 0)).run σ
      ((Hw.refillAct m).run σ σ)).regs rn w = σ.regs rn w := by
  rw [frame (fun hm => absurd (List.mem_singleton.mp hm) h1) σ _]
  exact refill_pres m σ h3

set_option maxHeartbeats 6400000 in
/-- **The retiring-fault square glue.** -/
theorem square_retire_fault_of (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hin : Inert σ)
    (hswz : ∀ (d : DomainId) (srcCur' : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          srcCur']).eval σ = 0#1)
    (hmemz : ∀ ad : Nat, ((Hw.coreAct m).run σ
        ((Hw.refillAct m).run σ σ)).mems "mem" ad 32
      = σ.mems "mem" ad 32)
    (E : DomainId) (hE : E.val = (σ.regs "if_dom" 2).toNat)
    (f : Fault)
    (hcoreF : ∀ acc, (Hw.retireFor E).run σ acc
      = (Hw.haltFault E f).run σ acc)
    (hspecF : retire { refillPhase m (Hw.abs σ) with inflight := none } E
        (σ.regs "if_word" 32)
      = haltWith { refillPhase m (Hw.abs σ) with inflight := none } E f) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := σ.regs "if_word" 32
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have hdomE : (finOfBv (by decide : 2 ^ 2 = numDomains)
      (σ.regs "if_dom" 2)) = E :=
    Fin.ext hE.symm
  have hspec : corePhase m (refillPhase m (Hw.abs σ))
      = ({ refillPhase m (Hw.abs σ) with inflight := none }).haltDom E
          (BitVec.ofNat 32 f.code) := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
    show retire { refillPhase m (Hw.abs σ) with inflight := none }
      (finOfBv (by decide) (σ.regs "if_dom" 2)) (σ.regs "if_word" 32) = _
    rw [hdomE]
    exact hspecF
  obtain ⟨hHD, hHG⟩ := abs_haltAct σ
    ((Act.write 1 "if_v" (.lit 0)).run σ ((Hw.refillAct m).run σ σ))
    ({ refillPhase m (Hw.abs σ) with inflight := none })
    E (BitVec.ofNat 32 f.code)
    (absDom_ifv m hwf hfit σ hsync)
    (absGate_ifv m hwf hfit σ hsync)
    ((acc_read_pres' m σ (Hw.dsrvV E) 1
      ((by decide +kernel : ∀ e : DomainId,
        ¬((Hw.dsrvV e, (1 : Nat)) = (("if_v" : String), (1 : Nat)))) E)
      ((by decide +kernel : ∀ e : DomainId, ((Hw.dsrvV e : String), (1 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) E)).symm)
    ((acc_read_pres' m σ (Hw.dsrv E) 2
      (fun hc => absurd (congrArg Prod.snd hc)
        (show ¬((2 : Nat) = 1) by decide))
      ((by decide +kernel : ∀ e : DomainId, ((Hw.dsrv e : String), (2 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) E)).symm)
    (fun g => (acc_read_pres' m σ (Hw.gactV g) 1
      ((by decide +kernel : ∀ g' : GateId,
        ¬((Hw.gactV g', (1 : Nat)) = (("if_v" : String), (1 : Nat)))) g)
      ((by decide +kernel : ∀ g' : GateId, ((Hw.gactV g' : String), (1 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) g)).symm)
    (fun g => (acc_read_pres' m σ (Hw.gcaller g) 2
      (fun hc => absurd (congrArg Prod.snd hc)
        (show ¬((2 : Nat) = 1) by decide))
      ((by decide +kernel : ∀ g' : GateId,
        ((Hw.gcaller g' : String), (2 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) g)).symm)
    (fun g => (acc_read_pres' m σ (Hw.gcallerRd g) 3
      (fun hc => absurd (congrArg Prod.snd hc)
        (show ¬((3 : Nat) = 1) by decide))
      ((by decide +kernel : ∀ g' : GateId,
        ((Hw.gcallerRd g' : String), (3 : Nat))
        ∉ ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) g)).symm)
  refine square_retire_store m hwf hfit σ hsync hifv hcl hin
    (Hw.haltFault E f) _
    (fun rn w => by
      rw [coreAct_run_retire_eq m σ _ hifv hcl,
        retireAct_run_regs σ _ E hE rn w, hcoreF]
      rfl)
    (by
      show (("if_v" : String), (1 : Nat))
        ∉ (Hw.haltAct E (BitVec.ofNat 32 f.code)).regWrites
      rw [show (Hw.haltAct E (BitVec.ofNat 32 f.code)).regWrites
        = (Hw.haltAct E 0).regWrites from rfl]
      exact (by decide +kernel : ∀ e : DomainId, (("if_v" : String), (1 : Nat))
        ∉ (Hw.haltAct e 0).regWrites) E)
    hspec
    (fun x => hHD x)
    (fun g => hHG g)
    (fun x => by
      rw [haltDom_caps']
      show ((refillPhase m (Hw.abs σ)).doms x).caps = _
      rw [refillPhase_caps])
    (fun x => by
      rw [haltDom_slotGen']
      show ((refillPhase m (Hw.abs σ)).doms x).slotGen = _
      rw [refillPhase_slotGen])
    (fun x => by
      rw [haltDom_regions']
      show ((refillPhase m (Hw.abs σ)).doms x).regions = _
      rw [refillPhase_regions])
    (by
      rw [haltDom_mover']
      show (refillPhase m (Hw.abs σ)).mover = _
      rw [refillPhase_mover]
      rfl)
    (fun b => by
      have h := congrFun (haltDom_mem'
        ({ refillPhase m (Hw.abs σ) with inflight := none }) E
        (BitVec.ofNat 32 f.code)) b
      rw [hmemz, h]
      rfl)
    (fun sc => by
      have h := congrFun (haltDom_mem'
        ({ refillPhase m (Hw.abs σ) with inflight := none }) E
        (BitVec.ofNat 32 f.code)) (sc.eval σ)
      rw [srcWord_quiescent σ hswz sc, h]
      rfl)
    (by
      rw [haltDom_cycle]
      rfl)
    (by
      rw [haltDom_inflight])


theorem square_retire_fault (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hben : ∀ mn' ∈ moverMns, (Hw.isMn mn').eval σ ≠ 1#1)
    (E : DomainId) (hE : E.val = (σ.regs "if_dom" 2).toNat)
    (f : Fault)
    (hcoreF : ∀ acc, (Hw.retireFor E).run σ acc
      = (Hw.haltFault E f).run σ acc)
    (hspecF : retire { refillPhase m (Hw.abs σ) with inflight := none } E
        (σ.regs "if_word" 32)
      = haltWith { refillPhase m (Hw.abs σ) with inflight := none } E f) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) :=
  square_retire_fault_of m hwf hfit σ hsync hifv hcl
    (Inert.of_benign σ hben)
    (fun d sc => andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (hben "sw" (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))
    (fun ad => by
      rw [coreAct_mems_benign m σ _ hifv hcl hben]
      exact Loom.Hw.Compile.run_mems_notin "mem" _
        (by rw [refillAct_memWrites]; simp) σ σ ad 32)
    E hE f hcoreF hspecF

/-- The unreachable-but-total decode-failure fallback: both sides fault
with illegal-instruction. -/
theorem square_retire_illegal (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hdec : Loom.Isa.decode isa (σ.regs "if_word" 32) = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hknown : ∀ mn ∈ allMns, (Hw.isMn mn).eval σ ≠ 1#1 := by
    intro mn hmn h
    rw [isMn_eval] at h
    have hopc : Machines.Lnp64u.sig.opcodeOf (σ.regs "if_word" 32)
        = Hw.opcodeOf mn := h
    obtain ⟨d, hd, hop⟩ := (by decide +kernel :
      ∀ mn' ∈ allMns, ∃ d ∈ isa, d.opcode = Hw.opcodeOf mn') mn hmn
    have := (Loom.Isa.isSome_decode_iff isa (σ.regs "if_word" 32)).mpr
      ⟨d, hd, by rw [hop, hopc]⟩
    rw [hdec] at this
    exact absurd this (by simp)
  refine square_retire_fault m hwf hfit σ hsync hifv hcl
    (fun mn' hmn' => hknown mn' ((by decide : ∀ x ∈ moverMns, x ∈ allMns)
      mn' hmn'))
    E rfl .illegalInstruction
    (fun acc => retireFor_run_none σ acc E (fun p hp =>
      hknown p.1 (by
        rw [← opCircs_fst_all E]
        exact List.mem_map_of_mem hp)))
    (retire_of_decode_none _ E _ hdec)

/-! ## The `lw` arm -/

/-- Memory authority of the advanced spec state is the pre-cycle
abstraction's (regions untouched). -/
theorem spec_covers_bridge (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId) (a : Addr) (need : Perms) :
    (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E a need)
      = (Hw.abs σ).domCovers E a need := by
  have hrg : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).doms E)).regions
      = ((Hw.abs σ).doms E).regions := by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E).regions = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).regions = _
    rw [refillPhase_regions]
  rw [MachineState.domCovers, MachineState.domCovers, hrg]

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 1000000 in
/-- The `lw` arm: opcode 9 — authorized load writes `rd` and advances;
missing authority faults. -/
theorem square_retire_lw (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 9#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (9#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (9#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  have hselC := retireFor_sel_of_opc σ E "lw" 9#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨.ite (Hw.domCoversE E (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12) ⟨true, false, false⟩)
      (.seq (Hw.writeReg E Hw.rdE (.memRead 32 "mem" (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12))) (Hw.pcAdvA E))
      (Hw.haltFault E .memoryAuthority), .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have haddr : (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ
      = effAddr (((Hw.abs σ).doms E).reg (operandsOf W).rs1)
          (operandsOf W).imm := by
    show ((Hw.readReg E Hw.rs1E).eval σ + Hw.immX.eval σ).extractLsb' 0 12 = _
    rw [hR1]
    rfl
  have hben : ∀ mn' ∈ moverMns, (Hw.isMn mn').eval σ ≠ 1#1 :=
    fun mn' hmn' => isMn_ne_of_opc σ mn' 9#6 hopc
      ((by decide +kernel : ∀ mn' ∈ moverMns, (9#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn')
  have hspecA : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1 = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    specReg_bridge m σ E (operandsOf W).rs1
  have hred : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (if ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (effAddr ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ⟨true, false, false⟩ = true
         then ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).setDom E (fun ds => ds.setReg (operandsOf W).rd (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).read (effAddr ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) (operandsOf W).imm)))
         else haltWith { refillPhase m (Hw.abs σ) with inflight := none } E .memoryAuthority) := by
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    show (match ((SpecM.reg E (operandsOf W).rs1 >>= fun a =>
        SpecM.load E (effAddr a (operandsOf W).imm) >>= fun v =>
        SpecM.setReg E (operandsOf W).rd v) (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))) with
      | .ok _ σ' => σ'
      | .err e σ' => σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
      | .fault fl => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E fl) = _
    simp only [specM_bind, SpecM.reg, SpecM.load, SpecM.get, SpecM.demand,
      SpecM.setReg, SpecM.modify, specM_pure]
    by_cases hc : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (effAddr ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ⟨true, false, false⟩ = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      rfl
  by_cases hcov : (Hw.domCoversE E (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12) ⟨true, false, false⟩).eval σ = 1#1
  · -- authorized load
    have hcovS : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (effAddr ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ⟨true, false, false⟩ = true := by
      rw [hspecA, spec_covers_bridge]
      have := (domCoversE_eval σ E (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12) ⟨true, false, false⟩).mp hcov
      rwa [haddr] at this
    refine square_retire_domShape m hwf hfit σ hsync hifv hcl 9#6 hopc
      (by decide +kernel) E rfl
      (.seq (Hw.writeReg E Hw.rdE (.memRead 32 "mem" (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12))) (Hw.pcAdvA E))
      (fun q hq => hq)
      (fun acc => by
        rw [hselC acc]
        show (if (Hw.domCoversE E (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12) ⟨true, false, false⟩).eval σ = 1#1
          then _ else _) = _
        rw [if_pos hcov])
      (fun ds => ({ ds with pc := ds.pc + 1 }).setReg (operandsOf W).rd
        (σ.mems "mem" ((effAddr (((Hw.abs σ).doms E).reg (operandsOf W).rs1)
          (operandsOf W).imm)).toNat 32))
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
    · -- the register file
      intro r
      rw [show ((Act.seq (.write 1 "if_v" (.lit 0))
          (.seq (Hw.writeReg E Hw.rdE (Expr.memRead 32 "mem" (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12))) (Hw.pcAdvA E))).run σ
            ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32
          = ((Hw.writeReg E Hw.rdE (Expr.memRead 32 "mem" (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12))).run σ
              ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ))).regs (Hw.dreg E r) 32 from
        frame (show (Hw.dreg E r, 32) ∉ (Hw.pcAdvA E).regWrites from by
          intro hm
          exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
            (show ¬((32 : Nat) = 12) by decide)) σ _]
      show _ = (({ Hw.absDom ((Hw.refillAct m).run σ σ) E with
          pc := (Hw.absDom ((Hw.refillAct m).run σ σ) E).pc + 1 }).setReg
          (operandsOf W).rd _).regs r
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
          rw [show ((Hw.rdE.eval σ)).toNat
            = ((operandsOf W).rd : Fin numRegs).val from rfl, h0]
          rfl)]
        rw [hifvframe]
        rfl
      · rw [if_neg h0]
        rw [writeReg_run_of_nz σ _ E Hw.rdE _ (operandsOf W).rd rfl
          (fun hc => h0 (Fin.ext hc))]
        show (RegEnv.set _ (Hw.dreg E (operandsOf W).rd) _)
          (Hw.dreg E r) 32 = _
        simp only [RegEnv.set]
        by_cases hr : r = (operandsOf W).rd
        · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial]
          show σ.mems "mem" (((Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12).eval σ)).toNat 32 = _
          rw [haddr]
        · rw [if_neg (fun hc => hr (dreg_inj E r (operandsOf W).rd hc)),
            if_neg hr]
          rw [hifvframe]
          rfl
    · -- pc
      show (RegEnv.set _ (Hw.dpc E)
        ((Expr.add (Hw.rPc E) (.lit 1)).eval σ)) (Hw.dpc E) 12 = _
      rw [show (RegEnv.set ((Hw.writeReg E Hw.rdE (Expr.memRead 32 "mem" (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12))).run σ
            ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ))).regs (Hw.dpc E)
          ((Expr.add (Hw.rPc E) (.lit 1)).eval σ)) (Hw.dpc E) 12
        = σ.regs (Hw.dpc E) 12 + 1 from by
        simp [RegEnv.set, Expr.eval, Hw.rPc]]
      show σ.regs (Hw.dpc E) 12 + 1
        = (({ Hw.absDom ((Hw.refillAct m).run σ σ) E with
            pc := (Hw.absDom ((Hw.refillAct m).run σ σ) E).pc + 1 }).setReg
            (operandsOf W).rd _).pc
      rw [setReg_pc]
      show σ.regs (Hw.dpc E) 12 + 1
        = ((Hw.refillAct m).run σ σ).regs (Hw.dpc E) 12 + 1
      rw [refill_pres m σ ((by decide +kernel : ∀ e : DomainId,
        ((Hw.dpc e : String), (12 : Nat)) ∉
        ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
          ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
          ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) E)]
    · -- spec
      rw [hred, if_pos hcovS, setDom_setDom, hspecA]
      rfl
  · -- authority fault
    have hcovS : ¬(((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).domCovers E (effAddr ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1) (operandsOf W).imm) ⟨true, false, false⟩ = true) := by
      rw [hspecA, spec_covers_bridge]
      intro hc
      apply hcov
      rw [show ((Hw.domCoversE E (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12) ⟨true, false, false⟩).eval σ = 1#1)
        ↔ _ from domCoversE_eval σ E _ _]
      rwa [haddr]
    refine square_retire_fault m hwf hfit σ hsync hifv hcl hben E rfl
      .memoryAuthority
      (fun acc => by
        rw [hselC acc]
        show (if (Hw.domCoversE E (Hw.field (.add (Hw.readReg E Hw.rs1E) Hw.immX) 0 12) ⟨true, false, false⟩).eval σ = 1#1
          then _ else _) = _
        rw [if_neg hcov])
      (by rw [hred, if_neg hcovS])

/-! ## The `yield` arm

`yield` zeroes the caller's remaining budget — the one benign op whose
footprint reaches past the file/`pc` into `dbudget`. -/

/-- The quiet names with the budget carved out. -/
def domQuietNamesY (x : DomainId) : List (String × Nat) :=
  ((List.finRange numSlots).flatMap fun s =>
      [(Hw.dcapV x s, 1), (Hw.dcapKind x s, 32), (Hw.dcapLinV x s, 1),
       (Hw.dcapLin x s, 4), (Hw.dgen x s, 8)])
  ++ ((List.finRange numLineage).flatMap fun l =>
      [(Hw.dcellV x l, 1), (Hw.dcellPar x l, 14)])
  ++ ((List.finRange numRegions).flatMap fun r =>
      [(Hw.drgnV x r, 1), (Hw.drgn x r, 42)])
  ++ [(Hw.drun x, 2), (Hw.drunG x, 2), (Hw.dsrvV x, 1), (Hw.dsrv x, 2),
      (Hw.dcause x, 32), (Hw.dmaxdon x, 32)]

/-- The `yield` payload with the latch clear in front. -/
def yieldFull (e : DomainId) : Act :=
  .seq (.write 1 "if_v" (.lit 0))
    (Hw.seqAll [.write 32 (Hw.dbudget e) (.lit 0),
      Hw.writeReg e Hw.rdE (.lit 0), Hw.pcAdvA e])

private theorem yieldFull_writes (e : DomainId) :
    (yieldFull e).regWrites
      = [("if_v", 1), (Hw.dbudget e, 32), (Hw.dreg e 1, 32),
         (Hw.dreg e 2, 32), (Hw.dreg e 3, 32), (Hw.dreg e 4, 32),
         (Hw.dreg e 5, 32), (Hw.dreg e 6, 32), (Hw.dreg e 7, 32),
         (Hw.dpc e, 12)] := rfl

private theorem quietY_notin (x e : DomainId) :
    ∀ q ∈ domQuietNamesY x, q ∉ (yieldFull e).regWrites := by
  rw [yieldFull_writes]
  fin_cases x <;> fin_cases e <;> decide +kernel

private theorem read_notin_yield_ne (x e : DomainId) (hne : x ≠ e) :
    ∀ q ∈ domReadNames x, q ∉ (yieldFull e).regWrites := by
  rw [yieldFull_writes]
  fin_cases x <;> fin_cases e <;>
    first
      | exact absurd rfl hne
      | decide +kernel

private theorem gate_notin_yield (g : GateId) (e : DomainId) :
    ∀ q ∈ gateReadNames g, q ∉ (yieldFull e).regWrites := by
  rw [yieldFull_writes]
  fin_cases g <;> fin_cases e <;> decide +kernel

/-- The regs/pc/budget face of `absDom` (quiet elsewhere). -/
theorem absDom_regpcbud {S1 S2 : Loom.Hw.St} (e : DomainId)
    (hq : ∀ q ∈ domQuietNamesY e, S2.regs q.1 q.2 = S1.regs q.1 q.2) :
    Hw.absDom S2 e =
      { Hw.absDom S1 e with
        regs := fun r => S2.regs (Hw.dreg e r) 32
        pc := S2.regs (Hw.dpc e) 12
        budget := (S2.regs (Hw.dbudget e) 32).toNat } := by
  have hs : ∀ (s : Slot) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.dcapV e s, 1), (Hw.dcapKind e s, 32),
        (Hw.dcapLinV e s, 1), (Hw.dcapLin e s, 4), (Hw.dgen e s, 8)] →
      S2.regs rn w = S1.regs rn w := fun s rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨s, List.mem_finRange s, hp⟩))))
  have hl : ∀ (l : Fin numLineage) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.dcellV e l, 1), (Hw.dcellPar e l, 14)] →
      S2.regs rn w = S1.regs rn w := fun l rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨l, List.mem_finRange l, hp⟩))))
  have hr : ∀ (r : RegionId) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.drgnV e r, 1), (Hw.drgn e r, 42)] →
      S2.regs rn w = S1.regs rn w := fun r rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨r, List.mem_finRange r, hp⟩)))
  have ht : ∀ (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.drun e, 2), (Hw.drunG e, 2), (Hw.dsrvV e, 1),
        (Hw.dsrv e, 2), (Hw.dcause e, 32), (Hw.dmaxdon e, 32)] →
      S2.regs rn w = S1.regs rn w := fun rn w hp =>
    hq (rn, w) (List.mem_append_right _ hp)
  apply domainState_ext'
  · rfl
  · rfl
  · show (Hw.absDom S2 e).caps = (Hw.absDom S1 e).caps
    funext s
    show (if S2.regs (Hw.dcapV e s) 1 = 1 then _ else none)
      = (if S1.regs (Hw.dcapV e s) 1 = 1 then _ else none)
    rw [hs s (Hw.dcapV e s) 1 (by simp), hs s (Hw.dcapKind e s) 32 (by simp),
      hs s (Hw.dcapLinV e s) 1 (by simp), hs s (Hw.dcapLin e s) 4 (by simp)]
  · show (Hw.absDom S2 e).slotGen = (Hw.absDom S1 e).slotGen
    funext s
    show S2.regs (Hw.dgen e s) 8 = S1.regs (Hw.dgen e s) 8
    rw [hs s (Hw.dgen e s) 8 (by simp)]
  · show (Hw.absDom S2 e).lineage = (Hw.absDom S1 e).lineage
    funext l
    show (if S2.regs (Hw.dcellV e l) 1 = 1 then _ else none)
      = (if S1.regs (Hw.dcellV e l) 1 = 1 then _ else none)
    rw [hl l (Hw.dcellV e l) 1 (by simp), hl l (Hw.dcellPar e l) 14 (by simp)]
  · show (Hw.absDom S2 e).regions = (Hw.absDom S1 e).regions
    funext r
    show (if S2.regs (Hw.drgnV e r) 1 = 1 then _ else none)
      = (if S1.regs (Hw.drgnV e r) 1 = 1 then _ else none)
    rw [hr r (Hw.drgnV e r) 1 (by simp), hr r (Hw.drgn e r) 42 (by simp)]
  · show decRun (S2.regs (Hw.drun e) 2) (S2.regs (Hw.drunG e) 2)
      = decRun (S1.regs (Hw.drun e) 2) (S1.regs (Hw.drunG e) 2)
    rw [ht (Hw.drun e) 2 (by simp), ht (Hw.drunG e) 2 (by simp)]
  · show (if S2.regs (Hw.dsrvV e) 1 = 1 then _ else none)
      = (if S1.regs (Hw.dsrvV e) 1 = 1 then _ else none)
    rw [ht (Hw.dsrvV e) 1 (by simp), ht (Hw.dsrv e) 2 (by simp)]
  · show S2.regs (Hw.dcause e) 32 = S1.regs (Hw.dcause e) 32
    rw [ht (Hw.dcause e) 32 (by simp)]
  · rfl
  · show (S2.regs (Hw.dmaxdon e) 32).toNat = (S1.regs (Hw.dmaxdon e) 32).toNat
    rw [ht (Hw.dmaxdon e) 32 (by simp)]

set_option maxHeartbeats 12800000 in
/-- The `yield` arm: opcode 25. -/
theorem square_retire_yield (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 25#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (25#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (25#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  have hselC := retireFor_sel_of_opc σ E "yield" 25#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨Hw.seqAll [.write 32 (Hw.dbudget E) (.lit 0),
      Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E], .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))
  have hben : ∀ mn' ∈ moverMns, (Hw.isMn mn').eval σ ≠ 1#1 :=
    fun mn' hmn' => isMn_ne_of_opc σ mn' 25#6 hopc
      ((by decide +kernel : ∀ mn' ∈ moverMns, (25#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn')
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y
    rw [← habs1]
    rfl
  have hspec : corePhase m (refillPhase m (Hw.abs σ))
      = ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => ({ { ds with pc := ds.pc + 1 } with
            budget := 0 }).setReg (operandsOf W).rd 0) := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
    show retire { refillPhase m (Hw.abs σ) with inflight := none }
      (finOfBv (by decide) (σ.regs "if_dom" 2)) W = _
    rw [← hEdef]
    have h1 : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
        = (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
            (fun ds => { ds with pc := ds.pc + 1 })).setDom E
            (fun ds => { ds with budget := 0 })).setDom E
            (fun ds => ds.setReg (operandsOf W).rd 0)) := by
      rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
      rfl
    rw [h1, setDom_setDom, setDom_setDom]
  have hτ2doms : ∀ x, (({ refillPhase m (Hw.abs σ) with inflight := none
      }).setDom E (fun ds => ({ { ds with pc := ds.pc + 1 } with
        budget := 0 }).setReg (operandsOf W).rd 0)).doms x
      = if x = E
        then ({ { (refillPhase m (Hw.abs σ)).doms E with
            pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 } with
            budget := 0 }).setReg (operandsOf W).rd 0
        else (refillPhase m (Hw.abs σ)).doms x := by
    intro x
    show (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x = _
    by_cases hx : x = E
    · subst hx
      rw [Loom.Fun.update_same, if_pos rfl]
    · rw [Loom.Fun.update_ne _ _ _ _ hx, if_neg hx]
  refine square_retire_benign m hwf hfit σ hsync hifv hcl hben
    (Hw.seqAll [.write 32 (Hw.dbudget E) (.lit 0),
      Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E]) _
    (fun rn w => by
      rw [coreAct_run_retire_eq m σ _ hifv hcl,
        retireAct_run_regs σ _ E rfl rn w, hselC]
      rfl)
    ((by decide +kernel : ∀ e : DomainId, (("if_v" : String), (1 : Nat))
      ∉ (Hw.seqAll [.write 32 (Hw.dbudget e) (.lit 0),
        Hw.writeReg e Hw.rdE (.lit 0), Hw.pcAdvA e]).regWrites) E)
    hspec ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- absDom faces
    intro x
    rw [hτ2doms x]
    by_cases hx : x = E
    · rw [if_pos hx]
      subst hx
      show Hw.absDom ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)) E = _
      have hq : ∀ q ∈ domQuietNamesY E,
          ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)).regs q.1 q.2
            = ((Hw.refillAct m).run σ σ).regs q.1 q.2 :=
        fun q hq' => frame (quietY_notin E E q hq') σ _
      rw [absDom_regpcbud E hq]
      rw [show (refillPhase m (Hw.abs σ)).doms E
        = Hw.absDom ((Hw.refillAct m).run σ σ) E from hL1 E]
      apply domainState_ext'
      · funext r
        show ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)).regs
          (Hw.dreg E r) 32 = _
        rw [show ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.dreg E r) 32
            = ((Hw.writeReg E Hw.rdE (.lit 0)).run σ
                ((Act.write 32 (Hw.dbudget E) (.lit 0)).run σ
                  ((Act.write 1 "if_v" (.lit 0)).run σ
                    ((Hw.refillAct m).run σ σ)))).regs (Hw.dreg E r) 32 from
          frame (show (Hw.dreg E r, 32)
              ∉ (Act.seq (Hw.pcAdvA E) Act.skip).regWrites from by
            intro hm
            rcases List.mem_append.mp (show (Hw.dreg E r, (32 : Nat)) ∈
                [(Hw.dpc E, (12 : Nat))] ++ [] from hm) with h | h
            · exact absurd (congrArg Prod.snd (List.mem_singleton.mp h))
                (show ¬((32 : Nat) = 12) by decide)
            · exact absurd h (List.not_mem_nil)) σ _]
        show _ = (({ { Hw.absDom ((Hw.refillAct m).run σ σ) E with
            pc := (Hw.absDom ((Hw.refillAct m).run σ σ) E).pc + 1 } with
            budget := 0 }).setReg (operandsOf W).rd 0).regs r
        rw [setReg_regs]
        have hbudframe :
            ((Act.write 32 (Hw.dbudget E) (.lit 0)).run σ
              ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ))).regs (Hw.dreg E r) 32
            = ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32 :=
          frame (fun hm => absurd
            (congrArg Prod.fst (List.mem_singleton.mp hm))
            ((by decide +kernel : ∀ (e : DomainId) (r' : RegId),
              ¬(Hw.dreg e r' = Hw.dbudget e)) E r)) σ _
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
          rw [hbudframe, hifvframe]
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
            rw [hbudframe, hifvframe]
            rfl
      · show ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)).regs
          (Hw.dpc E) 12 = _
        rw [show ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)).regs
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
            ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) E)]
      · rw [setReg_caps]
      · rw [setReg_slotGen]
      · rw [setReg_lineage]
      · rw [setReg_regions]
      · rw [setReg_run]
      · rw [setReg_serving]
      · rw [setReg_cause]
      · show (((yieldFull E).run σ ((Hw.refillAct m).run σ σ)).regs
          (Hw.dbudget E) 32).toNat = _
        have hbv : ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.dbudget E) 32
            = ((Act.write 32 (Hw.dbudget E) (.lit 0)).run σ
                ((Act.write 1 "if_v" (.lit 0)).run σ
                  ((Hw.refillAct m).run σ σ))).regs (Hw.dbudget E) 32 := by
          refine frame (a := Act.seq (Hw.writeReg E Hw.rdE (Expr.lit 0))
            (Act.seq (Hw.pcAdvA E) Act.skip)) ?_ σ _
          intro hm
          rcases List.mem_append.mp (show (Hw.dbudget E, (32 : Nat)) ∈
              (Hw.writeReg E Hw.rdE (Expr.lit 0)).regWrites
                ++ ((Hw.pcAdvA E).regWrites ++ []) from hm) with h | h
          · exact absurd h ((by decide +kernel : ∀ e : DomainId,
              ((Hw.dbudget e : String), (32 : Nat)) ∉
                (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) E)
          · rcases List.mem_append.mp h with h' | h'
            · exact absurd (congrArg Prod.snd (List.mem_singleton.mp h'))
                (show ¬((32 : Nat) = 12) by decide)
            · exact absurd h' (List.not_mem_nil)
        rw [hbv]
        rw [show ((Act.write 32 (Hw.dbudget E) (.lit 0)).run σ
            ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ))).regs (Hw.dbudget E) 32
          = (0#32 : BitVec 32) from by
          show (RegEnv.set _ (Hw.dbudget E) ((Expr.lit 0).eval σ))
            (Hw.dbudget E) 32 = _
          simp [RegEnv.set]
          rfl]
        rw [setReg_budget]
        rfl
      · rw [setReg_maxDonation]
    · rw [if_neg hx]
      show Hw.absDom ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)) x = _
      rw [hL1 x]
      exact absDom_congr x (fun p hp =>
        frame (read_notin_yield_ne x E hx p hp) σ _)
  · intro g
    show Hw.absGate ((yieldFull E).run σ ((Hw.refillAct m).run σ σ)) g = _
    rw [absGate_congr g (fun p hp =>
      frame (gate_notin_yield g E p hp) σ _)]
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
  · intro x
    rw [hτ2doms x]
    by_cases hx : x = E
    · rw [if_pos hx, setReg_regions]
      show ((refillPhase m (Hw.abs σ)).doms E).regions = _
      rw [refillPhase_regions, hx]
    · rw [if_neg hx, refillPhase_regions]
  · show (refillPhase m (Hw.abs σ)).mover = _
    rw [refillPhase_mover]
    rfl
  · intro b
    show (refillPhase m (Hw.abs σ)).mem b = _
    rfl
  · show (refillPhase m (Hw.abs σ)).cycle = _
    rfl
  · rfl

end Machines.Lnp64u.Theorems.RMC

