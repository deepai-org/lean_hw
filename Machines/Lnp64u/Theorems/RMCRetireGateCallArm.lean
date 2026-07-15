-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCall

/-!
# R-MC retirement: full gate_call arm

Top-level decode and specification reduction for the `gate_call` retirement
square.  The semantic, transfer, status-memory, and Mover bridges live in
`RMCRetireGateCall`; this file assembles them against the core cycle.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- The system table's opcode-22 entry is the named gate-call semantics used
by the proof-side bridge library. -/
theorem gateCall_system_exec :
    (Machines.Lnp64u.Isa.system.get ⟨6, by decide⟩).sem.exec =
      Machines.Lnp64u.Isa.Wip.gateCallExec := by
  rfl

/-- Exact retirement reduction for a decoded gate call: architectural PC
advance followed by the named gate-call body and the standard outcome
triage. -/
theorem retire_gateCall_exec (τ : MachineState) (E : DomainId)
    (W : Loom.Word32)
    (hdec : Loom.Isa.decode isa W =
      isa.find? (fun d => d.opcode == (22#6 : BitVec 6))) :
    retire τ E W =
      let c : Ctx := { d := E, pc := (τ.doms E).pc, op := operandsOf W }
      let τ0 := τ.setDom E fun ds => { ds with pc := ds.pc + 1 }
      match Machines.Lnp64u.Isa.Wip.gateCallExec c τ0 with
      | .ok _ τ' => τ'
      | .err e τ' =>
          τ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
      | .fault f => haltWith τ E f := by
  have hfind : isa.find? (fun d => d.opcode == (22#6 : BitVec 6)) =
      some (Machines.Lnp64u.Isa.system.get ⟨6, by decide⟩) := by
    rfl
  rw [retire_of_decode_some _ E W _ (hdec.trans hfind)]
  rw [gateCall_system_exec]
  rfl

/-- Opcode 22 selects the gate-call circuit's complete memory-port triple
from the domain and opcode folds. -/
theorem retireMem_gateCall_sel (σ : Loom.Hw.St) (E : DomainId)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6) :
    ((((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))).1).eval σ
      = (Hw.callCirc E).memEn.eval σ)
    ∧ ((Hw.callCirc E).memEn.eval σ = 1#1 →
        ((((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
            (.lit 0 : Expr 32))).2.1).eval σ = (Hw.callCirc E).memAddr.eval σ)
        ∧ ((((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
            (.lit 0 : Expr 32))).2.2).eval σ = (Hw.callCirc E).memData.eval σ)) := by
  have hmn : (Hw.isMn "gate_call").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "gate_call" = 22#6).symm
  have hmem : ("gate_call", Hw.callCirc E) ∈ Hw.opCircs E := by
    simp [Hw.opCircs]
  have hnd : ((Hw.opCircs E).map Prod.fst).Nodup := by
    rw [opCircs_fst_all E]
    exact allMns_nodup
  have hq : ∀ p ∈ Hw.opCircs E, p.1 ≠ "gate_call" →
      (Hw.isMn p.1).eval σ = 0#1 ∨ isLit0 p.2.memEn = true := by
    intro p hp hne
    left
    exact bv1_ne_one.mp (isMn_ne_of_opc σ p.1 22#6 hopc
      ((by decide +kernel : ∀ mn' ∈ allMns, mn' ≠ "gate_call" →
        (22#6 : BitVec 6) ≠ Hw.opcodeOf mn') p.1
        (by rw [← opCircs_fst_all E]; exact List.mem_map_of_mem hp) hne))
  exact retireMem_op_sel σ E "gate_call" (Hw.callCirc E) hifsel hifexcl
    hmn hmem hnd hq

/-- If the combined call predicate is false, opcode 22 leaves the core
memory port disabled. -/
theorem coreAct_mem_gateCall_failed (m : Manifest) (σ : Loom.Hw.St)
    (E : DomainId)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hok0 : (Hw.callOkE E).eval σ = 0#1) (b : Addr) :
    ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
      b.toNat 32 = σ.mems "mem" b.toNat 32 := by
  have hport := retireMem_gateCall_sel σ E hifsel hifexcl hopc
  rw [coreAct_run_retire_eq m σ _ hifv hcl,
    retireAct_run_mems σ _ b.toNat 32]
  show (if (((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1,
          .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
        (.lit 0 : Expr 32))).1).eval σ = 1#1 then _
    else ((Hw.refillAct m).run σ σ)).mems "mem" b.toNat 32 = _
  rw [if_neg (by
    rw [hport.1]
    show ¬((Hw.callCirc E).memEn.eval σ = 1#1)
    unfold Hw.callCirc Hw.sweepMem Hw.andAll
    change ¬((Hw.callOkE E).eval σ &&& _ = 1#1)
    rw [hok0]
    exact (by decide : ∀ x : BitVec 1, ¬(0#1 &&& x = 1#1)) _)]
  rw [refill_pres_mem m σ "mem" b.toNat 32]

end Machines.Lnp64u.Theorems.RMC
