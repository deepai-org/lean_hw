-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateReturnArm

/-!
# R-MC retirement: successful gate_return

Dynamic-selector reductions and whole-state abstraction for the successful
null and non-null reply-transfer paths.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- The optional transfer is skipped when the reply handle is null. -/
theorem gateReturnTransferA_run_zero (σ acc : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.retNZ d).eval σ = 0#1) :
    (gateReturnTransferA d).run σ acc = acc := by
  simp [gateReturnTransferA, Act.run, hz]

/-- A non-null reply selects the shared structural transfer action. -/
theorem gateReturnTransferA_run_nonzero (σ acc : Loom.Hw.St)
    (d : DomainId) (hnz : (Hw.retNZ d).eval σ = 1#1) :
    (gateReturnTransferA d).run σ acc =
      (Hw.transferA d (Hw.retCl d) (Hw.retSel d)).run σ acc := by
  simp [gateReturnTransferA, Act.run, hnz]

/-- The gate-clear fold selects exactly the serving gate. -/
theorem gateReturnClearA_run_selected (σ acc : Loom.Hw.St)
    (d : DomainId) (gid : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid) :
    (gateReturnClearA d).run σ acc =
      (Act.write 1 (Hw.gactV gid) (.lit 0)).run σ acc := by
  have hsel : (Expr.eq (Hw.retGid d) (Hw.gLit gid)).eval σ = 1#1 := by
    rw [eqE_eval]
    exact (bv2_lit_iff _ gid).mpr hgid
  have hexcl : ∀ g : GateId, g ≠ gid →
      (Expr.eq (Hw.retGid d) (Hw.gLit g)).eval σ ≠ 1#1 := by
    intro g hne hg
    rw [eqE_eval] at hg
    exact hne ((bv2_lit_iff _ g).mp hg |>.symm.trans hgid)
  exact seqAll_ite_run_unique σ acc
    (fun g : GateId => Expr.eq (Hw.retGid d) (Hw.gLit g))
    (fun g => Act.write 1 (Hw.gactV g) (.lit 0)) gid hsel hexcl
    (List.finRange numGates) (List.mem_finRange gid) (List.nodup_finRange _)

/-- The caller-resume fold selects exactly the active gate's caller. -/
theorem gateReturnResumeA_run_selected (σ acc : Loom.Hw.St)
    (d cl : DomainId)
    (hcl : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.retCl d).eval σ) = cl) :
    (gateReturnResumeA d).run σ acc =
      (Act.write 2 (Hw.drun cl) (.lit 0)).run σ acc := by
  have hsel : (Expr.eq (Hw.retCl d) (Hw.dLit cl)).eval σ = 1#1 := by
    rw [eqE_eval]
    exact (bv2_lit_iff _ cl).mpr hcl
  have hexcl : ∀ c : DomainId, c ≠ cl →
      (Expr.eq (Hw.retCl d) (Hw.dLit c)).eval σ ≠ 1#1 := by
    intro c hne hc
    rw [eqE_eval] at hc
    exact hne ((bv2_lit_iff _ c).mp hc |>.symm.trans hcl)
  exact seqAll_ite_run_unique σ acc
    (fun c : DomainId => Expr.eq (Hw.retCl d) (Hw.dLit c))
    (fun c => Act.write 2 (Hw.drun c) (.lit 0)) cl hsel hexcl
    (List.finRange numDomains) (List.mem_finRange cl)
    (List.nodup_finRange _)

/-- The reply-write fold selects exactly the active gate's caller. -/
theorem gateReturnReplyA_run_selected (σ acc : Loom.Hw.St)
    (d cl : DomainId)
    (hcl : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.retCl d).eval σ) = cl) :
    (gateReturnReplyA d).run σ acc =
      (Hw.writeReg cl
        (Hw.muxFin (fun g => .reg 3 (Hw.gcallerRd g)) (Hw.retGid d))
        (gateReturnReplyE d)).run σ acc := by
  have hsel : (Expr.eq (Hw.retCl d) (Hw.dLit cl)).eval σ = 1#1 := by
    rw [eqE_eval]
    exact (bv2_lit_iff _ cl).mpr hcl
  have hexcl : ∀ c : DomainId, c ≠ cl →
      (Expr.eq (Hw.retCl d) (Hw.dLit c)).eval σ ≠ 1#1 := by
    intro c hne hc
    rw [eqE_eval] at hc
    exact hne ((bv2_lit_iff _ c).mp hc |>.symm.trans hcl)
  exact seqAll_ite_run_unique σ acc
    (fun c : DomainId => Expr.eq (Hw.retCl d) (Hw.dLit c))
    (fun c => Hw.writeReg c
      (Hw.muxFin (fun g => .reg 3 (Hw.gcallerRd g)) (Hw.retGid d))
      (gateReturnReplyE d)) cl hsel hexcl
    (List.finRange numDomains) (List.mem_finRange cl)
    (List.nodup_finRange _)

end Machines.Lnp64u.Theorems.RMC
