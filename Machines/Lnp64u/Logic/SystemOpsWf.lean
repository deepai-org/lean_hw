import Machines.Lnp64u.Logic.ExecWf
import Machines.Lnp64u.Logic.BaseOpsWf
import Machines.Lnp64u.Isa.System

/-!
# System opcodes preserve the invariant (work in progress)

`SystemOpsPreserveWf` (the sole remaining Phase-1 obligation) requires all 11
system opcodes to preserve `Wf`. The scheduling/mapping ops (`yield`, `unmap`)
touch only budget/region state and are **proved** here via the `PreservesWf`
toolkit. The nine capability/gate/Mover ops call the capability-kernel
operations (`installDerived`, `clearSlot`, `destroyMarked`, `transferCap`, the
sweeps, gate call/return, the Mover programming) — proving those is exactly
T2/T3/T8/T9's kernel content, and they remain (each isolated as its own
`sorry` below, in the `Wip` namespace so the audit's sorry policy permits it).
-/

namespace Machines.Lnp64u.Isa.Wip

open Machines.Lnp64u Loom.Isa SpecM

/-- The per-opcode dispatch of `SystemOpsPreserveWf`. Two of eleven ops proved
(`unmap`, `yield`); the nine capability/gate/Mover ops are the remaining
kernel-level core. -/
theorem system_preserves : SystemOpsPreserveWf := by
  intro instr hmem c σ hwf hrun hinf
  fin_cases hmem
  case _ => sorry  -- cap_dup    (installDerived)
  case _ => sorry  -- cap_drop   (reparent/orphan + clearSlot + sweeps)
  case _ => sorry  -- cap_revoke (destroyMarked + sweeps)
  case _ => sorry  -- mem_grant  (installDerived, cross-domain)
  case _ => sorry  -- map        (region install)
  -- unmap: clear a region register — proved
  case _ =>
    refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
    · exact (PreservesWf.bind (PreservesWf.clearRegion _ _)
        (fun _ => PreservesWf.setReg _ _ _) σ hwf hinf).1 a σ' he |>.1
    · exact (PreservesWf.bind (PreservesWf.clearRegion _ _)
        (fun _ => PreservesWf.setReg _ _ _) σ hwf hinf).2 e σ' he |>.1
  case _ => sorry  -- gate_call
  case _ => sorry  -- gate_return
  case _ => sorry  -- move
  -- yield: zero the budget — proved
  case _ =>
    refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
    · exact (PreservesWf.bind (PreservesWf.updDomBudget _ _)
        (fun _ => PreservesWf.setReg _ _ _) σ hwf hinf).1 a σ' he |>.1
    · exact (PreservesWf.bind (PreservesWf.updDomBudget _ _)
        (fun _ => PreservesWf.setReg _ _ _) σ hwf hinf).2 e σ' he |>.1
  -- halt: voluntary domain-fatal — haltDom on the running caller
  case _ =>
    refine ⟨fun a σ' he => ?_, fun e σ' he => ?_⟩
    · simp only [SpecM.modify] at he; injection he with h1 h2; subst h2
      exact haltDom_preserves_wf σ c.d 0 hwf hrun hinf
    · simp [SpecM.modify] at he

end Machines.Lnp64u.Isa.Wip
