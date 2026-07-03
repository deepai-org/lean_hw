import Machines.Lnp64u.Logic.ExecWf
import Machines.Lnp64u.Isa.Base
import Mathlib.Tactic.FinCases

/-!
# Base opcodes preserve the invariant

The 14 base ALU/branch/memory instructions' `exec` are compositions of the
`PreservesWf` primitives, so each preserves `Wf`. Proved here via the toolkit,
concretely against the `Isa.base` declarations. This discharges the base half
of `ExecPreservesWf`, leaving only the 11 system opcodes.
-/

namespace Machines.Lnp64u.Isa

open Machines.Lnp64u Loom.Isa SpecM

/-- The register-register ALU shape preserves the invariant. Covers
`add`/`sub`/`and`/`or`/`xor`/`shl`/`shr` (7 opcodes). -/
theorem rrr_preserves (mn : String) (op : BitVec 6) (f) (s1 s2 : String)
    (c : Ctx) : PreservesWf ((rrr mn op f s1 s2).sem.exec c) :=
  PreservesWf.bind (PreservesWf.reg _ _)
    (fun _ => PreservesWf.bind (PreservesWf.reg _ _)
      (fun _ => PreservesWf.setReg _ _ _))

/-- The branch shape preserves the invariant. Covers `beq`/`blt` (2 opcodes). -/
theorem branch_preserves (mn : String) (op : BitVec 6) (test) (s1 s2 : String)
    (c : Ctx) : PreservesWf ((branch mn op test s1 s2).sem.exec c) :=
  PreservesWf.bind (PreservesWf.reg _ _)
    (fun a => PreservesWf.bind (PreservesWf.reg _ _)
      (fun b => PreservesWf.iteBool (test a b)
        (PreservesWf.updDomPc _ _) (PreservesWf.pure ())))

/-- **The base opcodes preserve the invariant.** Every declaration in
`Isa.base`, run on any operand context, preserves `Wf`. -/
theorem base_preserves : ∀ instr ∈ base, ∀ c : Ctx, PreservesWf (instr.sem.exec c) := by
  intro instr hmem c
  fin_cases hmem
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.setReg _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.setReg _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.setReg _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.setReg _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.setReg _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.setReg _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.setReg _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.setReg _ _ _)
  · exact PreservesWf.setReg _ _ _
  · exact PreservesWf.bind (PreservesWf.reg _ _)
      (fun _ => PreservesWf.bind (PreservesWf.load _ _) (fun _ => PreservesWf.setReg _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _)
      (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.store _ _ _))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.iteBool _ (PreservesWf.updDomPc _ _) (PreservesWf.pure ())))
  · exact PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.bind (PreservesWf.reg _ _) (fun _ => PreservesWf.iteBool _ (PreservesWf.updDomPc _ _) (PreservesWf.pure ())))
  · exact PreservesWf.bind (PreservesWf.reg _ _)
      (fun _ => PreservesWf.bind (PreservesWf.setReg _ _ _)
        (fun _ => PreservesWf.updDomPc _ _))

/-- The remaining obligation: the eleven system opcodes preserve the invariant.
Their `exec` calls the capability-kernel operations (`installDerived`,
`clearSlot`, `destroyMarked`, `transferCap`, the region/Mover sweeps, gate
call/return) — proving this is exactly T2/T3/T8/T9's kernel-level content. -/
def SystemOpsPreserveWf : Prop :=
  ∀ instr ∈ Machines.Lnp64u.Isa.system, ∀ c : Ctx, PreservesWf (instr.sem.exec c)

/-- `ExecPreservesWf` (the sole Phase-1 obligation for the whole invariant)
follows from the proved base-op preservation plus the system-op obligation.
`ExecPreservesWf`'s `(ok/err → Wf σ')` clauses are exactly what `PreservesWf`
gives (minus the extra `inflight` conclusion). -/
theorem execPreservesWf_of_system (hsys : SystemOpsPreserveWf) : ExecPreservesWf := by
  intro instr hmem c σ hwf hrun hinf
  have hp : PreservesWf (instr.sem.exec c) := by
    have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
      have : Machines.Lnp64u.isa = (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray :=
        rfl
      rw [this, Array.mem_toArray] at hmem; exact hmem
    rcases List.mem_append.mp hmem' with hb | hsys'
    · exact base_preserves instr hb c
    · exact hsys instr hsys' c
  exact ⟨fun a σ' he => (hp σ hwf hinf).1 a σ' he |>.1,
         fun e σ' he => (hp σ hwf hinf).2 e σ' he |>.1⟩

end Machines.Lnp64u.Isa
