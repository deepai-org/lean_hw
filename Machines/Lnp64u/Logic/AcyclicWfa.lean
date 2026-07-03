import Machines.Lnp64u.Logic.CapDropWfa
import Machines.Lnp64u.Theorems.AcyclicInv

/-!
# The combined `Wf ∧ Acyclic` exec obligation and invariant (L1)

Threads the combined system-op obligation through the exec chain: base opcodes
preserve both invariants (`base_preserves` + `base_preserves_acyclic`), and the
combined `ExecPreservesWfA` reduces to `SystemOpsPreserveWfA`. The revocation
opcodes need this combined form because `cap_drop`'s *Wf* clause itself uses
`Acyclic` — the two cannot be threaded independently.
-/

namespace Machines.Lnp64u

open Loom.Isa SpecM Machines.Lnp64u.Isa Machines.Lnp64u.Isa.Wip

/-- The combined exec obligation: every instruction preserves `Wf ∧ Acyclic`. -/
def ExecPreservesWfA : Prop :=
  ∀ (instr : Instr), instr ∈ isa → ∀ (c : Ctx) (σ : MachineState),
    Wf σ → Acyclic σ → (σ.doms c.d).run = .running → σ.inflight = none →
    (∀ a σ', instr.sem.exec c σ = .ok a σ' → Wf σ' ∧ Acyclic σ') ∧
    (∀ e σ', instr.sem.exec c σ = .err e σ' → Wf σ' ∧ Acyclic σ')

/-- `ExecPreservesWfA` reduces to the combined system-op obligation: base ops
preserve both invariants by construction. -/
theorem execPreservesWfA_of_system (hsys : SystemOpsPreserveWfA) : ExecPreservesWfA := by
  intro instr hmem c σ hwf hac hrun hinf
  have hmem' : instr ∈ Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system := by
    have hiseq : Machines.Lnp64u.isa =
      (Machines.Lnp64u.Isa.base ++ Machines.Lnp64u.Isa.system).toArray := rfl
    rw [hiseq, Array.mem_toArray] at hmem; exact hmem
  rcases List.mem_append.mp hmem' with hb | hsys'
  · refine ⟨fun a σ' he => ⟨?_, ?_⟩, fun e σ' he => ⟨?_, ?_⟩⟩
    · exact ((base_preserves instr hb c σ hwf hinf).1 a σ' he).1
    · exact (base_preserves_acyclic instr hb c σ hac).1 a σ' he
    · exact ((base_preserves instr hb c σ hwf hinf).2 e σ' he).1
    · exact (base_preserves_acyclic instr hb c σ hac).2 e σ' he
  · exact hsys instr hsys' c σ hwf hac hrun hinf

/-- `retire` preserves `Wf ∧ Acyclic`, reduced to `ExecPreservesWfA`. Combines
the Wf and Acyclic threads: decode-fail/fault halt, the pc bump preserves both,
and the instruction effect is the combined obligation. -/
theorem retire_preserves_wfa (hexec : ExecPreservesWfA) (σ : MachineState)
    (d : DomainId) (w : Loom.Word32) (hwf : Wf σ) (hac : Acyclic σ)
    (hdrun : (σ.doms d).run = .running) (hinf : σ.inflight = none) :
    Wf (retire σ d w) ∧ Acyclic (retire σ d w) := by
  unfold retire
  split
  · exact ⟨haltWith_preserves_wf σ d .illegalInstruction hwf hdrun hinf,
           acyclic_haltWith σ d .illegalInstruction hac⟩
  · rename_i instr hdec
    have hpcproj : ∀ (d' : DomainId),
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').caps = (σ.doms d').caps) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').lineage = (σ.doms d').lineage) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').slotGen = (σ.doms d').slotGen) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').regions = (σ.doms d').regions) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').run = (σ.doms d').run) ∧
        (((σ.setDom d (fun ds => { ds with pc := ds.pc + 1 })).doms d').serving = (σ.doms d').serving) := by
      intro d'; unfold MachineState.setDom
      by_cases hp : d' = d
      · subst hp; simp [Loom.Fun.update_same]
      · simp [Loom.Fun.update_ne _ _ _ _ hp]
    set σ1 := σ.setDom d (fun ds => { ds with pc := ds.pc + 1 }) with hσ1
    have hσ1wf : Wf σ1 := by
      refine wf_of_skeleton_sameGates σ σ1
        (fun d' => (hpcproj d').1) (fun d' => (hpcproj d').2.1) (fun d' => (hpcproj d').2.2.1)
        (fun d' => (hpcproj d').2.2.2.1) (fun d' => (hpcproj d').2.2.2.2.1)
        (fun d' => (hpcproj d').2.2.2.2.2) rfl rfl ?_ hwf
      intro fl' hfl'; rw [show σ1.inflight = σ.inflight from rfl, hinf] at hfl'
      exact absurd hfl' (by simp)
    have hσ1ac : Acyclic σ1 := acyclic_setDom σ d _ (fun ds => ⟨rfl, rfl⟩) hac
    have hσ1run : (σ1.doms d).run = .running := by rw [(hpcproj d).2.2.2.2.1]; exact hdrun
    have hmem : instr ∈ isa := Loom.Isa.decode_mem isa hdec
    obtain ⟨hok, herr⟩ := hexec instr hmem { d := d, pc := (σ.doms d).pc, op := operandsOf w }
      σ1 hσ1wf hσ1ac hσ1run hinf
    show (Wf (match instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
      | .ok _ σ' => σ'
      | .err e σ' => σ'.setDom d (fun ds => ds.setReg (operandsOf w).rd e.toWord)
      | .fault f => haltWith σ d f)) ∧ Acyclic _
    cases hexr : instr.sem.exec { d := d, pc := (σ.doms d).pc, op := operandsOf w } σ1 with
    | ok a σ' => simp only [hexr]; exact hok a σ' hexr
    | err e σ' =>
        simp only [hexr]
        obtain ⟨hw', ha'⟩ := herr e σ' hexr
        exact ⟨wf_setReg σ' d (operandsOf w).rd e.toWord hw',
               acyclic_setReg_dom σ' d (operandsOf w).rd e.toWord ha'⟩
    | fault f => simp only [hexr]
                 exact ⟨haltWith_preserves_wf σ d f hwf hdrun hinf, acyclic_haltWith σ d f hac⟩

end Machines.Lnp64u
