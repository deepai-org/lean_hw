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

/-- The Wf half of `corePhase` under the combined obligation: identical to
`corePhase_preserves_wf` except the `retire` branch uses `retire_preserves_wfa`. -/
theorem corePhase_Wf_from_wfa (hexec : ExecPreservesWfA) (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (h : Wf σ) (hac : Acyclic σ) : Wf (corePhase m σ) := by
  unfold corePhase
  cases hinf : σ.inflight with
  | some fl =>
      by_cases hc : fl.cyclesLeft ≤ 1
      · simp only [hc, if_true]
        refine (retire_preserves_wfa hexec { σ with inflight := none } fl.dom fl.word ?_ ?_ ?_ rfl).1
        · exact wf_of_skeleton_sameGates σ { σ with inflight := none }
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) rfl rfl (by simp) h
        · exact acyclic_of_parentRef_eq σ _
            (parentRef_eq_of_doms σ _ (fun _ => ⟨rfl, rfl⟩)) hac
        · show (σ.doms fl.dom).run = .running
          exact h.inflight_running fl hinf
      · simp only [hc, if_false]
        refine wf_of_skeleton_sameGates σ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl ?_ h
        intro fl' hfl'
        have hdom : fl'.dom = fl.dom := by
          simp only [Option.some.injEq] at hfl'; exact hfl' ▸ rfl
        rw [hdom]; exact h.inflight_running fl hinf
  | none =>
      simp only []
      split
      · exact h
      · rename_i d hsched
        have hdrun : (σ.doms d).run = .running := schedule_running m σ d hsched
        split
        · exact haltWith_preserves_wf σ d .memoryAuthority h hdrun hinf
        · rename_i w hfetch
          split
          · exact haltWith_preserves_wf σ d .illegalInstruction h hdrun hinf
          · rename_i instr hdec
            by_cases hbud : instr.cost.cost ≤ (σ.doms (σ.payer d)).budget
            · simp only [hbud, if_true]
              obtain ⟨pc, pl, pg, pr, pru, ps, pgates, pmov⟩ :=
                setBudget_proj σ (σ.payer d) (fun ds => ds.budget - instr.cost.cost)
              cases hserv : (σ.doms d).serving with
              | none =>
                  simp only [hserv]
                  refine wf_setInflight σ (σ.setDom (σ.payer d) (fun ds => { ds with budget := ds.budget - instr.cost.cost }))
                    (⟨d, w, instr.cost.cost⟩ : InFlight) pc pl pg pr pru ps
                    (fun g => by rw [pgates]) (fun g a' ha' => ⟨a', by rw [pgates] at ha'; exact ha', rfl, rfl⟩)
                    (fun g hh => by rw [pgates]; exact hh) pmov ?_ h
                  rw [pru]; exact hdrun
              | some g =>
                  simp only [hserv]
                  cases hact : (σ.gates g).act with
                  | none => exact haltWith_preserves_wf σ d .protocol h hdrun hinf
                  | some a =>
                      simp only [hact]
                      by_cases hdon : instr.cost.cost ≤ a.donated
                      · simp only [hdon, if_true]
                        set sb := σ.setDom (σ.payer d)
                          (fun ds => { ds with budget := ds.budget - instr.cost.cost }) with hsb
                        have hg0 : sb.gates = σ.gates := pgates
                        set gv : GateState :=
                          { (sb.gates g) with act := some { a with donated := a.donated - instr.cost.cost } }
                          with hgv
                        refine wf_setInflight σ
                          { sb with gates := Loom.Fun.update sb.gates g gv }
                          (⟨d, w, instr.cost.cost⟩ : InFlight) pc pl pg pr pru ps ?_ ?_ ?_ pmov ?_ h
                        · intro g'
                          show (Loom.Fun.update sb.gates g gv g').config = (σ.gates g').config
                          by_cases hg : g' = g
                          · subst hg; simp only [Loom.Fun.update_same, hgv, hg0]
                          · simp only [Loom.Fun.update_ne _ _ _ _ hg, hg0]
                        · intro g' a' ha'
                          simp only at ha'
                          show ∃ a0, (σ.gates g').act = some a0 ∧ _ ∧ _
                          by_cases hg : g' = g
                          · subst hg
                            rw [Loom.Fun.update_same, hgv] at ha'
                            injection ha' with haa; subst haa
                            exact ⟨a, hact, rfl, rfl⟩
                          · rw [Loom.Fun.update_ne _ _ _ _ hg, hg0] at ha'
                            exact ⟨a', ha', rfl, rfl⟩
                        · intro g' hh
                          show ((Loom.Fun.update sb.gates g gv g').act).isSome
                          by_cases hg : g' = g
                          · subst hg; simp only [Loom.Fun.update_same, hgv, Option.isSome_some]
                          · rw [Loom.Fun.update_ne _ _ _ _ hg, hg0]; exact hh
                        · rw [pru]; exact hdrun
                      · simp only [hdon, if_false]
                        exact haltWith_preserves_wf σ d .budget h hdrun hinf
            · simp only [hbud, if_false]; exact h

/-- `corePhase` preserves `Wf ∧ Acyclic` under the combined obligation. -/
theorem corePhase_preserves_wfa (hexec : ExecPreservesWfA) (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (h : Wf σ) (hac : Acyclic σ) :
    Wf (corePhase m σ) ∧ Acyclic (corePhase m σ) :=
  ⟨corePhase_Wf_from_wfa hexec m hwf σ h hac,
   corePhase_preserves_acyclic
     (fun instr hm c σ0 hwf0 hac0 hr0 hi0 =>
       ⟨fun a σ' he => ((hexec instr hm c σ0 hwf0 hac0 hr0 hi0).1 a σ' he).2,
        fun e σ' he => ((hexec instr hm c σ0 hwf0 hac0 hr0 hi0).2 e σ' he).2⟩)
     m σ h hac⟩


/-- One cycle preserves `Wf ∧ Acyclic`, reduced to `ExecPreservesWfA`. -/
theorem step_wfa (hexec : ExecPreservesWfA) (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (h : Wf σ) (hac : Acyclic σ) :
    Wf (step m σ) ∧ Acyclic (step m σ) := by
  unfold step
  have hc := corePhase_preserves_wfa hexec m hwf (refillPhase m σ)
    (refillPhase_preserves_wf m σ h) (acyclic_refillPhase m σ hac)
  exact ⟨wf_setCycle _ _ (moverPhase_preserves_wf _ hc.1),
         acyclic_setCycle _ _ (acyclic_moverPhase _ hc.2)⟩

/-- **The combined invariant, reduced to the combined system-op obligation.**
`Wf σ ∧ Acyclic σ` holds in every reachable state, given `SystemOpsPreserveWfA`
(8 of 11 ops proved; only `cap_revoke` and the two gate ops remain). -/
theorem wfa_invariant_of_system (hsys : SystemOpsPreserveWfA) (m : Manifest) (hwf : m.WF) :
    (machine m).Invariant (fun σ => Wf σ ∧ Acyclic σ) := by
  have hexec := execPreservesWfA_of_system hsys
  exact (Loom.TSys.Inductive.invariant
    { init := fun σ hi => ⟨hi ▸ Machines.Lnp64u.Theorems.Inv.init_wf m hwf, hi ▸ init_acyclic m⟩
      step := fun σ σ' hσ hstep => by
        have hst : step m σ = σ' := hstep
        exact hst ▸ step_wfa hexec m hwf σ hσ.1 hσ.2 })

end Machines.Lnp64u
