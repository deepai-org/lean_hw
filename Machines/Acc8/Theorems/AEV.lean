import Machines.Acc8.Core
import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.Axiom

/-!
# A-EV — the emitted µVerilog denotes the Acc8 core (task 2.4, pathfinder)

The emission theorem instantiated for Acc8: the compiled µVerilog module's
transition system equals the EDSL core's, under the state conversion. With
the round-trip theorem (task 2.3) and the µVerilog-semantics axiom, this
chains Acc8's spec → core (A-R) → µVerilog text. LNP64-µ's E-V is the same
statement at scale.
-/

namespace Machines.Acc8.Theorems.AEV

open Loom Loom.Hw Loom.Emit.MicroVerilog Machines.Acc8

/-- State conversion: EDSL design state ↔ µVerilog module state (both are
name-indexed register/memory valuations, so this is the identity on the
underlying maps). -/
def conv (σ : Loom.Hw.St) : Loom.Emit.MicroVerilog.St :=
  { regs := σ.regs, mems := σ.mems }

/-- **A-EV (cycle).** One µVerilog cycle equals one compiled-design cycle
under `conv`: the register mux-tree fold and the memory write-port fold the
compiler builds evaluate to the design's rule fold. -/
theorem cycle_agree (prog : BitVec 8 → BitVec 16) (σ : Loom.Hw.St) :
    (Compile.compile (Core.design prog)).cycle (conv σ)
      = conv ((Core.design prog).cycle σ) := by
  -- concrete side conditions of the generic lemmas, discharged by kernel
  -- evaluation (`prog` never occurs in the rule list, so everything reduces)
  have hnd_regs : ((Core.design prog).regs.map (·.name)).Nodup :=
    of_decide_eq_true rfl
  have hnd_mems : ((Core.design prog).mems.map (·.name)).Nodup :=
    of_decide_eq_true rfl
  have hwf_mem : Compile.MemWriteWF (Core.design prog)
      ⟨"mem", 8, 8, fun _ => 0⟩ :=
    ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩
  have hwf_prog : Compile.MemWriteWF (Core.design prog)
      ⟨"prog", 8, 16, fun a => prog (BitVec.ofNat 8 a)⟩ :=
    ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩
  -- every register write in the rules targets a declared (name, width)
  have hregw : (Core.design prog).rules.all
      (fun rl => rl.body.regWrites.all
        (fun p => decide (p = ("acc", 8) ∨ p = ("pc", 8) ∨ p = ("halted", 1))))
      = true := rfl
  -- every memory write in the rules targets "mem"
  have hmemw : (Core.design prog).rules.all
      (fun rl => rl.body.memWrites.all (fun s => s == "mem")) = true := rfl
  have hregs : ((Compile.compile (Core.design prog)).cycle (conv σ)).regs
      = ((Core.design prog).cycle σ).regs := by
    funext rn w
    by_cases h1 : rn = "acc" ∧ w = 8
    · obtain ⟨rfl, rfl⟩ := h1
      exact Compile.compile_cycle_regs (Core.design prog) σ ⟨"acc", 8, 0⟩
        (List.mem_cons_self ..) hnd_regs
    · by_cases h2 : rn = "pc" ∧ w = 8
      · obtain ⟨rfl, rfl⟩ := h2
        exact Compile.compile_cycle_regs (Core.design prog) σ ⟨"pc", 8, 0⟩
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hnd_regs
      · by_cases h3 : rn = "halted" ∧ w = 1
        · obtain ⟨rfl, rfl⟩ := h3
          exact Compile.compile_cycle_regs (Core.design prog) σ ⟨"halted", 1, 0⟩
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hnd_regs
        · -- (rn, w) matches no declared register: both sides leave it alone
          refine Eq.trans (Compile.foldl_set_preserve
            (Compile.compile (Core.design prog)).regs (conv σ).regs (conv σ)
            rn w ?_) ?_
          · intro rd hrd
            obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrd
            have hr' : r = (⟨"acc", 8, 0⟩ : Loom.Hw.RegDecl)
                ∨ r = (⟨"pc", 8, 0⟩ : Loom.Hw.RegDecl)
                ∨ r = (⟨"halted", 1, 0⟩ : Loom.Hw.RegDecl) := by
              simpa [Core.design] using hr
            rcases hr' with rfl | rfl | rfl
            · exact fun hc => h1 ⟨hc.1.symm, hc.2.symm⟩
            · exact fun hc => h2 ⟨hc.1.symm, hc.2.symm⟩
            · exact fun hc => h3 ⟨hc.1.symm, hc.2.symm⟩
          · refine (Compile.rules_run_regs_notin rn w (Core.design prog).rules
              ?_ σ σ).symm
            intro rl hrl hmem
            have hall := List.all_eq_true.mp hregw rl hrl
            have hp := of_decide_eq_true (List.all_eq_true.mp hall (rn, w) hmem)
            rcases hp with h | h | h
            · exact h1 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
            · exact h2 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
            · exact h3 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hmems : ((Compile.compile (Core.design prog)).cycle (conv σ)).mems
      = ((Core.design prog).cycle σ).mems := by
    funext n a' w'
    by_cases hpn : n = "prog"
    · subst hpn
      exact Compile.compile_cycle_mems_all (Core.design prog) σ
        ⟨"prog", 8, 16, fun a => prog (BitVec.ofNat 8 a)⟩
        (List.mem_cons_self ..) hnd_mems hwf_prog a' w'
    · by_cases hmn : n = "mem"
      · subst hmn
        exact Compile.compile_cycle_mems_all (Core.design prog) σ
          ⟨"mem", 8, 8, fun _ => 0⟩
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hnd_mems
          hwf_mem a' w'
      · -- n names no declared memory: both sides leave it alone
        refine Eq.trans (Compile.memsFold_other (conv σ) n
          (Compile.compile (Core.design prog)).mems ?_ (conv σ).mems a' w') ?_
        · intro md hmd
          obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hmd
          have hm0' : m0 = (⟨"prog", 8, 16, fun a => prog (BitVec.ofNat 8 a)⟩ :
                Loom.Hw.MemDecl)
              ∨ m0 = (⟨"mem", 8, 8, fun _ => 0⟩ : Loom.Hw.MemDecl) := by
            simpa [Core.design] using hm0
          rcases hm0' with rfl | rfl
          · exact fun he => hpn he.symm
          · exact fun he => hmn he.symm
        · refine (Compile.rules_run_mems_notin n (Core.design prog).rules
            ?_ σ σ a' w').symm
          intro rl hrl hmem
          have hall := List.all_eq_true.mp hmemw rl hrl
          have hp := List.all_eq_true.mp hall n hmem
          exact hmn (by simpa using hp)
  exact congr (congrArg Loom.Emit.MicroVerilog.St.mk hregs) hmems

/-- **A-EV.** The emitted module's transition system equals the core's. -/
theorem emission_correct (prog : BitVec 8 → BitVec 16) :
    Nonempty (Simulation (Core.design prog).toTSys
                (Compile.compile (Core.design prog)).toTSys) := by
  refine ⟨{ abs := fun s => ⟨s.regs, s.mems⟩, init_ok := ?_, square := ?_ }⟩
  · intro s hs
    replace hs : s = (Compile.compile (Core.design prog)).reset := hs
    show (⟨s.regs, s.mems⟩ : Loom.Hw.St) = (Core.design prog).reset
    rw [hs, Compile.compile_reset]
    rfl
  · intro s s' hstep
    replace hstep : (Compile.compile (Core.design prog)).cycle s = s' := hstep
    subst hstep
    show (Core.design prog).cycle ⟨s.regs, s.mems⟩ = _
    exact (congrArg (fun st : Loom.Emit.MicroVerilog.St =>
      (⟨st.regs, st.mems⟩ : Loom.Hw.St))
      (cycle_agree prog ⟨s.regs, s.mems⟩)).symm

end Machines.Acc8.Theorems.AEV
