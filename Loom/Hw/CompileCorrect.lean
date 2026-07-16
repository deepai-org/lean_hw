-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile

/-!
# Whole-design compiler correctness

The expression, register, reset, and memory theorems in `Compile` are joined
here into the forward simulation used by release artifacts. The explicit
well-formedness conditions rule out source writes to undeclared state and
establish the memory-port ordering discipline.
-/

namespace Loom.Hw.Compile

open Loom.Hw

/-- Conditions under which the structural compiler preserves the complete
design state, including the junk coordinates outside declared names/widths. -/
structure DesignWF (d : Design) : Prop where
  regNames : (d.regs.map (·.name)).Nodup
  memNames : (d.mems.map (·.name)).Nodup
  regWrites : ∀ rule ∈ d.rules, ∀ name width,
    (name, width) ∈ rule.body.regWrites →
      ∃ reg ∈ d.regs, reg.name = name ∧ reg.width = width
  memWrites : ∀ rule ∈ d.rules, ∀ name,
    name ∈ rule.body.memWrites → ∃ mem ∈ d.mems, mem.name = name
  memory : ∀ mem ∈ d.mems, MemWriteWF d mem

/-- Structural declaration/width check for one action. It avoids materializing
the potentially large `regWrites` and `memWrites` lists. -/
def actionDeclsOk (d : Design) : Act → Bool
  | .skip => true
  | .seq left right => actionDeclsOk d left && actionDeclsOk d right
  | .ite _ thenAct elseAct => actionDeclsOk d thenAct && actionDeclsOk d elseAct
  | .write width name _ =>
      d.regs.any fun reg => reg.name == name && reg.width == width
  | .memWrite aw dw name _ _ _ =>
      d.mems.any (fun mem => mem.name == name) &&
      d.mems.all (fun mem => mem.name != name ||
        (mem.addrWidth == aw && mem.dataWidth == dw))

/-- Executable whole-design well-formedness check. This is deliberately
separate from compiler execution and has a generic soundness theorem. -/
def designWFCheck (d : Design) : Bool :=
  decide (d.regs.map (·.name)).Nodup &&
  decide (d.mems.map (·.name)).Nodup &&
  d.rules.all (fun rule => actionDeclsOk d rule.body) &&
  d.mems.all (fun mem =>
    decide ((designTrace d mem.name).Pairwise (fun a b => a < b)))

private theorem actionDeclsOk_regWrites (d : Design) : ∀ (action : Act),
    actionDeclsOk d action = true → ∀ name width,
      (name, width) ∈ action.regWrites →
        ∃ reg ∈ d.regs, reg.name = name ∧ reg.width = width := by
  intro action
  induction action <;> intro h name width hwrite <;>
    simp only [actionDeclsOk, Act.regWrites] at h hwrite
  · contradiction
  · rename_i left right ihLeft ihRight
    simp only [actionDeclsOk, Bool.and_eq_true] at h
    rcases List.mem_append.mp hwrite with hwrite | hwrite
    · exact ihLeft h.1 name width hwrite
    · exact ihRight h.2 name width hwrite
  · rename_i guard thenAct elseAct ihThen ihElse
    simp only [Bool.and_eq_true] at h
    rcases List.mem_append.mp hwrite with hwrite | hwrite
    · exact ihThen h.1 name width hwrite
    · exact ihElse h.2 name width hwrite
  · rename_i actualWidth actualName value
    simp only [List.mem_singleton, Prod.mk.injEq] at hwrite
    rcases hwrite with ⟨rfl, rfl⟩
    obtain ⟨reg, hreg, hmatch⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    exact ⟨reg, hreg, hmatch⟩
  · contradiction

private theorem actionDeclsOk_memWrites (d : Design) : ∀ (action : Act),
    actionDeclsOk d action = true → ∀ name, name ∈ action.memWrites →
      ∃ mem ∈ d.mems, mem.name = name := by
  intro action
  induction action <;> intro h name hwrite <;>
    simp only [actionDeclsOk, Act.memWrites] at h hwrite
  · contradiction
  · rename_i left right ihLeft ihRight
    simp only [Bool.and_eq_true] at h
    rcases List.mem_append.mp hwrite with hwrite | hwrite
    · exact ihLeft h.1 name hwrite
    · exact ihRight h.2 name hwrite
  · rename_i guard thenAct elseAct ihThen ihElse
    simp only [Bool.and_eq_true] at h
    rcases List.mem_append.mp hwrite with hwrite | hwrite
    · exact ihThen h.1 name hwrite
    · exact ihElse h.2 name hwrite
  · contradiction
  · rename_i aw dw actualName port address value
    simp only [Bool.and_eq_true] at h
    simp only [List.mem_singleton] at hwrite
    subst actualName
    obtain ⟨mem, hmem, hname⟩ := List.any_eq_true.mp h.1
    exact ⟨mem, hmem, by simpa using hname⟩

private theorem actionDeclsOk_widths (d : Design) (mem : MemDecl)
    (hmem : mem ∈ d.mems) :
    ∀ (action : Act), actionDeclsOk d action = true →
      widthsOk mem.name mem.addrWidth mem.dataWidth action = true := by
  intro action
  induction action with
  | skip => intro _; rfl
  | seq left right ihLeft ihRight =>
      intro h
      simp only [actionDeclsOk, Bool.and_eq_true] at h
      simp only [widthsOk, Bool.and_eq_true]
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | ite guard thenAct elseAct ihThen ihElse =>
      intro h
      simp only [actionDeclsOk, Bool.and_eq_true] at h
      simp only [widthsOk, Bool.and_eq_true]
      exact ⟨ihThen h.1, ihElse h.2⟩
  | write => intro _; rfl
  | memWrite aw dw name port address value =>
    intro h
    simp only [actionDeclsOk, Bool.and_eq_true] at h
    by_cases hname : name = mem.name
    · have hall := List.all_eq_true.mp h.2 mem
      specialize hall hmem
      simp only [hname, bne_self_eq_false, Bool.false_or, Bool.and_eq_true,
        beq_iff_eq] at hall
      simp [widthsOk, hname, hall.1.symm, hall.2.symm]
    · simp [widthsOk, hname]

/-- Acceptance of `designWFCheck` supplies all semantic compiler side
conditions. -/
theorem designWFCheck_sound (d : Design) (h : designWFCheck d = true) :
    DesignWF d := by
  simp only [designWFCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hregs, hmems⟩, hactions⟩, hmemory⟩ := h
  refine ⟨hregs, hmems, ?_, ?_, ?_⟩
  · intro rule hrule name width hwrite
    exact actionDeclsOk_regWrites d rule.body
      (List.all_eq_true.mp hactions rule hrule) name width hwrite
  · intro rule hrule name hwrite
    exact actionDeclsOk_memWrites d rule.body
      (List.all_eq_true.mp hactions rule hrule) name hwrite
  · intro mem hmem
    exact ⟨fun rule hrule => actionDeclsOk_widths d mem hmem rule.body
      (List.all_eq_true.mp hactions rule hrule),
      by simpa using List.all_eq_true.mp hmemory mem hmem⟩

/-- Forget the nominal distinction between µVerilog and EDSL state records. -/
def forgetSt (state : Loom.Emit.MicroVerilog.St) : Loom.Hw.St :=
  ⟨state.regs, state.mems⟩

@[simp] theorem forgetSt_convSt (state : Loom.Hw.St) :
    forgetSt (convSt state) = state := by cases state; rfl

/-- One compiled cycle is exactly one source-design cycle. -/
theorem compile_cycle (d : Design) (wf : DesignWF d) (state : Loom.Hw.St) :
    forgetSt ((compile d).cycle (convSt state)) = d.cycle state := by
  apply congr (congrArg Loom.Hw.St.mk ?_) ?_
  · funext name width
    by_cases declared : ∃ reg ∈ d.regs,
        reg.name = name ∧ reg.width = width
    · obtain ⟨reg, hreg, rfl, rfl⟩ := declared
      exact compile_cycle_regs d state reg hreg wf.regNames
    · show ((compile d).cycle (convSt state)).regs name width =
          (d.cycle state).regs name width
      rw [show ((compile d).cycle (convSt state)).regs name width =
          (convSt state).regs name width by
        unfold Loom.Emit.MicroVerilog.Module.cycle
        apply foldl_set_preserve
        intro out hout hmatch
        unfold compile at hout
        obtain ⟨reg, hreg, rfl⟩ := List.mem_map.mp hout
        exact declared ⟨reg, hreg, hmatch⟩]
      unfold Design.cycle
      rw [rules_run_regs_notin name width d.rules (fun rule hrule => by
        intro hwrite
        obtain ⟨reg, hreg, hn, hw⟩ := wf.regWrites rule hrule name width hwrite
        exact declared ⟨reg, hreg, hn, hw⟩) state state]
      rfl
  · funext name address width
    by_cases declared : ∃ mem ∈ d.mems, mem.name = name
    · obtain ⟨mem, hmem, rfl⟩ := declared
      exact compile_cycle_mems_all d state mem hmem wf.memNames
        (wf.memory mem hmem) address width
    · show ((compile d).cycle (convSt state)).mems name address width =
          (d.cycle state).mems name address width
      rw [show ((compile d).cycle (convSt state)).mems name address width =
          (convSt state).mems name address width by
        unfold Loom.Emit.MicroVerilog.Module.cycle
        apply memsFold_other
        intro out hout heq
        unfold compile at hout
        obtain ⟨mem, hmem, rfl⟩ := List.mem_map.mp hout
        exact declared ⟨mem, hmem, heq⟩]
      unfold Design.cycle
      rw [rules_run_mems_notin name d.rules (fun rule hrule => by
        intro hwrite
        obtain ⟨mem, hmem, hn⟩ := wf.memWrites rule hrule name hwrite
        exact declared ⟨mem, hmem, hn⟩) state state address width]
      rfl

/-- The reference compiler forward-simulates the source design. -/
def simulation (d : Design) (wf : DesignWF d) :
    Loom.Simulation d.toTSys (compile d).toTSys where
  abs := forgetSt
  init_ok := by
    intro state hstate
    change forgetSt state = d.reset
    rw [hstate, compile_reset, forgetSt_convSt]
  square := by
    intro state next hstep
    change d.cycle (forgetSt state) = forgetSt next
    rw [← hstep]
    exact (compile_cycle d wf (forgetSt state)).symm

/-- Any module proved behaviorally equal to the compiler output inherits the
whole-design forward simulation. -/
theorem simulation_of_tsys_eq (d : Design) (wf : DesignWF d)
    (module : Loom.Emit.MicroVerilog.Module)
    (h : module.toTSys = (compile d).toTSys) :
    Nonempty (Loom.Simulation d.toTSys module.toTSys) := by
  rw [h]
  exact ⟨simulation d wf⟩

end Loom.Hw.Compile
