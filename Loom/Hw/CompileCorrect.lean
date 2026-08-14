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
def registerDeclOk (d : Design) (width : Nat) (name : String) : Bool :=
  d.regs.any fun reg => reg.name == name && reg.width == width

/-- Structural declaration and width check for one memory write. -/
def memoryDeclOk (d : Design) (addrWidth dataWidth : Nat)
    (name : String) : Bool :=
  d.mems.any (fun mem => mem.name == name) &&
  d.mems.all (fun mem => mem.name != name ||
    (mem.addrWidth == addrWidth && mem.dataWidth == dataWidth))

def actionDeclsOk (d : Design) : Act → Bool
  | .skip => true
  | .seq left right => actionDeclsOk d left && actionDeclsOk d right
  | .ite _ thenAct elseAct => actionDeclsOk d thenAct && actionDeclsOk d elseAct
  | .write width name _ => registerDeclOk d width name
  | .writeSlice width name _ _ _ _ => registerDeclOk d width name
  | .memWrite aw dw name _ _ _ => memoryDeclOk d aw dw name

/-- A compositional action-declaration certificate over a rule list. -/
def RulesDeclsOk (d : Design) : List Rule → Prop
  | [] => True
  | rule :: rest =>
      actionDeclsOk d rule.body = true ∧ RulesDeclsOk d rest

/-- A compositional rule-list certificate supplies the pointwise premise used
by `designWF_of_components`. -/
theorem RulesDeclsOk.all {d : Design} {rules : List Rule}
    (valid : RulesDeclsOk d rules) :
    ∀ rule ∈ rules, actionDeclsOk d rule.body = true := by
  induction rules with
  | nil => simp
  | cons head tail ih =>
      intro rule member
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using valid.1
      | inr member => exact ih valid.2 rule member

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
    simp only [actionDeclsOk, registerDeclOk, Act.regWrites] at h hwrite
  · contradiction
  · rename_i left right ihLeft ihRight
    simp only [Bool.and_eq_true] at h
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
  · rename_i actualWidth actualName lo fieldWidth inBounds value
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
    simp only [actionDeclsOk, memoryDeclOk, Act.memWrites] at h hwrite
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
  | writeSlice => intro _; rfl
  | memWrite aw dw name port address value =>
    intro h
    simp only [actionDeclsOk, memoryDeclOk, Bool.and_eq_true] at h
    by_cases hname : name = mem.name
    · have hall := List.all_eq_true.mp h.2 mem
      specialize hall hmem
      simp only [hname, bne_self_eq_false, Bool.false_or, Bool.and_eq_true,
        beq_iff_eq] at hall
      simp [widthsOk, hname, hall.1.symm, hall.2.symm]
    · simp [widthsOk, hname]

/-- Fragment-local declaration checking supplies register-write witnesses in
the enlarged design.  Extension certificates use this without rechecking the
base rules. -/
theorem RulesDeclsOk.regWrites {d : Design} {rules : List Rule}
    (valid : RulesDeclsOk d rules) {rule : Rule} (member : rule ∈ rules)
    {name : String} {width : Nat}
    (write : (name, width) ∈ rule.body.regWrites) :
    ∃ reg ∈ d.regs, reg.name = name ∧ reg.width = width :=
  actionDeclsOk_regWrites d rule.body (valid.all rule member) name width write

/-- Fragment-local declaration checking supplies memory-write witnesses in
the enlarged design. -/
theorem RulesDeclsOk.memWrites {d : Design} {rules : List Rule}
    (valid : RulesDeclsOk d rules) {rule : Rule} (member : rule ∈ rules)
    {name : String} (write : name ∈ rule.body.memWrites) :
    ∃ memory ∈ d.mems, memory.name = name :=
  actionDeclsOk_memWrites d rule.body (valid.all rule member) name write

/-- Fragment-local declaration checking also supplies the memory-width side
of `MemWriteWF`. -/
theorem RulesDeclsOk.widths {d : Design} {rules : List Rule}
    (valid : RulesDeclsOk d rules) {rule : Rule} (member : rule ∈ rules)
    {memory : MemDecl} (declared : memory ∈ d.mems) :
    widthsOk memory.name memory.addrWidth memory.dataWidth rule.body = true :=
  actionDeclsOk_widths d memory declared rule.body (valid.all rule member)

/-- An action that does not write a memory satisfies that memory's width
obligation without inspecting unrelated declarations. -/
theorem widthsOk_of_not_memWrites (memory : MemDecl) : ∀ action : Act,
    memory.name ∉ action.memWrites →
      widthsOk memory.name memory.addrWidth memory.dataWidth action = true := by
  intro action
  induction action with
  | skip => simp [widthsOk, Act.memWrites]
  | seq left right ihLeft ihRight =>
      simp only [Act.memWrites, List.mem_append, not_or]
      rintro ⟨hleft, hright⟩
      simp [widthsOk, ihLeft hleft, ihRight hright]
  | ite guard thenAct elseAct ihThen ihElse =>
      simp only [Act.memWrites, List.mem_append, not_or]
      rintro ⟨hthen, helse⟩
      simp [widthsOk, ihThen hthen, ihElse helse]
  | write => simp [widthsOk, Act.memWrites]
  | writeSlice => simp [widthsOk, Act.memWrites]
  | memWrite aw dw name port address value =>
      simp only [Act.memWrites, List.mem_singleton]
      intro different
      have reverse : name ≠ memory.name := fun equal => different equal.symm
      simp [widthsOk, reverse]

/-- The port trace for a memory is empty when the action does not write that
memory. -/
theorem portTrace_eq_nil_of_not_memWrites (memory : String) : ∀ action : Act,
    memory ∉ action.memWrites → portTrace memory action = [] := by
  intro action
  induction action with
  | skip => simp [portTrace]
  | seq left right ihLeft ihRight =>
      simp only [Act.memWrites, List.mem_append, not_or]
      rintro ⟨hleft, hright⟩
      simp [portTrace, ihLeft hleft, ihRight hright]
  | ite guard thenAct elseAct ihThen ihElse =>
      simp only [Act.memWrites, List.mem_append, not_or]
      rintro ⟨hthen, helse⟩
      simp [portTrace, ihThen hthen, ihElse helse]
  | write => simp [portTrace, Act.memWrites]
  | writeSlice => simp [portTrace, Act.memWrites]
  | memWrite aw dw name port address value =>
      simp only [Act.memWrites, List.mem_singleton]
      intro different
      have reverse : name ≠ memory := fun equal => different equal.symm
      simp [portTrace, reverse]

/-- Assemble compiler well-formedness from independently checked structural
components. This form lets large release designs certify action trees and
memory traces in bounded generated declarations instead of reducing one
monolithic Boolean. -/
theorem designWF_of_components (d : Design)
    (hregs : (d.regs.map (·.name)).Nodup)
    (hmems : (d.mems.map (·.name)).Nodup)
    (hactions : ∀ rule ∈ d.rules, actionDeclsOk d rule.body = true)
    (hmemory : ∀ mem ∈ d.mems,
      (designTrace d mem.name).Pairwise (fun a b => a < b)) :
    DesignWF d := by
  refine ⟨hregs, hmems, ?_, ?_, ?_⟩
  · intro rule hrule name width hwrite
    exact actionDeclsOk_regWrites d rule.body
      (hactions rule hrule) name width hwrite
  · intro rule hrule name hwrite
    exact actionDeclsOk_memWrites d rule.body
      (hactions rule hrule) name hwrite
  · intro mem hmem
    exact ⟨fun rule hrule => actionDeclsOk_widths d mem hmem rule.body
      (hactions rule hrule), hmemory mem hmem⟩

/-- Acceptance of `designWFCheck` supplies all semantic compiler side
conditions. -/
theorem designWFCheck_sound (d : Design) (h : designWFCheck d = true) :
    DesignWF d := by
  simp only [designWFCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hregs, hmems⟩, hactions⟩, hmemory⟩ := h
  exact designWF_of_components d hregs hmems
    (List.all_eq_true.mp hactions) (fun mem hmem => by
      simpa using List.all_eq_true.mp hmemory mem hmem)

/-- Forget the nominal distinction between µVerilog and EDSL state records. -/
def forgetSt (state : Loom.Emit.MicroVerilog.St) : Loom.Hw.St :=
  ⟨state.regs, state.mems⟩

@[simp] theorem forgetSt_convSt (state : Loom.Hw.St) :
    forgetSt (convSt state) = state := by cases state; rfl

@[simp] theorem convSt_forgetSt (state : Loom.Emit.MicroVerilog.St) :
    convSt (forgetSt state) = state := by cases state; rfl

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

/-! ## Open designs (D15)

Inputs are environment-owned register coordinates that no rule writes
(`DesignWF.regWrites` forbids writes outside `d.regs`), so both cycles
preserve them and the emission theorem extends to open designs: poke the
same input valuation on both sides, and one compiled open cycle is exactly
one source open cycle. -/

/-- Source and µVerilog input installation commute with the compiler's state
embedding. This is shared by open-cycle and combinational-output correctness. -/
theorem convSt_setInputs (σ : Loom.Hw.St) (ins : List InputDecl)
    (ι : InEnv) :
    Loom.Emit.MicroVerilog.St.setInputs (convSt σ)
      (ins.map fun i => { name := i.name, width := i.width }) ι =
    convSt (σ.setInputs ins ι) := by
  induction ins generalizing σ with
  | nil => rfl
  | cons head tail ih =>
      simpa [Loom.Emit.MicroVerilog.St.setInputs, St.setInputs,
        List.foldl_cons] using
        ih { σ with regs := σ.regs.set head.name (ι head.name head.width) }

/-- A compiled same-cycle output has exactly the source `Design` observation
for arbitrary current inputs and pre-edge state. -/
theorem compileCombOutput_evalOpen (d : Design) (output : CombOutput)
    (ι : InEnv) (state : Loom.Hw.St) :
    mvEval
        (Loom.Emit.MicroVerilog.St.setInputs (convSt state)
          (compile d).ins ι)
        (compileExpr output.value) =
      d.evalCombOutput ι state output := by
  rw [show (compile d).ins =
        d.inputs.map (fun i => { name := i.name, width := i.width }) from rfl,
      convSt_setInputs]
  exact compileExpr_eval output.value (state.setInputs d.inputs ι)

/-- The emission theorem for open designs: one compiled open cycle under an
input valuation is exactly one source open cycle under the same valuation. -/
theorem compile_cycleOpen (d : Design) (wf : DesignWF d) (ι : InEnv)
    (state : Loom.Hw.St) :
    forgetSt ((compile d).cycleOpen ι (convSt state)) = d.cycleOpen ι state := by
  unfold Loom.Emit.MicroVerilog.Module.cycleOpen Design.cycleOpen
  rw [show (compile d).ins =
        d.inputs.map (fun i => { name := i.name, width := i.width }) from rfl,
      convSt_setInputs]
  exact compile_cycle d wf (state.setInputs d.inputs ι)

/-- Compiler correctness including the reset pin: an asserted reset edge
establishes the exact source reset state, while a deasserted edge is the
existing cycle theorem. -/
theorem compile_cycleWithReset (d : Design) (wf : DesignWF d)
    (reset : Bool) (state : Loom.Hw.St) :
    forgetSt ((compile d).cycleWithReset reset (convSt state)) =
      d.cycleWithReset reset state := by
  cases reset <;>
    simp [Loom.Emit.MicroVerilog.Module.cycleWithReset,
      Design.cycleWithReset, compile_cycle, wf, compile_reset]

/-- Open-design form. Reset priority makes input values irrelevant on an
asserted edge, exactly as in the emitted `always` block. -/
theorem compile_cycleOpenWithReset (d : Design) (wf : DesignWF d)
    (reset : Bool) (ι : InEnv) (state : Loom.Hw.St) :
    forgetSt ((compile d).cycleOpenWithReset reset ι (convSt state)) =
      d.cycleOpenWithReset reset ι state := by
  cases reset <;>
    simp [Loom.Emit.MicroVerilog.Module.cycleOpenWithReset,
      Design.cycleOpenWithReset, compile_cycleOpen, wf, compile_reset]

/-- Every finite compiled open run has exactly the source Design semantics.
This is the iteration lemma used by the certified simulator/compiler square. -/
theorem compile_runOpen (d : Design) (wf : DesignWF d) (n : Nat)
    (ιs : Nat → InEnv) (state : Loom.Hw.St) :
    forgetSt ((compile d).runOpen ιs n (convSt state)) =
      d.runOpen ιs n state := by
  induction n generalizing ιs state with
  | zero => rfl
  | succ n ih =>
      simp only [Loom.Emit.MicroVerilog.Module.runOpen, Design.runOpen]
      have hcycle := compile_cycleOpen d wf (ιs 0) state
      have hstate :
          (compile d).cycleOpen (ιs 0) (convSt state) =
            convSt (d.cycleOpen (ιs 0) state) := by
        calc
          _ = convSt (forgetSt
                ((compile d).cycleOpen (ιs 0) (convSt state))) := by simp
          _ = convSt (d.cycleOpen (ιs 0) state) := congrArg convSt hcycle
      rw [hstate]
      exact ih (fun k => ιs (k + 1)) (d.cycleOpen (ιs 0) state)

/-- State-record-neutral form of `compile_runOpen`, convenient for clients
whose current state already inhabits the µVerilog semantics. -/
theorem compile_runOpen_from_module_state (d : Design) (wf : DesignWF d)
    (n : Nat) (ιs : Nat → InEnv) (state : Loom.Emit.MicroVerilog.St) :
    forgetSt ((compile d).runOpen ιs n state) =
      d.runOpen ιs n (forgetSt state) := by
  simpa using compile_runOpen d wf n ιs (forgetSt state)

end Loom.Hw.Compile
