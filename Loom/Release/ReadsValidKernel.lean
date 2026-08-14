-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.ToProgramWellFormed
import Loom.Release.SymbolicElaborate

/-!
# Kernel-reducible read-discipline check

`Symbolic.designReadsValidB` (decision D12) cannot be discharged by
kernel reduction: its register arms test `(wireNumber? name).isNone`,
and `wireNumber?` bottoms out in byte-level `String.drop`/`toNat?` the
kernel cannot whnf. This file provides a parallel Boolean with the same
soundness target (`Symbolic.DesignReadsValid`), using the
`String.toList`-recursive `isWireLikeB` instead — the same swap D13's
checker received. `toProgram_denotes` takes this Boolean as its read
hypothesis; the original remains for the interpreted pipeline.
-/

namespace Loom.Release.SSA

open Loom.Release Loom.Release.Symbolic

/-- Kernel-reducible mirror of `Symbolic.hwExprRegistersValidB`. -/
def hwExprReadsOkB (program : Program) :
    {width : Nat} → Loom.Hw.Expr width → Bool
  | width, .reg _ name =>
      match program.regs.find? (fun candidate => candidate.name == name) with
      | some reg => reg.width == width && !(isWireLikeB name)
      | none => false
  | _, .lit _ => true
  | _, .memRead _ _ address => hwExprReadsOkB program address
  | _, .and left right | _, .or left right | _, .xor left right
  | _, .add left right | _, .sub left right | _, .mul left right
  | _, .udiv left right | _, .urem left right | _, .shl left right
  | _, .shr left right | _, .eq left right | _, .ult left right
  | _, .slt left right =>
      hwExprReadsOkB program left && hwExprReadsOkB program right
  | _, .not value | _, .slice value _ _ | _, .zext value _
  | _, .sext value _ => hwExprReadsOkB program value
  | _, .mux condition yes no =>
      hwExprReadsOkB program condition &&
        hwExprReadsOkB program yes && hwExprReadsOkB program no

/-- Kernel-reducible mirror of `Symbolic.actRegistersValidB`. -/
def actReadsOkB (program : Program) : Loom.Hw.Act → Bool
  | .skip => true
  | .seq left right => actReadsOkB program left && actReadsOkB program right
  | .ite condition yes no =>
      hwExprReadsOkB program condition &&
        actReadsOkB program yes && actReadsOkB program no
  | .write _ _ value => hwExprReadsOkB program value
  | .writeSlice _ _ _ _ _ value => hwExprReadsOkB program value
  | .memWrite _ _ _ _ address value =>
      hwExprReadsOkB program address && hwExprReadsOkB program value

/-- Kernel-reducible mirror of `Symbolic.sourceRegisterValidB`. -/
def sourceReadsOkB (program : Program) (source : Loom.Hw.RegDecl) : Bool :=
  match program.regs.find? (fun candidate => candidate.name == source.name) with
  | some concrete => concrete.width == source.width &&
      !(isWireLikeB source.name)
  | none => false

/-- Kernel-reducible mirror of `Symbolic.designReadsValidB` (D12's
obligation, dischargeable by `decide`). -/
def designReadsOkB (design : Loom.Hw.Design) (program : Program) : Bool :=
  design.regs.all (sourceReadsOkB program) &&
    design.rules.all (fun rule => actReadsOkB program rule.body)

private theorem not_isWireLike_of_bnot {name : String}
    (h : (!(isWireLikeB name)) = true) : Symbolic.wireNumber? name = none :=
  wireNumber?_eq_none_of_not_isWireLike name (by
    cases hw : isWireLikeB name with
    | false => rfl
    | true => rw [hw] at h; exact absurd h (by decide))

theorem hwExprReadsOkB_sound {program : Program} {width : Nat}
    (expr : Loom.Hw.Expr width)
    (accepted : hwExprReadsOkB program expr = true) :
    Symbolic.HwExprRegistersValid program expr := by
  induction expr <;> simp_all [hwExprReadsOkB, Symbolic.HwExprRegistersValid,
    Bool.and_eq_true]
  case reg width name =>
    cases found : program.regs.find? (fun candidate =>
        candidate.name == name) with
    | none => simp [found] at accepted
    | some reg =>
        simp only [found, Bool.and_eq_true, beq_iff_eq] at accepted
        exact ⟨reg, rfl, accepted.1, not_isWireLike_of_bnot accepted.2⟩

theorem actReadsOkB_sound {program : Program} (action : Loom.Hw.Act)
    (accepted : actReadsOkB program action = true) :
    Symbolic.ActRegistersValid program action := by
  induction action <;> simp_all [actReadsOkB, Symbolic.ActRegistersValid,
    Bool.and_eq_true, hwExprReadsOkB_sound]

theorem sourceReadsOkB_sound {program : Program} (source : Loom.Hw.RegDecl)
    (accepted : sourceReadsOkB program source = true) :
    Symbolic.SourceRegisterValid program source := by
  unfold sourceReadsOkB at accepted
  unfold Symbolic.SourceRegisterValid
  cases found : program.regs.find? (fun candidate =>
      candidate.name == source.name) with
  | none => simp [found] at accepted
  | some concrete =>
      simp only [found, Bool.and_eq_true, beq_iff_eq] at accepted
      exact ⟨concrete, rfl, accepted.1, not_isWireLike_of_bnot accepted.2⟩

/-- Acceptance of the kernel-reducible check yields the same read
discipline D12's original Boolean targets. -/
theorem designReadsOkB_sound {design : Loom.Hw.Design} {program : Program}
    (accepted : designReadsOkB design program = true) :
    Symbolic.DesignReadsValid design program := by
  simp only [designReadsOkB, Bool.and_eq_true, List.all_eq_true] at accepted
  constructor
  · intro source sourceMem
    exact sourceReadsOkB_sound source (accepted.1 source sourceMem)
  · intro rule ruleMem
    exact actReadsOkB_sound rule.body (accepted.2 rule ruleMem)

end Loom.Release.SSA
