import Machines.Acc8.Core
import Machines.Acc8.Theorems.A1
import Mathlib.Tactic.Set

/-!
# A-R — the Acc8 core refines the Acc8 spec

The pathfinder refinement: one core cycle is exactly one spec step through
`Core.abs`. Exercises the `Simulation` spine end to end before LNP64-µ's
multicycle proof (R-MC) needs it.
-/

namespace Machines.Acc8.Theorems.AR

open Machines.Acc8 Loom Loom.Hw Loom.Isa

/-! ## A local, definitionally equal copy of the core's rule

`Core.execRule` and its shorthands are `private` to `Core.lean`, so they
cannot be *named* here; but definitional unfolding does not care about
visibility, so a verbatim copy is definitionally equal and `rfl` bridges
the two. -/

private def rAcc : Expr 8 := .reg 8 "acc"
private def rPc : Expr 8 := .reg 8 "pc"
private def rHalted : Expr 1 := .reg 1 "halted"
private def fetchW : Expr 16 := .memRead 16 "prog" rPc
private def opc : Expr 8 := .slice fetchW 0 8
private def imm : Expr 8 := .slice fetchW 8 8
private def pcNext : Act := .write 8 "pc" (.add rPc (.lit 1))
private def haltNow : Act := .write 1 "halted" (.lit 1)
private def isOp (n : Nat) : Expr 1 := .eq opc (.lit (BitVec.ofNat 8 n))

private def execRule : Act :=
  .ite rHalted .skip <|
  .ite (isOp 0) pcNext <|
  .ite (isOp 1) (.seq (.write 8 "acc" imm) pcNext) <|
  .ite (isOp 2) (.seq (.write 8 "acc" (.add rAcc imm)) pcNext) <|
  .ite (isOp 3) (.seq (.write 8 "acc" (.memRead 8 "mem" imm)) pcNext) <|
  .ite (isOp 4) (.seq (.memWrite 8 8 "mem" 0 imm rAcc) pcNext) <|
  .ite (isOp 5) (.ite (.eq rAcc (.lit 0)) pcNext (.write 8 "pc" imm)) <|
  .ite (isOp 6) (.seq (.write 8 "acc" (.sub rAcc imm)) pcNext) <|
  haltNow

/-- The one cycle of the core is the one rule, run against itself; the ROM
image parameter of the design is irrelevant to `cycle` (it only feeds
`reset`). Definitional. -/
private theorem cycle_eq (p : BitVec 8 → BitVec 16) (σ : Loom.Hw.St) :
    (Core.design p).cycle σ = execRule.run σ σ := rfl

/-! ## Decode facts -/

private theorem isa_size : isa.size = 8 := rfl

/-- Decode dispatch: a word whose opcode bits match declaration `i` decodes
to declaration `i`. -/
private theorem decode_eq {w : sig.Word} (i : Fin isa.size)
    (h : sig.opcodeOf w = isa[i].opcode) : decode isa w = some isa[i] := by
  have hc : decodeIdx isa w = decodeIdx isa (encode isa i w) :=
    decodeIdx_congr isa (by rw [h, opcodeOf_encode isa A1.sig_wf])
  rw [decode, hc, decodeIdx_encode isa A1.sig_wf A1.opcodes_distinct,
    Option.map_some]

/-- Decode failure: opcodes ≥ 8 match no declaration. -/
private theorem decode_none {w : sig.Word} (h : 8 ≤ (sig.opcodeOf w).toNat) :
    decode isa w = none := by
  cases hd : decode isa w with
  | none => rfl
  | some d =>
    exfalso
    have hs : (decode isa w).isSome := by rw [hd]; rfl
    rw [isSome_decode_iff] at hs
    obtain ⟨d', hmem, hop⟩ := hs
    have hall : ∀ d ∈ isa, d.opcode.toNat < 8 := by decide
    have hlt : (sig.opcodeOf w).toNat < 8 := hop ▸ hall d' hmem
    omega

/-- The spec step under a successful decode, characterized by the opcode
bits of the fetched word. -/
private theorem step_op (σA : St) (hH : σA.halted = false) (i : Fin isa.size)
    (hopc : sig.opcodeOf (σA.prog σA.pc) = isa[i].opcode) :
    step σA = isa[i].sem (immField.get (σA.prog σA.pc)) σA := by
  rw [step, hH]
  simp only [Bool.false_eq_true, if_false, decode_eq i hopc]

/-- The spec step under decode failure. -/
private theorem step_bad (σA : St) (hH : σA.halted = false)
    (h : 8 ≤ (sig.opcodeOf (σA.prog σA.pc)).toNat) :
    step σA = { σA with halted := true } := by
  rw [step, hH]
  simp only [Bool.false_eq_true, if_false, decode_none h]

/-! ## Semantics of each declaration (definitional) -/

private theorem sem0 : (isa[(⟨0, by decide⟩ : Fin isa.size)]).sem
    = fun _ σ => σ.next := rfl
private theorem sem1 : (isa[(⟨1, by decide⟩ : Fin isa.size)]).sem
    = fun v σ => { σ.next with acc := v } := rfl
private theorem sem2 : (isa[(⟨2, by decide⟩ : Fin isa.size)]).sem
    = fun v σ => { σ.next with acc := σ.acc + v } := rfl
private theorem sem3 : (isa[(⟨3, by decide⟩ : Fin isa.size)]).sem
    = fun a σ => { σ.next with acc := σ.mem a } := rfl
private theorem sem4 : (isa[(⟨4, by decide⟩ : Fin isa.size)]).sem
    = fun a σ => { σ.next with mem := Loom.Fun.update σ.mem a σ.acc } := rfl
private theorem sem5 : (isa[(⟨5, by decide⟩ : Fin isa.size)]).sem
    = fun a σ => if σ.acc = 0 then σ.next else { σ with pc := a } := rfl
private theorem sem6 : (isa[(⟨6, by decide⟩ : Fin isa.size)]).sem
    = fun v σ => { σ.next with acc := σ.acc - v } := rfl
private theorem sem7 : (isa[(⟨7, by decide⟩ : Fin isa.size)]).sem
    = fun _ σ => { σ with halted := true } := rfl

/-! ## Small kit -/

private theorem ite_bv1_eq_one {P : Prop} [Decidable P] :
    ((if P then (1#1 : BitVec 1) else 0#1) = 1#1) ↔ P := by
  split <;> simp_all

/-- The commuting square: a core cycle simulates a spec step. -/
theorem square (σ : Loom.Hw.St) :
    Core.abs ((Core.design (Core.abs σ).prog).cycle σ) = step (Core.abs σ) := by
  rw [cycle_eq]
  by_cases hh : σ.regs "halted" 1 = 1#1
  · -- halted: the rule skips, the spec is a fixed point
    have hrun : execRule.run σ σ = σ := by
      simp [execRule, Act.run, Expr.eval, rHalted, hh]
    rw [hrun, step]
    simp [Core.abs, hh]
  · -- running: dispatch on the opcode of the fetched word
    have hH : (Core.abs σ).halted = false := by
      simp [Core.abs, hh]
    set c : BitVec 8 :=
      (σ.mems "prog" (σ.regs "pc" 8).toNat 16).extractLsb' 0 8 with hc
    have hopcOf : sig.opcodeOf ((Core.abs σ).prog (Core.abs σ).pc) = c := rfl
    -- reduce the rule to the opcode-dispatch chain
    simp only [execRule, Act.run, Expr.eval, rHalted, isOp, opc, fetchW, rPc,
      ite_bv1_eq_one, hh, if_false, ← hc]
    by_cases h0 : c = 0#8
    · rw [step_op _ hH ⟨0, by decide⟩ (hopcOf.trans h0), sem0]
      simp [Core.abs, St.next, Act.run, Expr.eval, pcNext, rPc, RegEnv.set, h0]
    by_cases h1 : c = 1#8
    · rw [step_op _ hH ⟨1, by decide⟩ (hopcOf.trans h1), sem1]
      simp [Core.abs, St.next, Act.run, Expr.eval, pcNext, rPc, imm, fetchW,
        RegEnv.set, immField, Field.get, Loom.Word.extract, h1]
    by_cases h2 : c = 2#8
    · rw [step_op _ hH ⟨2, by decide⟩ (hopcOf.trans h2), sem2]
      simp [Core.abs, St.next, Act.run, Expr.eval, pcNext, rPc, rAcc, imm,
        fetchW, RegEnv.set, immField, Field.get, Loom.Word.extract, h2]
    by_cases h3 : c = 3#8
    · rw [step_op _ hH ⟨3, by decide⟩ (hopcOf.trans h3), sem3]
      simp [Core.abs, St.next, Act.run, Expr.eval, pcNext, rPc, imm, fetchW,
        RegEnv.set, immField, Field.get, Loom.Word.extract, h3]
    by_cases h4 : c = 4#8
    · rw [step_op _ hH ⟨4, by decide⟩ (hopcOf.trans h4), sem4]
      simp [Core.abs, St.next, Act.run, Expr.eval, pcNext, rPc, rAcc, imm,
        fetchW, RegEnv.set, MemEnv.set, immField, Field.get,
        Loom.Word.extract, h4]
      funext a
      by_cases ha : a = (σ.mems "prog" (σ.regs "pc" 8).toNat 16).extractLsb' 8 8
      · simp [ha, Loom.Fun.update]
      · have ha' : ¬ a.toNat =
            ((σ.mems "prog" (σ.regs "pc" 8).toNat 16).extractLsb' 8 8).toNat :=
          fun h => ha (BitVec.eq_of_toNat_eq h)
        simp [Loom.Fun.update, ha]
        intro h
        exact absurd h (by simpa using ha')
    by_cases h5 : c = 5#8
    · rw [step_op _ hH ⟨5, by decide⟩ (hopcOf.trans h5), sem5]
      by_cases hacc : σ.regs "acc" 8 = 0#8
      · simp [Core.abs, St.next, Act.run, Expr.eval, pcNext, rPc, rAcc,
          RegEnv.set, h5, hacc]
      · simp [Core.abs, Expr.eval, rPc, rAcc, imm, fetchW,
          RegEnv.set, immField, Field.get, Loom.Word.extract, h5, hacc]
    by_cases h6 : c = 6#8
    · rw [step_op _ hH ⟨6, by decide⟩ (hopcOf.trans h6), sem6]
      simp [Core.abs, St.next, Act.run, Expr.eval, pcNext, rPc, rAcc, imm,
        fetchW, RegEnv.set, immField, Field.get, Loom.Word.extract, h6]
    by_cases h7 : c = 7#8
    · rw [step_op _ hH ⟨7, by decide⟩ (hopcOf.trans h7), sem7]
      simp [Core.abs, Act.run, Expr.eval, haltNow, RegEnv.set, h7]
    · -- unknown opcode: both sides halt
      have hge : 8 ≤ c.toNat := by
        rcases Nat.lt_or_ge c.toNat 8 with hlt | hge
        · exfalso
          have hcases : c.toNat = 0 ∨ c.toNat = 1 ∨ c.toNat = 2 ∨
              c.toNat = 3 ∨ c.toNat = 4 ∨ c.toNat = 5 ∨ c.toNat = 6 ∨
              c.toNat = 7 := by omega
          have hbv : ∀ k : Nat, k < 8 → c.toNat = k → c = BitVec.ofNat 8 k := by
            intro k hk hck
            apply BitVec.eq_of_toNat_eq
            rw [hck, BitVec.toNat_ofNat]
            omega
          rcases hcases with h | h | h | h | h | h | h | h
          · exact h0 (hbv 0 (by omega) h)
          · exact h1 (hbv 1 (by omega) h)
          · exact h2 (hbv 2 (by omega) h)
          · exact h3 (hbv 3 (by omega) h)
          · exact h4 (hbv 4 (by omega) h)
          · exact h5 (hbv 5 (by omega) h)
          · exact h6 (hbv 6 (by omega) h)
          · exact h7 (hbv 7 (by omega) h)
        · exact hge
      rw [step_bad _ hH (hopcOf ▸ hge)]
      simp [Core.abs, Act.run, Expr.eval, haltNow, RegEnv.set,
        h0, h1, h2, h3, h4, h5, h6]

/-- Reset abstracts to boot. -/
private theorem abs_reset (prog : BitVec 8 → BitVec 16) :
    Core.abs (Core.design prog).reset = boot prog := by
  simp only [Core.abs, Core.design, Design.reset, boot]
  refine St.mk.injEq .. ▸ ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [List.foldl, RegEnv.set]

/-- **A-R.** The core refines the spec. -/
theorem refines (prog : BitVec 8 → BitVec 16) :
    Nonempty (Simulation (machine prog) (Core.design prog).toTSys) := by
  refine ⟨{ abs := Core.abs, init_ok := ?_, square := ?_ }⟩
  · intro s hs
    show Core.abs s = boot prog
    rw [show s = (Core.design prog).reset from hs, abs_reset]
  · intro s s' hstep
    show step (Core.abs s) = Core.abs s'
    rw [← show (Core.design prog).cycle s = s' from hstep]
    exact (square s).symm

end Machines.Acc8.Theorems.AR
