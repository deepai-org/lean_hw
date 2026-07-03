import Loom.Hw.Semantics
import Loom.Emit.MicroVerilog.Semantics

/-!
# The EDSL compiler (L3 → L4 boundary, task 2.2)

Compiles a rule-based `Design` to a µVerilog `Module`: every register's
next-value expression is the fold of the ordered rules' writes into a mux
tree (last write wins — exactly D9's commit semantics), and every memory's
single write port is the analogous guarded fold. Expressions map
structurally (D10).

Correctness (C-HW, stated in `Machines/*/Theorems`): the module's transition
system equals the design's under the evident state conversion.
-/

namespace Loom.Hw.Compile

open Loom.Hw
namespace MV
export Loom.Emit.MicroVerilog (Expr RegDef MemDef OutDef Module St)
end MV

/-- µVerilog expression evaluation, re-exposed for lemma statements. -/
abbrev mvEval {w : Nat} (σ : Loom.Emit.MicroVerilog.St) (e : MV.Expr w) : BitVec w :=
  Loom.Emit.MicroVerilog.Expr.eval σ e

/-- Structural expression translation. -/
def compileExpr : {w : Nat} → Expr w → MV.Expr w
  | _, .lit v => .lit v
  | w, .reg _ n => .reg w n
  | dw, .memRead _ m addr => .memRead dw m (compileExpr addr)
  | _, .and a b => .and (compileExpr a) (compileExpr b)
  | _, .or a b => .or (compileExpr a) (compileExpr b)
  | _, .xor a b => .xor (compileExpr a) (compileExpr b)
  | _, .not a => .not (compileExpr a)
  | _, .add a b => .add (compileExpr a) (compileExpr b)
  | _, .sub a b => .sub (compileExpr a) (compileExpr b)
  | _, .shl a b => .shl (compileExpr a) (compileExpr b)
  | _, .shr a b => .shr (compileExpr a) (compileExpr b)
  | _, .eq a b => .eq (compileExpr a) (compileExpr b)
  | _, .ult a b => .ult (compileExpr a) (compileExpr b)
  | _, .slt a b => .slt (compileExpr a) (compileExpr b)
  | _, .mux c t f => .mux (compileExpr c) (compileExpr t) (compileExpr f)
  | _, .slice a lo width => .slice (compileExpr a) lo width
  | _, .zext a w' => .zext (compileExpr a) w'
  | _, .sext a w' => .sext (compileExpr a) w'

/-- The state conversion between EDSL and µVerilog state (both are
name/width-indexed valuations, so this is definitional on the maps). -/
def convSt (σ : Loom.Hw.St) : MV.St := ⟨σ.regs, σ.mems⟩

/-- Expression translation preserves evaluation. The keystone of the
emission theorem: the compiled combinational logic computes what the source
expression means. -/
theorem compileExpr_eval : ∀ {w : Nat} (e : Expr w) (σ : Loom.Hw.St),
    mvEval (convSt σ) (compileExpr e) = e.eval σ := by
  intro w e
  induction e with
  | lit v => intro σ; rfl
  | reg w n => intro σ; rfl
  | memRead dw m addr ih => intro σ
                            show σ.mems m (mvEval (convSt σ) (compileExpr addr)).toNat dw = _
                            rw [ih σ]; rfl
  | and a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | or a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | xor a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | not a ih => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, ih]
  | add a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | sub a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | shl a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | shr a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | eq a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | ult a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | slt a b iha ihb => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, iha, ihb]
  | mux c t f ihc iht ihf => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, ihc, iht, ihf]
  | slice a lo width ih => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, ih]
  | zext a w' ih => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, ih]
  | sext a w' ih => intro σ; simp [compileExpr, mvEval, Loom.Emit.MicroVerilog.Expr.eval, Expr.eval, ih]

/-- Fold an action into a register's next-value expression: `cur` is the
value the register takes if this action does not write it. -/
def nextReg (r : String) (w : Nat) : Act → MV.Expr w → MV.Expr w
  | .skip, cur => cur
  | .seq a b, cur => nextReg r w b (nextReg r w a cur)
  | .ite c t e, cur =>
      .mux (compileExpr c) (nextReg r w t cur) (nextReg r w e cur)
  | .write w' r' v, cur =>
      if r' = r then
        if h : w' = w then h ▸ compileExpr v else cur
      else cur
  | .memWrite .., cur => cur

/-- A guarded memory write port under construction. -/
structure Port (aw dw : Nat) where
  en   : MV.Expr 1
  addr : MV.Expr aw
  data : MV.Expr dw

/-- Fold an action into a memory's write port (last write wins along each
path; branches merge by mux). -/
def memPort (m : String) (aw dw : Nat) : Act → Port aw dw → Port aw dw
  | .skip, cur => cur
  | .seq a b, cur => memPort m aw dw b (memPort m aw dw a cur)
  | .ite c t e, cur =>
      let ct := memPort m aw dw t cur
      let ce := memPort m aw dw e cur
      let g := compileExpr c
      { en := .mux g ct.en ce.en, addr := .mux g ct.addr ce.addr
        data := .mux g ct.data ce.data }
  | .memWrite aw' dw' m' a v, cur =>
      if m' = m then
        if h : aw' = aw ∧ dw' = dw then
          { en := .lit 1, addr := h.1 ▸ compileExpr a, data := h.2 ▸ compileExpr v }
        else cur
      else cur
  | .write .., cur => cur

/-- Compile a design. Registers become `RegDef`s whose next expression
folds all rules in order; memories get their guarded write port; every
register is exposed as an observability output. -/
def compile (d : Design) : MV.Module where
  name := d.name
  regs := d.regs.map fun r =>
    { name := r.name, width := r.width, init := r.init
      next := d.rules.foldl (fun cur rl => nextReg r.name r.width rl.body cur)
                (.reg r.width r.name) }
  mems := d.mems.map fun m =>
    let port := d.rules.foldl
      (fun cur rl => memPort m.name m.addrWidth m.dataWidth rl.body cur)
      { en := .lit 0, addr := .lit 0, data := .lit 0 }
    { name := m.name, addrWidth := m.addrWidth, dataWidth := m.dataWidth
      init := m.init, wrEn := port.en, wrAddr := port.addr, wrData := port.data }
  outs := d.regs.map fun r =>
    { name := s!"o_{r.name}", width := r.width, val := .reg r.width r.name }


/-! ## Register-fold correctness

The keystone half of the emission theorem: the compiled next-value mux tree
for a register evaluates, under `convSt`, to the value the design's action
writes to that register (last write wins). Proved by induction on actions,
using `compileExpr_eval` at the leaves. -/

open Loom.Emit.MicroVerilog in
/-- Reading a register out of the µVerilog state built from an EDSL state. -/
private theorem convSt_regs (σ : Loom.Hw.St) (rn : String) (w : Nat) :
    (convSt σ).regs rn w = σ.regs rn w := rfl

/-- `nextReg` correctness: the compiled next-value expression evaluates to the
register's post-action value, given the fallback expression `cur` already
reflects the accumulator's current value at that register. -/
theorem nextReg_correct : ∀ (a : Act) (σ acc : Loom.Hw.St) (rn : String) (w : Nat)
    (cur : MV.Expr w), mvEval (convSt σ) cur = acc.regs rn w →
    mvEval (convSt σ) (nextReg rn w a cur) = (a.run σ acc).regs rn w := by
  intro a
  induction a with
  | skip => intro σ acc rn w cur hcur; exact hcur
  | seq x y ihx ihy =>
      intro σ acc rn w cur hcur
      exact ihy σ (x.run σ acc) rn w (nextReg rn w x cur) (ihx σ acc rn w cur hcur)
  | ite c t e iht ihe =>
      intro σ acc rn w cur hcur
      have hce : Loom.Emit.MicroVerilog.Expr.eval (convSt σ) (compileExpr c) = c.eval σ :=
        compileExpr_eval c σ
      show Loom.Emit.MicroVerilog.Expr.eval (convSt σ)
            (.mux (compileExpr c) (nextReg rn w t cur) (nextReg rn w e cur)) = _
      simp only [Loom.Emit.MicroVerilog.Expr.eval, hce]
      by_cases hc : c.eval σ = 1#1
      · simp only [hc, if_true, Act.run]
        exact iht σ acc rn w cur hcur
      · simp only [hc, if_false, Act.run]
        exact ihe σ acc rn w cur hcur
  | write w' r' v =>
      intro σ acc rn w cur hcur
      by_cases hr : r' = rn
      · subst hr
        by_cases hw : w' = w
        · subst hw
          have hlhs : nextReg r' w' (Act.write w' r' v) cur = compileExpr v := by
            simp [nextReg]
          rw [hlhs, show mvEval (convSt σ) (compileExpr v)
                = v.eval σ from compileExpr_eval v σ]
          simp [Act.run, Loom.Hw.RegEnv.set]
        · have hlhs : nextReg r' w (Act.write w' r' v) cur = cur := by
            simp [nextReg, hw]
          rw [hlhs, hcur]
          simp [Act.run, Loom.Hw.RegEnv.set, hw]
      · have hlhs : nextReg rn w (Act.write w' r' v) cur = cur := by
          simp only [nextReg, if_neg hr]
        rw [hlhs, hcur]
        simp only [Act.run, Loom.Hw.RegEnv.set]
        rw [if_neg (fun (h : rn = r') => hr h.symm)]
  | memWrite aw dw mn addr data =>
      intro σ acc rn w cur hcur
      have hlhs : nextReg rn w (Act.memWrite aw dw mn addr data) cur = cur := rfl
      rw [hlhs, hcur]; rfl

end Loom.Hw.Compile
