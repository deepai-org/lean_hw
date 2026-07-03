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


/-- Lifting `nextReg_correct` over the ordered rule list: the fold of
`nextReg` across all rules evaluates to the register's value after the design
runs every rule in order (each rule reads the pre-cycle state `σ`). -/
theorem rules_nextReg (rules : List Rule) (σ : Loom.Hw.St) (rn : String) (w : Nat) :
    ∀ (acc : Loom.Hw.St) (cur : MV.Expr w),
      mvEval (convSt σ) cur = acc.regs rn w →
      mvEval (convSt σ) (rules.foldl (fun c rl => nextReg rn w rl.body c) cur)
        = (rules.foldl (fun a rl => rl.body.run σ a) acc).regs rn w := by
  induction rules with
  | nil => intro acc cur hcur; exact hcur
  | cons rl rest ih =>
      intro acc cur hcur
      exact ih (rl.body.run σ acc) (nextReg rn w rl.body cur)
        (nextReg_correct rl.body σ acc rn w cur hcur)

/-- A fold of register-`set`s over a list with no entry named `nm` leaves the
value at `nm` untouched. -/
theorem foldl_set_nomatch (L : List MV.RegDef) (ρ0 : Loom.Emit.MicroVerilog.RegEnv)
    (σmv : MV.St) (nm : String) (w : Nat) (h : ∀ rd ∈ L, rd.name ≠ nm) :
    (L.foldl (fun ρ rd => ρ.set rd.name (rd.next.eval σmv)) ρ0) nm w = ρ0 nm w := by
  induction L generalizing ρ0 with
  | nil => rfl
  | cons rd rest ih =>
      rw [List.foldl_cons]
      rw [ih (ρ0.set rd.name (rd.next.eval σmv))
        (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      show (ρ0.set rd.name (rd.next.eval σmv)) nm w = ρ0 nm w
      unfold Loom.Emit.MicroVerilog.RegEnv.set
      rw [if_neg (fun he => h rd (List.mem_cons_self ..) he.symm)]

/-- Fold-lookup under distinct register names: the fold of register-`set`s
returns the target register's own next-value. -/
theorem foldl_set_get (L : List MV.RegDef) (ρ0 : Loom.Emit.MicroVerilog.RegEnv)
    (σmv : MV.St) (rd0 : MV.RegDef) (hin : rd0 ∈ L)
    (hnd : (L.map (·.name)).Nodup) :
    (L.foldl (fun ρ rd => ρ.set rd.name (rd.next.eval σmv)) ρ0) rd0.name rd0.width
      = rd0.next.eval σmv := by
  induction L generalizing ρ0 with
  | nil => exact absurd hin (List.not_mem_nil)
  | cons rd rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hrd, hrest⟩ := hnd
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hin with heq | hmem
      · subst heq
        rw [foldl_set_nomatch rest _ σmv rd0.name rd0.width
          (fun x hx he => hrd (he ▸ List.mem_map_of_mem hx))]
        show (ρ0.set rd0.name (rd0.next.eval σmv)) rd0.name rd0.width = _
        unfold Loom.Emit.MicroVerilog.RegEnv.set
        rw [if_pos rfl, dif_pos rfl]
      · have hne : rd.name ≠ rd0.name := by
          intro he; exact hrd (he ▸ List.mem_map_of_mem hmem)
        exact ih _ hmem hrest

/-- **The register half of the emission theorem.** Every register of the
compiled µVerilog module takes, after one cycle, exactly the value the design
gives it — for every machine with distinct register names, no per-instruction
reasoning. -/
theorem compile_cycle_regs (d : Design) (σ : Loom.Hw.St) (r : RegDecl) (hr : r ∈ d.regs)
    (hnd : (d.regs.map (·.name)).Nodup) :
    ((Loom.Emit.MicroVerilog.Module.cycle (compile d) (convSt σ)).regs r.name r.width)
      = (d.cycle σ).regs r.name r.width := by
  -- the compiled reg def for r
  let rd0 : MV.RegDef :=
    { name := r.name, width := r.width, init := r.init
      next := d.rules.foldl (fun cur rl => nextReg r.name r.width rl.body cur)
                (.reg r.width r.name) }
  have hin : rd0 ∈ (compile d).regs := by
    unfold compile; exact List.mem_map_of_mem hr
  have hnd' : ((compile d).regs.map (·.name)).Nodup := by
    unfold compile
    simpa [List.map_map, Function.comp] using hnd
  show (((compile d).regs.foldl
    (fun ρ x => ρ.set x.name (x.next.eval (convSt σ))) (convSt σ).regs)) r.name r.width = _
  rw [show r.name = rd0.name from rfl, show r.width = rd0.width from rfl,
    foldl_set_get (compile d).regs (convSt σ).regs (convSt σ) rd0 hin hnd']
  show mvEval (convSt σ) rd0.next = (d.cycle σ).regs r.name r.width
  rw [show rd0.next = d.rules.foldl (fun c rl => nextReg r.name r.width rl.body c)
        (.reg r.width r.name) from rfl,
    rules_nextReg d.rules σ r.name r.width σ (.reg r.width r.name) rfl]
  rfl

/-! ## Write-footprint syntax and the memory well-formedness discipline

The EDSL lets an action fire several `memWrite`s to one memory in a cycle
(`Act.run` applies each), while the compiled module has a *single* guarded
write port per memory (`memPort` keeps the last write; branches merge by
mux). The two agree exactly when, along every control path across the whole
ordered rule list, at most one `memWrite` to each memory executes — a
syntactic discipline captured by `Act.memWfFor` (within one action) plus a
`countP ≤ 1` bound across rules. -/

/-- Names of the memories an action may write (with multiplicity). -/
def _root_.Loom.Hw.Act.memWrites : Act → List String
  | .skip => []
  | .seq a b => a.memWrites ++ b.memWrites
  | .ite _ t e => t.memWrites ++ e.memWrites
  | .write .. => []
  | .memWrite _ _ m _ _ => [m]

/-- `(name, width)` pairs of the registers an action may write. -/
def _root_.Loom.Hw.Act.regWrites : Act → List (String × Nat)
  | .skip => []
  | .seq a b => a.regWrites ++ b.regWrites
  | .ite _ t e => t.regWrites ++ e.regWrites
  | .write w r _ => [(r, w)]
  | .memWrite .. => []

/-- Syntactic well-formedness of an action w.r.t. memory `mn` of declared
dimensions `aw × dw`: along every control path at most one `memWrite` to
`mn` executes (a `seq` may mention `mn` on at most one side — the two arms
of an `ite` are separate paths and may both write), and every `memWrite` to
`mn` carries the declared dimensions. Under this discipline the compiled
single write port is faithful to the EDSL's write log. -/
def _root_.Loom.Hw.Act.memWfFor (mn : String) (aw dw : Nat) : Act → Bool
  | .skip => true
  | .seq a b => a.memWfFor mn aw dw && b.memWfFor mn aw dw
      && !(a.memWrites.contains mn && b.memWrites.contains mn)
  | .ite _ t e => t.memWfFor mn aw dw && e.memWfFor mn aw dw
  | .write .. => true
  | .memWrite aw' dw' m _ _ => !(m == mn) || (aw' == aw && dw' == dw)

/-- Running an action that never writes memory `mn` leaves `mn`'s contents
(at every address and width) untouched. -/
theorem run_mems_notin (mn : String) : ∀ (a : Act), mn ∉ a.memWrites →
    ∀ (σ acc : Loom.Hw.St) (ad w : Nat),
      (a.run σ acc).mems mn ad w = acc.mems mn ad w := by
  intro a
  induction a with
  | skip => intro _ σ acc ad w; rfl
  | seq x y ihx ihy =>
      intro h σ acc ad w
      simp only [Act.memWrites, List.mem_append, not_or] at h
      show (y.run σ (x.run σ acc)).mems mn ad w = _
      rw [ihy h.2, ihx h.1]
  | ite c t e iht ihe =>
      intro h σ acc ad w
      simp only [Act.memWrites, List.mem_append, not_or] at h
      show (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).mems mn ad w = _
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc]; exact iht h.1 σ acc ad w
      · rw [if_neg hc]; exact ihe h.2 σ acc ad w
  | write => intro _ σ acc ad w; rfl
  | memWrite aw' dw' m' addr v =>
      intro h σ acc ad w
      have hm : mn ≠ m' := by
        simpa [Act.memWrites] using h
      show (acc.mems.set m' (addr.eval σ).toNat (v.eval σ)) mn ad w = _
      unfold Loom.Hw.MemEnv.set
      rw [if_neg (fun hc => hm hc.1)]

/-- Running an action that never writes register `rn` at width `w` leaves
that entry untouched. -/
theorem run_regs_notin (rn : String) (w : Nat) : ∀ (a : Act),
    (rn, w) ∉ a.regWrites →
    ∀ (σ acc : Loom.Hw.St), (a.run σ acc).regs rn w = acc.regs rn w := by
  intro a
  induction a with
  | skip => intro _ σ acc; rfl
  | seq x y ihx ihy =>
      intro h σ acc
      simp only [Act.regWrites, List.mem_append, not_or] at h
      show (y.run σ (x.run σ acc)).regs rn w = _
      rw [ihy h.2, ihx h.1]
  | ite c t e iht ihe =>
      intro h σ acc
      simp only [Act.regWrites, List.mem_append, not_or] at h
      show (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).regs rn w = _
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc]; exact iht h.1 σ acc
      · rw [if_neg hc]; exact ihe h.2 σ acc
  | write w' r' v =>
      intro h σ acc
      have hp : ¬(r' = rn ∧ w' = w) := by
        intro ⟨h1, h2⟩
        exact h (by simp [Act.regWrites, h1, h2])
      show (acc.regs.set r' (v.eval σ)) rn w = _
      unfold Loom.Hw.RegEnv.set
      by_cases hr : rn = r'
      · rw [if_pos hr]
        have hw : w' ≠ w := fun hw => hp ⟨hr.symm, hw⟩
        rw [dif_neg hw]
      · rw [if_neg hr]
  | memWrite => intro _ σ acc; rfl

/-- Fold form of `run_mems_notin` over a rule list. -/
theorem rules_run_mems_notin (mn : String) (rules : List Rule)
    (h : ∀ rl ∈ rules, mn ∉ rl.body.memWrites) (σ : Loom.Hw.St) :
    ∀ (acc : Loom.Hw.St) (ad w : Nat),
      (rules.foldl (fun a rl => rl.body.run σ a) acc).mems mn ad w
        = acc.mems mn ad w := by
  induction rules with
  | nil => intro acc ad w; rfl
  | cons rl rest ih =>
      intro acc ad w
      rw [List.foldl_cons,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _ ad w,
        run_mems_notin mn rl.body (h rl (List.mem_cons_self ..)) σ acc ad w]

/-- Fold form of `run_regs_notin` over a rule list. -/
theorem rules_run_regs_notin (rn : String) (w : Nat) (rules : List Rule)
    (h : ∀ rl ∈ rules, (rn, w) ∉ rl.body.regWrites) (σ : Loom.Hw.St) :
    ∀ (acc : Loom.Hw.St),
      (rules.foldl (fun a rl => rl.body.run σ a) acc).regs rn w
        = acc.regs rn w := by
  induction rules with
  | nil => intro acc; rfl
  | cons rl rest ih =>
      intro acc
      rw [List.foldl_cons,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        run_regs_notin rn w rl.body (h rl (List.mem_cons_self ..)) σ acc]

/-- Width-aware register-fold preservation: entries whose `(name, width)`
matches no declared register are left untouched by the module's register
fold. -/
theorem foldl_set_preserve (L : List MV.RegDef) (ρ0 : Loom.Emit.MicroVerilog.RegEnv)
    (σmv : MV.St) (nm : String) (w : Nat)
    (h : ∀ rd ∈ L, ¬(rd.name = nm ∧ rd.width = w)) :
    (L.foldl (fun ρ rd => ρ.set rd.name (rd.next.eval σmv)) ρ0) nm w = ρ0 nm w := by
  induction L generalizing ρ0 with
  | nil => rfl
  | cons rd rest ih =>
      rw [List.foldl_cons,
        ih (ρ0.set rd.name (rd.next.eval σmv))
          (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      show (ρ0.set rd.name (rd.next.eval σmv)) nm w = ρ0 nm w
      unfold Loom.Emit.MicroVerilog.RegEnv.set
      have hrd := h rd (List.mem_cons_self ..)
      by_cases hn : nm = rd.name
      · rw [if_pos hn]
        have hw : rd.width ≠ w := fun hw => hrd ⟨hn.symm, hw⟩
        rw [dif_neg hw]
      · rw [if_neg hn]


/-! ## Memory-port correctness

The memory half of the emission theorem, mirroring the register half:
`memPort_correct` is the per-action induction, `rules_memPort` lifts it over
the ordered rule list, the `memFold_*` lemmas resolve the module-side fold
over memory definitions, and `compile_cycle_mems` assembles them. -/

/-- The invariant threaded through the memory-port fold: the accumulator's
contents at memory `mn` are exactly the pre-cycle contents overwritten by
the (at most one) write the port under construction has recorded. -/
def MemAgree (σ : Loom.Hw.St) (mn : String) {aw dw : Nat} (cur : Port aw dw)
    (acc : Loom.Hw.St) : Prop :=
  ∀ (a w : Nat),
    acc.mems mn a w =
      if mvEval (convSt σ) cur.en = 1#1 then
        (σ.mems.set mn (mvEval (convSt σ) cur.addr).toNat
          (mvEval (convSt σ) cur.data)) mn a w
      else σ.mems mn a w

/-- `MemAgree` only sees the port through its three evaluations. -/
theorem MemAgree.congr {σ : Loom.Hw.St} {mn : String} {aw dw : Nat}
    {cur cur' : Port aw dw} {acc : Loom.Hw.St}
    (hen : mvEval (convSt σ) cur'.en = mvEval (convSt σ) cur.en)
    (haddr : mvEval (convSt σ) cur'.addr = mvEval (convSt σ) cur.addr)
    (hdata : mvEval (convSt σ) cur'.data = mvEval (convSt σ) cur.data)
    (h : MemAgree σ mn cur acc) : MemAgree σ mn cur' acc := by
  intro a w
  unfold MemAgree at h
  rw [hen, haddr, hdata]
  exact h a w

/-- Folding an action that never writes `mn` into a port leaves the port's
three evaluations unchanged. -/
theorem memPort_notin_eval (mn : String) (aw dw : Nat) (σmv : MV.St) :
    ∀ (a : Act), mn ∉ a.memWrites → ∀ (cur : Port aw dw),
      mvEval σmv (memPort mn aw dw a cur).en = mvEval σmv cur.en ∧
      mvEval σmv (memPort mn aw dw a cur).addr = mvEval σmv cur.addr ∧
      mvEval σmv (memPort mn aw dw a cur).data = mvEval σmv cur.data := by
  intro a
  induction a with
  | skip => intro _ cur; exact ⟨rfl, rfl, rfl⟩
  | seq x y ihx ihy =>
      intro h cur
      simp only [Act.memWrites, List.mem_append, not_or] at h
      obtain ⟨e1, a1, d1⟩ := ihx h.1 cur
      obtain ⟨e2, a2, d2⟩ := ihy h.2 (memPort mn aw dw x cur)
      exact ⟨e2.trans e1, a2.trans a1, d2.trans d1⟩
  | ite c t e iht ihe =>
      intro h cur
      simp only [Act.memWrites, List.mem_append, not_or] at h
      obtain ⟨et, at', dt⟩ := iht h.1 cur
      obtain ⟨ee, ae, de⟩ := ihe h.2 cur
      have hmux : ∀ {w : Nat} (g : MV.Expr 1) (x y : MV.Expr w) (v : BitVec w),
          mvEval σmv x = v → mvEval σmv y = v →
          mvEval σmv (.mux g x y) = v := by
        intro w g x y v hx hy
        show (if mvEval σmv g = 1#1 then mvEval σmv x else mvEval σmv y) = v
        by_cases hc : mvEval σmv g = 1#1
        · rw [if_pos hc]; exact hx
        · rw [if_neg hc]; exact hy
      exact ⟨hmux _ _ _ _ et ee, hmux _ _ _ _ at' ae, hmux _ _ _ _ dt de⟩
  | write => intro _ cur; exact ⟨rfl, rfl, rfl⟩
  | memWrite aw' dw' m' addr v =>
      intro h cur
      have hm : m' ≠ mn := by simpa [Act.memWrites, eq_comm] using h
      have hp : memPort mn aw dw (.memWrite aw' dw' m' addr v) cur = cur := by
        show (if m' = mn then _ else cur) = cur
        rw [if_neg hm]
      rw [hp]
      exact ⟨rfl, rfl, rfl⟩

/-- The per-action memory-port correctness induction. `hen` records that if
this action is going to write `mn`, no earlier write has fired (the
discipline's cross-rule half); `Act.memWfFor` supplies the within-action
half. -/
theorem memPort_correct (mn : String) (aw dw : Nat) :
    ∀ (a : Act) (σ acc : Loom.Hw.St) (cur : Port aw dw),
      a.memWfFor mn aw dw = true →
      (mn ∈ a.memWrites → mvEval (convSt σ) cur.en ≠ 1#1) →
      MemAgree σ mn cur acc →
      MemAgree σ mn (memPort mn aw dw a cur) (a.run σ acc) := by
  intro a
  induction a with
  | skip => intro σ acc cur _ _ hcur; exact hcur
  | seq x y ihx ihy =>
      intro σ acc cur hwf hen hcur
      simp only [Act.memWfFor, Bool.and_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff] at hwf
      obtain ⟨⟨hwx, hwy⟩, honce⟩ := hwf
      have henx : mn ∈ x.memWrites → mvEval (convSt σ) cur.en ≠ 1#1 :=
        fun hx => hen (List.mem_append_left _ hx)
      have h1 := ihx σ acc cur hwx henx hcur
      have heny : mn ∈ y.memWrites →
          mvEval (convSt σ) (memPort mn aw dw x cur).en ≠ 1#1 := by
        intro hy
        have hxnot : mn ∉ x.memWrites := by
          intro hx
          rcases honce with h | h
          · rw [List.contains_eq_mem, decide_eq_false_iff_not] at h; exact h hx
          · rw [List.contains_eq_mem, decide_eq_false_iff_not] at h; exact h hy
        rw [(memPort_notin_eval mn aw dw (convSt σ) x hxnot cur).1]
        exact hen (List.mem_append_right _ hy)
      exact ihy σ (x.run σ acc) (memPort mn aw dw x cur) hwy heny h1
  | ite c t e iht ihe =>
      intro σ acc cur hwf hen hcur
      simp only [Act.memWfFor, Bool.and_eq_true] at hwf
      have hct := iht σ acc cur hwf.1
        (fun ht => hen (List.mem_append_left _ ht)) hcur
      have hce := ihe σ acc cur hwf.2
        (fun he => hen (List.mem_append_right _ he)) hcur
      have hgc : mvEval (convSt σ) (compileExpr c) = c.eval σ := compileExpr_eval c σ
      show MemAgree σ mn _ (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc)
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc]
        refine MemAgree.congr ?_ ?_ ?_ hct <;>
          · show mvEval (convSt σ) (.mux (compileExpr c) _ _) = _
            simp only [mvEval, Loom.Emit.MicroVerilog.Expr.eval] at hgc ⊢
            rw [hgc, if_pos hc]
      · rw [if_neg hc]
        refine MemAgree.congr ?_ ?_ ?_ hce <;>
          · show mvEval (convSt σ) (.mux (compileExpr c) _ _) = _
            simp only [mvEval, Loom.Emit.MicroVerilog.Expr.eval] at hgc ⊢
            rw [hgc, if_neg hc]
  | write => intro σ acc cur _ _ hcur; exact hcur
  | memWrite aw' dw' m' addr v =>
      intro σ acc cur hwf hen hcur
      by_cases hm : m' = mn
      · subst hm
        have hdim : aw' = aw ∧ dw' = dw := by
          simp only [Act.memWfFor, beq_self_eq_true, Bool.not_true,
            Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hwf
          exact hwf
        obtain ⟨rfl, rfl⟩ := hdim
        have hne : mvEval (convSt σ) cur.en ≠ 1#1 :=
          hen (by simp [Act.memWrites])
        have hacc : ∀ a w, acc.mems m' a w = σ.mems m' a w := by
          intro a w
          have := hcur a w
          rwa [if_neg hne] at this
        show MemAgree σ m' (if m' = m' then _ else cur) _
        rw [if_pos rfl, dif_pos (⟨rfl, rfl⟩ : aw' = aw' ∧ dw' = dw')]
        intro a w
        show (acc.mems.set m' (addr.eval σ).toNat (v.eval σ)) m' a w =
          (σ.mems.set m' (mvEval (convSt σ) (compileExpr addr)).toNat
            (mvEval (convSt σ) (compileExpr v))) m' a w
        rw [compileExpr_eval addr σ, compileExpr_eval v σ]
        unfold Loom.Hw.MemEnv.set
        by_cases hA : m' = m' ∧ a = (addr.eval σ).toNat
        · rw [if_pos hA, if_pos hA]
          by_cases hW : dw' = w
          · rw [dif_pos hW, dif_pos hW]
          · rw [dif_neg hW, dif_neg hW]; exact hacc a w
        · rw [if_neg hA, if_neg hA]; exact hacc a w
      · show MemAgree σ mn (if m' = mn then _ else cur) _
        rw [if_neg hm]
        intro a w
        show (acc.mems.set m' (addr.eval σ).toNat (v.eval σ)) mn a w = _
        unfold Loom.Hw.MemEnv.set
        rw [if_neg (fun hc => hm hc.1.symm)]
        exact hcur a w

/-- Lifting `memPort_correct` over the ordered rule list: at most one rule
may write `mn` (`countP ≤ 1`), each rule is internally well-formed, and no
write has fired before the list starts. -/
theorem rules_memPort (mn : String) (aw dw : Nat) (σ : Loom.Hw.St) :
    ∀ (rules : List Rule) (acc : Loom.Hw.St) (cur : Port aw dw),
      (∀ rl ∈ rules, rl.body.memWfFor mn aw dw = true) →
      rules.countP (fun rl => rl.body.memWrites.contains mn) ≤ 1 →
      ((∃ rl ∈ rules, mn ∈ rl.body.memWrites) → mvEval (convSt σ) cur.en ≠ 1#1) →
      MemAgree σ mn cur acc →
      MemAgree σ mn (rules.foldl (fun c rl => memPort mn aw dw rl.body c) cur)
        (rules.foldl (fun a rl => rl.body.run σ a) acc) := by
  intro rules
  induction rules with
  | nil => intro acc cur _ _ _ hcur; exact hcur
  | cons rl rest ih =>
      intro acc cur hwf honce hen hcur
      rw [List.foldl_cons, List.foldl_cons]
      have h1 := memPort_correct mn aw dw rl.body σ acc cur
        (hwf rl (List.mem_cons_self ..))
        (fun hin => hen ⟨rl, List.mem_cons_self .., hin⟩) hcur
      refine ih (rl.body.run σ acc) (memPort mn aw dw rl.body cur)
        (fun x hx => hwf x (List.mem_cons_of_mem _ hx)) ?_ ?_ h1
      · rw [List.countP_cons] at honce
        omega
      · rintro ⟨rl', hrl', hin'⟩
        have hrest : 0 < rest.countP (fun rl => rl.body.memWrites.contains mn) := by
          rw [List.countP_pos_iff]
          exact ⟨rl', hrl', by
            show rl'.body.memWrites.contains mn = true
            rwa [List.contains_eq_mem, decide_eq_true_iff]⟩
        have hhd : mn ∉ rl.body.memWrites := by
          intro hin
          have hb : rl.body.memWrites.contains mn = true := by
            rwa [List.contains_eq_mem, decide_eq_true_iff]
          simp only [List.countP_cons, hb, if_pos] at honce
          omega
        rw [(memPort_notin_eval mn aw dw (convSt σ) rl.body hhd cur).1]
        exact hen ⟨rl', List.mem_cons_of_mem _ hrl', hin'⟩

/-- The module-side memory fold leaves memories not named in the list
untouched. -/
theorem memFold_nomatch (σmv : MV.St) (nm : String) :
    ∀ (L : List MV.MemDef) (μ0 : Loom.Emit.MicroVerilog.MemEnv),
      (∀ md ∈ L, md.name ≠ nm) → ∀ (a w : Nat),
      (L.foldl
        (fun μ mem =>
          if mem.wrEn.eval σmv = 1#1 then
            fun n a w =>
              if n = mem.name ∧ a = (mem.wrAddr.eval σmv).toNat ∧ w = mem.dataWidth
              then (mem.wrData.eval σmv).setWidth w
              else μ n a w
          else μ)
        μ0) nm a w = μ0 nm a w := by
  intro L
  induction L with
  | nil => intro μ0 _ a w; rfl
  | cons md rest ih =>
      intro μ0 h a w
      rw [List.foldl_cons, ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      by_cases hen : md.wrEn.eval σmv = 1#1
      · rw [if_pos hen]
        exact if_neg (fun hc => h md (List.mem_cons_self ..) hc.1.symm)
      · rw [if_neg hen]

/-- Fold-lookup for the module-side memory fold under distinct memory names:
the fold's value at a declared memory is its own single guarded write applied
to the initial contents. -/
theorem memFold_lookup (σmv : MV.St) :
    ∀ (L : List MV.MemDef) (μ0 : Loom.Emit.MicroVerilog.MemEnv)
      (md0 : MV.MemDef), md0 ∈ L → (L.map (·.name)).Nodup → ∀ (a w : Nat),
      (L.foldl
        (fun μ mem =>
          if mem.wrEn.eval σmv = 1#1 then
            fun n a w =>
              if n = mem.name ∧ a = (mem.wrAddr.eval σmv).toNat ∧ w = mem.dataWidth
              then (mem.wrData.eval σmv).setWidth w
              else μ n a w
          else μ)
        μ0) md0.name a w =
      if md0.wrEn.eval σmv = 1#1 ∧ a = (md0.wrAddr.eval σmv).toNat
          ∧ w = md0.dataWidth
      then (md0.wrData.eval σmv).setWidth w
      else μ0 md0.name a w := by
  intro L
  induction L with
  | nil => intro μ0 md0 hin; exact absurd hin (List.not_mem_nil)
  | cons md rest ih =>
      intro μ0 md0 hin hnd a w
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hhd, hrest⟩ := hnd
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hin with heq | hmem
      · subst heq
        rw [memFold_nomatch σmv md0.name rest _
          (fun x hx he => hhd (he ▸ List.mem_map_of_mem hx))]
        by_cases hen : md0.wrEn.eval σmv = 1#1
        · rw [if_pos hen]
          by_cases haw : a = (md0.wrAddr.eval σmv).toNat ∧ w = md0.dataWidth
          · rw [if_pos ⟨rfl, haw.1, haw.2⟩, if_pos ⟨hen, haw⟩]
          · rw [if_neg (fun hc => haw ⟨hc.2.1, hc.2.2⟩),
              if_neg (fun hc => haw hc.2)]
        · rw [if_neg hen, if_neg (fun hc => hen hc.1)]
      · have hne : md.name ≠ md0.name :=
          fun he => hhd (he ▸ List.mem_map_of_mem hmem)
        rw [ih _ md0 hmem hrest a w]
        by_cases hen0 : md0.wrEn.eval σmv = 1#1 ∧ a = (md0.wrAddr.eval σmv).toNat
            ∧ w = md0.dataWidth
        · rw [if_pos hen0, if_pos hen0]
        · rw [if_neg hen0, if_neg hen0]
          by_cases hen : md.wrEn.eval σmv = 1#1
          · rw [if_pos hen]
            exact if_neg (fun hc => hne hc.1.symm)
          · rw [if_neg hen]

/-- **The memory half of the emission theorem.** Under the memory-write
discipline (each rule internally well-formed for `m`, at most one rule
writing `m`) and distinct memory names, every declared memory of the
compiled module holds, after one cycle, at every address and width, exactly
what the design's cycle gives it. -/
theorem compile_cycle_mems (d : Design) (σ : Loom.Hw.St) (m : MemDecl)
    (hm : m ∈ d.mems) (hnd : (d.mems.map (·.name)).Nodup)
    (hwf : ∀ rl ∈ d.rules, rl.body.memWfFor m.name m.addrWidth m.dataWidth = true)
    (honce : d.rules.countP (fun rl => rl.body.memWrites.contains m.name) ≤ 1)
    (a w : Nat) :
    ((Loom.Emit.MicroVerilog.Module.cycle (compile d) (convSt σ)).mems m.name a w)
      = (d.cycle σ).mems m.name a w := by
  -- the compiled memory definition for m
  let port : Port m.addrWidth m.dataWidth := d.rules.foldl
    (fun cur rl => memPort m.name m.addrWidth m.dataWidth rl.body cur)
    { en := .lit 0, addr := .lit 0, data := .lit 0 }
  let md0 : MV.MemDef :=
    { name := m.name, addrWidth := m.addrWidth, dataWidth := m.dataWidth
      init := m.init, wrEn := port.en, wrAddr := port.addr, wrData := port.data }
  have hin : md0 ∈ (compile d).mems := List.mem_map_of_mem hm
  have hnd' : ((compile d).mems.map (·.name)).Nodup := by
    unfold compile
    simpa [List.map_map, Function.comp] using hnd
  -- module side: resolve the fold to md0's guarded write
  have hmod := memFold_lookup (convSt σ) (compile d).mems (convSt σ).mems md0 hin hnd' a w
  refine hmod.trans ?_
  -- design side: resolve the rule fold through the port invariant
  have h0 : mvEval (convSt σ)
      (({ en := .lit 0, addr := .lit 0, data := .lit 0 } :
        Port m.addrWidth m.dataWidth)).en ≠ 1#1 := by
    show (0#1 : BitVec 1) ≠ 1#1
    decide
  have hd : (d.rules.foldl (fun a rl => rl.body.run σ a) σ).mems m.name a w =
      if mvEval (convSt σ) port.en = 1#1 then
        (σ.mems.set m.name (mvEval (convSt σ) port.addr).toNat
          (mvEval (convSt σ) port.data)) m.name a w
      else σ.mems m.name a w :=
    rules_memPort m.name m.addrWidth m.dataWidth σ d.rules σ
      { en := .lit 0, addr := .lit 0, data := .lit 0 } hwf honce
      (fun _ => h0)
      (fun a w => (if_neg h0).symm) a w
  show _ = (d.rules.foldl (fun a rl => rl.body.run σ a) σ).mems m.name a w
  rw [hd]
  -- equate the two guarded-write forms
  show (if Loom.Emit.MicroVerilog.Expr.eval (convSt σ) port.en = 1#1
      ∧ a = (Loom.Emit.MicroVerilog.Expr.eval (convSt σ) port.addr).toNat
      ∧ w = m.dataWidth
      then (Loom.Emit.MicroVerilog.Expr.eval (convSt σ) port.data).setWidth w
      else σ.mems m.name a w)
    = (if Loom.Emit.MicroVerilog.Expr.eval (convSt σ) port.en = 1#1
      then (σ.mems.set m.name
        (Loom.Emit.MicroVerilog.Expr.eval (convSt σ) port.addr).toNat
        (Loom.Emit.MicroVerilog.Expr.eval (convSt σ) port.data)) m.name a w
      else σ.mems m.name a w)
  by_cases hen : Loom.Emit.MicroVerilog.Expr.eval (convSt σ) port.en = 1#1
  · rw [if_pos hen]
    unfold Loom.Hw.MemEnv.set
    by_cases hA : a = (Loom.Emit.MicroVerilog.Expr.eval (convSt σ) port.addr).toNat
    · by_cases hW : w = m.dataWidth
      · subst hW
        rw [if_pos ⟨hen, hA, rfl⟩, if_pos ⟨rfl, hA⟩, dif_pos rfl,
          BitVec.setWidth_eq]
      · rw [if_neg (fun hc => hW hc.2.2), if_pos ⟨rfl, hA⟩,
          dif_neg (fun hc => hW hc.symm)]
    · rw [if_neg (fun hc => hA hc.2.1), if_neg (fun hc => hA hc.2)]
  · rw [if_neg hen, if_neg (fun hc => hen hc.1)]


/-! ## Reset preservation -/

/-- Compilation preserves the reset state: the module's reset folds are the
design's, entry by entry (the compiled lists carry the same names, widths,
and initial values). -/
theorem compile_reset (d : Design) :
    (compile d).reset = convSt d.reset := by
  have hregs : ∀ (L : List RegDecl) (ρ0 : Loom.Hw.RegEnv),
      (L.map (fun r =>
        ({ name := r.name, width := r.width, init := r.init,
           next := d.rules.foldl
             (fun cur rl => nextReg r.name r.width rl.body cur)
             (.reg r.width r.name) } : MV.RegDef))).foldl
        (fun ρ rd => Loom.Emit.MicroVerilog.RegEnv.set ρ rd.name rd.init) ρ0
      = L.foldl (fun ρ r => Loom.Hw.RegEnv.set ρ r.name r.init) ρ0 := by
    intro L
    induction L with
    | nil => intro ρ0; rfl
    | cons r rest ih =>
        intro ρ0
        rw [List.map_cons, List.foldl_cons, List.foldl_cons, ih]
        rfl
  have hmems : ∀ (L : List MemDecl) (μ0 : Loom.Hw.MemEnv),
      (L.map (fun m =>
        let port := d.rules.foldl
          (fun cur rl => memPort m.name m.addrWidth m.dataWidth rl.body cur)
          { en := .lit 0, addr := .lit 0, data := .lit 0 }
        ({ name := m.name, addrWidth := m.addrWidth, dataWidth := m.dataWidth,
           init := m.init, wrEn := port.en, wrAddr := port.addr,
           wrData := port.data } : MV.MemDef))).foldl
        (fun μ mem => fun n a w =>
          if n = mem.name ∧ w = mem.dataWidth then (mem.init a).setWidth w
          else μ n a w) μ0
      = L.foldl
        (fun μ m => fun n a w =>
          if n = m.name ∧ w = m.dataWidth then (m.init a).setWidth w
          else μ n a w) μ0 := by
    intro L
    induction L with
    | nil => intro μ0; rfl
    | cons m rest ih =>
        intro μ0
        rw [List.map_cons, List.foldl_cons, List.foldl_cons, ih]
  exact congr (congrArg Loom.Emit.MicroVerilog.St.mk
    (hregs d.regs (fun _ w => 0#w))) (hmems d.mems (fun _ _ w => 0#w))

end Loom.Hw.Compile
