import Loom.Hw.Semantics
import Loom.Emit.MicroVerilog.Semantics

/-!
# The EDSL compiler (L3 → L4 boundary, task 2.2)

Compiles a rule-based `Design` to a µVerilog `Module`: every register's
next-value expression is the fold of the ordered rules' writes into a mux
tree (last write wins — exactly D9's commit semantics), and every memory
gets one guarded write port per `Act.memWrite` port index the design uses,
each port the analogous fold over just its own writes. µVerilog commits a
memory's ports in ascending index order, so the compilation is
semantics-preserving when port indices respect the syntactic write order
(`MemWriteWF` below). Expressions map structurally (D10).

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

/-- A guarded memory write port under construction (the compiled artifact
is µVerilog's `WritePort` itself). -/
abbrev Port (aw dw : Nat) := Loom.Emit.MicroVerilog.WritePort aw dw

/-- Fold an action into write port `p` of memory `m`: only the `memWrite`s
carrying port index `p` (and the declared widths) land in this port; last
write wins along each path; branches merge by mux. -/
def memPort (m : String) (aw dw p : Nat) : Act → Port aw dw → Port aw dw
  | .skip, cur => cur
  | .seq a b, cur => memPort m aw dw p b (memPort m aw dw p a cur)
  | .ite c t e, cur =>
      let ct := memPort m aw dw p t cur
      let ce := memPort m aw dw p e cur
      let g := compileExpr c
      { en := .mux g ct.en ce.en, addr := .mux g ct.addr ce.addr
        data := .mux g ct.data ce.data }
  | .memWrite aw' dw' m' p' a v, cur =>
      if m' = m ∧ p' = p then
        if h : aw' = aw ∧ dw' = dw then
          { en := .lit 1, addr := h.1 ▸ compileExpr a, data := h.2 ▸ compileExpr v }
        else cur
      else cur
  | .write .., cur => cur

/-- Port indices of all syntactic writes to memory `m`, in preorder (both
branches of an `ite` contribute, `then` first). The compiler sizes the
emitted memory's port list off this; `MemWriteWF` constrains it. -/
def portTrace (m : String) : Act → List Nat
  | .skip => []
  | .seq a b => portTrace m a ++ portTrace m b
  | .ite _ t e => portTrace m t ++ portTrace m e
  | .memWrite _ _ m' p _ _ => if m' = m then [p] else []
  | .write .. => []

/-- The whole design's port trace for memory `m` (rule order). -/
def designTrace (d : Design) (m : String) : List Nat :=
  d.rules.flatMap fun rl => portTrace m rl.body

/-- Number of write ports the compiled memory `m` gets: one more than the
largest port index the design uses on it (at least one). -/
def numPorts (d : Design) (m : String) : Nat :=
  (designTrace d m).foldr (fun q acc => max (q + 1) acc) 1

/-- The compiled write port `p` of memory `m`: the fold of only the
port-`p` writes across the ordered rule list. -/
def compilePort (d : Design) (m : String) (aw dw p : Nat) : Port aw dw :=
  d.rules.foldl (fun cur rl => memPort m aw dw p rl.body cur)
    { en := .lit 0, addr := .lit 0, data := .lit 0 }

/-- Compile a design. Registers become `RegDef`s whose next expression
folds all rules in order; memories get one guarded write port per used
port index, in ascending order (the µVerilog commit order); every register
is exposed as an observability output. -/
def compile (d : Design) : MV.Module where
  name := d.name
  regs := d.regs.map fun r =>
    { name := r.name, width := r.width, init := r.init
      next := d.rules.foldl (fun cur rl => nextReg r.name r.width rl.body cur)
                (.reg r.width r.name) }
  mems := d.mems.map fun m =>
    { name := m.name, addrWidth := m.addrWidth, dataWidth := m.dataWidth
      init := m.init
      wrPorts := (List.range (numPorts d m.name)).map fun p =>
        compilePort d m.name m.addrWidth m.dataWidth p }
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
  | memWrite aw dw mn p addr data =>
      intro σ acc rn w cur hcur
      have hlhs : nextReg rn w (Act.memWrite aw dw mn p addr data) cur = cur := rfl
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

/-! ## Write-footprint syntax

Syntactic write footprints of actions, and the frame lemmas that go with
them: registers and memories an action never writes are left untouched by
`Act.run` (and by the rule fold). Used to discharge the "undeclared name"
cases of end-to-end emission proofs. -/

/-- Names of the memories an action may write (with multiplicity). -/
def _root_.Loom.Hw.Act.memWrites : Act → List String
  | .skip => []
  | .seq a b => a.memWrites ++ b.memWrites
  | .ite _ t e => t.memWrites ++ e.memWrites
  | .write .. => []
  | .memWrite _ _ m _ _ _ => [m]

/-- `(name, width)` pairs of the registers an action may write. -/
def _root_.Loom.Hw.Act.regWrites : Act → List (String × Nat)
  | .skip => []
  | .seq a b => a.regWrites ++ b.regWrites
  | .ite _ t e => t.regWrites ++ e.regWrites
  | .write w r _ => [(r, w)]
  | .memWrite .. => []

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
  | memWrite aw' dw' m' p' addr v =>
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
        ({ name := m.name, addrWidth := m.addrWidth, dataWidth := m.dataWidth,
           init := m.init,
           wrPorts := (List.range (numPorts d m.name)).map fun p =>
             compilePort d m.name m.addrWidth m.dataWidth p } : MV.MemDef))).foldl
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
/-! ## Memory-fold correctness

The memory half of the emission theorem, per write port. The EDSL semantics
applies a rule's memory writes in run order (last write wins); the compiled
module commits one guarded write port per port index, in ascending order.
The two agree when (`MemWriteWF`):

* every write to the memory carries its declared widths, and
* port indices strictly increase along the design's syntactic write order —
  so each port carries at most one write per cycle, and the ascending
  port-commit order linearizes the run order.

The proof factors through the *write log*: the list of (port, addr, data)
writes the design executes against a pre-cycle state, in run order.
`run_memLog` shows the design's cycle applies the log in order;
`memPort_correct` shows each compiled port evaluates to the log's last
port-`p` entry; `range_commit_applyLog` shows committing ports in ascending
index order replays a port-sorted log exactly. -/

/-- Width discipline: every write to `mn` carries the declared widths. -/
def widthsOk (mn : String) (aw dw : Nat) : Act → Bool
  | .skip => true
  | .seq a b => widthsOk mn aw dw a && widthsOk mn aw dw b
  | .ite _ t e => widthsOk mn aw dw t && widthsOk mn aw dw e
  | .memWrite aw' dw' m' _ _ _ => m' != mn || (aw' == aw && dw' == dw)
  | .write .. => true

/-- **MemWriteWF** — the correctness precondition of the memory half:
declared widths everywhere, and strictly increasing port indices along the
design's syntactic write order. Both decidable per design. -/
structure MemWriteWF (d : Design) (m : MemDecl) : Prop where
  widths : ∀ rl ∈ d.rules, widthsOk m.name m.addrWidth m.dataWidth rl.body
  ports  : (designTrace d m.name).Pairwise (· < ·)

/-- The (port, address, data) writes an action performs on memory `mn` when
run against pre-cycle state `σ`, in execution order (width-mismatched
writes are dropped; `MemWriteWF` rules them out). -/
def memLog (σ : Loom.Hw.St) (mn : String) (aw dw : Nat) :
    Act → List (Nat × BitVec aw × BitVec dw)
  | .skip => []
  | .seq a b => memLog σ mn aw dw a ++ memLog σ mn aw dw b
  | .ite c t e =>
      if c.eval σ = 1#1 then memLog σ mn aw dw t else memLog σ mn aw dw e
  | .memWrite aw' dw' m' p addr data =>
      if m' = mn then
        if h : aw' = aw ∧ dw' = dw then
          [(p, h.1 ▸ addr.eval σ, h.2 ▸ data.eval σ)]
        else []
      else []
  | .write .. => []

/-- The whole design's write log for memory `mn` (rule order). -/
def designLog (d : Design) (σ : Loom.Hw.St) (mn : String) (aw dw : Nat) :
    List (Nat × BitVec aw × BitVec dw) :=
  d.rules.flatMap fun rl => memLog σ mn aw dw rl.body

/-- Apply a write log to memory `mn`, in order. -/
def applyLog (mn : String) {aw dw : Nat}
    (L : List (Nat × BitVec aw × BitVec dw)) (μ : Loom.Hw.MemEnv) :
    Loom.Hw.MemEnv :=
  L.foldl (fun μ e => μ.set mn e.2.1.toNat e.2.2) μ

/-- The last port-`p` entry of a log, defaulting to `o`. -/
def lastP {aw dw : Nat} (p : Nat) (L : List (Nat × BitVec aw × BitVec dw))
    (o : Option (BitVec aw × BitVec dw)) : Option (BitVec aw × BitVec dw) :=
  L.foldl (fun o e => if e.1 = p then some e.2 else o) o

/-- A compiled port triple realizes an optional (address, data) write:
`none` means disabled, `some` means enabled with exactly those values. -/
def Matches (σ : Loom.Hw.St) {aw dw : Nat} (P : Port aw dw)
    (o : Option (BitVec aw × BitVec dw)) : Prop :=
  match o with
  | none => mvEval (convSt σ) P.en = 0#1
  | some (av, dv) =>
      mvEval (convSt σ) P.en = 1#1 ∧ mvEval (convSt σ) P.addr = av
        ∧ mvEval (convSt σ) P.data = dv

theorem lastP_append {aw dw : Nat} (p : Nat)
    (L₁ L₂ : List (Nat × BitVec aw × BitVec dw)) (o) :
    lastP p (L₁ ++ L₂) o = lastP p L₂ (lastP p L₁ o) := by
  unfold lastP; rw [List.foldl_append]

theorem lastP_of_not_mem {aw dw : Nat} (p : Nat)
    (L : List (Nat × BitVec aw × BitVec dw)) :
    ∀ o, p ∉ L.map (·.1) → lastP p L o = o := by
  induction L with
  | nil => intro o _; rfl
  | cons e L ih =>
      intro o h
      rw [List.map_cons, List.mem_cons, not_or] at h
      show lastP p L (if e.1 = p then some e.2 else o) = o
      rw [if_neg (fun he => h.1 he.symm)]
      exact ih _ h.2

/-- **`memPort` correctness (per port).** The compiled port-`p` triple of an
action evaluates to the last port-`p` write of its log. -/
theorem memPort_correct (σ : Loom.Hw.St) (mn : String) (aw dw p : Nat) :
    ∀ (a : Act) (cur : Port aw dw) (o : Option (BitVec aw × BitVec dw)),
      Matches σ cur o →
      Matches σ (memPort mn aw dw p a cur) (lastP p (memLog σ mn aw dw a) o) := by
  intro a
  induction a with
  | skip => intro cur o ho; exact ho
  | seq x y ihx ihy =>
      intro cur o ho
      show Matches σ (memPort mn aw dw p y (memPort mn aw dw p x cur)) _
      rw [show memLog σ mn aw dw (.seq x y)
            = memLog σ mn aw dw x ++ memLog σ mn aw dw y from rfl,
        lastP_append]
      exact ihy _ _ (ihx cur o ho)
  | ite c t e iht ihe =>
      intro cur o ho
      have hce : mvEval (convSt σ) (compileExpr c) = c.eval σ := compileExpr_eval c σ
      rw [show memLog σ mn aw dw (.ite c t e)
            = if c.eval σ = 1#1 then memLog σ mn aw dw t else memLog σ mn aw dw e
          from rfl]
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc]
        have ht := iht cur o ho
        rcases hlp : lastP p (memLog σ mn aw dw t) o with _ | ⟨av, dv⟩ <;>
          rw [hlp] at ht <;>
          simp only [Matches, memPort, mvEval, Loom.Emit.MicroVerilog.Expr.eval,
            hce, hc, if_true] <;> exact ht
      · rw [if_neg hc]
        have he := ihe cur o ho
        rcases hlp : lastP p (memLog σ mn aw dw e) o with _ | ⟨av, dv⟩ <;>
          rw [hlp] at he <;>
          simp only [Matches, memPort, mvEval, Loom.Emit.MicroVerilog.Expr.eval,
            hce, hc, if_false] <;> exact he
  | write w r v => intro cur o ho; exact ho
  | memWrite aw' dw' m' p' addr data =>
      intro cur o ho
      by_cases hm : m' = mn
      · subst hm
        by_cases hwd : aw' = aw ∧ dw' = dw
        · obtain ⟨rfl, rfl⟩ := hwd
          by_cases hp : p' = p
          · subst hp
            show Matches σ (memPort m' aw' dw' p' (.memWrite aw' dw' m' p' addr data) cur) _
            rw [show memLog σ m' aw' dw' (.memWrite aw' dw' m' p' addr data)
                  = [(p', addr.eval σ, data.eval σ)] by
                simp [memLog]]
            rw [show memPort m' aw' dw' p' (.memWrite aw' dw' m' p' addr data) cur
                  = { en := .lit 1, addr := compileExpr addr, data := compileExpr data } by
                simp [memPort]]
            show Matches σ _ (if p' = p' then some (addr.eval σ, data.eval σ) else o)
            rw [if_pos rfl]
            exact ⟨rfl, compileExpr_eval addr σ, compileExpr_eval data σ⟩
          · rw [show memLog σ m' aw' dw' (.memWrite aw' dw' m' p' addr data)
                  = [(p', addr.eval σ, data.eval σ)] by
                simp [memLog]]
            rw [show memPort m' aw' dw' p (.memWrite aw' dw' m' p' addr data) cur = cur by
                simp [memPort, hp]]
            show Matches σ cur (if p' = p then some (addr.eval σ, data.eval σ) else o)
            rw [if_neg hp]
            exact ho
        · rw [show memLog σ m' aw dw (.memWrite aw' dw' m' p' addr data) = [] by
              simp [memLog, hwd]]
          rw [show memPort m' aw dw p (.memWrite aw' dw' m' p' addr data) cur = cur by
              simp [memPort, hwd]]
          exact ho
      · rw [show memLog σ mn aw dw (.memWrite aw' dw' m' p' addr data) = [] by
            simp [memLog, hm]]
        rw [show memPort mn aw dw p (.memWrite aw' dw' m' p' addr data) cur = cur by
            simp [memPort, hm]]
        exact ho

/-- Lifting `memPort_correct` over the ordered rule list. -/
theorem rules_memPort (rules : List Rule) (σ : Loom.Hw.St) (mn : String)
    (aw dw p : Nat) :
    ∀ (cur : Port aw dw) (o : Option (BitVec aw × BitVec dw)),
      Matches σ cur o →
      Matches σ (rules.foldl (fun c rl => memPort mn aw dw p rl.body c) cur)
        (lastP p (rules.flatMap fun rl => memLog σ mn aw dw rl.body) o) := by
  induction rules with
  | nil => intro cur o ho; exact ho
  | cons rl rest ih =>
      intro cur o ho
      rw [List.flatMap_cons, lastP_append, List.foldl_cons]
      exact ih _ _ (memPort_correct σ mn aw dw p rl.body cur o ho)

/-- The compiled port `p` of a design realizes the design log's last
port-`p` write. -/
theorem compilePort_correct (d : Design) (σ : Loom.Hw.St) (mn : String)
    (aw dw p : Nat) :
    Matches σ (compilePort d mn aw dw p)
      (lastP p (designLog d σ mn aw dw) none) :=
  rules_memPort d.rules σ mn aw dw p _ none rfl

/-- `applyLog` reads memory `mn` only at width `dw`: pointwise congruence. -/
theorem applyLog_congr (mn : String) {aw dw : Nat}
    (L : List (Nat × BitVec aw × BitVec dw)) (μ₁ μ₂ : Loom.Hw.MemEnv)
    (h : ∀ x, μ₁ mn x dw = μ₂ mn x dw) :
    ∀ x, applyLog mn L μ₁ mn x dw = applyLog mn L μ₂ mn x dw := by
  induction L generalizing μ₁ μ₂ with
  | nil => exact h
  | cons e L ih =>
      refine ih _ _ (fun x => ?_)
      show (μ₁.set mn e.2.1.toNat e.2.2) mn x dw = (μ₂.set mn e.2.1.toNat e.2.2) mn x dw
      unfold Loom.Hw.MemEnv.set
      by_cases hx : mn = mn ∧ x = e.2.1.toNat
      · rw [if_pos hx, if_pos hx, dif_pos rfl, dif_pos rfl]
      · rw [if_neg hx, if_neg hx]; exact h x

theorem applyLog_append (mn : String) {aw dw : Nat}
    (L₁ L₂ : List (Nat × BitVec aw × BitVec dw)) (μ : Loom.Hw.MemEnv) :
    applyLog mn (L₁ ++ L₂) μ = applyLog mn L₂ (applyLog mn L₁ μ) := by
  unfold applyLog; rw [List.foldl_append]

/-- **Run agrees with the log**: an action's effect on memory `mn` at the
declared width is exactly its write log applied in order. -/
theorem run_memLog (σ : Loom.Hw.St) (mn : String) (aw dw : Nat) :
    ∀ (a : Act) (acc : Loom.Hw.St), widthsOk mn aw dw a → ∀ x,
      (a.run σ acc).mems mn x dw
        = applyLog mn (memLog σ mn aw dw a) acc.mems mn x dw := by
  intro a
  induction a with
  | skip => intro acc _ x; rfl
  | seq a b iha ihb =>
      intro acc hw x
      rw [widthsOk, Bool.and_eq_true] at hw
      show (b.run σ (a.run σ acc)).mems mn x dw = _
      rw [ihb (a.run σ acc) hw.2 x,
        show memLog σ mn aw dw (.seq a b)
          = memLog σ mn aw dw a ++ memLog σ mn aw dw b from rfl,
        applyLog_append]
      exact applyLog_congr mn _ _ _ (fun y => iha acc hw.1 y) x
  | ite c t e iht ihe =>
      intro acc hw x
      rw [widthsOk, Bool.and_eq_true] at hw
      rw [show memLog σ mn aw dw (.ite c t e)
            = if c.eval σ = 1#1 then memLog σ mn aw dw t else memLog σ mn aw dw e
          from rfl]
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc, show (Act.ite c t e).run σ acc = t.run σ acc by
            simp [Act.run, hc]]
        exact iht acc hw.1 x
      · rw [if_neg hc, show (Act.ite c t e).run σ acc = e.run σ acc by
            simp [Act.run, hc]]
        exact ihe acc hw.2 x
  | write w r v => intro acc _ x; rfl
  | memWrite aw' dw' m' p addr data =>
      intro acc hw x
      rw [widthsOk] at hw
      by_cases hm : m' = mn
      · subst hm
        have hwd : aw' = aw ∧ dw' = dw := by simpa using hw
        obtain ⟨rfl, rfl⟩ := hwd
        show (acc.mems.set m' (addr.eval σ).toNat (data.eval σ)) m' x dw' = _
        rw [show memLog σ m' aw' dw' (.memWrite aw' dw' m' p addr data)
              = [(p, addr.eval σ, data.eval σ)] by simp [memLog]]
        rfl
      · show (acc.mems.set m' (addr.eval σ).toNat (data.eval σ)) mn x dw = _
        rw [show memLog σ mn aw dw (.memWrite aw' dw' m' p addr data) = [] by
            simp [memLog, hm]]
        show _ = acc.mems mn x dw
        unfold Loom.Hw.MemEnv.set
        rw [if_neg (fun hc => hm hc.1.symm)]

/-- Lifting `run_memLog` over the ordered rule list. -/
theorem rules_run_memLog (σ : Loom.Hw.St) (mn : String) (aw dw : Nat) :
    ∀ (rules : List Rule) (acc : Loom.Hw.St),
      (∀ rl ∈ rules, widthsOk mn aw dw rl.body) → ∀ x,
      (rules.foldl (fun a rl => rl.body.run σ a) acc).mems mn x dw
        = applyLog mn (rules.flatMap fun rl => memLog σ mn aw dw rl.body)
            acc.mems mn x dw := by
  intro rules
  induction rules with
  | nil => intro acc _ x; rfl
  | cons rl rest ih =>
      intro acc hw x
      rw [List.foldl_cons, List.flatMap_cons, applyLog_append,
        ih (rl.body.run σ acc) (fun r hr => hw r (List.mem_cons_of_mem _ hr)) x]
      exact applyLog_congr mn _ _ _
        (fun y => run_memLog σ mn aw dw rl.body acc (hw rl (List.mem_cons_self ..)) y) x

/-- The executed log's ports are a sublist of the syntactic port trace. -/
theorem memLog_ports_sublist (σ : Loom.Hw.St) (mn : String) (aw dw : Nat) :
    ∀ a : Act, ((memLog σ mn aw dw a).map (·.1)).Sublist (portTrace mn a) := by
  intro a
  induction a with
  | skip => simp [memLog, portTrace]
  | seq a b iha ihb =>
      rw [show memLog σ mn aw dw (.seq a b)
            = memLog σ mn aw dw a ++ memLog σ mn aw dw b from rfl,
        show portTrace mn (.seq a b) = portTrace mn a ++ portTrace mn b from rfl,
        List.map_append]
      exact iha.append ihb
  | ite c t e iht ihe =>
      rw [show memLog σ mn aw dw (.ite c t e)
            = if c.eval σ = 1#1 then memLog σ mn aw dw t else memLog σ mn aw dw e
          from rfl,
        show portTrace mn (.ite c t e) = portTrace mn t ++ portTrace mn e from rfl]
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc]; exact iht.trans (List.sublist_append_left ..)
      · rw [if_neg hc]; exact ihe.trans (List.sublist_append_right ..)
  | write w r v => simp [memLog, portTrace]
  | memWrite aw' dw' m' p addr data =>
      by_cases hm : m' = mn
      · subst hm
        by_cases hwd : aw' = aw ∧ dw' = dw
        · obtain ⟨rfl, rfl⟩ := hwd; simp [memLog, portTrace]
        · simp [memLog, portTrace, hwd]
      · simp [memLog, portTrace, hm]

theorem designLog_ports_sublist (d : Design) (σ : Loom.Hw.St) (mn : String)
    (aw dw : Nat) :
    ((designLog d σ mn aw dw).map (·.1)).Sublist (designTrace d mn) := by
  unfold designLog designTrace
  induction d.rules with
  | nil => simp
  | cons rl rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append]
      exact (memLog_ports_sublist σ mn aw dw rl.body).append ih

/-- Every port index in a list is below the derived port count. -/
theorem lt_foldr_max (L : List Nat) (p : Nat) (hp : p ∈ L) :
    p < L.foldr (fun q acc => max (q + 1) acc) 1 := by
  induction L with
  | nil => cases hp
  | cons q L ih =>
      rcases List.mem_cons.mp hp with rfl | hp'
      · rw [List.foldr_cons]; omega
      · have := ih hp'; rw [List.foldr_cons]; omega

/-! ### Port commits, pointwise -/

/-- Pointwise reading of one committed write port. -/
theorem commit_at {aw dw : Nat} (mn : String) (σmv : MV.St) (P : Port aw dw)
    (μ : Loom.Emit.MicroVerilog.MemEnv) (n : String) (x w : Nat) :
    (P.commit mn σmv μ) n x w
      = if Loom.Emit.MicroVerilog.Expr.eval σmv P.en = 1#1
          ∧ n = mn ∧ x = (Loom.Emit.MicroVerilog.Expr.eval σmv P.addr).toNat ∧ w = dw
        then (Loom.Emit.MicroVerilog.Expr.eval σmv P.data).setWidth w
        else μ n x w := by
  unfold Loom.Emit.MicroVerilog.WritePort.commit
  by_cases hen : Loom.Emit.MicroVerilog.Expr.eval σmv P.en = 1#1
  · rw [if_pos hen]
    show (if n = mn ∧ x = (Loom.Emit.MicroVerilog.Expr.eval σmv P.addr).toNat ∧ w = dw
          then (Loom.Emit.MicroVerilog.Expr.eval σmv P.data).setWidth w
          else μ n x w) = _
    by_cases hc : n = mn ∧ x = (Loom.Emit.MicroVerilog.Expr.eval σmv P.addr).toNat ∧ w = dw
    · rw [if_pos hc, if_pos ⟨hen, hc⟩]
    · rw [if_neg hc, if_neg (fun h => hc h.2)]
  · rw [if_neg hen, if_neg (fun h => hen h.1)]

/-- A disabled port commits nothing. -/
theorem commit_disabled {aw dw : Nat} (mn : String) (σmv : MV.St) (P : Port aw dw)
    (μ : Loom.Emit.MicroVerilog.MemEnv)
    (h : Loom.Emit.MicroVerilog.Expr.eval σmv P.en = 0#1) :
    P.commit mn σmv μ = μ := by
  unfold Loom.Emit.MicroVerilog.WritePort.commit
  rw [if_neg (by rw [h]; decide)]

/-- An enabled port, read at its own memory and declared width. -/
theorem commit_enabled_at {aw dw : Nat} (mn : String) (σmv : MV.St)
    (P : Port aw dw) (μ : Loom.Emit.MicroVerilog.MemEnv)
    (av : BitVec aw) (dv : BitVec dw)
    (hen : Loom.Emit.MicroVerilog.Expr.eval σmv P.en = 1#1)
    (ha : Loom.Emit.MicroVerilog.Expr.eval σmv P.addr = av)
    (hd : Loom.Emit.MicroVerilog.Expr.eval σmv P.data = dv) (x : Nat) :
    (P.commit mn σmv μ) mn x dw = if x = av.toNat then dv else μ mn x dw := by
  rw [commit_at]
  by_cases hx : x = av.toNat
  · rw [if_pos ⟨hen, rfl, by rw [ha]; exact hx, rfl⟩, if_pos hx, hd,
      BitVec.setWidth_eq]
  · rw [if_neg (fun hc => hx (ha ▸ hc.2.2.1)), if_neg hx]

/-- Folding a list of disabled ports commits nothing. -/
theorem foldPorts_disabled {aw dw : Nat} (mn : String) (σmv : MV.St)
    (F : Nat → Port aw dw) :
    ∀ (T : List Nat) (μ : Loom.Emit.MicroVerilog.MemEnv),
      (∀ p ∈ T, Loom.Emit.MicroVerilog.Expr.eval σmv (F p).en = 0#1) →
      T.foldl (fun μ p => (F p).commit mn σmv μ) μ = μ := by
  intro T
  induction T with
  | nil => intro μ _; rfl
  | cons q T ih =>
      intro μ h
      rw [List.foldl_cons, commit_disabled mn σmv (F q) μ (h q (List.mem_cons_self ..))]
      exact ih μ (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- **Ascending port commits replay a port-sorted log.** Committing ports
`0, 1, …, n-1` in order — each realizing the log's last write on that port —
reproduces the log applied in order, provided the log's ports strictly
increase (so commit order linearizes run order) and all lie below `n`. -/
theorem range_commit_applyLog (σ : Loom.Hw.St) (mn : String) {aw dw : Nat}
    (F : Nat → Port aw dw) :
    ∀ (L : List (Nat × BitVec aw × BitVec dw)) (n : Nat),
      (∀ p, p < n → Matches σ (F p) (lastP p L none)) →
      ((L.map (·.1)).Pairwise (· < ·)) →
      (∀ e ∈ L, e.1 < n) →
      ∀ (μ : Loom.Emit.MicroVerilog.MemEnv) (x : Nat),
      ((List.range n).foldl (fun μ p => (F p).commit mn (convSt σ) μ) μ) mn x dw
        = applyLog mn L μ mn x dw := by
  -- reverse induction on the log, done by hand (Loom imports no Mathlib)
  suffices key : ∀ (R : List (Nat × BitVec aw × BitVec dw)) (n : Nat),
      (∀ p, p < n → Matches σ (F p) (lastP p R.reverse none)) →
      ((R.reverse.map (·.1)).Pairwise (· < ·)) →
      (∀ e ∈ R.reverse, e.1 < n) →
      ∀ (μ : Loom.Emit.MicroVerilog.MemEnv) (x : Nat),
      ((List.range n).foldl (fun μ p => (F p).commit mn (convSt σ) μ) μ) mn x dw
        = applyLog mn R.reverse μ mn x dw by
    intro L n hM hS hn μ x
    have h := key L.reverse n (by simpa [List.reverse_reverse] using hM)
      (by simpa [List.reverse_reverse] using hS)
      (by simpa [List.reverse_reverse] using hn) μ x
    simpa [List.reverse_reverse] using h
  intro R
  induction R with
  | nil =>
      intro n hM _ _ μ x
      rw [foldPorts_disabled mn (convSt σ) F (List.range n) μ
        (fun p hp => hM p (List.mem_range.mp hp))]
      rfl
  | cons e R ih =>
      simp only [List.reverse_cons]
      intro n hM hS hn μ x
      -- rename the reversed prefix to L to match the append shape
      generalize hLdef : R.reverse = L at *
      obtain ⟨q, av, dv⟩ := e
      -- port structure of the log
      have hmap : ((L ++ [(q, av, dv)]).map (·.1)) = L.map (·.1) ++ [q] := by
        rw [List.map_append]; rfl
      rw [hmap] at hS
      have hpa := List.pairwise_append.mp hS
      have hLq : ∀ r ∈ L.map (·.1), r < q :=
        fun r hr => hpa.2.2 r hr q (List.mem_singleton_self q)
      have hq : q < n :=
        hn (q, av, dv) (List.mem_append_right _ (List.mem_singleton_self _))
      have hlast : ∀ p, lastP p (L ++ [(q, av, dv)]) none
          = if q = p then some (av, dv) else lastP p L none := by
        intro p; rw [lastP_append]; rfl
      have hMq : Matches σ (F q) (some (av, dv)) := by
        have h := hM q hq; rwa [hlast q, if_pos rfl] at h
      obtain ⟨hen, ha, hd⟩ := hMq
      -- decompose the port range at q
      have hnq : n = q + ((n - q - 1) + 1) := by omega
      have hrange : List.range n
          = List.range q ++ (List.range ((n - q - 1) + 1)).map (q + ·) := by
        conv => lhs; rw [hnq, List.range_add]
      have hsucc : (List.range ((n - q - 1) + 1)).map (q + ·)
          = q :: (List.range (n - q - 1)).map (fun i => q + (i + 1)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        simp only [Function.comp_def, Nat.add_zero, Nat.succ_eq_add_one]
      rw [hrange, hsucc, List.foldl_append, List.foldl_cons]
      -- the ports above q are disabled
      rw [foldPorts_disabled mn (convSt σ) F _ _ (fun p hp => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
        have hik : i < n - q - 1 := List.mem_range.mp hi
        have h := hM (q + (i + 1)) (by omega)
        rwa [hlast, if_neg (by omega),
          lastP_of_not_mem _ _ _ (fun hmem => absurd (hLq _ hmem) (by omega))] at h)]
      -- port q commits the appended write onto the replayed prefix
      rw [commit_enabled_at mn (convSt σ) (F q) _ av dv hen ha hd x, applyLog_append]
      have hIH : ((List.range q).foldl (fun μ p => (F p).commit mn (convSt σ) μ) μ) mn x dw
          = applyLog mn L μ mn x dw :=
        ih q (fun p hp => by
            have h := hM p (by omega)
            rwa [hlast, if_neg (by omega)] at h)
          hpa.1 (fun e' he' => hLq e'.1 (List.mem_map_of_mem he')) μ x
      show (if x = av.toNat then dv else _) = ((applyLog mn L μ).set mn av.toNat dv) mn x dw
      unfold Loom.Hw.MemEnv.set
      by_cases hx : x = av.toNat
      · rw [if_pos hx, if_pos ⟨rfl, hx⟩, dif_pos rfl]
      · rw [if_neg hx, if_neg (fun hc => hx hc.2), hIH]

/-! ### The memory fold over the module's `MemDef` list -/

/-- A port fold reads its own memory only: pointwise congruence. -/
theorem portsFold_congr {aw dw : Nat} (mn : String) (σmv : MV.St)
    (ps : List (Port aw dw)) :
    ∀ (μ₁ μ₂ : Loom.Emit.MicroVerilog.MemEnv),
      (∀ x w, μ₁ mn x w = μ₂ mn x w) →
      ∀ x w, (ps.foldl (fun μ P => P.commit mn σmv μ) μ₁) mn x w
        = (ps.foldl (fun μ P => P.commit mn σmv μ) μ₂) mn x w := by
  induction ps with
  | nil => intro μ₁ μ₂ h x w; exact h x w
  | cons P ps ih =>
      intro μ₁ μ₂ h x w
      refine ih _ _ (fun y v => ?_) x w
      show (P.commit mn σmv μ₁) mn y v = (P.commit mn σmv μ₂) mn y v
      rw [commit_at, commit_at]
      by_cases hc : Loom.Emit.MicroVerilog.Expr.eval σmv P.en = 1#1
          ∧ mn = mn ∧ y = (Loom.Emit.MicroVerilog.Expr.eval σmv P.addr).toNat ∧ v = dw
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]; exact h y v

/-- A port fold touches only its own memory. -/
theorem portsFold_other {aw dw : Nat} (mn n : String) (σmv : MV.St)
    (ps : List (Port aw dw)) (h : n ≠ mn) :
    ∀ (μ : Loom.Emit.MicroVerilog.MemEnv) (x w),
      (ps.foldl (fun μ P => P.commit mn σmv μ) μ) n x w = μ n x w := by
  induction ps with
  | nil => intro μ x w; rfl
  | cons P ps ih =>
      intro μ x w
      rw [List.foldl_cons, ih _ x w, commit_at,
        if_neg (fun hc => h hc.2.1)]

/-- Foreign memories' commits never touch `mn`. -/
theorem memsFold_other (σmv : MV.St) (mn : String) :
    ∀ (mems : List MV.MemDef), (∀ md ∈ mems, md.name ≠ mn) →
    ∀ (μ : Loom.Emit.MicroVerilog.MemEnv) (x w),
      (mems.foldl
          (fun μ md => md.wrPorts.foldl (fun μ p => p.commit md.name σmv μ) μ) μ)
          mn x w
        = μ mn x w := by
  intro mems
  induction mems with
  | nil => intro _ μ x w; rfl
  | cons md rest ih =>
      intro h μ x w
      rw [List.foldl_cons, ih (fun md' h' => h md' (List.mem_cons_of_mem _ h')) _ x w]
      exact portsFold_other md.name mn σmv md.wrPorts
        (fun he => h md (List.mem_cons_self ..) he.symm) μ x w

/-- Fold-lookup under distinct memory names: the module's memory fold reads,
at memory `md0`, exactly `md0`'s own port fold. -/
theorem memsFold_get (σmv : MV.St) (md0 : MV.MemDef) :
    ∀ (mems : List MV.MemDef), md0 ∈ mems → (mems.map (·.name)).Nodup →
    ∀ (μ : Loom.Emit.MicroVerilog.MemEnv) (x w),
      (mems.foldl
          (fun μ md => md.wrPorts.foldl (fun μ p => p.commit md.name σmv μ) μ) μ)
          md0.name x w
        = (md0.wrPorts.foldl (fun μ p => p.commit md0.name σmv μ) μ) md0.name x w := by
  intro mems
  induction mems with
  | nil => intro hin _ _ _ _; exact absurd hin List.not_mem_nil
  | cons md rest ih =>
      intro hin hnd μ x w
      rw [List.map_cons, List.nodup_cons] at hnd
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hin with heq | hmem
      · subst heq
        exact memsFold_other σmv md0.name rest
          (fun md' h' hne => hnd.1 (hne ▸ List.mem_map_of_mem h')) _ x w
      · have hne : md.name ≠ md0.name :=
          fun he => hnd.1 (he ▸ List.mem_map_of_mem hmem)
        rw [ih hmem hnd.2 _ x w]
        exact portsFold_congr md0.name σmv md0.wrPorts _ _
          (fun y v => portsFold_other md.name md0.name σmv md.wrPorts hne.symm μ y v) x w

/-- **The memory half of the emission theorem.** Every memory of the
compiled µVerilog module holds, after one cycle and at every address of its
declared width, exactly the value the design gives it — for every design
with distinct memory names whose write ports are well-formed
(`MemWriteWF`), no per-instruction reasoning. -/
theorem compile_cycle_mems (d : Design) (σ : Loom.Hw.St) (m : MemDecl)
    (hm : m ∈ d.mems) (hnd : (d.mems.map (·.name)).Nodup)
    (hwf : MemWriteWF d m) (x : Nat) :
    ((Loom.Emit.MicroVerilog.Module.cycle (compile d) (convSt σ)).mems
        m.name x m.dataWidth)
      = (d.cycle σ).mems m.name x m.dataWidth := by
  -- the compiled mem def for m
  let md0 : MV.MemDef :=
    { name := m.name, addrWidth := m.addrWidth, dataWidth := m.dataWidth
      init := m.init
      wrPorts := (List.range (numPorts d m.name)).map fun p =>
        compilePort d m.name m.addrWidth m.dataWidth p }
  have hin : md0 ∈ (compile d).mems := by
    unfold compile; exact List.mem_map_of_mem hm
  have hnd' : ((compile d).mems.map (·.name)).Nodup := by
    unfold compile
    simpa [List.map_map, Function.comp] using hnd
  show ((compile d).mems.foldl
      (fun μ md => md.wrPorts.foldl (fun μ p => p.commit md.name (convSt σ) μ) μ)
      (convSt σ).mems) m.name x m.dataWidth = _
  rw [show m.name = md0.name from rfl, show m.dataWidth = md0.dataWidth from rfl,
    memsFold_get (convSt σ) md0 (compile d).mems hin hnd' (convSt σ).mems x md0.dataWidth]
  show (((List.range (numPorts d m.name)).map fun p =>
      compilePort d m.name m.addrWidth m.dataWidth p).foldl
      (fun μ p => p.commit m.name (convSt σ) μ) (convSt σ).mems) m.name x m.dataWidth = _
  rw [List.foldl_map]
  rw [range_commit_applyLog σ m.name
    (fun p => compilePort d m.name m.addrWidth m.dataWidth p)
    (designLog d σ m.name m.addrWidth m.dataWidth) (numPorts d m.name)
    (fun p _ => compilePort_correct d σ m.name m.addrWidth m.dataWidth p)
    (List.Pairwise.sublist (designLog_ports_sublist d σ m.name m.addrWidth m.dataWidth)
      hwf.ports)
    (fun e he => lt_foldr_max (designTrace d m.name) e.1
      ((designLog_ports_sublist d σ m.name m.addrWidth m.dataWidth).subset
        (List.mem_map_of_mem he)))
    (convSt σ).mems x]
  exact (rules_run_memLog σ m.name m.addrWidth m.dataWidth d.rules σ hwf.widths x).symm

/-! ## Off-width preservation

Both semantics observe a memory only at its declared data width; the
entries at every other width are untouched by a cycle. These lemmas extend
`compile_cycle_mems` from the declared width to all widths. -/

/-- Committing the ports of a `dw`-wide memory never touches entries of
`mn` at widths other than `dw`. -/
theorem portsFold_offwidth {aw dw : Nat} (mn : String) (σmv : MV.St)
    (ps : List (Port aw dw)) (w : Nat) (hw : w ≠ dw) :
    ∀ (μ : Loom.Emit.MicroVerilog.MemEnv) (x : Nat),
      (ps.foldl (fun μ P => P.commit mn σmv μ) μ) mn x w = μ mn x w := by
  induction ps with
  | nil => intro μ x; rfl
  | cons P ps ih =>
      intro μ x
      rw [List.foldl_cons, ih _ x, commit_at,
        if_neg (fun hc => hw hc.2.2.2)]

/-- Under the width discipline, running an action leaves memory `mn`'s
entries at widths other than the declared `dw` untouched. -/
theorem run_mems_offwidth (mn : String) (aw dw w : Nat) (hw : w ≠ dw) :
    ∀ (a : Act), widthsOk mn aw dw a →
    ∀ (σ acc : Loom.Hw.St) (x : Nat),
      (a.run σ acc).mems mn x w = acc.mems mn x w := by
  intro a
  induction a with
  | skip => intro _ σ acc x; rfl
  | seq a b iha ihb =>
      intro h σ acc x
      simp only [widthsOk, Bool.and_eq_true] at h
      show (b.run σ (a.run σ acc)).mems mn x w = _
      rw [ihb h.2, iha h.1]
  | ite c t e iht ihe =>
      intro h σ acc x
      simp only [widthsOk, Bool.and_eq_true] at h
      show (if c.eval σ = 1#1 then t.run σ acc else e.run σ acc).mems mn x w = _
      by_cases hc : c.eval σ = 1#1
      · rw [if_pos hc]; exact iht h.1 σ acc x
      · rw [if_neg hc]; exact ihe h.2 σ acc x
  | write => intro _ σ acc x; rfl
  | memWrite aw' dw' m' p' addr v =>
      intro h σ acc x
      show (acc.mems.set m' (addr.eval σ).toNat (v.eval σ)) mn x w = _
      unfold Loom.Hw.MemEnv.set
      by_cases hm : mn = m' ∧ x = (addr.eval σ).toNat
      · have hdw : dw' = dw := by
          simp only [widthsOk, ← hm.1, bne_self_eq_false, Bool.false_or,
            Bool.and_eq_true, beq_iff_eq] at h
          exact h.2
        rw [if_pos hm, dif_neg (fun hc => hw (hdw.symm.trans hc).symm)]
      · rw [if_neg hm]

/-- Fold form of `run_mems_offwidth` over a rule list. -/
theorem rules_run_mems_offwidth (mn : String) (aw dw w : Nat) (hw : w ≠ dw)
    (rules : List Rule) (h : ∀ rl ∈ rules, widthsOk mn aw dw rl.body)
    (σ : Loom.Hw.St) :
    ∀ (acc : Loom.Hw.St) (x : Nat),
      (rules.foldl (fun a rl => rl.body.run σ a) acc).mems mn x w
        = acc.mems mn x w := by
  induction rules with
  | nil => intro acc x; rfl
  | cons rl rest ih =>
      intro acc x
      rw [List.foldl_cons,
        ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) _ x,
        run_mems_offwidth mn aw dw w hw rl.body
          (h rl (List.mem_cons_self ..)) σ acc x]

/-- `compile_cycle_mems` at every width: at the declared data width the two
semantics agree by the memory half of the emission theorem, and at every
other width both leave the entry untouched. -/
theorem compile_cycle_mems_all (d : Design) (σ : Loom.Hw.St) (m : MemDecl)
    (hm : m ∈ d.mems) (hnd : (d.mems.map (·.name)).Nodup)
    (hwf : MemWriteWF d m) (x w : Nat) :
    ((Loom.Emit.MicroVerilog.Module.cycle (compile d) (convSt σ)).mems m.name x w)
      = (d.cycle σ).mems m.name x w := by
  by_cases hww : w = m.dataWidth
  · subst hww; exact compile_cycle_mems d σ m hm hnd hwf x
  · -- the compiled mem def for m
    let md0 : MV.MemDef :=
      { name := m.name, addrWidth := m.addrWidth, dataWidth := m.dataWidth
        init := m.init
        wrPorts := (List.range (numPorts d m.name)).map fun p =>
          compilePort d m.name m.addrWidth m.dataWidth p }
    have hin : md0 ∈ (compile d).mems := by
      unfold compile; exact List.mem_map_of_mem hm
    have hnd' : ((compile d).mems.map (·.name)).Nodup := by
      unfold compile
      simpa [List.map_map, Function.comp] using hnd
    show ((compile d).mems.foldl
        (fun μ md => md.wrPorts.foldl (fun μ p => p.commit md.name (convSt σ) μ) μ)
        (convSt σ).mems) m.name x w = _
    rw [show m.name = md0.name from rfl,
      memsFold_get (convSt σ) md0 (compile d).mems hin hnd' (convSt σ).mems x w]
    rw [portsFold_offwidth md0.name (convSt σ) md0.wrPorts w hww (convSt σ).mems x]
    exact (rules_run_mems_offwidth m.name m.addrWidth m.dataWidth w hww
      d.rules hwf.widths σ σ x).symm

end Loom.Hw.Compile
