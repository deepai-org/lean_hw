import Loom.Dp.Bmc

/-!
# k-induction over µVerilog modules (task 1.2d)

Where `Bmc` refutes bounded counterexamples *from reset*, k-induction proves
an **unbounded** invariant from two certificates:

* **base** — `P` holds on the first `k` states of the run (a depth-`(k-1)`
  BMC check, reusing `Bmc.bmc_sound`);
* **step** — for *every* state `s`, if `P` holds on `s, cycle s, …,
  cycle^{k-1} s` then it holds on `cycle^k s` (`kind_step_sound`).

`kinduction_sound` combines them into `∀ n, P.eval (m.run n m.reset) = 1#1`.

The step query is the transition unrolling **without** an init constraint —
its start state is free — plus unit clauses assuming `P` at the first `k`
steps and the negation of `P` at step `k`. The whole assembly is reused from
`Bmc` but generalized over the start state `s0`; the crucial fact that the
*clauses* do not depend on `s0` (only the satisfying assignment does) is
`Cnf.blast_struct`, lifted here to `gBuildSteps_struct` / `gBuildProps_struct`.
So one `s0`-free CNF is checked once, yet its refutation rules out a
counterexample from *any* start — exactly what soundness of the step needs.
-/

namespace Loom.Dp.KInduction

open Loom.Emit.MicroVerilog Loom.Dp.Cnf Loom.Dp.Bmc Loom.Dp.Cert Std.Sat Function

/-! ## Run composition -/

theorem run_add (m : Module) (a b : Nat) (s : St) :
    m.run (a + b) s = m.run a (m.run b s) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 from by omega, run_succ, ih, run_succ]

/-! ## Start-state-generalized transition assembly

These mirror `Bmc.encReg … buildProps` but take an explicit start state
`s0`, so the trace is `m.run · s0` (`Bmc` is the `s0 = m.reset` case). -/

/-- Registers of `f` track the `s0`-run at every step. -/
def GTraceOK (m : Module) (s0 : St) (f : Var → Bool) : Prop :=
  ∀ t nm w bit, f (.reg t nm w bit) = ((m.run t s0).regs nm w).getLsbD bit

theorem GTraceOK.regOK {m : Module} {s0 : St} {f : Var → Bool} (h : GTraceOK m s0 f)
    (t : Nat) : RegOK f (m.run t s0) t := fun nm w bit => h t nm w bit

theorem GTraceOK.of_agree {m : Module} {s0 : St} {f g : Var → Bool} {n : Nat}
    (h : GTraceOK m s0 g) (ha : AgreeLt n f g) : GTraceOK m s0 f :=
  fun t nm w bit => by rw [ha (.reg t nm w bit) trivial]; exact h t nm w bit

/-- One register's transition at step `j` (start `s0`). -/
def gEncReg (m : Module) (s0 : St) (j n : Nat) (f : Var → Bool) (rd : RegDef) :
    BCnf × Nat × (Var → Bool) :=
  let r := blast j (m.run j s0) rd.next n f
  (r.2.1 ++ (List.range rd.width).flatMap (fun i =>
      eqCl (Bit.lit (.reg (j + 1) rd.name rd.width i) true) (r.1.getD i (Bit.const false))),
    r.2.2.1, r.2.2.2)

theorem gEncReg_ok (m : Module) (s0 : St) (j n : Nat) (f : Var → Bool) (rd : RegDef)
    (hf : GTraceOK m s0 f) (hin : rd ∈ m.regs) (hnd : (m.regs.map (·.name)).Nodup) :
    BuildOK n f (gEncReg m s0 j n f rd) := by
  have Ga := blast_spec j (m.run j s0) rd.next n f (hf.regOK j)
  refine ⟨Ga.le, Ga.agree, ?_, ?_⟩
  · intro cl hcl b hb
    rcases List.mem_append.mp hcl with hcl | hcl
    · exact Ga.cnfscope cl hcl b hb
    · obtain ⟨i, _, hcl⟩ := List.mem_flatMap.mp hcl
      exact eqCl_scope (by trivial) (getD_BLt Ga.bitscope i) cl hcl b hb
  · refine Holds.append Ga.holds ?_
    intro cl hcl
    obtain ⟨i, hi, hcl⟩ := List.mem_flatMap.mp hcl
    rw [List.mem_range] at hi
    refine eqCl_holds ?_ cl hcl
    show ((blast j (m.run j s0) rd.next n f).2.2.2 (.reg (j + 1) rd.name rd.width i) == true)
      = Bit.denote (blast j (m.run j s0) rd.next n f).2.2.2
          ((blast j (m.run j s0) rd.next n f).1.getD i (Bit.const false))
    rw [Ga.getD_denote i, Ga.agree (.reg (j + 1) rd.name rd.width i) trivial,
      hf (j + 1) rd.name rd.width i, run_succ, cycle_regs_get m (m.run j s0) rd hin hnd]
    simp

theorem gEncReg_traceOK (m : Module) (s0 : St) (j n : Nat) (f : Var → Bool) (rd : RegDef)
    (hf : GTraceOK m s0 f) (hin : rd ∈ m.regs) (hnd : (m.regs.map (·.name)).Nodup) :
    GTraceOK m s0 (gEncReg m s0 j n f rd).2.2 :=
  hf.of_agree (gEncReg_ok m s0 j n f rd hf hin hnd).agree

/-- Transitions of the registers in `L` at step `j`. -/
def gBuildRegs (m : Module) (s0 : St) (j : Nat) :
    Nat → (Var → Bool) → List RegDef → BCnf × Nat × (Var → Bool)
  | n, f, [] => ([], n, f)
  | n, f, rd :: rest =>
    let r1 := gEncReg m s0 j n f rd
    let r2 := gBuildRegs m s0 j r1.2.1 r1.2.2 rest
    (r1.1 ++ r2.1, r2.2.1, r2.2.2)

theorem gBuildRegs_ok (m : Module) (s0 : St) (j : Nat) (hnd : (m.regs.map (·.name)).Nodup) :
    ∀ (L : List RegDef) (n : Nat) (f : Var → Bool), GTraceOK m s0 f →
    (∀ rd ∈ L, rd ∈ m.regs) →
    BuildOK n f (gBuildRegs m s0 j n f L) ∧ GTraceOK m s0 (gBuildRegs m s0 j n f L).2.2 := by
  intro L
  induction L with
  | nil => intro n f hf _; exact ⟨BuildOK.nil n f, hf⟩
  | cons rd rest ih =>
    intro n f hf hsub
    have hin : rd ∈ m.regs := hsub rd List.mem_cons_self
    have hA := gEncReg_ok m s0 j n f rd hf hin hnd
    have hfA := gEncReg_traceOK m s0 j n f rd hf hin hnd
    obtain ⟨hB, hfB⟩ := ih (gEncReg m s0 j n f rd).2.1 (gEncReg m s0 j n f rd).2.2 hfA
      (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
    exact ⟨hA.append hB, hfB⟩

/-- `count` steps of transitions starting at step `j0`. -/
def gBuildSteps (m : Module) (s0 : St) :
    Nat → Nat → Nat → (Var → Bool) → BCnf × Nat × (Var → Bool)
  | 0, _, n, f => ([], n, f)
  | count + 1, j0, n, f =>
    let r1 := gBuildRegs m s0 j0 n f m.regs
    let r2 := gBuildSteps m s0 count (j0 + 1) r1.2.1 r1.2.2
    (r1.1 ++ r2.1, r2.2.1, r2.2.2)

theorem gBuildSteps_ok (m : Module) (s0 : St) (hnd : (m.regs.map (·.name)).Nodup) :
    ∀ (count j0 n : Nat) (f : Var → Bool), GTraceOK m s0 f →
    BuildOK n f (gBuildSteps m s0 count j0 n f) ∧
      GTraceOK m s0 (gBuildSteps m s0 count j0 n f).2.2 := by
  intro count
  induction count with
  | zero => intro j0 n f hf; exact ⟨BuildOK.nil n f, hf⟩
  | succ count ih =>
    intro j0 n f hf
    obtain ⟨hA, hfA⟩ := gBuildRegs_ok m s0 j0 hnd m.regs n f hf (fun _ h => h)
    obtain ⟨hB, hfB⟩ := ih (j0 + 1) (gBuildRegs m s0 j0 n f m.regs).2.1
      (gBuildRegs m s0 j0 n f m.regs).2.2 hfA
    exact ⟨hA.append hB, hfB⟩

/-- Property blasts at steps `j0 .. j0+count-1` (start `s0`). -/
def gBuildProps (m : Module) (s0 : St) (P : Expr 1) :
    Nat → Nat → Nat → (Var → Bool) → BCnf × List Bit × Nat × (Var → Bool)
  | 0, _, n, f => ([], [], n, f)
  | count + 1, j0, n, f =>
    let r := blast j0 (m.run j0 s0) P n f
    let rest := gBuildProps m s0 P count (j0 + 1) r.2.2.1 r.2.2.2
    (r.2.1 ++ rest.1, (r.1.getD 0 (Bit.const false)) :: rest.2.1, rest.2.2.1, rest.2.2.2)

theorem gBuildProps_ok (m : Module) (s0 : St) (P : Expr 1) :
    ∀ (count j0 n : Nat) (f : Var → Bool), GTraceOK m s0 f →
    n ≤ (gBuildProps m s0 P count j0 n f).2.2.1 ∧
    AgreeLt n (gBuildProps m s0 P count j0 n f).2.2.2 f ∧
    (∀ cl ∈ (gBuildProps m s0 P count j0 n f).1, ∀ b ∈ cl,
      BLt (gBuildProps m s0 P count j0 n f).2.2.1 b) ∧
    Holds (gBuildProps m s0 P count j0 n f).2.2.2 (gBuildProps m s0 P count j0 n f).1 ∧
    GTraceOK m s0 (gBuildProps m s0 P count j0 n f).2.2.2 ∧
    (gBuildProps m s0 P count j0 n f).2.1.length = count ∧
    (∀ idx, idx < count →
      ((gBuildProps m s0 P count j0 n f).2.1.getD idx (Bit.const false)).denote
          (gBuildProps m s0 P count j0 n f).2.2.2
        = (P.eval (m.run (j0 + idx) s0)).getLsbD 0) := by
  intro count
  induction count with
  | zero =>
    intro j0 n f hf
    exact ⟨Nat.le_refl _, fun _ _ => rfl, by intro cl hcl; simp [gBuildProps] at hcl,
      Holds.nil, hf, rfl, by intro idx hidx; omega⟩
  | succ count ih =>
    intro j0 n f hf
    have Gb := blast_spec j0 (m.run j0 s0) P n f (hf.regOK j0)
    have hfr : GTraceOK m s0 (blast j0 (m.run j0 s0) P n f).2.2.2 := hf.of_agree Gb.agree
    obtain ⟨hle, hag, hscope, hh, hfrest, hlen, hval⟩ :=
      ih (j0 + 1) (blast j0 (m.run j0 s0) P n f).2.2.1 (blast j0 (m.run j0 s0) P n f).2.2.2 hfr
    have hfb : gBuildProps m s0 P (count + 1) j0 n f
        = ((blast j0 (m.run j0 s0) P n f).2.1
            ++ (gBuildProps m s0 P count (j0+1) (blast j0 (m.run j0 s0) P n f).2.2.1
                  (blast j0 (m.run j0 s0) P n f).2.2.2).1,
           ((blast j0 (m.run j0 s0) P n f).1.getD 0 (Bit.const false))
            :: (gBuildProps m s0 P count (j0+1) (blast j0 (m.run j0 s0) P n f).2.2.1
                  (blast j0 (m.run j0 s0) P n f).2.2.2).2.1,
           (gBuildProps m s0 P count (j0+1) (blast j0 (m.run j0 s0) P n f).2.2.1
                  (blast j0 (m.run j0 s0) P n f).2.2.2).2.2.1,
           (gBuildProps m s0 P count (j0+1) (blast j0 (m.run j0 s0) P n f).2.2.1
                  (blast j0 (m.run j0 s0) P n f).2.2.2).2.2.2) := rfl
    rw [hfb]
    refine ⟨Nat.le_trans Gb.le hle, (hag.mono Gb.le).trans Gb.agree, ?_, ?_, hfrest,
      by simp [hlen], ?_⟩
    · intro cl hcl b hb
      rcases List.mem_append.mp hcl with hcl | hcl
      · exact BLt.mono hle (Gb.cnfscope cl hcl b hb)
      · exact hscope cl hcl b hb
    · exact Holds.append (Holds_stable hag.symm Gb.cnfscope Gb.holds) hh
    · intro idx hidx
      cases idx with
      | zero =>
        rw [List.getD_cons_zero, denote_stable hag (getD_BLt Gb.bitscope 0), Gb.getD_denote 0]
        simp
      | succ j =>
        rw [List.getD_cons_succ, show j0 + (j + 1) = (j0 + 1) + j from by omega]
        exact hval j (by omega)


/-! ## Start-state independence of the clauses (via `Cnf.blast_struct`) -/

theorem gEncReg_struct (m : Module) (s0 s0' : St) (j n : Nat) (f f' : Var → Bool)
    (rd : RegDef) :
    (gEncReg m s0 j n f rd).1 = (gEncReg m s0' j n f' rd).1 ∧
    (gEncReg m s0 j n f rd).2.1 = (gEncReg m s0' j n f' rd).2.1 := by
  obtain ⟨hbits, hcnf, hcnt⟩ := blast_struct j (m.run j s0) (m.run j s0') rd.next n f f'
  refine ⟨?_, hcnt⟩
  simp only [gEncReg]; rw [hcnf, hbits]

theorem gBuildRegs_struct (m : Module) (s0 s0' : St) (j : Nat) :
    ∀ (L : List RegDef) (n : Nat) (f f' : Var → Bool),
    (gBuildRegs m s0 j n f L).1 = (gBuildRegs m s0' j n f' L).1 ∧
    (gBuildRegs m s0 j n f L).2.1 = (gBuildRegs m s0' j n f' L).2.1 := by
  intro L
  induction L with
  | nil => intro n f f'; exact ⟨rfl, rfl⟩
  | cons rd rest ih =>
    intro n f f'
    obtain ⟨he1, hn1⟩ := gEncReg_struct m s0 s0' j n f f' rd
    obtain ⟨hr, hrn⟩ := ih (gEncReg m s0 j n f rd).2.1 (gEncReg m s0 j n f rd).2.2
      (gEncReg m s0' j n f' rd).2.2
    refine ⟨?_, ?_⟩ <;> simp only [gBuildRegs, ← hn1, he1]
    · rw [hr]
    · rw [hrn]

theorem gBuildSteps_struct (m : Module) (s0 s0' : St) :
    ∀ (count j0 n : Nat) (f f' : Var → Bool),
    (gBuildSteps m s0 count j0 n f).1 = (gBuildSteps m s0' count j0 n f').1 ∧
    (gBuildSteps m s0 count j0 n f).2.1 = (gBuildSteps m s0' count j0 n f').2.1 := by
  intro count
  induction count with
  | zero => intro j0 n f f'; exact ⟨rfl, rfl⟩
  | succ count ih =>
    intro j0 n f f'
    obtain ⟨he1, hn1⟩ := gBuildRegs_struct m s0 s0' j0 m.regs n f f'
    obtain ⟨hr, hrn⟩ := ih (j0 + 1) (gBuildRegs m s0 j0 n f m.regs).2.1
      (gBuildRegs m s0 j0 n f m.regs).2.2 (gBuildRegs m s0' j0 n f' m.regs).2.2
    refine ⟨?_, ?_⟩ <;> simp only [gBuildSteps, ← hn1, he1]
    · rw [hr]
    · rw [hrn]

theorem gBuildProps_struct (m : Module) (s0 s0' : St) (P : Expr 1) :
    ∀ (count j0 n : Nat) (f f' : Var → Bool),
    (gBuildProps m s0 P count j0 n f).1 = (gBuildProps m s0' P count j0 n f').1 ∧
    (gBuildProps m s0 P count j0 n f).2.1 = (gBuildProps m s0' P count j0 n f').2.1 ∧
    (gBuildProps m s0 P count j0 n f).2.2.1 = (gBuildProps m s0' P count j0 n f').2.2.1 := by
  intro count
  induction count with
  | zero => intro j0 n f f'; exact ⟨rfl, rfl, rfl⟩
  | succ count ih =>
    intro j0 n f f'
    obtain ⟨hbits, hcnf, hcnt⟩ := blast_struct j0 (m.run j0 s0) (m.run j0 s0') P n f f'
    obtain ⟨hr1, hr2, hr3⟩ := ih (j0 + 1) (blast j0 (m.run j0 s0) P n f).2.2.1
      (blast j0 (m.run j0 s0) P n f).2.2.2 (blast j0 (m.run j0 s0') P n f').2.2.2
    refine ⟨?_, ?_, ?_⟩ <;> simp only [gBuildProps, ← hcnt, hbits, hcnf]
    · rw [hr1]
    · rw [hr2]
    · rw [hr3]

/-! ## The step query and its soundness -/

/-- The reference start-state model read off the `s0`-run. -/
def gtrace (m : Module) (s0 : St) : Var → Bool
  | .reg t nm w bit => ((m.run t s0).regs nm w).getLsbD bit
  | .aux _ => false

theorem gtrace_ok (m : Module) (s0 : St) : GTraceOK m s0 (gtrace m s0) :=
  fun _ _ _ _ => rfl

/-- Unit clauses assuming `P` holds at steps `0 .. k-1`. -/
def assumeClauses (pbits : List Bit) (k : Nat) : BCnf :=
  (List.range k).map (fun j => [pbits.getD j (Bit.const false)])

/-- The step query built over a specific start `s0` (its clauses are
independent of `s0` — see `kindStepBCnf_at_indep`). -/
def kindStepBCnf_at (m : Module) (P : Expr 1) (k : Nat) (s0 : St) : BCnf :=
  let trans := gBuildSteps m s0 k 0 0 (gtrace m s0)
  let props := gBuildProps m s0 P (k + 1) 0 trans.2.1 trans.2.2
  trans.1 ++ props.1 ++ assumeClauses props.2.1 k
    ++ [[(props.2.1.getD k (Bit.const false)).not]]

/-- The step query is start-state-independent. -/
theorem kindStepBCnf_at_indep (m : Module) (P : Expr 1) (k : Nat) (s0 s0' : St) :
    kindStepBCnf_at m P k s0 = kindStepBCnf_at m P k s0' := by
  obtain ⟨hTc, hTn⟩ := gBuildSteps_struct m s0 s0' k 0 0 (gtrace m s0) (gtrace m s0')
  obtain ⟨hPc, hPp, _⟩ := gBuildProps_struct m s0 s0' P (k + 1) 0
    (gBuildSteps m s0 k 0 0 (gtrace m s0)).2.1 (gBuildSteps m s0 k 0 0 (gtrace m s0)).2.2
    (gBuildSteps m s0' k 0 0 (gtrace m s0')).2.2
  simp only [kindStepBCnf_at, ← hTn, hTc, hPc, hPp]

/-- The k-induction **step** query (variable level): transitions for `k`
steps from a *free* start, `P` assumed at steps `0 .. k-1`, `¬P` at step `k`. -/
def kindStepBCnf (m : Module) (P : Expr 1) (k : Nat) : BCnf :=
  kindStepBCnf_at m P k m.reset

/-- The step query as a `CNF Nat`. -/
def kindStepCnf (m : Module) (P : Expr 1) (k : Nat) : CNF Nat := convCnf (kindStepBCnf m P k)

open Loom.Dp.Cert in
/-- **Soundness of the k-induction step.** An UNSAT certificate for the step
query proves the induction step for *every* start state. -/
theorem kind_step_sound (m : Module) (P : Expr 1) (k : Nat)
    (hnd : (m.regs.map (·.name)).Nodup) (cert : List Check.Step)
    (hchk : Check.check (kindStepCnf m P k) cert = true) :
    ∀ s0, (∀ i, i < k → P.eval (m.run i s0) = 1#1) → P.eval (m.run k s0) = 1#1 := by
  intro s0 hassume
  by_contra hne
  have hbv1 : ∀ x : BitVec 1, x ≠ 1#1 → x.getLsbD 0 = false := by decide
  have hPk : (P.eval (m.run k s0)).getLsbD 0 = false := hbv1 _ hne
  have hf0 : GTraceOK m s0 (gtrace m s0) := gtrace_ok m s0
  set trans := gBuildSteps m s0 k 0 0 (gtrace m s0) with htr
  have hS := gBuildSteps_ok m s0 hnd k 0 0 (gtrace m s0) hf0
  set props := gBuildProps m s0 P (k + 1) 0 trans.2.1 trans.2.2 with hpr
  obtain ⟨hPle, hPag, hPscope, hPholds, hPf, hPlen, hPval⟩ :=
    gBuildProps_ok m s0 P (k + 1) 0 trans.2.1 trans.2.2 hS.2
  rw [← hpr] at hPle hPag hPscope hPholds hPf hPlen hPval
  -- Holds directly against the s0-version of the query
  have hHolds : Holds props.2.2.2 (kindStepBCnf_at m P k s0) := by
    have htrH : Holds props.2.2.2 trans.1 :=
      Holds_stable hPag.symm hS.1.scope hS.1.holds
    have hasH : Holds props.2.2.2 (assumeClauses props.2.1 k) := by
      intro cl hcl
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcl
      rw [List.mem_range] at hj
      refine ⟨props.2.1.getD j (Bit.const false), List.mem_cons_self, ?_⟩
      rw [hPval j (by omega), Nat.zero_add, hassume j hj]; rfl
    have hbadH : Holds props.2.2.2 [[(props.2.1.getD k (Bit.const false)).not]] := by
      intro cl hcl
      rcases List.mem_cons.mp hcl with rfl | hcl
      · refine ⟨(props.2.1.getD k (Bit.const false)).not, List.mem_cons_self, ?_⟩
        rw [Bit.denote_not, hPval k (by omega), Nat.zero_add, hPk]; rfl
      · exact absurd hcl (List.not_mem_nil)
    show Holds props.2.2.2
      (trans.1 ++ props.1 ++ assumeClauses props.2.1 k
        ++ [[(props.2.1.getD k (Bit.const false)).not]])
    exact ((htrH.append hPholds).append hasH).append hbadH
  have hUnsat : CNF.Unsat (kindStepCnf m P k) := Check.check_sound hchk
  have hev : CNF.eval (toNatAssign props.2.2.2) (kindStepCnf m P k) = true := by
    show CNF.eval (toNatAssign props.2.2.2) (convCnf (kindStepBCnf m P k)) = true
    rw [kindStepBCnf, kindStepBCnf_at_indep m P k m.reset s0]
    exact convCnf_eval_of_Holds hHolds
  rw [hUnsat (toNatAssign props.2.2.2)] at hev
  exact absurd hev (by decide)

open Loom.Dp.Cert in
/-- **k-induction soundness.** A base certificate (BMC to depth `k-1`) and a
step certificate together prove `P` is an invariant of the run from reset. -/
theorem kinduction_sound (m : Module) (P : Expr 1) (k : Nat) (hk : 0 < k)
    (hnd : (m.regs.map (·.name)).Nodup)
    (baseCert : List Check.Step)
    (hbase : Check.check (bmcCnf m P (k - 1)) baseCert = true)
    (stepCert : List Check.Step)
    (hstep : Check.check (kindStepCnf m P k) stepCert = true) :
    ∀ n, P.eval (m.run n m.reset) = 1#1 := by
  have hb := bmc_sound m P (k - 1) hnd baseCert hbase
  have hs := kind_step_sound m P k hnd stepCert hstep
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < k
    · exact hb n (by omega)
    · have key := hs (m.run (n - k) m.reset) (fun i hi => by
        rw [← run_add]; exact ih (i + (n - k)) (by omega))
      rw [← run_add, show k + (n - k) = n from by omega] at key
      exact key

end Loom.Dp.KInduction
