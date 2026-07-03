import Loom.Dp.Cnf
import Mathlib

/-!
# Bounded model checking over µVerilog modules (task 1.2c)

`bmcCnf m P k` is a `Std.Sat.CNF Nat` that is **UNSAT iff** the property
`P : Expr 1` cannot be violated within `k` steps of the module's one-cycle
transition relation from the reset state. `bmc_sound` turns a kernel-checked
UNSAT certificate (`Check.check (bmcCnf m P k) cert = true`) into the real
theorem `∀ j ≤ k, P.eval (m.run j m.reset) = 1#1`.

The formula is the classic BMC unrolling:

* **init** — step-0 register bits equal the reset state (unit clauses);
* **transition** — step-`(j+1)` register bits equal the Tseitin encoding of
  each register's next-value expression evaluated at step `j`
  (`Cnf.blast`), for `j < k`;
* **bad** — a single clause asserting `P` is *false* at some step `j ≤ k`.

Soundness is the easy Tseitin direction (`Cnf.blast_spec`): a real
violating trace yields a satisfying assignment, so UNSAT rules it out. The
arithmetic-over-approximation of `blast` (see `Cnf.lean`) means BMC here is
sound but incomplete — it never reports a false "safe", and the certificate
it accepts is a genuine proof of safety up to depth `k`.
-/

namespace Loom.Dp.Bmc

open Loom.Emit.MicroVerilog Loom.Dp.Cnf Std.Sat Function

instance : Nonempty Var := ⟨.aux 0⟩

/-! ## µVerilog cycle/run lemmas -/

/-- `run (j+1)` is one `cycle` applied to `run j` (the def unfolds the other
way). -/
theorem run_succ (m : Module) (n : Nat) (σ : St) :
    m.run (n + 1) σ = m.cycle (m.run n σ) := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    rw [show m.run (n + 2) σ = m.run (n + 1) (m.cycle σ) from rfl, ih (m.cycle σ)]
    rfl

/-- The state at time `j`. -/
abbrev stateAt (m : Module) (j : Nat) : St := m.run j m.reset

theorem stateAt_succ (m : Module) (j : Nat) :
    stateAt m (j + 1) = m.cycle (stateAt m j) := run_succ m j m.reset

/-- A register-fold `set` over a list without name `nm` leaves `nm` alone. -/
theorem foldl_set_nomatch (val : (r : RegDef) → BitVec r.width) (L : List RegDef)
    (ρ0 : RegEnv) (nm : String) (w : Nat) (h : ∀ rd ∈ L, rd.name ≠ nm) :
    (L.foldl (fun ρ r => ρ.set r.name (val r)) ρ0) nm w = ρ0 nm w := by
  induction L generalizing ρ0 with
  | nil => rfl
  | cons rd rest ih =>
    rw [List.foldl_cons,
      ih (ρ0.set rd.name (val rd)) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    show (ρ0.set rd.name (val rd)) nm w = ρ0 nm w
    unfold RegEnv.set
    rw [if_neg (fun he => h rd (List.mem_cons_self ..) he.symm)]

/-- Fold-lookup under distinct register names. -/
theorem foldl_set_get (val : (r : RegDef) → BitVec r.width) (L : List RegDef)
    (ρ0 : RegEnv) (rd0 : RegDef) (hin : rd0 ∈ L) (hnd : (L.map (·.name)).Nodup) :
    (L.foldl (fun ρ r => ρ.set r.name (val r)) ρ0) rd0.name rd0.width = val rd0 := by
  induction L generalizing ρ0 with
  | nil => exact absurd hin (List.not_mem_nil)
  | cons rd rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hrd, hrest⟩ := hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hin with heq | hmem
    · subst heq
      rw [foldl_set_nomatch val rest _ rd0.name rd0.width
        (fun x hx he => hrd (he ▸ List.mem_map_of_mem hx))]
      show (ρ0.set rd0.name (val rd0)) rd0.name rd0.width = _
      unfold RegEnv.set
      rw [if_pos rfl, dif_pos rfl]
    · have hne : rd.name ≠ rd0.name := fun he => hrd (he ▸ List.mem_map_of_mem hmem)
      exact ih _ hmem hrest

/-- After one cycle, a declared register holds its next-value expression. -/
theorem cycle_regs_get (m : Module) (σ : St) (rd : RegDef) (hin : rd ∈ m.regs)
    (hnd : (m.regs.map (·.name)).Nodup) :
    (m.cycle σ).regs rd.name rd.width = rd.next.eval σ :=
  foldl_set_get (fun r => r.next.eval σ) m.regs σ.regs rd hin hnd

/-- The reset state holds each declared register's initial value. -/
theorem reset_regs_get (m : Module) (rd : RegDef) (hin : rd ∈ m.regs)
    (hnd : (m.regs.map (·.name)).Nodup) :
    m.reset.regs rd.name rd.width = rd.init :=
  foldl_set_get (fun r => r.init) m.regs (fun _ w => 0#w) rd hin hnd

/-! ## Injective renaming `Var → Nat` and model transport -/

/-- An injective encoding of `String` into `Nat` (Encodable of the toNat
character list). -/
def strNat (s : String) : Nat := Encodable.encode (s.toList.map Char.toNat)

theorem strNat_injective : Injective strNat := by
  intro a b h
  have h1 := Encodable.encode_injective h
  have hc : Injective Char.toNat := fun x y hxy => Char.ext (UInt32.toNat_inj.mp hxy)
  exact String.toList_inj.mp (hc.list_map h1)

/-- An injective encoding of a CNF `Var` into `Nat`. Constructor tag in the
low bit; `reg`'s four fields paired; `aux`'s id shifted. -/
def rename : Var → Nat
  | .reg t nm w bit => 2 * (Nat.pair t (Nat.pair (strNat nm) (Nat.pair w bit)))
  | .aux id => 2 * id + 1

theorem rename_injective : Function.Injective rename := by
  intro a b h
  cases a with
  | reg t nm w bit =>
    cases b with
    | reg t' nm' w' bit' =>
      simp only [rename] at h
      have h' : Nat.pair t (Nat.pair (strNat nm) (Nat.pair w bit))
        = Nat.pair t' (Nat.pair (strNat nm') (Nat.pair w' bit')) := by omega
      obtain ⟨ht, e1⟩ := Nat.pair_eq_pair.mp h'
      obtain ⟨hs, e2⟩ := Nat.pair_eq_pair.mp e1
      obtain ⟨hw, hbit⟩ := Nat.pair_eq_pair.mp e2
      have hnm : nm = nm' := strNat_injective hs
      subst ht; subst hnm; subst hw; subst hbit; rfl
    | aux id => simp only [rename] at h; omega
  | aux id =>
    cases b with
    | reg t' nm' w' bit' => simp only [rename] at h; omega
    | aux id' =>
      simp only [rename] at h
      have : id = id' := by omega
      subst this; rfl

/-! ## `BCnf → CNF Nat` conversion (drop tautological clauses / false bits) -/

/-- Convert one clause, dropping tautological (`const true`) clauses and
`const false` bits. -/
def convClause (cl : BClause) : Option (CNF.Clause Nat) :=
  if cl.any (fun b => b == Bit.const true) then none
  else some (cl.filterMap (fun b => match b with
    | .lit v pol => some (rename v, pol)
    | .const _ => none))

/-- Convert a `BCnf` to `CNF Nat`. -/
def convCnf (L : BCnf) : CNF Nat := L.filterMap convClause

open Function in
/-- The `Nat`-model induced by a `Var`-model through the (injective)
renaming. -/
noncomputable def toNatAssign (f : Var → Bool) : Nat → Bool :=
  fun k => f (invFun rename k)

theorem toNatAssign_rename (f : Var → Bool) (v : Var) :
    toNatAssign f (rename v) = f v := by
  unfold toNatAssign
  rw [Function.leftInverse_invFun rename_injective v]

/-- A `Var`-model of the `BCnf` is a `Nat`-model of its conversion. -/
theorem convCnf_eval_of_Holds {f : Var → Bool} {L : BCnf} (h : Holds f L) :
    CNF.eval (toNatAssign f) (convCnf L) = true := by
  rw [CNF.eval, List.all_eq_true]
  intro c' hc'
  obtain ⟨cl, hcl, hconv⟩ := List.mem_filterMap.mp hc'
  -- cl has no const-true bit (else convClause = none)
  unfold convClause at hconv
  split at hconv
  · cases hconv
  · rename_i hnot
    injection hconv with hconv; subst hconv
    obtain ⟨b, hb, hbd⟩ := h cl hcl
    -- b is a satisfied bit; it must be a lit
    cases b with
    | const c =>
      cases c with
      | true =>
        simp only [List.any_eq_true, not_exists] at hnot
        exact absurd (hnot (Bit.const true) ⟨hb, by simp⟩) (by simp)
      | false => simp [Bit.denote] at hbd
    | lit v pol =>
      rw [CNF.Clause.eval, List.any_eq_true]
      refine ⟨(rename v, pol), ?_, ?_⟩
      · exact List.mem_filterMap.mpr ⟨.lit v pol, hb, rfl⟩
      · simp only [toNatAssign_rename]
        simpa [Bit.denote] using hbd


/-! ## Transition/BMC assembly

Everything below threads a monotone aux counter `n` and an assignment `f`
in the same style as `Cnf.blast`, so the pieces compose (`BuildOK.append`)
and one global assignment satisfies the whole unrolling. -/

/-- An equality constraint between two bits: `[[x, ¬y], [¬x, y]]`. -/
def eqCl (x y : Bit) : BCnf := [[x, y.not], [x.not, y]]

theorem eqCl_holds {x y : Bit} {f : Var → Bool} (h : x.denote f = y.denote f) :
    Holds f (eqCl x y) := by
  intro cl hcl
  simp only [eqCl, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · rcases hx : x.denote f with _ | _
    · exact ⟨y.not, by simp, by simp [Bit.denote_not, ← h, hx]⟩
    · exact ⟨x, by simp, hx⟩
  · rcases hy : y.denote f with _ | _
    · exact ⟨x.not, by simp, by simp [Bit.denote_not, h, hy]⟩
    · exact ⟨y, by simp, hy⟩

theorem eqCl_scope {n : Nat} {x y : Bit} (hx : BLt n x) (hy : BLt n y) :
    ∀ cl ∈ eqCl x y, ∀ b ∈ cl, BLt n b := by
  intro cl hcl b hb
  simp only [eqCl, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl <;>
    (simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
     rcases hb with rfl | rfl) <;> first | exact hx | exact hy | exact hx.not | exact hy.not

/-- The registers of `f` track the real trace at every step. -/
def TraceOK (f : Var → Bool) (m : Module) : Prop :=
  ∀ t nm w bit, f (.reg t nm w bit) = ((stateAt m t).regs nm w).getLsbD bit

theorem TraceOK.regOK {f : Var → Bool} {m : Module} (h : TraceOK f m) (t : Nat) :
    RegOK f (stateAt m t) t := fun nm w bit => h t nm w bit

theorem TraceOK.of_agree {f g : Var → Bool} {m : Module} {n : Nat}
    (h : TraceOK g m) (ha : AgreeLt n f g) : TraceOK f m :=
  fun t nm w bit => by rw [ha (.reg t nm w bit) trivial]; exact h t nm w bit

/-- The compositional invariant of the assembly. -/
structure BuildOK (n : Nat) (f0 : Var → Bool) (res : BCnf × Nat × (Var → Bool)) :
    Prop where
  le : n ≤ res.2.1
  agree : AgreeLt n res.2.2 f0
  scope : ∀ cl ∈ res.1, ∀ b ∈ cl, BLt res.2.1 b
  holds : Holds res.2.2 res.1

theorem BuildOK.nil (n : Nat) (f0 : Var → Bool) : BuildOK n f0 ([], n, f0) :=
  ⟨Nat.le_refl _, fun _ _ => rfl, by intro cl hcl; simp at hcl, Holds.nil⟩

/-- Two builds whose second starts where the first ends compose. -/
theorem BuildOK.append {n : Nat} {f0 : Var → Bool}
    {rA : BCnf × Nat × (Var → Bool)} (hA : BuildOK n f0 rA)
    {rB : BCnf × Nat × (Var → Bool)} (hB : BuildOK rA.2.1 rA.2.2 rB) :
    BuildOK n f0 (rA.1 ++ rB.1, rB.2.1, rB.2.2) := by
  refine ⟨Nat.le_trans hA.le hB.le, (hB.agree.mono hA.le).trans hA.agree, ?_, ?_⟩
  · intro cl hcl b hb
    rcases List.mem_append.mp hcl with hcl | hcl
    · exact BLt.mono hB.le (hA.scope cl hcl b hb)
    · exact hB.scope cl hcl b hb
  · exact Holds.append (Holds_stable hB.agree.symm hA.scope hA.holds) hB.holds

/-! ### Per-register transition encoding -/

/-- Encode one register's transition at step `j`: blast its next-value
expression, then equate step-`(j+1)` register bits to the blasted bits. -/
def encReg (m : Module) (j : Nat) (n : Nat) (f : Var → Bool) (rd : RegDef) :
    BCnf × Nat × (Var → Bool) :=
  let r := blast j (stateAt m j) rd.next n f
  (r.2.1 ++ (List.range rd.width).flatMap (fun i =>
      eqCl (Bit.lit (.reg (j + 1) rd.name rd.width i) true) (r.1.getD i (Bit.const false))),
    r.2.2.1, r.2.2.2)

theorem encReg_ok (m : Module) (j n : Nat) (f : Var → Bool) (rd : RegDef)
    (hf : TraceOK f m) (hin : rd ∈ m.regs) (hnd : (m.regs.map (·.name)).Nodup) :
    BuildOK n f (encReg m j n f rd) := by
  have Ga := blast_spec j (stateAt m j) rd.next n f (hf.regOK j)
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
    show ((blast j (stateAt m j) rd.next n f).2.2.2 (.reg (j + 1) rd.name rd.width i) == true)
      = Bit.denote (blast j (stateAt m j) rd.next n f).2.2.2
          ((blast j (stateAt m j) rd.next n f).1.getD i (Bit.const false))
    rw [Ga.getD_denote i, Ga.agree (.reg (j + 1) rd.name rd.width i) trivial,
      hf (j + 1) rd.name rd.width i, stateAt_succ, cycle_regs_get m (stateAt m j) rd hin hnd]
    simp

theorem encReg_traceOK (m : Module) (j n : Nat) (f : Var → Bool) (rd : RegDef)
    (hf : TraceOK f m) (hin : rd ∈ m.regs) (hnd : (m.regs.map (·.name)).Nodup) :
    TraceOK (encReg m j n f rd).2.2 m :=
  hf.of_agree (encReg_ok m j n f rd hf hin hnd).agree

/-! ### Fold over a step's registers, then over steps -/

/-- Encode the transitions of the registers in `L` at step `j`. -/
def buildRegs (m : Module) (j : Nat) : Nat → (Var → Bool) → List RegDef →
    BCnf × Nat × (Var → Bool)
  | n, f, [] => ([], n, f)
  | n, f, rd :: rest =>
    let r1 := encReg m j n f rd
    let r2 := buildRegs m j r1.2.1 r1.2.2 rest
    (r1.1 ++ r2.1, r2.2.1, r2.2.2)

theorem buildRegs_ok (m : Module) (j : Nat) (hnd : (m.regs.map (·.name)).Nodup) :
    ∀ (L : List RegDef) (n : Nat) (f : Var → Bool), TraceOK f m →
    (∀ rd ∈ L, rd ∈ m.regs) →
    BuildOK n f (buildRegs m j n f L) ∧ TraceOK (buildRegs m j n f L).2.2 m := by
  intro L
  induction L with
  | nil => intro n f hf _; exact ⟨BuildOK.nil n f, hf⟩
  | cons rd rest ih =>
    intro n f hf hsub
    have hin : rd ∈ m.regs := hsub rd List.mem_cons_self
    have hA := encReg_ok m j n f rd hf hin hnd
    have hfA := encReg_traceOK m j n f rd hf hin hnd
    obtain ⟨hB, hfB⟩ := ih (encReg m j n f rd).2.1 (encReg m j n f rd).2.2 hfA
      (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
    exact ⟨hA.append hB, hfB⟩

/-- Encode `count` steps of transitions starting at step `j0`. -/
def buildSteps (m : Module) : Nat → Nat → Nat → (Var → Bool) → BCnf × Nat × (Var → Bool)
  | 0, _, n, f => ([], n, f)
  | count + 1, j0, n, f =>
    let r1 := buildRegs m j0 n f m.regs
    let r2 := buildSteps m count (j0 + 1) r1.2.1 r1.2.2
    (r1.1 ++ r2.1, r2.2.1, r2.2.2)

theorem buildSteps_ok (m : Module) (hnd : (m.regs.map (·.name)).Nodup) :
    ∀ (count j0 n : Nat) (f : Var → Bool), TraceOK f m →
    BuildOK n f (buildSteps m count j0 n f) ∧ TraceOK (buildSteps m count j0 n f).2.2 m := by
  intro count
  induction count with
  | zero => intro j0 n f hf; exact ⟨BuildOK.nil n f, hf⟩
  | succ count ih =>
    intro j0 n f hf
    obtain ⟨hA, hfA⟩ := buildRegs_ok m j0 hnd m.regs n f hf (fun _ h => h)
    obtain ⟨hB, hfB⟩ := ih (j0 + 1) (buildRegs m j0 n f m.regs).2.1
      (buildRegs m j0 n f m.regs).2.2 hfA
    exact ⟨hA.append hB, hfB⟩

/-! ### Init clauses, property clauses, and the assembled formula -/

/-- The reference assignment read off the real trace. -/
def traceAssign (m : Module) : Var → Bool
  | .reg t nm w bit => ((stateAt m t).regs nm w).getLsbD bit
  | .aux _ => false

theorem traceAssign_traceOK (m : Module) : TraceOK (traceAssign m) m :=
  fun _ _ _ _ => rfl

/-- Unit clauses pinning the step-0 register bits to the reset state. -/
def initClauses (m : Module) : BCnf :=
  m.regs.flatMap (fun rd => (List.range rd.width).map (fun i =>
    [Bit.lit (.reg 0 rd.name rd.width i) (rd.init.getLsbD i)]))

theorem initClauses_holds (m : Module) (hnd : (m.regs.map (·.name)).Nodup)
    {f : Var → Bool} (hf : TraceOK f m) : Holds f (initClauses m) := by
  intro cl hcl
  obtain ⟨rd, hrd, hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hcl
  refine ⟨_, List.mem_cons_self, ?_⟩
  show (f (.reg 0 rd.name rd.width i) == rd.init.getLsbD i) = true
  rw [hf 0 rd.name rd.width i, show stateAt m 0 = m.reset from rfl,
    reset_regs_get m rd hrd hnd]
  simp

/-- Blast the property `P` at steps `j0 .. j0+count-1`, collecting per-step
property bits. -/
def buildProps (m : Module) (P : Expr 1) :
    Nat → Nat → Nat → (Var → Bool) → BCnf × List Bit × Nat × (Var → Bool)
  | 0, _, n, f => ([], [], n, f)
  | count + 1, j0, n, f =>
    let r := blast j0 (stateAt m j0) P n f
    let rest := buildProps m P count (j0 + 1) r.2.2.1 r.2.2.2
    (r.2.1 ++ rest.1, (r.1.getD 0 (Bit.const false)) :: rest.2.1, rest.2.2.1, rest.2.2.2)

theorem buildProps_ok (m : Module) (P : Expr 1) :
    ∀ (count j0 n : Nat) (f : Var → Bool), TraceOK f m →
    n ≤ (buildProps m P count j0 n f).2.2.1 ∧
    AgreeLt n (buildProps m P count j0 n f).2.2.2 f ∧
    (∀ cl ∈ (buildProps m P count j0 n f).1, ∀ b ∈ cl,
      BLt (buildProps m P count j0 n f).2.2.1 b) ∧
    Holds (buildProps m P count j0 n f).2.2.2 (buildProps m P count j0 n f).1 ∧
    TraceOK (buildProps m P count j0 n f).2.2.2 m ∧
    (buildProps m P count j0 n f).2.1.length = count ∧
    (∀ idx, idx < count →
      ((buildProps m P count j0 n f).2.1.getD idx (Bit.const false)).denote
          (buildProps m P count j0 n f).2.2.2
        = (P.eval (stateAt m (j0 + idx))).getLsbD 0) := by
  intro count
  induction count with
  | zero =>
    intro j0 n f hf
    exact ⟨Nat.le_refl _, fun _ _ => rfl, by intro cl hcl; simp [buildProps] at hcl,
      Holds.nil, hf, rfl, by intro idx hidx; omega⟩
  | succ count ih =>
    intro j0 n f hf
    have Ga := blast_spec j0 (stateAt m j0) P (buildProps m P (count+1) j0 n f).2.2.1 f
    -- unfold to the recursive tuple
    set r := blast j0 (stateAt m j0) P n f with hr
    have hfr : TraceOK r.2.2.2 m := hf.of_agree (blast_spec j0 (stateAt m j0) P n f (hf.regOK j0)).agree
    obtain ⟨hle, hag, hscope, hh, hfrest, hlen, hval⟩ :=
      ih (j0 + 1) r.2.2.1 r.2.2.2 hfr
    have Gb := blast_spec j0 (stateAt m j0) P n f (hf.regOK j0)
    have hfb : buildProps m P (count + 1) j0 n f
        = (r.2.1 ++ (buildProps m P count (j0+1) r.2.2.1 r.2.2.2).1,
           (r.1.getD 0 (Bit.const false)) :: (buildProps m P count (j0+1) r.2.2.1 r.2.2.2).2.1,
           (buildProps m P count (j0+1) r.2.2.1 r.2.2.2).2.2.1,
           (buildProps m P count (j0+1) r.2.2.1 r.2.2.2).2.2.2) := rfl
    rw [hfb]
    refine ⟨Nat.le_trans Gb.le hle, ?_, ?_, ?_, hfrest, by simp [hlen], ?_⟩
    · exact (hag.mono Gb.le).trans Gb.agree
    · intro cl hcl b hb
      rcases List.mem_append.mp hcl with hcl | hcl
      · exact BLt.mono hle (Gb.cnfscope cl hcl b hb)
      · exact hscope cl hcl b hb
    · exact Holds.append (Holds_stable hag.symm Gb.cnfscope Gb.holds) hh
    · intro idx hidx
      cases idx with
      | zero =>
        rw [List.getD_cons_zero,
          denote_stable hag (getD_BLt Gb.bitscope 0), Gb.getD_denote 0]
        simp
      | succ j =>
        rw [List.getD_cons_succ, show j0 + (j + 1) = (j0 + 1) + j from by omega]
        exact hval j (by omega)

/-! ### The assembled BMC formula and its soundness -/

/-- The property-violation clause: `P` is false at some collected step. -/
def badClause (pbits : List Bit) : BClause := pbits.map Bit.not

/-- The BMC `BCnf` (variable level): init ∧ transitions (`k` steps) ∧ a
disjunction "`P` false at some step `0..k`". -/
def bmcBCnf (m : Module) (P : Expr 1) (k : Nat) : BCnf :=
  let trans := buildSteps m k 0 0 (traceAssign m)
  let props := buildProps m P (k + 1) 0 trans.2.1 trans.2.2
  initClauses m ++ trans.1 ++ props.1 ++ [badClause props.2.1]

/-- The BMC formula as a kernel-checkable `CNF Nat`. -/
def bmcCnf (m : Module) (P : Expr 1) (k : Nat) : CNF Nat := convCnf (bmcBCnf m P k)

open Loom.Dp.Cert in
/-- **BMC soundness.** A kernel-checked UNSAT certificate for `bmcCnf m P k`
proves that the property `P` holds at every step `0 ≤ j ≤ k` of the module's
run from reset. Requires the (syntactic) discipline that register names are
distinct. -/
theorem bmc_sound (m : Module) (P : Expr 1) (k : Nat)
    (hnd : (m.regs.map (·.name)).Nodup) (cert : List Check.Step)
    (hchk : Check.check (bmcCnf m P k) cert = true) :
    ∀ j, j ≤ k → P.eval (m.run j m.reset) = 1#1 := by
  intro j hjk
  by_contra hne
  have hbv1 : ∀ x : BitVec 1, x ≠ 1#1 → x.getLsbD 0 = false := by decide
  have hPfalse : (P.eval (stateAt m j)).getLsbD 0 = false := hbv1 _ hne
  have hf0ok : TraceOK (traceAssign m) m := traceAssign_traceOK m
  set trans := buildSteps m k 0 0 (traceAssign m) with htrans
  have hS := buildSteps_ok m hnd k 0 0 (traceAssign m) hf0ok
  set props := buildProps m P (k + 1) 0 trans.2.1 trans.2.2 with hprops
  obtain ⟨hPle, hPag, hPscope, hPholds, hPf, hPlen, hPval⟩ :=
    buildProps_ok m P (k + 1) 0 trans.2.1 trans.2.2 hS.2
  rw [← hprops] at hPle hPag hPscope hPholds hPf hPlen hPval
  have hHolds : Holds props.2.2.2 (bmcBCnf m P k) := by
    have hinit : Holds props.2.2.2 (initClauses m) := initClauses_holds m hnd hPf
    have htr : Holds props.2.2.2 trans.1 :=
      Holds_stable hPag.symm hS.1.scope hS.1.holds
    have hbad : Holds props.2.2.2 [badClause props.2.1] := by
      intro cl hcl
      rcases List.mem_cons.mp hcl with rfl | hcl
      · have hjlen : j < props.2.1.length := by rw [hPlen]; omega
        have hmemx : props.2.1.getD j (Bit.const false) ∈ props.2.1 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlen]
          exact List.getElem_mem hjlen
        refine ⟨(props.2.1.getD j (Bit.const false)).not,
          List.mem_map.mpr ⟨_, hmemx, rfl⟩, ?_⟩
        rw [Bit.denote_not, hPval j (by omega), Nat.zero_add, hPfalse]; rfl
      · exact absurd hcl (List.not_mem_nil)
    show Holds props.2.2.2 (initClauses m ++ trans.1 ++ props.1 ++ [badClause props.2.1])
    exact ((hinit.append htr).append hPholds).append hbad
  have hUnsat : CNF.Unsat (bmcCnf m P k) := Check.check_sound hchk
  have hev : CNF.eval (toNatAssign props.2.2.2) (bmcCnf m P k) = true :=
    convCnf_eval_of_Holds hHolds
  rw [hUnsat (toNatAssign props.2.2.2)] at hev
  exact absurd hev (by decide)

end Loom.Dp.Bmc
