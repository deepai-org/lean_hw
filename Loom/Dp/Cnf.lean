import Loom.Emit.MicroVerilog.Semantics
import Loom.Dp.Cert.Check
import Mathlib.Tactic.Set

/-!
# CNF encoding of µVerilog transition systems (task 1.2b)

Tseitin-style bit-blasting of a `Module`'s one-cycle transition relation
into `Std.Sat.CNF Nat`, the type `Loom.Dp.Cert.Check.check` consumes. The
engines (`Loom/Dp/Bmc.lean`, `Loom/Dp/KInduction.lean`) assemble these
pieces into per-query formulas; `Loom/Dp/Solver.lean` ships them to cadical.

## Correctness story (read this before trusting anything)

Only **one** direction is verified, and it is the one the engines need:

* `encode` soundness (`stepV_holds`, `initV_holds`, `propV_holds` and
  friends): a *real* trace of the module yields a satisfying assignment of
  the encoding (the "easy" direction of Tseitin — each gate's clauses are
  satisfied by the gate's semantics). Consequently a kernel-checked
  `CNF.Unsat` of the encoding (via `Check.check_sound`) refutes the
  existence of a real counterexample trace, which is exactly what
  `Bmc.bmc_sound` and `KInduction.kinduction_sound` deliver.
* The converse (every satisfying assignment decodes to a real trace) is
  **not** proved: a SAT answer from the solver is a *candidate*
  counterexample only, to be corroborated by replaying `Module.run`
  (untrusted `#eval`-level, see `Bmc.findCex`).

## Coverage (v1) and the free-variable over-approximation

Bit-blasted **exactly** (with defining Tseitin clauses): `lit`, `reg`,
`and`, `or`, `xor`, `not`, `mux`, `slice`, `zext`, `sext`.

**Over-approximated** as fresh unconstrained output variables (no clauses;
sound for UNSAT, a documented completeness loss): `memRead` (memory
contents are not bit-blasted — every read is free), `add`, `sub`, `eq`,
`ult`, `slt`, `shl`, `shr`. A property proved through this encoding holds
*even if those operators returned arbitrary data*. This v1 fragment is
exactly what the Acc8 "`halted` is sticky" demo needs — the property is a
tautology of the `mux`/`or`/`reg` structure alone, so the certificate is
kernel-checked despite the over-approximated arithmetic and comparators.
The `mkGate2`/`mkGate3`/`orReduce` machinery below already bit-blasts the
arithmetic-free path; extending the precise fragment to `add`/`sub` (ripple
carry via `mkGate3`) and `eq` (`orReduce`) is future work — the invariant
`blast_spec` is structured to admit it without touching the engines.

## Design notes

Variables are *structurally named* (`Var.reg t name w bit`) or auxiliary
Tseitin gate outputs with a globally-unique id from a monotone counter
(`Var.aux id`). The intended satisfying assignment is threaded *through*
`blast` alongside the CNF: each gate's output variable is set to the gate's
real value on the given trace, so `blast_spec` proves both "the clauses
hold" and "the output bits denote the real value" in one structural
induction — no separate freshness/disjointness bookkeeping. A final
`renameNat` pass (see `Bmc.lean`) turns `Var`s into the `Nat`s that
`Check.check` and DIMACS consume.
-/

namespace Loom.Dp.Cnf

open Loom.Emit.MicroVerilog
open Std.Sat

/-! ## Variables, bits, clauses -/

/-- A CNF variable: either a register bit at a time step (`reg t name w
bit`), or an auxiliary Tseitin gate variable identified by a globally
unique id allocated from a monotone counter (`aux id`). -/
inductive Var where
  /-- Bit `bit` of register `name` (declared width `w`) at time `t`. -/
  | reg (t : Nat) (name : String) (w : Nat) (bit : Nat)
  /-- Auxiliary gate variable with a globally-unique allocation id. -/
  | aux (id : Nat)
deriving DecidableEq, Repr

/-- A bit-level operand: a constant or a possibly-negated variable. -/
inductive Bit where
  | const (b : Bool)
  | lit (v : Var) (pol : Bool)
deriving DecidableEq, Repr

namespace Bit

/-- Value of a `Bit` under an assignment. -/
def denote (f : Var → Bool) : Bit → Bool
  | .const b => b
  | .lit v pol => f v == pol

@[simp] theorem denote_const (f : Var → Bool) (b : Bool) :
    (Bit.const b).denote f = b := rfl

@[simp] theorem denote_lit (f : Var → Bool) (v : Var) (p : Bool) :
    (Bit.lit v p).denote f = (f v == p) := rfl

/-- Negation is free (polarity flip). -/
def not : Bit → Bit
  | .const b => .const !b
  | .lit v pol => .lit v !pol

@[simp] theorem denote_not (f : Var → Bool) (b : Bit) :
    b.not.denote f = !(b.denote f) := by
  cases b with
  | const c => rfl
  | lit v p => cases p <;> cases h : f v <;> simp [not, h]

/-- The `Bit` computing `fun b => cond b bt bf` of `x` — without a gate. -/
def sel (bf bt : Bool) (x : Bit) : Bit :=
  match bf, bt with
  | false, false => .const false
  | false, true => x
  | true, false => x.not
  | true, true => .const true

@[simp] theorem denote_sel (f : Var → Bool) (bf bt : Bool) (x : Bit) :
    (sel bf bt x).denote f = cond (x.denote f) bt bf := by
  cases bf <;> cases bt <;> cases h : x.denote f <;> simp [sel, h]

end Bit

/-- A clause over `Bit`s (pre-normalization). -/
abbrev BClause := List Bit

/-- A CNF over `Bit`s (pre-normalization). -/
abbrev BCnf := List BClause

/-- Satisfaction of a `BCnf`: every clause has a true bit. -/
def Holds (f : Var → Bool) (L : BCnf) : Prop :=
  ∀ cl ∈ L, ∃ b ∈ cl, b.denote f = true

theorem Holds.append {f : Var → Bool} {L₁ L₂ : BCnf}
    (h₁ : Holds f L₁) (h₂ : Holds f L₂) : Holds f (L₁ ++ L₂) := by
  intro cl hcl
  rcases List.mem_append.mp hcl with h | h
  · exact h₁ cl h
  · exact h₂ cl h

theorem Holds.nil {f : Var → Bool} : Holds f [] := fun _ h => absurd h (List.not_mem_nil)

theorem Holds.flatMap {α : Type} {f : Var → Bool} {l : List α} {g : α → BCnf}
    (h : ∀ a ∈ l, Holds f (g a)) : Holds f (l.flatMap g) := by
  intro cl hcl
  obtain ⟨a, ha, hmem⟩ := List.mem_flatMap.mp hcl
  exact h a ha cl hmem

theorem Holds.singleton {f : Var → Bool} {cl : BClause}
    (h : ∃ b ∈ cl, b.denote f = true) : Holds f [cl] := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | h'
  · exact h
  · exact absurd h' (List.not_mem_nil)

/-! ## Gates

Two generic truth-table gates cover every operator: `mkGate2` (4 minterm
clauses) and `mkGate3` (8), both constant-folding when an operand is a
`Bit.const` (the folded output is a wire; no clauses). Soundness is stated
against the *intended* value `hv` of the gate's output variable. -/

/-- Minterm clause of a 2-input gate for input combination `(p, q)`:
"inputs are not `(p, q)`, or the output variable equals `tbl p q`". -/
def mint2 (tbl : Bool → Bool → Bool) (v : Var) (x y : Bit) (p q : Bool) : BClause :=
  [cond p x.not x, cond q y.not y, .lit v (tbl p q)]

/-- A 2-input truth-table gate. Output bit plus defining clauses. -/
def mkGate2 (tbl : Bool → Bool → Bool) (v : Var) (x y : Bit) : Bit × BCnf :=
  match x, y with
  | .const bx, y => (y.sel (tbl bx false) (tbl bx true), [])
  | x, .const by' => (x.sel (tbl false by') (tbl true by'), [])
  | x, y =>
    (.lit v true,
     [mint2 tbl v x y false false, mint2 tbl v x y false true,
      mint2 tbl v x y true false, mint2 tbl v x y true true])

theorem mint2_holds {tbl : Bool → Bool → Bool} {v : Var} {x y : Bit}
    {f : Var → Bool} (hv : f v = tbl (x.denote f) (y.denote f)) (p q : Bool) :
    ∃ b ∈ mint2 tbl v x y p q, b.denote f = true := by
  by_cases hx : x.denote f = p
  · by_cases hy : y.denote f = q
    · refine ⟨.lit v (tbl p q), by simp [mint2], ?_⟩
      simp [hv, hx, hy]
    · refine ⟨cond q y.not y, by simp [mint2], ?_⟩
      cases q <;> simp_all
  · refine ⟨cond p x.not x, by simp [mint2], ?_⟩
    cases p <;> simp_all

theorem mkGate2_sound {tbl : Bool → Bool → Bool} {v : Var} {x y : Bit}
    {f : Var → Bool} (hv : f v = tbl (x.denote f) (y.denote f)) :
    (mkGate2 tbl v x y).1.denote f = tbl (x.denote f) (y.denote f)
    ∧ Holds f (mkGate2 tbl v x y).2 := by
  cases x with
  | const bx =>
    refine ⟨?_, Holds.nil⟩
    show (y.sel (tbl bx false) (tbl bx true)).denote f = _
    rw [Bit.denote_sel]
    cases h : y.denote f <;> simp [h]
  | lit vx px =>
    cases y with
    | const by' =>
      refine ⟨?_, Holds.nil⟩
      show ((Bit.lit vx px).sel (tbl false by') (tbl true by')).denote f = _
      rw [Bit.denote_sel]
      cases h : (Bit.lit vx px).denote f <;> simp [h]
    | lit vy py =>
      constructor
      · show (Bit.lit v true).denote f = _
        simp [hv]
      · intro cl hcl
        simp only [mkGate2, List.mem_cons, List.not_mem_nil, or_false] at hcl
        rcases hcl with rfl | rfl | rfl | rfl <;> exact mint2_holds hv _ _

/-- Minterm clause of a 3-input gate. -/
def mint3 (tbl : Bool → Bool → Bool → Bool) (v : Var) (x y z : Bit)
    (p q r : Bool) : BClause :=
  [cond p x.not x, cond q y.not y, cond r z.not z, .lit v (tbl p q r)]

/-- A 3-input truth-table gate; folds to `mkGate2` when an operand is
constant. -/
def mkGate3 (tbl : Bool → Bool → Bool → Bool) (v : Var) (x y z : Bit) :
    Bit × BCnf :=
  match x, y, z with
  | .const bx, y, z => mkGate2 (fun q r => tbl bx q r) v y z
  | x, .const by', z => mkGate2 (fun p r => tbl p by' r) v x z
  | x, y, .const bz => mkGate2 (fun p q => tbl p q bz) v x y
  | x, y, z =>
    (.lit v true,
     [mint3 tbl v x y z false false false, mint3 tbl v x y z false false true,
      mint3 tbl v x y z false true false, mint3 tbl v x y z false true true,
      mint3 tbl v x y z true false false, mint3 tbl v x y z true false true,
      mint3 tbl v x y z true true false, mint3 tbl v x y z true true true])

theorem mint3_holds {tbl : Bool → Bool → Bool → Bool} {v : Var} {x y z : Bit}
    {f : Var → Bool}
    (hv : f v = tbl (x.denote f) (y.denote f) (z.denote f)) (p q r : Bool) :
    ∃ b ∈ mint3 tbl v x y z p q r, b.denote f = true := by
  by_cases hx : x.denote f = p
  · by_cases hy : y.denote f = q
    · by_cases hz : z.denote f = r
      · refine ⟨.lit v (tbl p q r), by simp [mint3], ?_⟩
        simp [hv, hx, hy, hz]
      · refine ⟨cond r z.not z, by simp [mint3], ?_⟩
        cases r <;> simp_all
    · refine ⟨cond q y.not y, by simp [mint3], ?_⟩
      cases q <;> simp_all
  · refine ⟨cond p x.not x, by simp [mint3], ?_⟩
    cases p <;> simp_all

theorem mkGate3_sound {tbl : Bool → Bool → Bool → Bool} {v : Var} {x y z : Bit}
    {f : Var → Bool}
    (hv : f v = tbl (x.denote f) (y.denote f) (z.denote f)) :
    (mkGate3 tbl v x y z).1.denote f = tbl (x.denote f) (y.denote f) (z.denote f)
    ∧ Holds f (mkGate3 tbl v x y z).2 := by
  cases x with
  | const bx =>
    have h := mkGate2_sound (tbl := fun q r => tbl bx q r) (v := v)
      (x := y) (y := z) (f := f) (by simpa using hv)
    simpa [mkGate3] using h
  | lit vx px =>
    cases y with
    | const by' =>
      have h := mkGate2_sound (tbl := fun p r => tbl p by' r) (v := v)
        (x := .lit vx px) (y := z) (f := f) (by simpa using hv)
      simpa [mkGate3] using h
    | lit vy py =>
      cases z with
      | const bz =>
        have h := mkGate2_sound (tbl := fun p q => tbl p q bz) (v := v)
          (x := .lit vx px) (y := .lit vy py) (f := f)
          (by simpa using hv)
        simpa [mkGate3] using h
      | lit vz pz =>
        constructor
        · show (Bit.lit v true).denote f = _
          simp [hv]
        · intro cl hcl
          simp only [mkGate3, List.mem_cons, List.not_mem_nil, or_false] at hcl
          rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact mint3_holds hv _ _ _


/-! ## Variable-scope predicates and stability

Aux variables are allocated from a monotone `Nat` counter, so every value
below is phrased as "mentions only variables allocated so far" (`< n`).
Register variables are always in scope. -/

/-- `v` is in scope at counter `n`: register vars always, aux vars if
allocated (`id < n`). -/
def VLt (n : Nat) : Var → Prop
  | .reg .. => True
  | .aux id => id < n

/-- A `Bit` mentions only in-scope variables. -/
def BLt (n : Nat) : Bit → Prop
  | .const _ => True
  | .lit v _ => VLt n v

theorem VLt.mono {n n' : Nat} (h : n ≤ n') : ∀ {v}, VLt n v → VLt n' v
  | .reg .. , _ => trivial
  | .aux _, hv => Nat.lt_of_lt_of_le hv h

theorem BLt.mono {n n' : Nat} (h : n ≤ n') {b : Bit} (hb : BLt n b) : BLt n' b := by
  cases b with
  | const _ => trivial
  | lit v _ => exact VLt.mono h hb

/-- Two assignments agreeing on all in-scope variables. -/
def AgreeLt (n : Nat) (f g : Var → Bool) : Prop := ∀ v, VLt n v → f v = g v

theorem AgreeLt.mono {n n' : Nat} (h : n' ≤ n) {f g : Var → Bool}
    (ha : AgreeLt n f g) : AgreeLt n' f g :=
  fun v hv => ha v (VLt.mono h hv)

theorem AgreeLt.symm {n : Nat} {f g : Var → Bool} (ha : AgreeLt n f g) :
    AgreeLt n g f := fun v hv => (ha v hv).symm

theorem AgreeLt.trans {n : Nat} {f g h : Var → Bool} (ha : AgreeLt n f g)
    (hb : AgreeLt n g h) : AgreeLt n f h := fun v hv => (ha v hv).trans (hb v hv)

/-- Denotation is stable across assignments that agree in scope. -/
theorem denote_stable {n : Nat} {f g : Var → Bool} (ha : AgreeLt n f g)
    {b : Bit} (hb : BLt n b) : b.denote f = b.denote g := by
  cases b with
  | const _ => rfl
  | lit v p => simp only [Bit.denote_lit, ha v hb]

/-- `Holds` is stable across assignments agreeing in scope, when the CNF is
in scope. -/
theorem Holds_stable {n : Nat} {f g : Var → Bool} (ha : AgreeLt n f g)
    {L : BCnf} (hL : ∀ cl ∈ L, ∀ b ∈ cl, BLt n b) (h : Holds f L) : Holds g L := by
  intro cl hcl
  obtain ⟨b, hb, hbd⟩ := h cl hcl
  exact ⟨b, hb, by rw [← denote_stable ha (hL cl hcl b hb)]; exact hbd⟩

/-- Set one aux variable. -/
def setV (f : Var → Bool) (id : Nat) (val : Bool) : Var → Bool :=
  fun w => if w = .aux id then val else f w

theorem setV_agree (f : Var → Bool) {n id : Nat} (h : n ≤ id) (val : Bool) :
    AgreeLt n (setV f id val) f := by
  intro v hv
  cases v with
  | reg t nm w b => simp [setV]
  | aux j =>
    have hj : j < n := hv
    simp only [setV]
    rw [if_neg]
    intro he; injection he with he; omega

@[simp] theorem setV_self (f : Var → Bool) (id : Nat) (val : Bool) :
    setV f id val (.aux id) = val := by simp [setV]

/-! ## The bit-blaster

`blast t σ e n f` bit-blasts `Expr w` `e` (evaluated at concrete state `σ`,
time `t`), allocating aux ids from `n`, extending assignment `f`. Returns
`(bits, cnf, n', f')`. The soundness invariant (`blast_spec`) says: under
`f'`, each output bit denotes the corresponding bit of `e.eval σ`, and
`cnf` holds — provided `f` already reads registers correctly (`RegOK`).

Coverage: `lit, reg, and, or, xor, not, eq, mux, slice, zext, sext` are
bit-blasted exactly (with defining clauses). `add, sub, ult, slt, shl, shr,
memRead` are **over-approximated**: each emits fresh unconstrained output
variables (no clauses), which the constructed assignment still sets to the
real value bits — so `blast_spec` holds uniformly and the UNSAT direction is
sound, while the solver is free to pick other values there (a documented
completeness loss; see the module header). -/

/-- Registers are read correctly by `f` at time `t`. -/
def RegOK (f : Var → Bool) (σ : St) (t : Nat) : Prop :=
  ∀ (name : String) (w bit : Nat), f (.reg t name w bit) = (σ.regs name w).getLsbD bit

/-- LSB-first list of `w` register literals for `reg t name w`. -/
def regBits (t : Nat) (name : String) (w : Nat) : List Bit :=
  (List.range w).map (fun i => .lit (.reg t name w i) true)

/-- `w` fresh aux variables (over-approximation output), returning bits,
next counter, and the assignment set to `vals i` at bit `i`. -/
def freshBits (n w : Nat) (f : Var → Bool) (vals : Nat → Bool) :
    List Bit × Nat × (Var → Bool) :=
  match w with
  | 0 => ([], n, f)
  | w + 1 =>
    let (rest, n', f') := freshBits (n + 1) w (setV f n (vals 0)) (fun i => vals (i + 1))
    (Bit.lit (.aux n) true :: rest, n', f')

/-- Bitwise binary gate over two equal-length bit lists (used for
`and/or/xor`). -/
def mapGate2 (tbl : Bool → Bool → Bool) (f : Var → Bool) :
    Nat → List Bit → List Bit → List Bit × BCnf × Nat × (Var → Bool)
  | n, x :: xs, y :: ys =>
    let v : Var := .aux n
    let (b, c) := mkGate2 tbl v x y
    let f1 := setV f n (tbl (x.denote f) (y.denote f))
    let (bs, cs, n', f') := mapGate2 tbl f1 (n + 1) xs ys
    (b :: bs, c ++ cs, n', f')
  | n, _, _ => ([], [], n, f)


/-- `getD` of an in-scope list is in scope (elements are, and so is the
default `const false`). -/
theorem getD_BLt {n : Nat} {L : List Bit} (h : ∀ b ∈ L, BLt n b) (i : Nat) :
    BLt n (L.getD i (Bit.const false)) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : L[i]? with
  | none => trivial
  | some b => exact h b (List.mem_of_getElem? hi)

/-- Negation preserves scope. -/
theorem BLt.not {n : Nat} {b : Bit} (h : BLt n b) : BLt n b.not := by
  cases b with
  | const _ => trivial
  | lit v p => exact h

/-- `sel` preserves scope. -/
theorem BLt.sel {n : Nat} {bf bt : Bool} {x : Bit} (h : BLt n x) :
    BLt n (x.sel bf bt) := by
  cases bf <;> cases bt <;> simp only [Bit.sel] <;> first | trivial | exact h | exact h.not

/-- `mkGate2` output and clauses stay within scope `n+1` when inputs are in
scope `n` and the output var is `aux n`. -/
theorem mkGate2_scope {tbl : Bool → Bool → Bool} {n : Nat} {x y : Bit}
    (hx : BLt n x) (hy : BLt n y) :
    BLt (n + 1) (mkGate2 tbl (.aux n) x y).1
    ∧ (∀ cl ∈ (mkGate2 tbl (.aux n) x y).2, ∀ b ∈ cl, BLt (n + 1) b) := by
  have hx' : BLt (n + 1) x := BLt.mono (Nat.le_succ n) hx
  have hy' : BLt (n + 1) y := BLt.mono (Nat.le_succ n) hy
  have hv : BLt (n + 1) (Bit.lit (.aux n) true) := by simp [BLt, VLt]
  cases x with
  | const bx =>
    refine ⟨?_, by intro cl hcl; simp [mkGate2] at hcl⟩
    exact BLt.sel hy'
  | lit vx px =>
    cases y with
    | const by' =>
      refine ⟨BLt.sel hx', by intro cl hcl; simp [mkGate2] at hcl⟩
    | lit vy py =>
      refine ⟨hv, ?_⟩
      intro cl hcl
      simp only [mkGate2, List.mem_cons, List.not_mem_nil, or_false] at hcl
      have hbit : ∀ (p q : Bool) b, b ∈ mint2 tbl (.aux n) (.lit vx px) (.lit vy py) p q →
          BLt (n + 1) b := by
        intro p q b hb
        simp only [mint2, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl
        · cases p <;> first | exact hx' | exact hx'.not
        · cases q <;> first | exact hy' | exact hy'.not
        · exact hv
      rcases hcl with rfl | rfl | rfl | rfl <;> exact hbit _ _

/-- `mkGate3` output and clauses stay within scope `n+1`. -/
theorem mkGate3_scope {tbl : Bool → Bool → Bool → Bool} {n : Nat} {x y z : Bit}
    (hx : BLt n x) (hy : BLt n y) (hz : BLt n z) :
    BLt (n + 1) (mkGate3 tbl (.aux n) x y z).1
    ∧ (∀ cl ∈ (mkGate3 tbl (.aux n) x y z).2, ∀ b ∈ cl, BLt (n + 1) b) := by
  have hx' : BLt (n + 1) x := BLt.mono (Nat.le_succ n) hx
  have hy' : BLt (n + 1) y := BLt.mono (Nat.le_succ n) hy
  have hz' : BLt (n + 1) z := BLt.mono (Nat.le_succ n) hz
  have hv : BLt (n + 1) (Bit.lit (.aux n) true) := by simp [BLt, VLt]
  cases x with
  | const bx => simpa [mkGate3] using mkGate2_scope (tbl := fun q r => tbl bx q r) hy hz
  | lit vx px =>
    cases y with
    | const by' =>
      simpa [mkGate3] using
        mkGate2_scope (tbl := fun p r => tbl p by' r) (x := .lit vx px) hx hz
    | lit vy py =>
      cases z with
      | const bz =>
        simpa [mkGate3] using
          mkGate2_scope (tbl := fun p q => tbl p q bz) (x := .lit vx px) (y := .lit vy py) hx hy
      | lit vz pz =>
        refine ⟨hv, ?_⟩
        intro cl hcl
        simp only [mkGate3, List.mem_cons, List.not_mem_nil, or_false] at hcl
        have hbit : ∀ (p q r : Bool) b,
            b ∈ mint3 tbl (.aux n) (.lit vx px) (.lit vy py) (.lit vz pz) p q r →
            BLt (n + 1) b := by
          intro p q r b hb
          simp only [mint3, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl | rfl
          · cases p <;> first | exact hx' | exact hx'.not
          · cases q <;> first | exact hy' | exact hy'.not
          · cases r <;> first | exact hz' | exact hz'.not
          · exact hv
        rcases hcl with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hbit _ _ _

/-- Specification of `freshBits`: `w` fresh vars, each denoting `vals i`. -/
theorem freshBits_spec (n w : Nat) (f : Var → Bool) (vals : Nat → Bool) :
    n ≤ (freshBits n w f vals).2.1 ∧ AgreeLt n (freshBits n w f vals).2.2 f ∧
    (freshBits n w f vals).1.length = w ∧
    (∀ b ∈ (freshBits n w f vals).1, BLt (freshBits n w f vals).2.1 b) ∧
    (∀ i, i < w →
      ((freshBits n w f vals).1.getD i (Bit.const false)).denote (freshBits n w f vals).2.2
        = vals i) := by
  induction w generalizing n f vals with
  | zero =>
    refine ⟨Nat.le_refl _, fun _ _ => rfl, rfl, by intro b hb; simp [freshBits] at hb,
      by intro i hi; omega⟩
  | succ w ih =>
    obtain ⟨hle, hag, hlen, hbl, hval⟩ := ih (n + 1) (setV f n (vals 0)) (fun i => vals (i + 1))
    have hfb : freshBits n (w + 1) f vals
        = (Bit.lit (.aux n) true :: (freshBits (n + 1) w (setV f n (vals 0)) (fun i => vals (i + 1))).1,
           (freshBits (n + 1) w (setV f n (vals 0)) (fun i => vals (i + 1))).2.1,
           (freshBits (n + 1) w (setV f n (vals 0)) (fun i => vals (i + 1))).2.2) := rfl
    rw [hfb]
    refine ⟨Nat.le_trans (Nat.le_succ n) hle, ?_, by simp [hlen], ?_, ?_⟩
    · exact (hag.mono (Nat.le_succ n)).trans (setV_agree f (Nat.le_refl n) (vals 0))
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · show BLt _ (Bit.lit (.aux n) true); simp only [BLt, VLt]; omega
      · exact hbl b hb
    · intro i hi
      cases i with
      | zero =>
        show (Bit.lit (.aux n) true).denote _ = vals 0
        rw [Bit.denote_lit, hag (.aux n) (by show n < n + 1; omega), setV_self]
        simp
      | succ j =>
        show ((freshBits (n + 1) w (setV f n (vals 0)) (fun i => vals (i + 1))).1.getD j
          (Bit.const false)).denote _ = vals (j + 1)
        exact hval j (by omega)

/-- Specification of `mapGate2` over equal-length in-scope bit lists. -/
theorem mapGate2_spec (tbl : Bool → Bool → Bool) :
    ∀ (xs ys : List Bit) (f : Var → Bool) (n : Nat), xs.length = ys.length →
    (∀ b ∈ xs, BLt n b) → (∀ b ∈ ys, BLt n b) →
    n ≤ (mapGate2 tbl f n xs ys).2.2.1 ∧
    AgreeLt n (mapGate2 tbl f n xs ys).2.2.2 f ∧
    (mapGate2 tbl f n xs ys).1.length = xs.length ∧
    (∀ b ∈ (mapGate2 tbl f n xs ys).1, BLt (mapGate2 tbl f n xs ys).2.2.1 b) ∧
    (∀ cl ∈ (mapGate2 tbl f n xs ys).2.1, ∀ b ∈ cl,
      BLt (mapGate2 tbl f n xs ys).2.2.1 b) ∧
    Holds (mapGate2 tbl f n xs ys).2.2.2 (mapGate2 tbl f n xs ys).2.1 ∧
    (∀ i, i < xs.length →
      ((mapGate2 tbl f n xs ys).1.getD i (Bit.const false)).denote
          (mapGate2 tbl f n xs ys).2.2.2
        = tbl ((xs.getD i (Bit.const false)).denote f)
              ((ys.getD i (Bit.const false)).denote f)) := by
  intro xs
  induction xs with
  | nil =>
    intro ys f n hlen _ _
    have : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst this
    exact ⟨Nat.le_refl _, fun _ _ => rfl, rfl, by intro b hb; simp [mapGate2] at hb,
      by intro cl hcl; simp [mapGate2] at hcl, Holds.nil, by intro i hi; simp at hi⟩
  | cons x xs ih =>
    intro ys f n hlen hxs hys
    match ys, hlen with
    | y :: ys, hlen =>
      have hxbl : BLt n x := hxs x List.mem_cons_self
      have hybl : BLt n y := hys y List.mem_cons_self
      set f1 := setV f n (tbl (x.denote f) (y.denote f)) with hf1
      have hxs' : ∀ b ∈ xs, BLt (n + 1) b :=
        fun b hb => BLt.mono (Nat.le_succ n) (hxs b (List.mem_cons_of_mem _ hb))
      have hys' : ∀ b ∈ ys, BLt (n + 1) b :=
        fun b hb => BLt.mono (Nat.le_succ n) (hys b (List.mem_cons_of_mem _ hb))
      have hlen' : xs.length = ys.length := by simpa using hlen
      set p := mapGate2 tbl f1 (n + 1) xs ys with hpdef
      obtain ⟨hle, hag, hrlen, hrbl, hrcl, hrh, hrv⟩ := ih ys f1 (n + 1) hlen' hxs' hys'
      rw [← hpdef] at hle hag hrlen hrbl hrcl hrh hrv
      have hgate := mkGate2_scope (tbl := tbl) (n := n) hxbl hybl
      have hfagree_f : AgreeLt n f1 f := setV_agree f (Nat.le_refl n) _
      have hgvsound := mkGate2_sound (tbl := tbl) (v := .aux n) (x := x) (y := y) (f := f1)
        (by rw [hf1]; simp only [setV_self];
            rw [denote_stable hfagree_f hxbl, denote_stable hfagree_f hybl])
      have hgv : (mkGate2 tbl (.aux n) x y).1.denote f1
          = tbl (x.denote f) (y.denote f) := by
        rw [hgvsound.1, denote_stable hfagree_f hxbl, denote_stable hfagree_f hybl]
      have hfb : mapGate2 tbl f n (x :: xs) (y :: ys)
          = ((mkGate2 tbl (.aux n) x y).1 :: p.1,
             (mkGate2 tbl (.aux n) x y).2 ++ p.2.1, p.2.2.1, p.2.2.2) := rfl
      rw [hfb]
      have hxsn : ∀ b ∈ xs, BLt n b :=
        fun b hb => hxs b (List.mem_cons_of_mem _ hb)
      have hysn : ∀ b ∈ ys, BLt n b :=
        fun b hb => hys b (List.mem_cons_of_mem _ hb)
      refine ⟨Nat.le_trans (Nat.le_succ n) hle, ?_, by simp [hrlen], ?_, ?_, ?_, ?_⟩
      · exact (hag.mono (Nat.le_succ n)).trans hfagree_f
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact BLt.mono hle hgate.1
        · exact hrbl b hb
      · intro cl hcl b hb
        rcases List.mem_append.mp hcl with hcl | hcl
        · exact BLt.mono hle (hgate.2 cl hcl b hb)
        · exact hrcl cl hcl b hb
      · refine Holds.append ?_ hrh
        exact Holds_stable hag.symm (fun cl hcl b hb => hgate.2 cl hcl b hb) hgvsound.2
      · intro i hi
        cases i with
        | zero =>
          show ((mkGate2 tbl (.aux n) x y).1).denote p.2.2.2 = _
          rw [List.getD_cons_zero, List.getD_cons_zero,
            denote_stable hag hgate.1, hgv]
        | succ j =>
          show (p.1.getD j (Bit.const false)).denote p.2.2.2 = _
          rw [List.getD_cons_succ, List.getD_cons_succ]
          have := hrv j (by simpa using Nat.lt_of_succ_lt_succ hi)
          rw [this, denote_stable hfagree_f (getD_BLt hxsn j),
            denote_stable hfagree_f (getD_BLt hysn j)]


/-! ## OR-reduction (for `eq`) -/

/-- OR-reduce a bit list to a single bit denoting `bs.any denote`. -/
def orReduce (f : Var → Bool) : Nat → List Bit → Bit × BCnf × Nat × (Var → Bool)
  | n, [] => (Bit.const false, [], n, f)
  | n, b :: bs =>
    let r := orReduce f n bs
    let v : Var := .aux r.2.2.1
    let g := mkGate2 (· || ·) v b r.1
    (g.1, g.2 ++ r.2.1, r.2.2.1 + 1,
      setV r.2.2.2 r.2.2.1 ((b.denote r.2.2.2) || (r.1.denote r.2.2.2)))

theorem orReduce_spec (f : Var → Bool) (n : Nat) :
    ∀ (bs : List Bit), (∀ b ∈ bs, BLt n b) →
    n ≤ (orReduce f n bs).2.2.1 ∧
    AgreeLt n (orReduce f n bs).2.2.2 f ∧
    BLt (orReduce f n bs).2.2.1 (orReduce f n bs).1 ∧
    (∀ cl ∈ (orReduce f n bs).2.1, ∀ b ∈ cl, BLt (orReduce f n bs).2.2.1 b) ∧
    Holds (orReduce f n bs).2.2.2 (orReduce f n bs).2.1 ∧
    (orReduce f n bs).1.denote (orReduce f n bs).2.2.2 = bs.any (·.denote f) := by
  intro bs
  induction bs with
  | nil =>
    intro _
    exact ⟨Nat.le_refl _, fun _ _ => rfl, trivial, by intro cl hcl; simp [orReduce] at hcl,
      Holds.nil, rfl⟩
  | cons b bs ih =>
    intro hbs
    have hbbl : BLt n b := hbs b List.mem_cons_self
    have hbsbl : ∀ b ∈ bs, BLt n b := fun b hb => hbs b (List.mem_cons_of_mem _ hb)
    obtain ⟨hle, hag, hrbl, hrcl, hrh, hrv⟩ := ih hbsbl
    set r := orReduce f n bs with hrdef
    set n1 := r.2.2.1 with hn1
    set f1 := r.2.2.2 with hf1
    have hbbl1 : BLt n1 b := BLt.mono hle hbbl
    -- gate over (b, r.1) with output var aux n1
    have hgate := mkGate2_scope (tbl := (· || ·)) (n := n1) hbbl1 hrbl
    have hgvsound := mkGate2_sound (tbl := (· || ·)) (v := .aux n1) (x := b) (y := r.1)
      (f := setV f1 n1 (b.denote f1 || r.1.denote f1)) (by
        rw [setV_self, denote_stable (setV_agree f1 (Nat.le_refl n1) _) hbbl1,
          denote_stable (setV_agree f1 (Nat.le_refl n1) _) hrbl])
    have hfb : orReduce f n (b :: bs)
        = ((mkGate2 (· || ·) (.aux n1) b r.1).1,
           (mkGate2 (· || ·) (.aux n1) b r.1).2 ++ r.2.1, n1 + 1,
           setV f1 n1 (b.denote f1 || r.1.denote f1)) := rfl
    rw [hfb]
    have hsetag : AgreeLt n1 (setV f1 n1 (b.denote f1 || r.1.denote f1)) f1 :=
      setV_agree f1 (Nat.le_refl n1) _
    refine ⟨Nat.le_trans hle (Nat.le_succ n1), ?_, ?_, ?_, ?_, ?_⟩
    · exact (hsetag.mono hle).trans hag
    · exact hgate.1
    · intro cl hcl bb hbb
      rcases List.mem_append.mp hcl with hcl | hcl
      · exact hgate.2 cl hcl bb hbb
      · exact BLt.mono (Nat.le_succ n1) (hrcl cl hcl bb hbb)
    · refine Holds.append ?_ (Holds_stable hsetag.symm hrcl hrh)
      exact hgvsound.2
    · rw [hgvsound.1,
        denote_stable (setV_agree f1 (Nat.le_refl n1) _) hbbl1,
        denote_stable (setV_agree f1 (Nat.le_refl n1) _) hrbl, hrv,
        denote_stable hag hbbl]
      simp [List.any_cons]

/-! ## Mux-mapping (for `mux`) -/

/-- Table for a 1-bit mux: select `t` when the control bit is set. -/
def muxTbl (c t g : Bool) : Bool := if c then t else g

/-- Per-bit mux over two equal-length lists with a shared control bit `c`. -/
def mapMux (c : Bit) (f : Var → Bool) :
    Nat → List Bit → List Bit → List Bit × BCnf × Nat × (Var → Bool)
  | n, t :: ts, g :: gs =>
    let v : Var := .aux n
    let gt := mkGate3 muxTbl v c t g
    let f1 := setV f n (muxTbl (c.denote f) (t.denote f) (g.denote f))
    let r := mapMux c f1 (n + 1) ts gs
    (gt.1 :: r.1, gt.2 ++ r.2.1, r.2.2.1, r.2.2.2)
  | n, _, _ => ([], [], n, f)

theorem mapMux_spec (c : Bit) :
    ∀ (ts gs : List Bit) (f : Var → Bool) (n : Nat), ts.length = gs.length →
    BLt n c → (∀ b ∈ ts, BLt n b) → (∀ b ∈ gs, BLt n b) →
    n ≤ (mapMux c f n ts gs).2.2.1 ∧
    AgreeLt n (mapMux c f n ts gs).2.2.2 f ∧
    (mapMux c f n ts gs).1.length = ts.length ∧
    (∀ b ∈ (mapMux c f n ts gs).1, BLt (mapMux c f n ts gs).2.2.1 b) ∧
    (∀ cl ∈ (mapMux c f n ts gs).2.1, ∀ b ∈ cl, BLt (mapMux c f n ts gs).2.2.1 b) ∧
    Holds (mapMux c f n ts gs).2.2.2 (mapMux c f n ts gs).2.1 ∧
    (∀ i, i < ts.length →
      ((mapMux c f n ts gs).1.getD i (Bit.const false)).denote (mapMux c f n ts gs).2.2.2
        = muxTbl (c.denote f) ((ts.getD i (Bit.const false)).denote f)
                 ((gs.getD i (Bit.const false)).denote f)) := by
  intro ts
  induction ts with
  | nil =>
    intro gs f n hlen _ _ _
    have : gs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst this
    exact ⟨Nat.le_refl _, fun _ _ => rfl, rfl, by intro b hb; simp [mapMux] at hb,
      by intro cl hcl; simp [mapMux] at hcl, Holds.nil, by intro i hi; simp at hi⟩
  | cons t ts ih =>
    intro gs f n hlen hc ht hg
    match gs, hlen with
    | g :: gs, hlen =>
      have htbl : BLt n t := ht t List.mem_cons_self
      have hgbl : BLt n g := hg g List.mem_cons_self
      set f1 := setV f n (muxTbl (c.denote f) (t.denote f) (g.denote f)) with hf1
      have hts' : ∀ b ∈ ts, BLt (n + 1) b :=
        fun b hb => BLt.mono (Nat.le_succ n) (ht b (List.mem_cons_of_mem _ hb))
      have hgs' : ∀ b ∈ gs, BLt (n + 1) b :=
        fun b hb => BLt.mono (Nat.le_succ n) (hg b (List.mem_cons_of_mem _ hb))
      have htsn : ∀ b ∈ ts, BLt n b := fun b hb => ht b (List.mem_cons_of_mem _ hb)
      have hgsn : ∀ b ∈ gs, BLt n b := fun b hb => hg b (List.mem_cons_of_mem _ hb)
      have hlen' : ts.length = gs.length := by simpa using hlen
      set p := mapMux c f1 (n + 1) ts gs with hpdef
      obtain ⟨hle, hag, hrlen, hrbl, hrcl, hrh, hrv⟩ :=
        ih gs f1 (n + 1) hlen' (BLt.mono (Nat.le_succ n) hc) hts' hgs'
      rw [← hpdef] at hle hag hrlen hrbl hrcl hrh hrv
      -- 3-input gate scope
      have hcbl : BLt n c := hc
      have hfagree_f : AgreeLt n f1 f := setV_agree f (Nat.le_refl n) _
      have hhv : f1 (.aux n) = muxTbl (c.denote f1) (t.denote f1) (g.denote f1) := by
        rw [denote_stable hfagree_f hcbl, denote_stable hfagree_f htbl,
          denote_stable hfagree_f hgbl, hf1, setV_self]
      have hgvsound := mkGate3_sound (tbl := muxTbl) (v := .aux n) (x := c) (y := t) (z := g)
        (f := f1) hhv
      -- scope of the gate output and clauses
      have hcbl' : BLt (n + 1) c := BLt.mono (Nat.le_succ n) hcbl
      have htbl' : BLt (n + 1) t := BLt.mono (Nat.le_succ n) htbl
      have hgbl' : BLt (n + 1) g := BLt.mono (Nat.le_succ n) hgbl
      have hgscope := mkGate3_scope (tbl := muxTbl) (n := n) hcbl htbl hgbl
      have hfb : mapMux c f n (t :: ts) (g :: gs)
          = ((mkGate3 muxTbl (.aux n) c t g).1 :: p.1,
             (mkGate3 muxTbl (.aux n) c t g).2 ++ p.2.1, p.2.2.1, p.2.2.2) := rfl
      rw [hfb]
      refine ⟨Nat.le_trans (Nat.le_succ n) hle, ?_, by simp [hrlen], ?_, ?_, ?_, ?_⟩
      · exact (hag.mono (Nat.le_succ n)).trans hfagree_f
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact BLt.mono hle hgscope.1
        · exact hrbl b hb
      · intro cl hcl b hb
        rcases List.mem_append.mp hcl with hcl | hcl
        · exact BLt.mono hle (hgscope.2 cl hcl b hb)
        · exact hrcl cl hcl b hb
      · refine Holds.append ?_ hrh
        exact Holds_stable hag.symm (fun cl hcl b hb => hgscope.2 cl hcl b hb) hgvsound.2
      · intro i hi
        cases i with
        | zero =>
          show ((mkGate3 muxTbl (.aux n) c t g).1).denote p.2.2.2 = _
          rw [List.getD_cons_zero, List.getD_cons_zero,
            denote_stable hag hgscope.1, hgvsound.1,
            denote_stable hfagree_f hcbl, denote_stable hfagree_f htbl,
            denote_stable hfagree_f hgbl]
        | succ j =>
          show (p.1.getD j (Bit.const false)).denote p.2.2.2 = _
          rw [List.getD_cons_succ, List.getD_cons_succ]
          have := hrv j (by simpa using Nat.lt_of_succ_lt_succ hi)
          rw [this, denote_stable hfagree_f hcbl,
            denote_stable hfagree_f (getD_BLt htsn j),
            denote_stable hfagree_f (getD_BLt hgsn j)]


/-! ## The main bit-blaster over expressions -/

/-- Constant bit list for a literal. -/
def litBits {w : Nat} (v : BitVec w) : List Bit :=
  (List.range w).map (fun i => Bit.const (v.getLsbD i))

/-- Bit-blast an expression `e : Expr w` evaluated at concrete state `σ`
(time `t`), allocating aux ids from `n` and extending assignment `f`.
Returns `(bits, cnf, n', f')`. -/
def blast (t : Nat) (σ : St) : {w : Nat} → Expr w → Nat → (Var → Bool) →
    List Bit × BCnf × Nat × (Var → Bool)
  | w, .lit v, n, f => (litBits v, [], n, f)
  | w, .reg _ nm, n, f => (regBits t nm w, [], n, f)
  | _, .and a b, n, f =>
      let ra := blast t σ a n f
      let rb := blast t σ b ra.2.2.1 ra.2.2.2
      let rg := mapGate2 (· && ·) rb.2.2.2 rb.2.2.1 ra.1 rb.1
      (rg.1, ra.2.1 ++ rb.2.1 ++ rg.2.1, rg.2.2.1, rg.2.2.2)
  | _, .or a b, n, f =>
      let ra := blast t σ a n f
      let rb := blast t σ b ra.2.2.1 ra.2.2.2
      let rg := mapGate2 (· || ·) rb.2.2.2 rb.2.2.1 ra.1 rb.1
      (rg.1, ra.2.1 ++ rb.2.1 ++ rg.2.1, rg.2.2.1, rg.2.2.2)
  | _, .xor a b, n, f =>
      let ra := blast t σ a n f
      let rb := blast t σ b ra.2.2.1 ra.2.2.2
      let rg := mapGate2 (· ^^ ·) rb.2.2.2 rb.2.2.1 ra.1 rb.1
      (rg.1, ra.2.1 ++ rb.2.1 ++ rg.2.1, rg.2.2.1, rg.2.2.2)
  | _, .not a, n, f =>
      let ra := blast t σ a n f
      (ra.1.map Bit.not, ra.2.1, ra.2.2.1, ra.2.2.2)
  | _, .mux c tt ff, n, f =>
      let rc := blast t σ c n f
      let rt := blast t σ tt rc.2.2.1 rc.2.2.2
      let rf := blast t σ ff rt.2.2.1 rt.2.2.2
      let rm := mapMux (rc.1.getD 0 (Bit.const false)) rf.2.2.2 rf.2.2.1 rt.1 rf.1
      (rm.1, rc.2.1 ++ rt.2.1 ++ rf.2.1 ++ rm.2.1, rm.2.2.1, rm.2.2.2)
  | _, .slice a lo width, n, f =>
      let ra := blast t σ a n f
      ((List.range width).map (fun j => ra.1.getD (lo + j) (Bit.const false)),
        ra.2.1, ra.2.2.1, ra.2.2.2)
  | _, .zext a w', n, f =>
      let ra := blast t σ a n f
      ((List.range w').map (fun j => ra.1.getD j (Bit.const false)),
        ra.2.1, ra.2.2.1, ra.2.2.2)
  | _, @Expr.sext wa a w', n, f =>
      let ra := blast t σ a n f
      ((List.range w').map (fun j =>
          if j < wa then ra.1.getD j (Bit.const false)
          else ra.1.getD (wa - 1) (Bit.const false)),
        ra.2.1, ra.2.2.1, ra.2.2.2)
  -- Over-approximated: fresh vars set to the real value bits, no clauses.
  | w, e@(.memRead ..), n, f =>
      let r := freshBits n w f (fun i => (e.eval σ).getLsbD i)
      (r.1, [], r.2.1, r.2.2)
  | w, e@(.add ..), n, f =>
      let r := freshBits n w f (fun i => (e.eval σ).getLsbD i)
      (r.1, [], r.2.1, r.2.2)
  | w, e@(.sub ..), n, f =>
      let r := freshBits n w f (fun i => (e.eval σ).getLsbD i)
      (r.1, [], r.2.1, r.2.2)
  | w, e@(.shl ..), n, f =>
      let r := freshBits n w f (fun i => (e.eval σ).getLsbD i)
      (r.1, [], r.2.1, r.2.2)
  | w, e@(.shr ..), n, f =>
      let r := freshBits n w f (fun i => (e.eval σ).getLsbD i)
      (r.1, [], r.2.1, r.2.2)
  | _, e@(.eq ..), n, f =>
      let r := freshBits n 1 f (fun i => (e.eval σ).getLsbD i)
      (r.1, [], r.2.1, r.2.2)
  | _, e@(.ult ..), n, f =>
      let r := freshBits n 1 f (fun i => (e.eval σ).getLsbD i)
      (r.1, [], r.2.1, r.2.2)
  | _, e@(.slt ..), n, f =>
      let r := freshBits n 1 f (fun i => (e.eval σ).getLsbD i)
      (r.1, [], r.2.1, r.2.2)

/-- The soundness bundle: a real trace makes `blast`'s clauses hold and its
output bits denote the real value. -/
structure Good (σ : St) (t : Nat) {w : Nat} (bv : BitVec w) (n : Nat)
    (f : Var → Bool) (res : List Bit × BCnf × Nat × (Var → Bool)) : Prop where
  le : n ≤ res.2.2.1
  agree : AgreeLt n res.2.2.2 f
  len : res.1.length = w
  bitscope : ∀ b ∈ res.1, BLt res.2.2.1 b
  cnfscope : ∀ cl ∈ res.2.1, ∀ b ∈ cl, BLt res.2.2.1 b
  holds : Holds res.2.2.2 res.2.1
  value : ∀ i, i < w → (res.1.getD i (Bit.const false)).denote res.2.2.2 = bv.getLsbD i

/-- `RegOK` is preserved by any assignment agreeing on register variables. -/
theorem RegOK_of_agree {f g : Var → Bool} {σ : St} {t n : Nat}
    (h : RegOK f σ t) (ha : AgreeLt n g f) : RegOK g σ t :=
  fun nm w bit => by rw [ha (.reg t nm w bit) trivial]; exact h nm w bit


/-- `getD` into a `range`-map at an in-range index. -/
theorem range_map_getD {α : Type} (g : Nat → α) (w i : Nat) (d : α) (h : i < w) :
    ((List.range w).map g).getD i d = g i := by
  have hlen : i < ((List.range w).map g).length := by simp [h]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

/-- `getD` into a `map f` at an in-range index. -/
theorem map_getD {α β : Type} (g : α → β) (L : List α) (i : Nat) (da : α) (db : β)
    (h : i < L.length) : (L.map g).getD i db = g (L.getD i da) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  simp

theorem litBits_length {w : Nat} (v : BitVec w) : (litBits v).length = w := by
  simp [litBits]

theorem litBits_getD {w : Nat} (v : BitVec w) (f : Var → Bool) (i : Nat) (h : i < w) :
    ((litBits v).getD i (Bit.const false)).denote f = v.getLsbD i := by
  rw [litBits, range_map_getD _ _ _ _ h]; rfl

theorem regBits_length (t : Nat) (nm : String) (w : Nat) :
    (regBits t nm w).length = w := by simp [regBits]

theorem regBits_getD (t : Nat) (nm : String) (w : Nat) (f : Var → Bool) (i : Nat)
    (h : i < w) : ((regBits t nm w).getD i (Bit.const false)).denote f
      = (f (.reg t nm w i) == true) := by
  rw [regBits, range_map_getD _ _ _ _ h]; rfl

/-- From a `Good` bundle: every index (even out of range) reads the real
value bit. -/
theorem Good.getD_denote {σ : St} {t : Nat} {w : Nat} {bv : BitVec w} {n : Nat}
    {f : Var → Bool} {res : List Bit × BCnf × Nat × (Var → Bool)}
    (hg : Good σ t bv n f res) (k : Nat) :
    (res.1.getD k (Bit.const false)).denote res.2.2.2 = bv.getLsbD k := by
  by_cases hk : k < w
  · exact hg.value k hk
  · have : res.1.getD k (Bit.const false) = Bit.const false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hg.len]; omega)]; rfl
    rw [this, BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hk)]; rfl


/-- Assemble a `Good` for a binary bitwise gate from the two sub-`Good`s. -/
theorem good_bin (tbl : Bool → Bool → Bool) {σ : St} {t w : Nat}
    {av bv cv : BitVec w} {n : Nat} {f : Var → Bool}
    {ra rb : List Bit × BCnf × Nat × (Var → Bool)}
    (Ga : Good σ t av n f ra) (Gb : Good σ t bv ra.2.2.1 ra.2.2.2 rb)
    (hlsb : ∀ i, i < w → cv.getLsbD i = tbl (av.getLsbD i) (bv.getLsbD i)) :
    Good σ t cv n f
      ((mapGate2 tbl rb.2.2.2 rb.2.2.1 ra.1 rb.1).1,
       ra.2.1 ++ rb.2.1 ++ (mapGate2 tbl rb.2.2.2 rb.2.2.1 ra.1 rb.1).2.1,
       (mapGate2 tbl rb.2.2.2 rb.2.2.1 ra.1 rb.1).2.2.1,
       (mapGate2 tbl rb.2.2.2 rb.2.2.1 ra.1 rb.1).2.2.2) := by
  have hlab : ra.1.length = rb.1.length := by rw [Ga.len, Gb.len]
  have hraB : ∀ b ∈ ra.1, BLt rb.2.2.1 b :=
    fun b hb => BLt.mono Gb.le (Ga.bitscope b hb)
  obtain ⟨hle, hag, hglen, hgbl, hgcl, hgh, hgv⟩ :=
    mapGate2_spec tbl ra.1 rb.1 rb.2.2.2 rb.2.2.1 hlab hraB Gb.bitscope
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans Ga.le (Nat.le_trans Gb.le hle)
  · exact ((hag.mono (Nat.le_trans Ga.le Gb.le)).trans
      (Gb.agree.mono Ga.le)).trans Ga.agree
  · rw [hglen, Ga.len]
  · exact hgbl
  · intro cl hcl b hb
    rcases List.mem_append.mp hcl with hcl | hcl
    · rcases List.mem_append.mp hcl with hcl | hcl
      · exact BLt.mono (Nat.le_trans Gb.le hle) (Ga.cnfscope cl hcl b hb)
      · exact BLt.mono hle (Gb.cnfscope cl hcl b hb)
    · exact hgcl cl hcl b hb
  · refine Holds.append (Holds.append ?_ ?_) hgh
    · exact Holds_stable ((hag.mono Gb.le).trans Gb.agree).symm Ga.cnfscope Ga.holds
    · exact Holds_stable hag.symm Gb.cnfscope Gb.holds
  · intro i hi
    rw [hgv i (by rw [Ga.len]; exact hi), hlsb i hi]
    congr 1
    · rw [denote_stable Gb.agree (getD_BLt Ga.bitscope i)]
      exact Ga.getD_denote i
    · exact Gb.getD_denote i

/-- Assemble a `Good` for an over-approximated node (fresh vars, no clauses). -/
theorem good_over {σ : St} {t w : Nat} (bv : BitVec w) (n : Nat) (f : Var → Bool) :
    Good σ t bv n f
      ((freshBits n w f (fun i => bv.getLsbD i)).1, [],
       (freshBits n w f (fun i => bv.getLsbD i)).2.1,
       (freshBits n w f (fun i => bv.getLsbD i)).2.2) := by
  obtain ⟨hle, hag, hlen, hbl, hval⟩ := freshBits_spec n w f (fun i => bv.getLsbD i)
  exact ⟨hle, hag, hlen, hbl, by intro cl hcl; simp at hcl, Holds.nil, hval⟩


theorem bv1_getLsbD (x : BitVec 1) : x.getLsbD 0 = decide (x = 1#1) := by
  revert x; decide

/-- Assemble a `Good` for a `mux` node from the control/then/else sub-`Good`s. -/
theorem good_mux {σ : St} {t w : Nat} {cv : BitVec 1} {tv fv : BitVec w}
    {n : Nat} {f : Var → Bool}
    {rc rt rf : List Bit × BCnf × Nat × (Var → Bool)}
    (Gc : Good σ t cv n f rc)
    (Gt : Good σ t tv rc.2.2.1 rc.2.2.2 rt)
    (Gf : Good σ t fv rt.2.2.1 rt.2.2.2 rf) :
    Good σ t (if cv = 1#1 then tv else fv) n f
      ((mapMux (rc.1.getD 0 (Bit.const false)) rf.2.2.2 rf.2.2.1 rt.1 rf.1).1,
       rc.2.1 ++ rt.2.1 ++ rf.2.1 ++
         (mapMux (rc.1.getD 0 (Bit.const false)) rf.2.2.2 rf.2.2.1 rt.1 rf.1).2.1,
       (mapMux (rc.1.getD 0 (Bit.const false)) rf.2.2.2 rf.2.2.1 rt.1 rf.1).2.2.1,
       (mapMux (rc.1.getD 0 (Bit.const false)) rf.2.2.2 rf.2.2.1 rt.1 rf.1).2.2.2) := by
  set cb := rc.1.getD 0 (Bit.const false) with hcb
  have hcbl : BLt rf.2.2.1 cb :=
    BLt.mono (Nat.le_trans Gt.le Gf.le) (getD_BLt Gc.bitscope 0)
  have htf : rt.1.length = rf.1.length := by rw [Gt.len, Gf.len]
  have hrtB : ∀ b ∈ rt.1, BLt rf.2.2.1 b := fun b hb => BLt.mono Gf.le (Gt.bitscope b hb)
  obtain ⟨hle, hag, hmlen, hmbl, hmcl, hmh, hmv⟩ :=
    mapMux_spec cb rt.1 rf.1 rf.2.2.2 rf.2.2.1 htf hcbl hrtB Gf.bitscope
  -- control bit value under rf.f
  have hcval : cb.denote rf.2.2.2 = decide (cv = 1#1) := by
    rw [denote_stable ((Gf.agree.mono Gt.le).trans Gt.agree) (getD_BLt Gc.bitscope 0),
      Gc.getD_denote 0, bv1_getLsbD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans Gc.le (Nat.le_trans Gt.le (Nat.le_trans Gf.le hle))
  · exact (((hag.mono (Nat.le_trans Gc.le (Nat.le_trans Gt.le Gf.le))).trans
      (Gf.agree.mono (Nat.le_trans Gc.le Gt.le))).trans (Gt.agree.mono Gc.le)).trans Gc.agree
  · rw [hmlen, Gt.len]
  · exact hmbl
  · intro cl hcl b hb
    rcases List.mem_append.mp hcl with hcl | hcl
    · rcases List.mem_append.mp hcl with hcl | hcl
      · rcases List.mem_append.mp hcl with hcl | hcl
        · exact BLt.mono (Nat.le_trans Gt.le (Nat.le_trans Gf.le hle))
            (Gc.cnfscope cl hcl b hb)
        · exact BLt.mono (Nat.le_trans Gf.le hle) (Gt.cnfscope cl hcl b hb)
      · exact BLt.mono hle (Gf.cnfscope cl hcl b hb)
    · exact hmcl cl hcl b hb
  · refine Holds.append (Holds.append (Holds.append ?_ ?_) ?_) hmh
    · exact Holds_stable (((hag.mono (Nat.le_trans Gt.le Gf.le)).trans
        (Gf.agree.mono Gt.le)).trans Gt.agree).symm Gc.cnfscope Gc.holds
    · exact Holds_stable ((hag.mono Gf.le).trans Gf.agree).symm Gt.cnfscope Gt.holds
    · exact Holds_stable hag.symm Gf.cnfscope Gf.holds
  · intro i hi
    rw [hmv i (by rw [Gt.len]; exact hi), hcval]
    have htv : (rt.1.getD i (Bit.const false)).denote rf.2.2.2 = tv.getLsbD i := by
      rw [denote_stable Gf.agree (getD_BLt Gt.bitscope i)]; exact Gt.getD_denote i
    have hfv : (rf.1.getD i (Bit.const false)).denote rf.2.2.2 = fv.getLsbD i :=
      Gf.getD_denote i
    rw [htv, hfv, muxTbl]
    by_cases hc : cv = 1#1
    · simp [hc]
    · simp [hc]


/-- **Encoding soundness (the easy Tseitin direction).** For every real
state `σ`, the assignment `blast` threads out satisfies all the CNF's
clauses, and every output bit denotes the corresponding bit of the
expression's real value. This is the lemma the BMC/k-induction soundness
theorems rely on: a real counterexample trace yields a satisfying
assignment, so a kernel-checked UNSAT rules out any real counterexample. -/
theorem blast_spec (t : Nat) (σ : St) :
    ∀ {w : Nat} (e : Expr w) (n : Nat) (f : Var → Bool), RegOK f σ t →
    Good σ t (e.eval σ) n f (blast t σ e n f) := by
  intro w e
  induction e with
  | lit v =>
    intro n f _
    rw [show blast t σ (Expr.lit v) n f = (litBits v, [], n, f) from rfl]
    refine ⟨Nat.le_refl _, fun _ _ => rfl, litBits_length v, ?_,
      by intro cl hcl; simp at hcl, Holds.nil, ?_⟩
    · intro b hb; simp only [litBits, List.mem_map, List.mem_range] at hb
      obtain ⟨i, _, rfl⟩ := hb; trivial
    · intro i hi; rw [litBits_getD v f i hi]; rfl
  | reg w nm =>
    intro n f hreg
    rw [show blast t σ (Expr.reg w nm) n f = (regBits t nm w, [], n, f) from rfl]
    refine ⟨Nat.le_refl _, fun _ _ => rfl, regBits_length t nm w,
      ?_, by intro cl hcl; simp at hcl, Holds.nil, ?_⟩
    · intro b hb; simp only [regBits, List.mem_map, List.mem_range] at hb
      obtain ⟨i, _, rfl⟩ := hb; trivial
    · intro i hi
      rw [regBits_getD t nm w f i hi, hreg nm w i]
      show ((σ.regs nm w).getLsbD i == true) = _; simp; rfl
  | and a b iha ihb =>
    intro n f hreg
    have Ga := iha n f hreg
    exact good_bin (· && ·) Ga
      (ihb (blast t σ a n f).2.2.1 (blast t σ a n f).2.2.2 (RegOK_of_agree hreg Ga.agree))
      (fun i hi => by show (a.eval σ &&& b.eval σ).getLsbD i = _; rw [BitVec.getLsbD_and])
  | or a b iha ihb =>
    intro n f hreg
    have Ga := iha n f hreg
    exact good_bin (· || ·) Ga
      (ihb (blast t σ a n f).2.2.1 (blast t σ a n f).2.2.2 (RegOK_of_agree hreg Ga.agree))
      (fun i hi => by show (a.eval σ ||| b.eval σ).getLsbD i = _; rw [BitVec.getLsbD_or])
  | xor a b iha ihb =>
    intro n f hreg
    have Ga := iha n f hreg
    exact good_bin (· ^^ ·) Ga
      (ihb (blast t σ a n f).2.2.1 (blast t σ a n f).2.2.2 (RegOK_of_agree hreg Ga.agree))
      (fun i hi => by show (a.eval σ ^^^ b.eval σ).getLsbD i = _; rw [BitVec.getLsbD_xor])
  | not a iha =>
    intro n f hreg
    have Ga := iha n f hreg
    rw [show blast t σ (Expr.not a) n f
        = ((blast t σ a n f).1.map Bit.not, (blast t σ a n f).2.1,
           (blast t σ a n f).2.2.1, (blast t σ a n f).2.2.2) from rfl]
    refine ⟨Ga.le, Ga.agree, ?_, ?_, Ga.cnfscope, Ga.holds, ?_⟩
    · rw [List.length_map]; exact Ga.len
    · intro bb hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      exact BLt.not (Ga.bitscope b' hb')
    · intro i hi
      rw [map_getD Bit.not _ i (Bit.const false) (Bit.const false) (by rw [Ga.len]; exact hi),
        Bit.denote_not, Ga.getD_denote i,
        show (Expr.not a).eval σ = ~~~(a.eval σ) from rfl, BitVec.getLsbD_not]
      simp [hi]
  | mux c tt ff ihc iht ihf =>
    intro n f hreg
    have Gc := ihc n f hreg
    have Gt := iht (blast t σ c n f).2.2.1 (blast t σ c n f).2.2.2 (RegOK_of_agree hreg Gc.agree)
    have Gf := ihf (blast t σ tt (blast t σ c n f).2.2.1 (blast t σ c n f).2.2.2).2.2.1
      (blast t σ tt (blast t σ c n f).2.2.1 (blast t σ c n f).2.2.2).2.2.2
      (RegOK_of_agree (RegOK_of_agree hreg Gc.agree) Gt.agree)
    have hmux := good_mux Gc Gt Gf
    show Good σ t ((Expr.mux c tt ff).eval σ) n f _
    rw [show (Expr.mux c tt ff).eval σ
      = if c.eval σ = 1#1 then tt.eval σ else ff.eval σ from rfl]
    exact hmux
  | @slice wa a lo width iha =>
    intro n f hreg
    have Ga := iha n f hreg
    rw [show blast t σ (Expr.slice a lo width) n f
        = ((List.range width).map
            (fun j => (blast t σ a n f).1.getD (lo + j) (Bit.const false)),
           (blast t σ a n f).2.1, (blast t σ a n f).2.2.1, (blast t σ a n f).2.2.2)
        from rfl]
    refine ⟨Ga.le, Ga.agree, ?_, ?_, Ga.cnfscope, Ga.holds, ?_⟩
    · show ((List.range width).map _).length = width; simp
    · intro bb hb
      simp only [List.mem_map, List.mem_range] at hb
      obtain ⟨j, _, rfl⟩ := hb
      exact getD_BLt Ga.bitscope _
    · intro i hi
      rw [range_map_getD _ _ _ _ hi, Ga.getD_denote (lo + i)]
      show (a.eval σ).getLsbD (lo + i) = ((a.eval σ).extractLsb' lo width).getLsbD i
      rw [BitVec.getLsbD_extractLsb']; simp [hi]
  | @zext wa a w' iha =>
    intro n f hreg
    have Ga := iha n f hreg
    rw [show blast t σ (Expr.zext a w') n f
        = ((List.range w').map (fun j => (blast t σ a n f).1.getD j (Bit.const false)),
           (blast t σ a n f).2.1, (blast t σ a n f).2.2.1, (blast t σ a n f).2.2.2)
        from rfl]
    refine ⟨Ga.le, Ga.agree, ?_, ?_, Ga.cnfscope, Ga.holds, ?_⟩
    · show ((List.range w').map _).length = w'; simp
    · intro bb hb
      simp only [List.mem_map, List.mem_range] at hb
      obtain ⟨j, _, rfl⟩ := hb; exact getD_BLt Ga.bitscope _
    · intro i hi
      rw [range_map_getD _ _ _ _ hi, Ga.getD_denote i]
      show (a.eval σ).getLsbD i = ((a.eval σ).setWidth w').getLsbD i
      rw [BitVec.getLsbD_setWidth]; simp [hi]
  | @sext wa a w' iha =>
    intro n f hreg
    have Ga := iha n f hreg
    rw [show blast t σ (Expr.sext a w') n f
        = ((List.range w').map (fun j =>
              if j < wa then (blast t σ a n f).1.getD j (Bit.const false)
              else (blast t σ a n f).1.getD (wa - 1) (Bit.const false)),
           (blast t σ a n f).2.1, (blast t σ a n f).2.2.1, (blast t σ a n f).2.2.2)
        from rfl]
    refine ⟨Ga.le, Ga.agree, ?_, ?_, Ga.cnfscope, Ga.holds, ?_⟩
    · show ((List.range w').map _).length = w'; simp
    · intro bb hb
      simp only [List.mem_map, List.mem_range] at hb
      obtain ⟨j, _, rfl⟩ := hb
      by_cases hj : j < wa <;> simp only [hj, if_true, if_false] <;> exact getD_BLt Ga.bitscope _
    · intro i hi
      rw [range_map_getD _ _ _ _ hi]
      show (if i < wa then (blast t σ a n f).1.getD i (Bit.const false)
              else (blast t σ a n f).1.getD (wa - 1) (Bit.const false)).denote _
            = ((a.eval σ).signExtend w').getLsbD i
      rw [BitVec.getLsbD_signExtend]
      by_cases hj : i < wa
      · rw [if_pos hj, Ga.getD_denote i]; simp [hi, hj]
      · rw [if_neg hj, Ga.getD_denote _]
        simp only [hi, decide_true, Bool.true_and, hj, if_false]
        rw [BitVec.msb_eq_getLsbD_last]
  | memRead dw m addr _ => intro n f _; exact good_over _ n f
  | add a b _ _ => intro n f _; exact good_over _ n f
  | sub a b _ _ => intro n f _; exact good_over _ n f
  | shl a b _ _ => intro n f _; exact good_over _ n f
  | shr a b _ _ => intro n f _; exact good_over _ n f
  | eq a b _ _ => intro n f _; exact good_over _ n f
  | ult a b _ _ => intro n f _; exact good_over _ n f
  | slt a b _ _ => intro n f _; exact good_over _ n f

/-! ## Structural independence from the concrete state

`blast`'s clause list, output bits, and aux counter depend only on the
expression, time index and starting counter — never on the concrete state
`σ` or the base assignment `f` (which affect only the returned assignment).
This lets the engines build one `σ`-free CNF and instantiate the satisfying
assignment from any real trace (needed for k-induction's free-start step
query). -/

theorem freshBits_struct (n w : Nat) (f f' : Var → Bool) (vals vals' : Nat → Bool) :
    (freshBits n w f vals).1 = (freshBits n w f' vals').1 ∧
    (freshBits n w f vals).2.1 = (freshBits n w f' vals').2.1 := by
  induction w generalizing n f f' vals vals' with
  | zero => exact ⟨rfl, rfl⟩
  | succ w ih =>
    obtain ⟨hb, hn⟩ := ih (n + 1) (setV f n (vals 0)) (setV f' n (vals' 0))
      (fun i => vals (i + 1)) (fun i => vals' (i + 1))
    exact ⟨by simp only [freshBits]; rw [hb], by simp only [freshBits]; rw [hn]⟩

theorem mapGate2_struct (tbl : Bool → Bool → Bool) (n : Nat) :
    ∀ (xs ys : List Bit) (f f' : Var → Bool),
    (mapGate2 tbl f n xs ys).1 = (mapGate2 tbl f' n xs ys).1 ∧
    (mapGate2 tbl f n xs ys).2.1 = (mapGate2 tbl f' n xs ys).2.1 ∧
    (mapGate2 tbl f n xs ys).2.2.1 = (mapGate2 tbl f' n xs ys).2.2.1 := by
  intro xs
  induction xs generalizing n with
  | nil => intro ys f f'; exact ⟨rfl, rfl, rfl⟩
  | cons x xs ih =>
    intro ys f f'
    cases ys with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons y ys =>
      obtain ⟨hb, hc, hn⟩ := ih (n + 1) ys (setV f n (tbl (x.denote f) (y.denote f)))
        (setV f' n (tbl (x.denote f') (y.denote f')))
      refine ⟨?_, ?_, ?_⟩
      · simp only [mapGate2]; rw [hb]
      · simp only [mapGate2]; rw [hc]
      · simp only [mapGate2]; exact hn

theorem mapMux_struct (c : Bit) (n : Nat) :
    ∀ (ts gs : List Bit) (f f' : Var → Bool),
    (mapMux c f n ts gs).1 = (mapMux c f' n ts gs).1 ∧
    (mapMux c f n ts gs).2.1 = (mapMux c f' n ts gs).2.1 ∧
    (mapMux c f n ts gs).2.2.1 = (mapMux c f' n ts gs).2.2.1 := by
  intro ts
  induction ts generalizing n with
  | nil => intro gs f f'; exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
    intro gs f f'
    cases gs with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons g gs =>
      obtain ⟨hb, hc, hn⟩ := ih (n + 1) gs
        (setV f n (muxTbl (c.denote f) (t.denote f) (g.denote f)))
        (setV f' n (muxTbl (c.denote f') (t.denote f') (g.denote f')))
      refine ⟨?_, ?_, ?_⟩
      · simp only [mapMux]; rw [hb]
      · simp only [mapMux]; rw [hc]
      · simp only [mapMux]; exact hn

/-- `blast`'s bits, clauses and counter are independent of `σ` and `f`. -/
theorem blast_struct (t : Nat) (σ σ' : St) :
    ∀ {w : Nat} (e : Expr w) (n : Nat) (f f' : Var → Bool),
    (blast t σ e n f).1 = (blast t σ' e n f').1 ∧
    (blast t σ e n f).2.1 = (blast t σ' e n f').2.1 ∧
    (blast t σ e n f).2.2.1 = (blast t σ' e n f').2.2.1 := by
  intro w e
  induction e with
  | lit v => intro n f f'; exact ⟨rfl, rfl, rfl⟩
  | reg w nm => intro n f f'; exact ⟨rfl, rfl, rfl⟩
  | and a b iha ihb =>
    intro n f f'
    obtain ⟨hab, hac, han⟩ := iha n f f'
    obtain ⟨hbb, hbc, hbn⟩ :=
      ihb (blast t σ a n f).2.2.1 (blast t σ a n f).2.2.2 (blast t σ' a n f').2.2.2
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [blast, ← han, ← hab, ← hac, ← hbb, ← hbc, ← hbn]
    · exact (mapGate2_struct (· && ·) _ _ _ _ _).1
    · rw [(mapGate2_struct (· && ·) _ _ _ _ _).2.1]
    · exact (mapGate2_struct (· && ·) _ _ _ _ _).2.2
  | or a b iha ihb =>
    intro n f f'
    obtain ⟨hab, hac, han⟩ := iha n f f'
    obtain ⟨hbb, hbc, hbn⟩ :=
      ihb (blast t σ a n f).2.2.1 (blast t σ a n f).2.2.2 (blast t σ' a n f').2.2.2
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [blast, ← han, ← hab, ← hac, ← hbb, ← hbc, ← hbn]
    · exact (mapGate2_struct (· || ·) _ _ _ _ _).1
    · rw [(mapGate2_struct (· || ·) _ _ _ _ _).2.1]
    · exact (mapGate2_struct (· || ·) _ _ _ _ _).2.2
  | xor a b iha ihb =>
    intro n f f'
    obtain ⟨hab, hac, han⟩ := iha n f f'
    obtain ⟨hbb, hbc, hbn⟩ :=
      ihb (blast t σ a n f).2.2.1 (blast t σ a n f).2.2.2 (blast t σ' a n f').2.2.2
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [blast, ← han, ← hab, ← hac, ← hbb, ← hbc, ← hbn]
    · exact (mapGate2_struct (· ^^ ·) _ _ _ _ _).1
    · rw [(mapGate2_struct (· ^^ ·) _ _ _ _ _).2.1]
    · exact (mapGate2_struct (· ^^ ·) _ _ _ _ _).2.2
  | not a iha =>
    intro n f f'
    obtain ⟨hb, hc, hn⟩ := iha n f f'
    exact ⟨by simp only [blast]; rw [hb], by simp only [blast]; rw [hc], by
      simp only [blast]; rw [hn]⟩
  | mux c tt ff ihc iht ihf =>
    intro n f f'
    obtain ⟨hcb, hcc, hcn⟩ := ihc n f f'
    obtain ⟨htb, htc, htn⟩ := iht (blast t σ c n f).2.2.1 (blast t σ c n f).2.2.2
      (blast t σ' c n f').2.2.2
    obtain ⟨hfb, hfc, hfn⟩ :=
      ihf (blast t σ tt (blast t σ c n f).2.2.1 (blast t σ c n f).2.2.2).2.2.1
      (blast t σ tt (blast t σ c n f).2.2.1 (blast t σ c n f).2.2.2).2.2.2
      (blast t σ' tt (blast t σ c n f).2.2.1 (blast t σ' c n f').2.2.2).2.2.2
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [blast, ← hcn, ← htn, ← hcb, ← htb, ← htc, ← hfb, ← hfc, ← hfn]
    · exact (mapMux_struct _ _ _ _ _ _).1
    · rw [(mapMux_struct _ _ _ _ _ _).2.1, hcc]
    · exact (mapMux_struct _ _ _ _ _ _).2.2
  | slice a lo width iha =>
    intro n f f'
    obtain ⟨hb, hc, hn⟩ := iha n f f'
    exact ⟨by simp only [blast]; rw [hb], by simp only [blast]; rw [hc], by
      simp only [blast]; rw [hn]⟩
  | zext a w' iha =>
    intro n f f'
    obtain ⟨hb, hc, hn⟩ := iha n f f'
    exact ⟨by simp only [blast]; rw [hb], by simp only [blast]; rw [hc], by
      simp only [blast]; rw [hn]⟩
  | sext a w' iha =>
    intro n f f'
    obtain ⟨hb, hc, hn⟩ := iha n f f'
    exact ⟨by simp only [blast]; rw [hb], by simp only [blast]; rw [hc], by
      simp only [blast]; rw [hn]⟩
  | memRead dw m addr _ =>
    intro n f f'
    refine ⟨?_, rfl, ?_⟩
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).1
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).2
  | add a b _ _ =>
    intro n f f'
    refine ⟨?_, rfl, ?_⟩
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).1
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).2
  | sub a b _ _ =>
    intro n f f'
    refine ⟨?_, rfl, ?_⟩
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).1
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).2
  | shl a b _ _ =>
    intro n f f'
    refine ⟨?_, rfl, ?_⟩
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).1
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).2
  | shr a b _ _ =>
    intro n f f'
    refine ⟨?_, rfl, ?_⟩
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).1
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).2
  | eq a b _ _ =>
    intro n f f'
    refine ⟨?_, rfl, ?_⟩
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).1
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).2
  | ult a b _ _ =>
    intro n f f'
    refine ⟨?_, rfl, ?_⟩
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).1
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).2
  | slt a b _ _ =>
    intro n f f'
    refine ⟨?_, rfl, ?_⟩
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).1
    · simp only [blast]; exact (freshBits_struct n _ f f' _ _).2


end Loom.Dp.Cnf
