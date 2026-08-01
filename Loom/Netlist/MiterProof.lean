-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Netlist.Miter

/-!
# The encoder, proved (D32) — part 2: the µVerilog side

`blastE` (`Loom/Netlist/Miter.lean`) turns a µVerilog `Expr` into bits over
the shared free variables. This file proves it **faithful**: for every
expression in the verified fragment, the bits it returns denote exactly the
bits of `Expr.eval` on the state the assignment describes — and both
directions of that (a model of the clauses forces the bits; every state
extends to a model). See `Loom/Netlist/Encode.lean` for `EncA`.

`shl` and `shr` are *not* in the fragment: their barrel shifter is on the
unverified path. `encVerified` is the decidable predicate the tool
evaluates to report which side-A expressions are covered.
-/

namespace Loom.Netlist

open Loom.Dp.Cnf
open Loom.Emit.MicroVerilog

/-! ## The state an assignment describes -/

/-- Build a bit vector from a bit function (LSB = index 0). -/
def bvOfFn : (w : Nat) → (Nat → Bool) → BitVec w
  | 0, _ => 0#0
  | k + 1, b => BitVec.cons (b k) (bvOfFn k b)

theorem bvOfFn_getLsbD : ∀ (w : Nat) (b : Nat → Bool) (i : Nat), i < w →
    (bvOfFn w b).getLsbD i = b i
  | 0, _, _, h => absurd h (by omega)
  | k + 1, b, i, h => by
    rw [bvOfFn, BitVec.getLsbD_cons]
    by_cases hi : i = k
    · simp [hi]
    · simp only [hi, if_false]
      exact bvOfFn_getLsbD k b i (by omega)

/-- The µVerilog state a CNF assignment describes: bit `i` of the register
or input `name` (declared width `w`) is the shared free variable
`stateBit name w i`. Memories are irrelevant — `blastE` refuses every
memory read (the checker compares the *cut* reading, in which a read is a
free symbol). -/
def stOf (f : Var → Bool) : Loom.Emit.MicroVerilog.St where
  regs := fun n w => bvOfFn w (fun i => f (.reg 0 n w i))
  mems := fun _ _ w => 0#w

theorem stOf_regs (f : Var → Bool) (n : String) (w i : Nat) (h : i < w) :
    ((stOf f).regs n w).getLsbD i = (stateBit n w i).denote f := by
  simp [stOf, bvOfFn_getLsbD w _ i h, stateBit, Bit.denote]

/-- An assignment's state depends only on its named variables, so it is the
same for any two assignments that agree below any `n₀`. -/
theorem stOf_congr {n₀ : Nat} {f g : Var → Bool} (ha : Agree n₀ f g) : stOf f = stOf g := by
  have : ∀ (n : String) (w : Nat), ((stOf f).regs n w) = ((stOf g).regs n w) := by
    intro n w
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [stOf_regs f n w i hi, stOf_regs g n w i hi]
    exact (show BitWF n₀ (stateBit n w i) by trivial).denote_congr ha
  have hregs : (stOf f).regs = (stOf g).regs := by
    funext n w; exact this n w
  cases hf : stOf f
  cases hg : stOf g
  simp_all [stOf]

theorem Stable.eval {n₀ w : Nat} (e : Expr w) : Stable n₀ (fun f => e.eval (stOf f)) := by
  intro f g ha
  show e.eval (stOf f) = e.eval (stOf g)
  rw [stOf_congr ha]

/-! ## The verified fragment -/

/-- The operators whose encoding D32 proves. `shl`/`shr` are excluded: the
barrel shifter in `Miter.shiftBits` is on the unverified path, and the tool
says so per design. `memRead` is excluded because `blastE` refuses it (the
comparison is made on the cut reading of the text). -/
def encVerified : {w : Nat} → Expr w → Bool
  | _, .lit _ => true
  | _, .reg _ _ => true
  | _, .memRead _ _ _ => false
  | _, .and a b => encVerified a && encVerified b
  | _, .or a b => encVerified a && encVerified b
  | _, .xor a b => encVerified a && encVerified b
  | _, .not a => encVerified a
  | _, .add a b => encVerified a && encVerified b
  | _, .sub a b => encVerified a && encVerified b
  | _, .shl _ _ => false
  | _, .shr _ _ => false
  | _, .eq a b => encVerified a && encVerified b
  | _, .ult a b => encVerified a && encVerified b
  | _, .slt _ _ => false
  | _, .mux c t f => encVerified c && encVerified t && encVerified f
  | _, .slice a _ _ => encVerified a
  | _, .zext a _ => encVerified a
  | _, .sext a _ => encVerified a

/-! ## `blastE` is faithful -/

theorem EncA_throw {n₀ w : Nat} {msg : String} {val : (Var → Bool) → BitVec w}
    (hst : Stable n₀ val) : EncA n₀ w (throw msg) val := by
  refine ⟨fun s bits s' hrun => by rw [run_throw] at hrun; simp at hrun, hst, ?_⟩
  intro s a s' hs hn hrun
  rw [run_throw] at hrun
  simp at hrun

theorem bv1_cases (v : BitVec 1) : v = 0#1 ∨ v = 1#1 := by
  have hlt : v.toNat < 2 := by simpa using v.isLt
  rcases Nat.lt_or_ge v.toNat 1 with h | h
  · left; apply BitVec.eq_of_toNat_eq; simp; omega
  · right; apply BitVec.eq_of_toNat_eq; simp; omega

theorem bv1_getLsbD_zero (v : BitVec 1) : (v.getLsbD 0 = true) ↔ v = 1#1 := by
  rcases bv1_cases v with rfl | rfl <;> simp

/-- Sequencing for bit-vector encoders: the continuation's value may depend
on the bits the first action returned. -/
theorem EncA.bindA {n₀ w w' : Nat} {ea : M (Array Bit)} {va : (Var → Bool) → BitVec w}
    {k : Array Bit → M (Array Bit)} {valB : Array Bool → (Var → Bool) → BitVec w'}
    {val : (Var → Bool) → BitVec w'}
    (ha : EncA n₀ w ea va)
    (hst : Stable n₀ val)
    (hksz : ∀ (x : Array Bit), x.size = w →
        ∀ s bits s', M.run (k x) s = (.ok bits, s') → bits.size = w')
    (hk : ∀ (x : Array Bit) (n : Nat), n₀ ≤ n → (∀ b ∈ x, BitWF n b) → x.size = w →
        EncA n w' (k x) (fun f => valB (x.map (·.denote f)) f))
    (hval : ∀ f, valB (bitsOf (va f)) f = val f) :
    EncA n₀ w' (do let x ← ea; k x) val := by
  obtain ⟨hsza, hsta, henca⟩ := ha
  refine ⟨?_, hst, ?_⟩
  · intro s bits s' hrun
    rw [run_bind] at hrun
    revert hrun
    cases hr : M.run ea s with
    | mk r s₁ =>
      cases r with
      | error e => intro hh; simp at hh
      | ok x =>
        simp only []
        intro hh
        exact hksz x (hsza s x s₁ hr) s₁ bits s' hh
  · refine Enc.congr (α := Array Bit) (β := Array Bool)
      (val := fun f => bitsOf (valB (bitsOf (va f)) f))
      (fun f => by show bitsOf (valB (bitsOf (va f)) f) = bitsOf (val f); rw [hval f]) ?_
    refine Enc.bind' (α := Array Bit) (α' := Array Bit) (P := fun x => x.size = w)
      (valA := fun f => bitsOf (va f))
      (valB := fun xv f => bitsOf (valB xv f)) hsta.bits hsza henca ?_
    intro x n hn hwx hxw
    exact (hk x n hn hwx hxw).2.2

theorem arr_getElem?_pos {α : Type} (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]? = some a[i] := (Array.getElem?_eq_some_getElem_iff a i h).mpr trivial

theorem arr_getElem?_neg {α : Type} (a : Array α) (i : Nat) (h : ¬ i < a.size) :
    a[i]? = none := ((none_eq_getElem?_iff a i).mpr h).symm

/-- Reading past the end of the blasted operand denotes `false`, on both
sides — the encoder's `getD (.const false)` and its Boolean shadow. -/
theorem denote_getD (x : Array Bit) (f : Var → Bool) (j : Nat) :
    (x[j]?.getD (.const false)).denote f = ((x.map (·.denote f))[j]?.getD false) := by
  rw [Array.getElem?_map]
  cases hx : x[j]? <;> simp

/-! ## Arithmetic: the ripple-carry adder and the comparators -/

/-- The carry into position `k` of the ripple-carry adder, as a value. -/
def carryB (xv yv : Array Bool) (cin : Bool) : Nat → Bool
  | 0 => cin
  | k + 1 => (xv[k]!).atLeastTwo (yv[k]!) (carryB xv yv cin k)

/-- The low `k` sum bits, as a value. -/
def sumB (xv yv : Array Bool) (cin : Bool) : Nat → Array Bool
  | 0 => #[]
  | k + 1 => (sumB xv yv cin k).push ((xv[k]!) ^^ ((yv[k]!) ^^ carryB xv yv cin k))

theorem sumB_size (xv yv : Array Bool) (cin : Bool) : ∀ k : Nat, (sumB xv yv cin k).size = k
  | 0 => rfl
  | k + 1 => by rw [sumB, Array.size_push, sumB_size xv yv cin k]

theorem carryB_eq {w : Nat} (x y : BitVec w) (cin : Bool) :
    ∀ k : Nat, k ≤ w → carryB (bitsOf x) (bitsOf y) cin k = BitVec.carry k x y cin
  | 0, _ => by rw [carryB, BitVec.carry_zero]
  | k + 1, h => by
    rw [carryB, BitVec.carry_succ, carryB_eq x y cin k (by omega),
      bitsOf_getElem_bang x k (by omega), bitsOf_getElem_bang y k (by omega)]

theorem sumB_eq {w : Nat} (x y : BitVec w) (cin : Bool) :
    ∀ k : Nat, k ≤ w → ∀ i, i < k →
      (sumB (bitsOf x) (bitsOf y) cin k)[i]! =
        (x + y + BitVec.setWidth w (BitVec.ofBool cin)).getLsbD i
  | 0, _, i, hi => absurd hi (by omega)
  | k + 1, h, i, hi => by
    rw [sumB]
    have hsz : ∀ m : Nat, (sumB (bitsOf x) (bitsOf y) cin m).size = m :=
      fun m => sumB_size _ _ _ m
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [getElem_bang _ i (by rw [Array.size_push, hsz]; omega),
        Array.getElem_push_lt (by rw [hsz]; omega), ← getElem_bang _ i (by rw [hsz]; omega)]
      exact sumB_eq x y cin k (by omega) i hik
    · have : i = k := by omega
      subst this
      rw [getElem_bang _ i (by rw [Array.size_push, hsz]; omega)]
      rw [Array.getElem_push]
      simp only [hsz, Nat.lt_irrefl, dif_neg, reduceDIte]
      rw [BitVec.getLsbD_add_add_bool (by omega), carryB_eq x y cin i (by omega),
        bitsOf_getElem_bang x i (by omega), bitsOf_getElem_bang y i (by omega)]

theorem Enc_addBitsGo {n₀ : Nat} (a b : Array Bit) (cin : Bit)
    (hwa : ∀ i : Nat, BitWF n₀ (a[i]!)) (hwb : ∀ i : Nat, BitWF n₀ (b[i]!))
    (hwc : BitWF n₀ cin) :
    ∀ k : Nat, Enc n₀ (addBitsGo a b cin k)
      (fun f => (sumB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k,
                 carryB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k))
  | 0 => by
    rw [addBitsGo]
    refine Enc.pure ⟨fun c hc => absurd hc (by simp), hwc⟩ (fun f => ?_)
    show ((#[] : Array Bit).map (·.denote f), cin.denote f) = _
    rw [sumB, carryB]
    simp
  | k + 1 => by
    rw [addBitsGo]
    have hmap : ∀ (arr : Array Bit) (f : Var → Bool) (i : Nat),
        (arr.map (·.denote f))[i]! = (arr[i]!).denote f := by
      intro arr f i
      rcases Nat.lt_or_ge i arr.size with h | h
      · exact getElem_bang_map arr f i h
      · rw [getElem!_neg _ _ (by simpa using h), getElem!_neg _ _ (by omega)]
        rfl
    refine Enc.congr (α := Array Bit × Bit) (β := Array Bool × Bool)
      (val := fun f => ((sumB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k).push
            (((a[k]!).denote f ^^ (b[k]!).denote f) ^^
              carryB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k),
          ((a[k]!).denote f && (b[k]!).denote f) ||
            (((a[k]!).denote f ^^ (b[k]!).denote f) &&
              carryB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k)))
      (fun f => ?_) ?_
    · simp only []
      rw [sumB, carryB, hmap a f k, hmap b f k]
      refine Prod.ext ?_ ?_ <;> simp only [] <;>
        cases hx : (a[k]!).denote f <;> cases hy : (b[k]!).denote f <;>
        cases hc : carryB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k <;> simp
    refine Enc.bind (α := Array Bit × Bit) (α' := Array Bit × Bit)
      (valA := fun f => (sumB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k,
        carryB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k))
      (valB := fun pv f => (pv.1.push (((a[k]!).denote f ^^ (b[k]!).denote f) ^^ pv.2),
        ((a[k]!).denote f && (b[k]!).denote f) ||
          (((a[k]!).denote f ^^ (b[k]!).denote f) && pv.2)))
      ?_ (Enc_addBitsGo a b cin hwa hwb hwc k) ?_
    · -- stability of the recursive value
      intro f g ha
      have hb : ∀ (arr : Array Bit) (i : Nat), BitWF n₀ (arr[i]!) →
          (arr.map (·.denote f))[i]! = (arr.map (·.denote g))[i]! := by
        intro arr i hw
        rw [hmap arr f i, hmap arr g i, hw.denote_congr ha]
      have hc : ∀ m : Nat,
          carryB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) m
            = carryB (a.map (·.denote g)) (b.map (·.denote g)) (cin.denote g) m := by
        intro m
        induction m with
        | zero => exact hwc.denote_congr ha
        | succ n ih => rw [carryB, carryB, hb a n (hwa n), hb b n (hwb n), ih]
      have hs : ∀ m : Nat,
          sumB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) m
            = sumB (a.map (·.denote g)) (b.map (·.denote g)) (cin.denote g) m := by
        intro m
        induction m with
        | zero => rfl
        | succ n ih => rw [sumB, sumB, hb a n (hwa n), hb b n (hwb n), hc n, ih]
      rw [Prod.ext_iff]
      exact ⟨hs k, hc k⟩
    -- the tail: five gates and a `pure`
    rintro ⟨out, cb⟩ n hn ⟨hwout, hwc2⟩
    simp only [den_prod, den_bit, den_bits]
    have hwx : BitWF n (a[k]!) := BitWF.mono hn (hwa k)
    have hwy : BitWF n (b[k]!) := BitWF.mono hn (hwb k)
    refine Enc.bind (α := Bit) (α' := Array Bit × Bit)
      (valA := fun f => (a[k]!).denote f ^^ (b[k]!).denote f)
      (valB := fun tv f => (((out.map (·.denote f))).push (tv ^^ (cb.denote f)),
        ((a[k]!).denote f && (b[k]!).denote f) || (tv && (cb.denote f))))
      (Stable.bop (Nat.le_refl n) (fun _ _ => Stable.const _) hwx hwy)
      (Enc_mkXor hwx hwy) ?_
    intro t n1 hn1 hwt
    refine Enc.bind (α := Bit) (α' := Array Bit × Bit)
      (valA := fun f => t.denote f ^^ (cb.denote f))
      (valB := fun sv f => (((out.map (·.denote f))).push sv,
        ((a[k]!).denote f && (b[k]!).denote f) || (t.denote f && (cb.denote f))))
      (Stable.bop (Nat.le_refl n1) (fun _ _ => Stable.const _) hwt (BitWF.mono hn1 hwc2))
      (Enc_mkXor hwt (BitWF.mono hn1 hwc2)) ?_
    intro sum n2 hn2 hwsum
    refine Enc.bind (α := Bit) (α' := Array Bit × Bit)
      (valA := fun f => (a[k]!).denote f && (b[k]!).denote f)
      (valB := fun abv f => (((out.map (·.denote f))).push (sum.denote f),
        abv || (t.denote f && (cb.denote f))))
      (Stable.bop (Nat.le_refl n2) (fun _ _ => Stable.const _)
        (BitWF.mono (Nat.le_trans hn1 hn2) hwx) (BitWF.mono (Nat.le_trans hn1 hn2) hwy))
      (Enc_mkAnd (BitWF.mono (Nat.le_trans hn1 hn2) hwx)
        (BitWF.mono (Nat.le_trans hn1 hn2) hwy)) ?_
    intro ab n3 hn3 hwab
    refine Enc.bind (α := Bit) (α' := Array Bit × Bit)
      (valA := fun f => t.denote f && (cb.denote f))
      (valB := fun tcv f => (((out.map (·.denote f))).push (sum.denote f),
        ab.denote f || tcv))
      (Stable.bop (Nat.le_refl n3) (fun _ _ => Stable.const _)
        (BitWF.mono hn3 (BitWF.mono hn2 hwt))
        (BitWF.mono hn3 (BitWF.mono hn2 (BitWF.mono hn1 hwc2))))
      (Enc_mkAnd (BitWF.mono hn3 (BitWF.mono hn2 hwt))
        (BitWF.mono hn3 (BitWF.mono hn2 (BitWF.mono hn1 hwc2)))) ?_
    intro tc n4 hn4 hwtc
    refine Enc.bind (α := Bit) (α' := Array Bit × Bit)
      (valA := fun f => ab.denote f || tc.denote f)
      (valB := fun cv f => (((out.map (·.denote f))).push (sum.denote f), cv))
      (Stable.bop (Nat.le_refl n4) (fun _ _ => Stable.const _) (BitWF.mono hn4 hwab) hwtc)
      (Enc_mkOr (BitWF.mono hn4 hwab) hwtc) ?_
    intro c' n5 hn5 hwc'
    refine Enc.pure ⟨fun z hz => ?_, hwc'⟩ (fun f => ?_)
    · rcases Array.mem_push.mp hz with h | h
      · exact BitWF.mono (Nat.le_trans hn2 (Nat.le_trans hn3 (Nat.le_trans hn4 hn5)))
          (BitWF.mono hn1 (hwout z h))
      · exact h ▸ BitWF.mono (Nat.le_trans hn3 (Nat.le_trans hn4 hn5)) hwsum
    · show ((out.push sum).map (·.denote f), c'.denote f) = _
      simp

theorem bitsOf_not {w : Nat} (v : BitVec w) : (bitsOf v).map (!·) = bitsOf (~~~v) := by
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp only [Array.size_map, bitsOf_size] at h₁
    rw [Array.getElem_map, bitsOf_getElem, bitsOf_getElem, BitVec.getLsbD_not]
    simp [h₁]

theorem addBitsGo_size {a b : Array Bit} {cin : Bit} :
    ∀ (k : Nat) (s : St) (p : Array Bit × Bit) (s' : St),
      M.run (addBitsGo a b cin k) s = (.ok p, s') → p.1.size = k
  | 0, s, p, s', hrun => by rw [addBitsGo, run_pure] at hrun; cases hrun; simp
  | k + 1, s, p, s', hrun => by
    rw [addBitsGo, run_bind] at hrun
    revert hrun
    cases hr : M.run (addBitsGo a b cin k) s with
    | mk r s₁ =>
      cases r with
      | error e => intro hh; simp at hh
      | ok q =>
        obtain ⟨out, c⟩ := q
        simp only []
        intro hh
        have hout : out.size = k := addBitsGo_size k s (out, c) s₁ hr
        -- walk the five gates: each is a bind, and the final `pure` pushes one bit
        revert hh
        rw [run_bind]
        cases h1 : M.run (mkXor a[k]! b[k]!) s₁ with
        | mk r1 s2 => cases r1 with
          | error e => intro hh; simp at hh
          | ok t =>
            simp only []
            rw [run_bind]
            cases h2 : M.run (mkXor t c) s2 with
            | mk r2 s3 => cases r2 with
              | error e => intro hh; simp at hh
              | ok sum =>
                simp only []
                rw [run_bind]
                cases h3 : M.run (mkAnd a[k]! b[k]!) s3 with
                | mk r3 s4 => cases r3 with
                  | error e => intro hh; simp at hh
                  | ok ab =>
                    simp only []
                    rw [run_bind]
                    cases h4 : M.run (mkAnd t c) s4 with
                    | mk r4 s5 => cases r4 with
                      | error e => intro hh; simp at hh
                      | ok tc =>
                        simp only []
                        rw [run_bind]
                        cases h5 : M.run (mkOr ab tc) s5 with
                        | mk r5 s6 => cases r5 with
                          | error e => intro hh; simp at hh
                          | ok c' =>
                            simp only [run_pure]
                            intro hh
                            cases hh
                            simp [hout]

/-- The ripple-carry shape: `add` and `sub`, the latter as `a + ~b + 1`. -/
theorem EncA_addLike {n₀ w : Nat} {ea eb : M (Array Bit)} {va vb val : (Var → Bool) → BitVec w}
    (cin : Bit) (cinv : Bool) (hcinden : ∀ f, cin.denote f = cinv) (hwcin : BitWF n₀ cin)
    (mod : Array Bit → Array Bit) (φ : Array Bool → Array Bool) (modv : BitVec w → BitVec w)
    (hmodsz : ∀ y : Array Bit, y.size = w → (mod y).size = w)
    (hmodwf : ∀ (n : Nat) (y : Array Bit), (∀ b ∈ y, BitWF n b) → ∀ b ∈ mod y, BitWF n b)
    (hmodden : ∀ (f : Var → Bool) (y : Array Bit), (mod y).map (·.denote f) = φ (y.map (·.denote f)))
    (hφ : ∀ v : BitVec w, φ (bitsOf v) = bitsOf (modv v))
    (ha : EncA n₀ w ea va) (hb : EncA n₀ w eb vb)
    (hval : ∀ f, val f = va f + modv (vb f) + BitVec.setWidth w (BitVec.ofBool cinv)) :
    EncA n₀ w (ea >>= fun x => eb >>= fun y =>
      addBits x (mod y) cin >>= fun p => Pure.pure p.1) val := by
  obtain ⟨hsza, hsta, henca⟩ := ha
  obtain ⟨hszb, hstb, hencb⟩ := hb
  have hstval : Stable n₀ val := by
    intro f g hag
    rw [hval f, hval g, hsta f g hag, hstb f g hag]
  refine ⟨?_, hstval, ?_⟩
  · -- width
    intro s bits s' hrun
    rw [run_bind] at hrun
    revert hrun
    cases hr : M.run ea s with
    | mk r s₁ =>
      cases r with
      | error e => intro hh; simp at hh
      | ok x =>
        simp only []
        rw [run_bind]
        cases hr2 : M.run eb s₁ with
        | mk r2 s₂ =>
          cases r2 with
          | error e => intro hh; simp at hh
          | ok y =>
            simp only []
            rw [run_bind]
            cases hr3 : M.run (addBits x (mod y) cin) s₂ with
            | mk r3 s₃ =>
              cases r3 with
              | error e => intro hh; simp at hh
              | ok p =>
                simp only [run_pure]
                intro hh
                cases hh
                rw [← hsza s x s₁ hr]
                exact addBitsGo_size x.size s₂ p _ hr3
  · refine Enc.congr (α := Array Bit) (β := Array Bool)
      (val := fun f => sumB (bitsOf (va f)) (φ (bitsOf (vb f))) cinv w) (fun f => ?_) ?_
    · show sumB (bitsOf (va f)) (φ (bitsOf (vb f))) cinv w = bitsOf (val f)
      rw [hφ (vb f)]
      apply Array.ext
      · rw [bitsOf_size, sumB_size]
      · intro i h₁ h₂
        simp only [bitsOf_size] at h₂
        rw [← getElem_bang _ i h₁, sumB_eq (va f) (modv (vb f)) cinv w (Nat.le_refl _) i h₂,
          bitsOf_getElem, hval f]
    refine Enc.bind' (α := Array Bit) (α' := Array Bit) (P := fun x => x.size = w)
      (valA := fun f => bitsOf (va f))
      (valB := fun xv f => sumB xv (φ (bitsOf (vb f))) cinv w)
      hsta.bits hsza henca ?_
    intro x n hn hwx hxw
    refine Enc.bind' (α := Array Bit) (α' := Array Bit) (P := fun y => y.size = w)
      (valA := fun f => bitsOf (vb f))
      (valB := fun yv f => sumB (x.map (·.denote f)) (φ yv) cinv w)
      (Stable.mono hn hstb.bits) hszb (Enc.mono hn hencb) ?_
    intro y n' hn' hwy hyw
    refine Enc.congr (α := Array Bit) (β := Array Bool)
      (val := fun f => sumB (x.map (·.denote f)) ((mod y).map (·.denote f)) (cin.denote f) x.size)
      (fun f => by
        show sumB (x.map (·.denote f)) ((mod y).map (·.denote f)) (cin.denote f) x.size = _
        rw [hmodden f y, hcinden f, hxw]
        rfl) ?_
    refine Enc.bind (α := Array Bit × Bit) (α' := Array Bit)
      (valA := fun f => (sumB (x.map (·.denote f)) ((mod y).map (·.denote f)) (cin.denote f) x.size,
        carryB (x.map (·.denote f)) ((mod y).map (·.denote f)) (cin.denote f) x.size))
      (valB := fun pv _ => pv.1) ?_ ?_ ?_
    · -- stability of the pair value
      intro f g hag
      have hwxb : ∀ i : Nat, BitWF n' (x[i]!) := by
        intro i
        rcases Nat.lt_or_ge i x.size with h | h
        · rw [getElem_bang x i h]; exact BitWF.mono hn' (hwx _ (Array.getElem_mem h))
        · rw [getElem!_neg _ _ (by omega)]; trivial
      have hwyb : ∀ i : Nat, BitWF n' ((mod y)[i]!) := by
        intro i
        rcases Nat.lt_or_ge i (mod y).size with h | h
        · rw [getElem_bang (mod y) i h]
          exact hmodwf n' y hwy _ (Array.getElem_mem h)
        · rw [getElem!_neg _ _ (by omega)]; trivial
      have hmap : ∀ (arr : Array Bit) (i : Nat), BitWF n' (arr[i]!) →
          (arr.map (·.denote f))[i]! = (arr.map (·.denote g))[i]! := by
        intro arr i hw
        rcases Nat.lt_or_ge i arr.size with h | h
        · rw [getElem_bang_map arr f i h, getElem_bang_map arr g i h, hw.denote_congr hag]
        · rw [getElem!_neg _ _ (by simpa using h), getElem!_neg _ _ (by simpa using h)]
      have hc : ∀ m : Nat, carryB (x.map (·.denote f)) ((mod y).map (·.denote f)) (cin.denote f) m
          = carryB (x.map (·.denote g)) ((mod y).map (·.denote g)) (cin.denote g) m := by
        intro m
        induction m with
        | zero => exact (BitWF.mono (Nat.le_trans hn hn') hwcin).denote_congr hag
        | succ q ih => rw [carryB, carryB, hmap x q (hwxb q), hmap (mod y) q (hwyb q), ih]
      have hs : ∀ m : Nat, sumB (x.map (·.denote f)) ((mod y).map (·.denote f)) (cin.denote f) m
          = sumB (x.map (·.denote g)) ((mod y).map (·.denote g)) (cin.denote g) m := by
        intro m
        induction m with
        | zero => rfl
        | succ q ih => rw [sumB, sumB, hmap x q (hwxb q), hmap (mod y) q (hwyb q), hc q, ih]
      rw [Prod.ext_iff]
      exact ⟨hs x.size, hc x.size⟩
    · refine Enc_addBitsGo x (mod y) cin ?_ ?_ (BitWF.mono (Nat.le_trans hn hn') hwcin) x.size
      · intro i
        rcases Nat.lt_or_ge i x.size with h | h
        · rw [getElem_bang x i h]; exact BitWF.mono hn' (hwx _ (Array.getElem_mem h))
        · rw [getElem!_neg _ _ (by omega)]; trivial
      · intro i
        rcases Nat.lt_or_ge i (mod y).size with h | h
        · rw [getElem_bang (mod y) i h]; exact hmodwf n' y hwy _ (Array.getElem_mem h)
        · rw [getElem!_neg _ _ (by omega)]; trivial
    · rintro ⟨out, c⟩ n2 hn2 ⟨hwout, hwc⟩
      exact Enc.pure hwout (fun f => rfl)

instance : Deno (List Bit) (List Bool) where
  wf := fun n l => ∀ b ∈ l, BitWF n b
  den := fun f l => l.map (·.denote f)
  den_congr := by
    intro n f g l hwf ha
    induction l with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons]
      rw [(hwf b (by simp)).denote_congr ha, ih (fun x hx => hwf x (by simp [hx]))]
  wf_mono := fun h hwf b hb => BitWF.mono h (hwf b hb)

@[simp] theorem den_list (f : Var → Bool) (l : List Bit) :
    (Deno.den f l : List Bool) = l.map (·.denote f) := rfl

/-! ### Comparators -/

/-- One bit of result, as a width-1 vector. -/
theorem EncA_of_bit {n₀ : Nat} {act : M Bit} {vb : (Var → Bool) → Bool}
    {val : (Var → Bool) → BitVec 1} (h : Enc n₀ act vb) (hst : Stable n₀ val)
    (hval : ∀ f, (val f).getLsbD 0 = vb f) :
    EncA n₀ 1 (act >>= fun b => Pure.pure #[b]) val := by
  have hstvb : Stable n₀ vb := by
    intro f g ha; rw [← hval f, ← hval g, hst f g ha]
  refine ⟨?_, hst, ?_⟩
  · intro s bits s' hrun
    rw [run_bind] at hrun
    revert hrun
    cases hr : M.run act s with
    | mk r s₁ =>
      cases r with
      | error e => intro hh; simp at hh
      | ok b => intro hh; simp only [run_pure] at hh; cases hh; simp
  · refine Enc.congr (α := Array Bit) (β := Array Bool) (val := fun f => #[vb f])
      (fun f => ?_) ?_
    · apply Array.ext
      · simp
      · intro i h₁ h₂
        have hi : i = 0 := by simp at h₁; omega
        subst hi
        rw [bitsOf_getElem, hval f]
        rfl
    refine Enc.bind (α := Bit) (α' := Array Bit) (valA := vb)
      (valB := fun bv _ => #[bv]) hstvb h ?_
    intro b n hn hwb
    refine Enc.pure (fun c hc => ?_) (fun f => by simp [den_bits])
    have : c = b := by simpa using hc
    exact this ▸ hwb

/-- The per-bit equalities, as a value. -/
def eqValB (xv yv : Array Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => (!(xv[k]! ^^ yv[k]!)) :: eqValB xv yv k

theorem Enc_eqAcc {n₀ : Nat} (a b : Array Bit)
    (hwa : ∀ i : Nat, BitWF n₀ (a[i]!)) (hwb : ∀ i : Nat, BitWF n₀ (b[i]!)) :
    ∀ k : Nat, Enc n₀ (eqAcc a b k)
      (fun f => eqValB (a.map (·.denote f)) (b.map (·.denote f)) k)
  | 0 => Enc.pure (fun c hc => absurd hc (by simp)) (fun f => rfl)
  | k + 1 => by
    rw [eqAcc]
    have hmap : ∀ (arr : Array Bit) (f : Var → Bool) (i : Nat),
        (arr.map (·.denote f))[i]! = (arr[i]!).denote f := by
      intro arr f i
      rcases Nat.lt_or_ge i arr.size with h | h
      · exact getElem_bang_map arr f i h
      · rw [getElem!_neg _ _ (by simpa using h), getElem!_neg _ _ (by omega)]
        rfl
    refine Enc.congr (α := List Bit) (β := List Bool)
      (val := fun f => (!((a[k]!).denote f ^^ (b[k]!).denote f)) ::
        eqValB (a.map (·.denote f)) (b.map (·.denote f)) k) (fun f => ?_) ?_
    · show _ = eqValB (a.map (·.denote f)) (b.map (·.denote f)) (k + 1)
      rw [show eqValB (a.map (·.denote f)) (b.map (·.denote f)) (k + 1)
            = (!((a.map (·.denote f))[k]! ^^ (b.map (·.denote f))[k]!)) ::
              eqValB (a.map (·.denote f)) (b.map (·.denote f)) k from rfl,
        hmap a f k, hmap b f k]
    refine Enc.bind (α := List Bit) (α' := List Bit)
      (valA := fun f => eqValB (a.map (·.denote f)) (b.map (·.denote f)) k)
      (valB := fun lv f => (!((a[k]!).denote f ^^ (b[k]!).denote f)) :: lv) ?_
      (Enc_eqAcc a b hwa hwb k) ?_
    · intro f g ha
      induction k with
      | zero => rfl
      | succ m ih =>
        show (!((a.map (·.denote f))[m]! ^^ (b.map (·.denote f))[m]!)) :: _
          = (!((a.map (·.denote g))[m]! ^^ (b.map (·.denote g))[m]!)) :: _
        rw [hmap a f m, hmap b f m, hmap a g m, hmap b g m,
          (hwa m).denote_congr ha, (hwb m).denote_congr ha]
        exact congrArg _ ih
    · intro l n hn hwl
      refine Enc.bind (α := Bit) (α' := List Bit)
        (valA := fun f => (a[k]!).denote f ^^ (b[k]!).denote f)
        (valB := fun tv f => (!tv) :: (l.map (·.denote f)))
        (Stable.bop (n₀ := n₀) hn (fun _ _ => Stable.const _)
          (BitWF.mono hn (hwa k)) (BitWF.mono hn (hwb k)))
        (Enc.mono hn (Enc_mkXor (hwa k) (hwb k))) ?_
      intro t n' hn' hwt
      refine Enc.pure (fun c hc => ?_) (fun f => by simp [den_list])
      rcases List.mem_cons.mp hc with h' | h'
      · exact h' ▸ hwt.not
      · exact BitWF.mono hn' (hwl c h')

theorem eqValB_all {w : Nat} (x y : BitVec w) :
    ∀ k : Nat, k ≤ w → ((eqValB (bitsOf x) (bitsOf y) k).all id = true ↔
      ∀ i, i < k → x.getLsbD i = y.getLsbD i)
  | 0, _ => by simp [eqValB]
  | k + 1, h => by
    rw [eqValB]
    simp only [List.all_cons, Bool.and_eq_true, id, Bool.not_eq_true',
      eqValB_all x y k (by omega), bitsOf_getElem_bang x k (by omega),
      bitsOf_getElem_bang y k (by omega)]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i k with h' | h'
      · exact h2 i h'
      · have : i = k := by omega
        subst this
        cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all
    · intro hall
      refine ⟨?_, fun i hi => hall i (by omega)⟩
      have := hall k (by omega)
      rw [this]
      cases y.getLsbD k <;> rfl

/-- Stability of the accumulated values, once and for all. -/
theorem Stable_eqValB {n₀ : Nat} {a b : Array Bit}
    (hwa : ∀ i : Nat, BitWF n₀ (a[i]!)) (hwb : ∀ i : Nat, BitWF n₀ (b[i]!)) (k : Nat) :
    Stable n₀ (fun f => eqValB (a.map (·.denote f)) (b.map (·.denote f)) k) := by
  intro f g ha
  have hmap : ∀ (arr : Array Bit) (i : Nat), BitWF n₀ (arr[i]!) →
      (arr.map (·.denote f))[i]! = (arr.map (·.denote g))[i]! := by
    intro arr i hw
    rcases Nat.lt_or_ge i arr.size with h | h
    · rw [getElem_bang_map arr f i h, getElem_bang_map arr g i h, hw.denote_congr ha]
    · rw [getElem!_neg _ _ (by simpa using h), getElem!_neg _ _ (by simpa using h)]
  induction k with
  | zero => rfl
  | succ m ih =>
    show (!((a.map (·.denote f))[m]! ^^ (b.map (·.denote f))[m]!)) :: _
      = (!((a.map (·.denote g))[m]! ^^ (b.map (·.denote g))[m]!)) :: _
    rw [hmap a m (hwa m), hmap b m (hwb m)]
    exact congrArg _ ih

theorem Stable_carryB {n₀ : Nat} {a b : Array Bit} {cin : Bit}
    (hwa : ∀ i : Nat, BitWF n₀ (a[i]!)) (hwb : ∀ i : Nat, BitWF n₀ (b[i]!))
    (hwc : BitWF n₀ cin) (k : Nat) :
    Stable n₀ (fun f =>
      carryB (a.map (·.denote f)) (b.map (·.denote f)) (cin.denote f) k) := by
  intro f g ha
  have hmap : ∀ (arr : Array Bit) (i : Nat), BitWF n₀ (arr[i]!) →
      (arr.map (·.denote f))[i]! = (arr.map (·.denote g))[i]! := by
    intro arr i hw
    rcases Nat.lt_or_ge i arr.size with h | h
    · rw [getElem_bang_map arr f i h, getElem_bang_map arr g i h, hw.denote_congr ha]
    · rw [getElem!_neg _ _ (by simpa using h), getElem!_neg _ _ (by simpa using h)]
  induction k with
  | zero => exact hwc.denote_congr ha
  | succ m ih =>
    show (Bool.atLeastTwo ((a.map (·.denote f))[m]!) ((b.map (·.denote f))[m]!) _) = _
    rw [hmap a m (hwa m), hmap b m (hwb m)]
    exact congrArg _ ih

theorem Enc_eqBits {n₀ : Nat} (a b : Array Bit)
    (hwa : ∀ i : Nat, BitWF n₀ (a[i]!)) (hwb : ∀ i : Nat, BitWF n₀ (b[i]!)) :
    Enc n₀ (eqBits a b)
      (fun f => (eqValB (a.map (·.denote f)) (b.map (·.denote f)) a.size).all id) := by
  refine Enc.bind (α := List Bit) (α' := Bit)
    (valA := fun f => eqValB (a.map (·.denote f)) (b.map (·.denote f)) a.size)
    (valB := fun lv _ => lv.all id) (Stable_eqValB hwa hwb a.size)
    (Enc_eqAcc a b hwa hwb a.size) ?_
  intro l n hn hwl
  refine Enc.congr (α := Bit) (β := Bool) (val := fun f => l.all (fun x => x.denote f))
    (fun f => by simp) (Enc_mkAndList l hwl)

theorem map_not_wf {n₀ : Nat} {b : Array Bit} (hwb : ∀ i : Nat, BitWF n₀ (b[i]!)) :
    ∀ i : Nat, BitWF n₀ ((b.map (·.not))[i]!) := by
  intro i
  rcases Nat.lt_or_ge i (b.map (·.not)).size with h | h
  · rw [getElem_bang _ i h, Array.getElem_map]
    have hb : b[i]'(by simpa using h) = b[i]! := (getElem_bang b i (by simpa using h)).symm
    rw [hb]
    exact (hwb i).not
  · rw [getElem!_neg _ _ (by omega)]; trivial

theorem Enc_ultBits {n₀ : Nat} (a b : Array Bit)
    (hwa : ∀ i : Nat, BitWF n₀ (a[i]!)) (hwb : ∀ i : Nat, BitWF n₀ (b[i]!)) :
    Enc n₀ (ultBits a b)
      (fun f => !(carryB (a.map (·.denote f)) ((b.map (·.not)).map (·.denote f))
        true a.size)) := by
  refine Enc.congr (α := Bit) (β := Bool)
    (val := fun f => !(carryB (a.map (·.denote f)) ((b.map (·.not)).map (·.denote f))
      ((Bit.const true).denote f) a.size)) (fun f => rfl) ?_
  refine Enc.bind (α := Array Bit × Bit) (α' := Bit)
    (valA := fun f => (sumB (a.map (·.denote f)) ((b.map (·.not)).map (·.denote f))
        ((Bit.const true).denote f) a.size,
      carryB (a.map (·.denote f)) ((b.map (·.not)).map (·.denote f))
        ((Bit.const true).denote f) a.size))
    (valB := fun pv _ => !pv.2) ?_
    (Enc_addBitsGo a (b.map (·.not)) (.const true) hwa (map_not_wf hwb) (by trivial) a.size) ?_
  · intro f g ha
    have h2 := Stable_carryB (cin := Bit.const true) hwa (map_not_wf hwb) (by trivial) a.size f g ha
    have h1 : sumB (a.map (·.denote f)) ((b.map (·.not)).map (·.denote f))
          ((Bit.const true).denote f) a.size
        = sumB (a.map (·.denote g)) ((b.map (·.not)).map (·.denote g))
          ((Bit.const true).denote g) a.size := by
      have hmap : ∀ (arr : Array Bit) (i : Nat), BitWF n₀ (arr[i]!) →
          (arr.map (·.denote f))[i]! = (arr.map (·.denote g))[i]! := by
        intro arr i hw
        rcases Nat.lt_or_ge i arr.size with h | h
        · rw [getElem_bang_map arr f i h, getElem_bang_map arr g i h, hw.denote_congr ha]
        · rw [getElem!_neg _ _ (by simpa using h), getElem!_neg _ _ (by simpa using h)]
      induction a.size with
      | zero => rfl
      | succ m ih =>
        show (sumB _ _ _ m).push _ = (sumB _ _ _ m).push _
        rw [hmap a m (hwa m), hmap (b.map (·.not)) m (map_not_wf hwb m),
          show carryB (a.map (·.denote f)) ((b.map (·.not)).map (·.denote f))
              ((Bit.const true).denote f) m
            = carryB (a.map (·.denote g)) ((b.map (·.not)).map (·.denote g))
              ((Bit.const true).denote g) m from
            Stable_carryB (cin := Bit.const true) hwa (map_not_wf hwb) (by trivial) m f g ha, ih]
    rw [Prod.ext_iff]
    exact ⟨h1, h2⟩
  · rintro ⟨out, c⟩ n hn ⟨hwout, hwc⟩
    exact Enc.pure hwc.not (fun f => by simp [den_bit, den_prod])

/-- The comparator shape: blast both operands, then one bit of result. -/
theorem EncA_cmp {n₀ w : Nat} {ea eb : M (Array Bit)} {va vb : (Var → Bool) → BitVec w}
    {val : (Var → Bool) → BitVec 1} {op : Array Bit → Array Bit → M Bit}
    {bop : Array Bool → Array Bool → Bool}
    (hop : ∀ (n : Nat) (x y : Array Bit), n₀ ≤ n → (∀ b ∈ x, BitWF n b) → (∀ b ∈ y, BitWF n b) →
        x.size = w → y.size = w →
        Enc n (op x y) (fun f => bop (x.map (·.denote f)) (y.map (·.denote f))))
    (ha : EncA n₀ w ea va) (hb : EncA n₀ w eb vb)
    (hstval : Stable n₀ val)
    (hval : ∀ f, (val f).getLsbD 0 = bop (bitsOf (va f)) (bitsOf (vb f))) :
    EncA n₀ 1 (ea >>= fun x => eb >>= fun y => op x y >>= fun z => Pure.pure #[z]) val := by
  obtain ⟨hsza, hsta, henca⟩ := ha
  obtain ⟨hszb, hstb, hencb⟩ := hb
  have hact : Enc n₀ (ea >>= fun x => eb >>= fun y => op x y)
      (fun f => bop (bitsOf (va f)) (bitsOf (vb f))) := by
    refine Enc.bind' (α := Array Bit) (α' := Bit) (P := fun x => x.size = w)
      (valA := fun f => bitsOf (va f)) (valB := fun xv f => bop xv (bitsOf (vb f)))
      hsta.bits hsza henca ?_
    intro x n hn hwx hxw
    refine Enc.bind' (α := Array Bit) (α' := Bit) (P := fun y => y.size = w)
      (valA := fun f => bitsOf (vb f))
      (valB := fun yv f => bop (x.map (·.denote f)) yv)
      (Stable.mono hn hstb.bits) hszb (Enc.mono hn hencb) ?_
    intro y n' hn' hwy hyw
    exact hop n' x y (Nat.le_trans hn hn') (fun b hb => BitWF.mono hn' (hwx b hb)) hwy hxw hyw
  have hconv : (ea >>= fun x => eb >>= fun y => op x y >>= fun z => Pure.pure #[z])
      = ((ea >>= fun x => eb >>= fun y => op x y) >>= fun z => Pure.pure #[z]) := by
    rw [bind_assoc]
    exact congrArg _ (funext fun x => (bind_assoc _ _ _).symm)
  rw [hconv]
  exact EncA_of_bit hact hstval hval

/-! ## The main theorem

`blastE` encodes exactly `Expr.eval`, for every expression in the verified
fragment, in both directions. -/
set_option maxHeartbeats 1000000 in
theorem Enc_blastE (syms : List (String × Nat)) :
    ∀ {w : Nat} (e : Expr w), encVerified e = true →
      EncA 0 w (blastE syms e) (fun f => e.eval (stOf f))
  | w, .lit v, _ => by
    show EncA 0 w (Pure.pure (Array.ofFn (n := w) fun i : Fin w => Bit.const (v.getLsbD i.val))) _
    exact EncA_ofFn _ _ (fun _ => by trivial) (fun f i => by simp [Expr.eval])
  | _, .reg w' n, _ => by
    rw [blastE]
    cases hfind : syms.find? (fun kv => kv.1 == n) with
    | none => exact EncA_throw (Stable.eval _)
    | some p =>
      obtain ⟨nm, dw⟩ := p
      simp only []
      by_cases hdw : dw != w'
      · simp only [hdw, if_true]
        exact EncA_throw (Stable.eval _)
      · simp only [hdw, if_false]
        have hdw' : dw = w' := by simpa using hdw
        subst hdw'
        show EncA 0 dw (Pure.pure (Array.ofFn (n := dw) fun i : Fin dw =>
          stateBit n dw i.val)) _
        refine EncA_ofFn _ _ (fun _ => by trivial) (fun f i => ?_)
        rw [show ((Expr.reg dw n).eval (stOf f)) = (stOf f).regs n dw from rfl,
          stOf_regs f n dw i.val i.isLt]
  | _, .memRead _ _ _, h => by simp only [encVerified] at h; exact Bool.noConfusion h
  | _, .and a b, h => by
    simp only [encVerified, Bool.and_eq_true] at h
    rw [blastE]
    exact EncA_binop (bop := fun _ p q => p && q)
      (fun _ x y _ hx hy => Enc_mkAnd hx hy) (fun _ _ => Stable.const _)
      (Enc_blastE syms a h.1) (Enc_blastE syms b h.2)
      (fun f i hi => by simp [Expr.eval])
  | _, .or a b, h => by
    simp only [encVerified, Bool.and_eq_true] at h
    rw [blastE]
    exact EncA_binop (bop := fun _ p q => p || q)
      (fun _ x y _ hx hy => Enc_mkOr hx hy) (fun _ _ => Stable.const _)
      (Enc_blastE syms a h.1) (Enc_blastE syms b h.2)
      (fun f i hi => by simp [Expr.eval])
  | _, .xor a b, h => by
    simp only [encVerified, Bool.and_eq_true] at h
    rw [blastE]
    exact EncA_binop (bop := fun _ p q => p ^^ q)
      (fun _ x y _ hx hy => Enc_mkXor hx hy) (fun _ _ => Stable.const _)
      (Enc_blastE syms a h.1) (Enc_blastE syms b h.2)
      (fun f i hi => by simp [Expr.eval])
  | w, .not a, h => by
    simp only [encVerified] at h
    rw [blastE]
    refine EncA.bindPure (Enc_blastE syms a h) (fun x => x.map (·.not))
      (fun ys => ys.map (!·)) (fun v => ~~~v) (fun x hx => by simp [hx]) ?_ ?_ ?_
    · intro n x hx c hc
      obtain ⟨b, hb, rfl⟩ := Array.mem_map.mp hc
      exact (hx b hb).not
    · intro f x
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_map] at h₁ h₂
        simp
    · intro v
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_map, bitsOf_size] at h₁
        rw [Array.getElem_map, bitsOf_getElem, bitsOf_getElem, BitVec.getLsbD_not]
        simp [h₁]
  | _, .add a b, h => by
    simp only [encVerified, Bool.and_eq_true] at h
    rw [blastE]
    refine EncA_addLike (.const false) false (fun _ => rfl) (by trivial)
      (fun y => y) (fun ys => ys) (fun v => v) (fun y hy => hy) (fun n y hy => hy)
      (fun f y => rfl) (fun v => rfl)
      (Enc_blastE syms a h.1) (Enc_blastE syms b h.2) ?_
    intro f
    show (Expr.add a b).eval (stOf f) = _
    simp [Expr.eval]
  | _, .sub a b, h => by
    simp only [encVerified, Bool.and_eq_true] at h
    rw [blastE]
    refine EncA_addLike (.const true) true (fun _ => rfl) (by trivial)
      (fun y => y.map (·.not)) (fun ys => ys.map (!·)) (fun v => ~~~v)
      ?_ ?_ ?_ ?_ (Enc_blastE syms a h.1) (Enc_blastE syms b h.2) ?_
    · intro y hy; simpa using hy
    · intro n y hy c hc
      obtain ⟨z, hz, rfl⟩ := Array.mem_map.mp hc
      exact (hy z hz).not
    · intro f y
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_map] at h₁ h₂
        simp
    · intro v; exact bitsOf_not v
    · intro f
      show (Expr.sub a b).eval (stOf f) = _
      show a.eval (stOf f) - b.eval (stOf f) = _
      rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, ← BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.ofBool, BitVec.toNat_setWidth]
  | _, .shl _ _, h => by simp only [encVerified] at h; exact Bool.noConfusion h
  | _, .shr _ _, h => by simp only [encVerified] at h; exact Bool.noConfusion h
  | _, @Expr.eq wq a b, h => by
    simp only [encVerified, Bool.and_eq_true] at h
    rw [blastE]
    refine EncA_cmp (w := wq) (bop := fun xv yv => (eqValB xv yv wq).all id) ?_
      (Enc_blastE syms a h.1) (Enc_blastE syms b h.2) (Stable.eval _) ?_
    · intro n x y hn hwx hwy hxw hyw
      have hwx' : ∀ i : Nat, BitWF n (x[i]!) := by
        intro i
        rcases Nat.lt_or_ge i x.size with hh | hh
        · rw [getElem_bang x i hh]; exact hwx _ (Array.getElem_mem hh)
        · rw [getElem!_neg _ _ (by omega)]; trivial
      have hwy' : ∀ i : Nat, BitWF n (y[i]!) := by
        intro i
        rcases Nat.lt_or_ge i y.size with hh | hh
        · rw [getElem_bang y i hh]; exact hwy _ (Array.getElem_mem hh)
        · rw [getElem!_neg _ _ (by omega)]; trivial
      have := Enc_eqBits (n₀ := n) x y hwx' hwy'
      rw [hxw] at this
      exact this
    · intro f
      show ((Expr.eq a b).eval (stOf f)).getLsbD 0 = _
      show (if a.eval (stOf f) = b.eval (stOf f) then 1#1 else 0#1).getLsbD 0 = _
      show _ = (eqValB (bitsOf (a.eval (stOf f))) (bitsOf (b.eval (stOf f))) wq).all id
      by_cases hq : a.eval (stOf f) = b.eval (stOf f)
      · rw [if_pos hq]
        have : (eqValB (bitsOf (a.eval (stOf f))) (bitsOf (b.eval (stOf f))) wq).all id = true :=
          (eqValB_all _ _ _ (Nat.le_refl _)).mpr (fun i hi => by rw [hq])
        rw [this]
        rfl
      · rw [if_neg hq]
        have : ¬ ((eqValB (bitsOf (a.eval (stOf f))) (bitsOf (b.eval (stOf f))) wq).all id
            = true) := by
          intro hc
          exact hq (BitVec.eq_of_getLsbD_eq ((eqValB_all _ _ _ (Nat.le_refl _)).mp hc))
        rw [Bool.eq_false_iff.mpr this]
        rfl
  | _, @Expr.ult wq a b, h => by
    simp only [encVerified, Bool.and_eq_true] at h
    rw [blastE]
    refine EncA_cmp (w := wq) (bop := fun xv yv => !(carryB xv (yv.map (!·)) true wq)) ?_
      (Enc_blastE syms a h.1) (Enc_blastE syms b h.2) (Stable.eval _) ?_
    · intro n x y hn hwx hwy hxw hyw
      have hwx' : ∀ i : Nat, BitWF n (x[i]!) := by
        intro i
        rcases Nat.lt_or_ge i x.size with hh | hh
        · rw [getElem_bang x i hh]; exact hwx _ (Array.getElem_mem hh)
        · rw [getElem!_neg _ _ (by omega)]; trivial
      have hwy' : ∀ i : Nat, BitWF n (y[i]!) := by
        intro i
        rcases Nat.lt_or_ge i y.size with hh | hh
        · rw [getElem_bang y i hh]; exact hwy _ (Array.getElem_mem hh)
        · rw [getElem!_neg _ _ (by omega)]; trivial
      have hmapnot : ∀ f : Var → Bool,
          (y.map (·.not)).map (·.denote f) = (y.map (·.denote f)).map (!·) := by
        intro f
        apply Array.ext
        · simp
        · intro i h₁ h₂
          simp only [Array.size_map] at h₁ h₂
          simp
      have := Enc_ultBits (n₀ := n) x y hwx' hwy'
      rw [hxw] at this
      refine Enc.congr (α := Bit) (β := Bool) (fun f => by rw [hmapnot f]) this
    · intro f
      show ((Expr.ult a b).eval (stOf f)).getLsbD 0 = _
      show (if (a.eval (stOf f)).ult (b.eval (stOf f)) then 1#1 else 0#1).getLsbD 0
        = !(carryB (bitsOf (a.eval (stOf f))) ((bitsOf (b.eval (stOf f))).map (!·)) true wq)
      rw [bitsOf_not, carryB_eq _ _ _ _ (Nat.le_refl _), ← BitVec.ult_eq_not_carry]
      cases hu : (a.eval (stOf f)).ult (b.eval (stOf f)) <;> simp
  | _, .slt _ _, h => by simp only [encVerified] at h; exact Bool.noConfusion h
  | w, .mux c t e, h => by
    simp only [encVerified, Bool.and_eq_true] at h
    rw [blastE]
    refine EncA.bindA (Enc_blastE syms c h.1.1) (Stable.eval _)
      (valB := fun cv f => if cv[0]! = true then t.eval (stOf f) else e.eval (stOf f))
      (fun x hx => binop_size (Enc_blastE syms t h.1.2).1) ?_ ?_
    · intro x n hn hwx hxw
      refine EncA_binop (bop := fun f p q => cond ((x[0]!).denote f) p q)
        (fun n' u v hn' hu hv => Enc_mkIte ?_ hu hv) ?_
        ((Enc_blastE syms t h.1.2).mono (Nat.zero_le _))
        ((Enc_blastE syms e h.2).mono (Nat.zero_le _)) ?_
      · rw [getElem_bang x 0 (by omega)]
        exact BitWF.mono hn' (hwx _ (Array.getElem_mem (by omega)))
      · intro p q f g ha
        show cond ((x[0]!).denote f) p q = cond ((x[0]!).denote g) p q
        rw [(show BitWF n (x[0]!) by
          rw [getElem_bang x 0 (by omega)]
          exact hwx _ (Array.getElem_mem (by omega))).denote_congr ha]
      · intro f i hi
        show (if (x.map (·.denote f))[0]! = true then _ else _ : BitVec w).getLsbD i = _
        cases hb : (x[0]!).denote f <;>
          simp [getElem_bang_map x f 0 (by omega), hb]
    · intro f
      show (if (bitsOf (c.eval (stOf f)))[0]! = true then t.eval (stOf f) else e.eval (stOf f))
          = (Expr.mux c t e).eval (stOf f)
      rw [bitsOf_getElem_bang _ 0 (by omega)]
      show _ = (if c.eval (stOf f) = 1#1 then t.eval (stOf f) else e.eval (stOf f))
      by_cases hc : (c.eval (stOf f)).getLsbD 0 = true
      · rw [if_pos hc, if_pos ((bv1_getLsbD_zero _).mp hc)]
      · rw [if_neg hc, if_neg (fun hh => hc ((bv1_getLsbD_zero _).mpr hh))]
  | _, .slice a lo width, h => by
    simp only [encVerified] at h
    rw [blastE]
    refine EncA.bindPure (Enc_blastE syms a h)
      (fun x => Array.ofFn (n := width) fun i : Fin width => x[lo + i.val]?.getD (.const false))
      (fun ys => Array.ofFn (n := width) fun i : Fin width => ys[lo + i.val]?.getD false)
      (fun v => v.extractLsb' lo width) (fun x hx => by simp) ?_ ?_ ?_
    · intro n x hx c hc
      obtain ⟨i, rfl⟩ := (Array.mem_ofFn ..).mp hc
      cases hxi : x[lo + i.val]? with
      | none => simp [hxi]; trivial
      | some b => simp only [hxi, Option.getD]; exact hx b (Array.mem_of_getElem? hxi)
    · intro f x
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_map, Array.size_ofFn] at h₁
        rw [Array.getElem_map, Array.getElem_ofFn, Array.getElem_ofFn]
        exact denote_getD x f _
    · intro v
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_ofFn] at h₁
        rw [Array.getElem_ofFn, bitsOf_getElem, BitVec.getLsbD_extractLsb']
        simp only [h₁, decide_true, Bool.true_and]
        rcases Nat.lt_or_ge (lo + i) (bitsOf v).size with hlt | hge
        · rw [arr_getElem?_pos _ _ hlt]
          simp [bitsOf_getElem]
        · rw [arr_getElem?_neg _ _ (by omega)]
          simp only [Option.getD]
          rw [BitVec.getLsbD_of_ge]
          simpa using hge
  | _, .zext a w', h => by
    simp only [encVerified] at h
    rw [blastE]
    refine EncA.bindPure (Enc_blastE syms a h)
      (fun x => Array.ofFn (n := w') fun i : Fin w' => x[i.val]?.getD (.const false))
      (fun ys => Array.ofFn (n := w') fun i : Fin w' => ys[i.val]?.getD false)
      (fun v => v.setWidth w') (fun x hx => by simp) ?_ ?_ ?_
    · intro n x hx c hc
      obtain ⟨i, rfl⟩ := (Array.mem_ofFn ..).mp hc
      cases hxi : x[i.val]? with
      | none => simp [hxi]; trivial
      | some b => simp only [hxi, Option.getD]; exact hx b (Array.mem_of_getElem? hxi)
    · intro f x
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_map, Array.size_ofFn] at h₁
        rw [Array.getElem_map, Array.getElem_ofFn, Array.getElem_ofFn]
        exact denote_getD x f _
    · intro v
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_ofFn] at h₁
        rw [Array.getElem_ofFn, bitsOf_getElem, BitVec.getLsbD_setWidth]
        simp only [h₁, decide_true, Bool.true_and]
        rcases Nat.lt_or_ge i (bitsOf v).size with hlt | hge
        · rw [arr_getElem?_pos _ _ hlt]
          simp [bitsOf_getElem]
        · rw [arr_getElem?_neg _ _ (by omega)]
          simp only [Option.getD]
          rw [BitVec.getLsbD_of_ge]
          simpa using hge

  | _, @Expr.sext wa a w', h => by
    simp only [encVerified] at h
    rw [blastE]
    refine EncA.bindPure (Enc_blastE syms a h)
      (fun x => Array.ofFn (n := w') fun i : Fin w' =>
        if i.val < wa then x[i.val]?.getD (.const false) else x[wa - 1]?.getD (.const false))
      (fun ys => Array.ofFn (n := w') fun i : Fin w' =>
        if i.val < wa then ys[i.val]?.getD false else ys[wa - 1]?.getD false)
      (fun v => v.signExtend w') (fun x hx => by simp) ?_ ?_ ?_
    · intro n x hx c hc
      obtain ⟨i, rfl⟩ := (Array.mem_ofFn ..).mp hc
      by_cases hi : i.val < wa
      · simp only [hi, if_true]
        cases hxi : x[i.val]? with
        | none => simp [hxi]; trivial
        | some b => simp only [hxi, Option.getD]; exact hx b (Array.mem_of_getElem? hxi)
      · simp only [hi, if_false]
        cases hxi : x[wa - 1]? with
        | none => simp [hxi]; trivial
        | some b => simp only [hxi, Option.getD]; exact hx b (Array.mem_of_getElem? hxi)
    · intro f x
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_map, Array.size_ofFn] at h₁
        rw [Array.getElem_map, Array.getElem_ofFn, Array.getElem_ofFn]
        by_cases hi : i < wa
        · simp only [hi, if_true]; exact denote_getD x f _
        · simp only [hi, if_false]; exact denote_getD x f _
    · intro v
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_ofFn] at h₁
        rw [Array.getElem_ofFn, bitsOf_getElem, BitVec.getLsbD_signExtend]
        simp only [h₁, decide_true, Bool.true_and]
        by_cases hi : i < wa
        · simp only [hi, if_true]
          rw [arr_getElem?_pos _ _ (by simpa using hi)]
          simp [bitsOf_getElem]
        · simp only [hi, if_false]
          rcases Nat.eq_zero_or_pos wa with rfl | hwa
          · rw [arr_getElem?_neg _ _ (by simp)]
            simp only [Option.getD]
            rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_of_ge]
            omega
          · rw [arr_getElem?_pos _ _ (by simp; omega)]
            simp [bitsOf_getElem, BitVec.msb_eq_getLsbD_last]

/-! ## DIMACS: normalization and numbering

`toDimacs` is the last step before the solver: it renames the `Var`s to
DIMACS ids `1 … n` and normalizes each clause (dropping repeated literals
and tautologies — required for the LRAT leg, EQCHECK_SPEC.md §Deviations).
Both are proved satisfiability-preserving here, so the normalization sits
*inside* `encode_sound`, not beside it. -/

open Std.Sat

/-- The numbering is a bijection between the ids `1 … vars.size` and the
variables in `vars`. -/
def Numbering.WF (nb : Numbering) : Prop :=
  ∀ (v : Var) (i : Nat), nb.idx[v]? = some i →
    ∃ h : i - 1 < nb.vars.size, 0 < i ∧ nb.vars[i - 1] = v

/-- One numbering extends another: ids are never reassigned and `vars` only
grows at the end. -/
def Numbering.Ext (nb nb' : Numbering) : Prop :=
  (∀ (v : Var) (i : Nat), nb.idx[v]? = some i → nb'.idx[v]? = some i) ∧
  (∀ (i : Nat) (h : i < nb.vars.size), ∃ h' : i < nb'.vars.size, nb'.vars[i] = nb.vars[i])

theorem Numbering.Ext.refl (nb : Numbering) : nb.Ext nb :=
  ⟨fun _ _ h => h, fun i h => ⟨h, rfl⟩⟩

theorem Numbering.Ext.trans {a b c : Numbering} (h₁ : a.Ext b) (h₂ : b.Ext c) : a.Ext c :=
  ⟨fun v i h => h₂.1 v i (h₁.1 v i h),
   fun i h => by
     obtain ⟨h', he⟩ := h₁.2 i h
     obtain ⟨h'', he'⟩ := h₂.2 i h'
     exact ⟨h'', by rw [he', he]⟩⟩

theorem Numbering.get_ext (nb : Numbering) (v : Var) : nb.Ext (nb.get v).2 := by
  unfold Numbering.get
  cases h : nb.idx[v]? with
  | some i => exact Numbering.Ext.refl _
  | none =>
    refine ⟨fun u j hu => ?_, fun i hi => ?_⟩
    · simp only [Std.HashMap.getElem?_insert]
      have : ¬ (v = u) := by intro hv; rw [hv] at h; rw [h] at hu; simp at hu
      simp [this, hu]
    · refine ⟨by simp only [Array.size_push]; omega, ?_⟩
      simp [Array.getElem_push_lt hi]

theorem Numbering.get_wf {nb : Numbering} (hwf : nb.WF) (v : Var) : (nb.get v).2.WF := by
  unfold Numbering.get
  cases h : nb.idx[v]? with
  | some i => exact hwf
  | none =>
    intro u j hu
    simp only [Std.HashMap.getElem?_insert] at hu
    by_cases hvu : v = u
    · subst hvu
      simp at hu
      subst hu
      exact ⟨by simp, by omega, by simp⟩
    · rw [if_neg (by simpa using hvu)] at hu
      obtain ⟨h', h0, he⟩ := hwf u j hu
      exact ⟨by simp; omega, h0, by rw [Array.getElem_push_lt h']; exact he⟩

/-- After `get`, the variable is numbered, and its id points back at it. -/
theorem Numbering.get_spec {nb : Numbering} (hwf : nb.WF) (v : Var) :
    (nb.get v).2.idx[v]? = some (nb.get v).1 ∧ 0 < (nb.get v).1 := by
  cases h : nb.idx[v]? with
  | some i =>
    have hg : nb.get v = (i, nb) := by simp [Numbering.get, h]
    rw [hg]; exact ⟨h, (hwf v i h).2.1⟩
  | none =>
    have hg : nb.get v =
        (nb.vars.size + 1, ⟨nb.idx.insert v (nb.vars.size + 1), nb.vars.push v⟩) := by
      simp [Numbering.get, h]
    rw [hg]
    exact ⟨by simp, Nat.succ_pos _⟩

/-- The Boolean assignment a DIMACS model describes, and vice versa. -/
def Corr (nb : Numbering) (f : Var → Bool) (τ : Nat → Bool) : Prop :=
  ∀ (v : Var) (i : Nat), nb.idx[v]? = some i → τ (i - 1) = f v

theorem normLits_ext : ∀ (bs : List Bit) (nb : Numbering) (sat : Bool)
    (lits : Array (Nat × Bool)), nb.Ext (normLits nb sat lits bs).2.2
  | [], nb, sat, lits => Numbering.Ext.refl _
  | .const true :: bs, nb, sat, lits => by rw [normLits]; exact normLits_ext bs nb true lits
  | .const false :: bs, nb, sat, lits => by rw [normLits]; exact normLits_ext bs nb sat lits
  | .lit v pol :: bs, nb, sat, lits => by
    rw [normLits]
    simp only []
    split
    · exact (nb.get_ext v).trans (normLits_ext bs (nb.get v).2 true lits)
    · split
      · exact (nb.get_ext v).trans (normLits_ext bs (nb.get v).2 sat lits)
      · exact (nb.get_ext v).trans (normLits_ext bs (nb.get v).2 sat _)

theorem normLits_wf : ∀ (bs : List Bit) (nb : Numbering) (sat : Bool)
    (lits : Array (Nat × Bool)), nb.WF → (normLits nb sat lits bs).2.2.WF
  | [], nb, sat, lits, h => h
  | .const true :: bs, nb, sat, lits, h => by rw [normLits]; exact normLits_wf bs nb true lits h
  | .const false :: bs, nb, sat, lits, h => by rw [normLits]; exact normLits_wf bs nb sat lits h
  | .lit v pol :: bs, nb, sat, lits, h => by
    rw [normLits]
    simp only []
    split
    · exact normLits_wf bs _ true lits (nb.get_wf h v)
    · split
      · exact normLits_wf bs _ sat lits (nb.get_wf h v)
      · exact normLits_wf bs _ sat _ (nb.get_wf h v)

/-- The heart of the normalization proof: the emitted literals, read under a
DIMACS model, say exactly what the original clause says under the
corresponding Boolean assignment — *including* the two normalizations
(a repeated literal adds nothing; a complementary pair makes the clause
true under every assignment, which is why dropping it is sound). -/
theorem normLits_spec {nbF : Numbering} {f : Var → Bool} {τ : Nat → Bool}
    (hcorr : Corr nbF f τ) :
    ∀ (bs : List Bit) (nb : Numbering) (sat : Bool) (lits : Array (Nat × Bool)),
      nb.WF → (normLits nb sat lits bs).2.2.Ext nbF →
      (((normLits nb sat lits bs).1 = true ∨
          ∃ p ∈ (normLits nb sat lits bs).2.1, τ (p.1 - 1) = p.2)
        ↔ (sat = true ∨ (∃ p ∈ lits, τ (p.1 - 1) = p.2) ∨
            ∃ b ∈ bs, b.denote f = true))
  | [], nb, sat, lits, _, _ => by
    rw [normLits]
    simp
  | .const true :: bs, nb, sat, lits, hwf, hext => by
    rw [normLits] at hext ⊢
    rw [normLits_spec hcorr bs nb true lits hwf hext]
    simp
  | .const false :: bs, nb, sat, lits, hwf, hext => by
    rw [normLits] at hext ⊢
    rw [normLits_spec hcorr bs nb sat lits hwf hext]
    simp
  | .lit v pol :: bs, nb, sat, lits, hwf, hext => by
    rw [normLits] at hext ⊢
    simp only [] at hext ⊢
    have hget := nb.get_spec hwf v
    have hwf' : (nb.get v).2.WF := nb.get_wf hwf v
    by_cases hc : lits.contains ((nb.get v).1, !pol) = true
    · rw [if_pos hc] at hext ⊢
      have hτv : τ ((nb.get v).1 - 1) = f v :=
        hcorr v _ (((normLits_ext bs (nb.get v).2 true lits).trans hext).1 v _ hget.1)
      rw [normLits_spec hcorr bs _ true lits hwf' hext]
      have hmem : ((nb.get v).1, !pol) ∈ lits := by simpa using hc
      simp only [true_or, true_iff]
      cases hτb : τ ((nb.get v).1 - 1) with
      | true =>
        cases hp : pol with
        | true =>
          exact Or.inr (Or.inr ⟨Bit.lit v true, by simp,
            by simp [Bit.denote, ← hτv, hτb]⟩)
        | false =>
          subst hp
          exact Or.inr (Or.inl ⟨_, hmem, by simp [hτb]⟩)
      | false =>
        cases hp : pol with
        | true =>
          subst hp
          exact Or.inr (Or.inl ⟨_, hmem, by simp [hτb]⟩)
        | false =>
          exact Or.inr (Or.inr ⟨Bit.lit v false, by simp,
            by simp [Bit.denote, ← hτv, hτb]⟩)
    · rw [if_neg hc] at hext ⊢
      by_cases hr : lits.contains ((nb.get v).1, pol) = true
      · rw [if_pos hr] at hext ⊢
        have hτv : τ ((nb.get v).1 - 1) = f v :=
          hcorr v _ (((normLits_ext bs (nb.get v).2 sat lits).trans hext).1 v _ hget.1)
        have hmem : ((nb.get v).1, pol) ∈ lits := by simpa using hr
        rw [normLits_spec hcorr bs _ sat lits hwf' hext]
        constructor
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (by
              obtain ⟨b, hb, hbv⟩ := h
              exact ⟨b, by simp [hb], hbv⟩))
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · obtain ⟨b, hb, hbv⟩ := h
            rcases List.mem_cons.mp hb with rfl | hb'
            · refine Or.inr (Or.inl ⟨((nb.get v).1, pol), hmem, ?_⟩)
              simp only [Bit.denote_lit, beq_iff_eq] at hbv
              simp [hτv, hbv]
            · exact Or.inr (Or.inr ⟨b, hb', hbv⟩)
      · rw [if_neg hr] at hext ⊢
        have hτv : τ ((nb.get v).1 - 1) = f v :=
          hcorr v _ (((normLits_ext bs (nb.get v).2 sat (lits.push ((nb.get v).1, pol))).trans
            hext).1 v _ hget.1)
        rw [normLits_spec hcorr bs _ sat (lits.push ((nb.get v).1, pol)) hwf' hext]
        constructor
        · rintro (h | h | h)
          · exact Or.inl h
          · obtain ⟨p, hp, hpv⟩ := h
            rcases Array.mem_push.mp hp with h' | h'
            · exact Or.inr (Or.inl ⟨p, h', hpv⟩)
            · refine Or.inr (Or.inr ⟨Bit.lit v pol, by simp, ?_⟩)
              subst h'
              simp only [Bit.denote_lit]
              simp [← hτv, hpv]
          · exact Or.inr (Or.inr (by
              obtain ⟨b, hb, hbv⟩ := h
              exact ⟨b, by simp [hb], hbv⟩))
        · rintro (h | h | h)
          · exact Or.inl h
          · obtain ⟨p, hp, hpv⟩ := h
            exact Or.inr (Or.inl ⟨p, Array.mem_push.mpr (Or.inl hp), hpv⟩)
          · obtain ⟨b, hb, hbv⟩ := h
            rcases List.mem_cons.mp hb with rfl | hb'
            · refine Or.inr (Or.inl ⟨((nb.get v).1, pol),
                Array.mem_push.mpr (Or.inr rfl), ?_⟩)
              simp only [Bit.denote_lit, beq_iff_eq] at hbv
              simp [hτv, hbv]
            · exact Or.inr (Or.inr ⟨b, hb', hbv⟩)

theorem normClauses_ext : ∀ (cls : List BClause) (nb : Numbering) (lines : Array String)
    (cnf : Array (List (Nat × Bool))), nb.Ext (normClauses nb lines cnf cls).1
  | [], nb, lines, cnf => Numbering.Ext.refl _
  | cl :: cls, nb, lines, cnf => by
    rw [normClauses]
    simp only []
    split <;> exact (normLits_ext cl nb false #[]).trans (normClauses_ext cls _ _ _)

theorem normClauses_wf : ∀ (cls : List BClause) (nb : Numbering) (lines : Array String)
    (cnf : Array (List (Nat × Bool))), nb.WF → (normClauses nb lines cnf cls).1.WF
  | [], nb, lines, cnf, h => h
  | cl :: cls, nb, lines, cnf, h => by
    rw [normClauses]
    simp only []
    split <;> exact normClauses_wf cls _ _ _ (normLits_wf cl nb false #[] h)

/-- A DIMACS clause is satisfied by the model exactly when some emitted
literal is. -/
theorem clause_eval_iff (τ : Nat → Bool) (lits : Array (Nat × Bool)) :
    CNF.Clause.eval τ (lits.toList.map (fun p => (p.1 - 1, p.2))) = true
      ↔ ∃ p ∈ lits, τ (p.1 - 1) = p.2 := by
  simp only [CNF.Clause.eval, List.any_eq_true, List.mem_map, Array.mem_toList_iff]
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, hq⟩
    exact ⟨p, hp, by simpa using hq⟩
  · rintro ⟨p, hp, hpv⟩
    exact ⟨(p.1 - 1, p.2), ⟨p, hp, rfl⟩, by simpa using hpv⟩

theorem normClauses_spec {nbF : Numbering} {f : Var → Bool} {τ : Nat → Bool}
    (hcorr : Corr nbF f τ) :
    ∀ (cls : List BClause) (nb : Numbering) (lines : Array String)
      (cnf : Array (List (Nat × Bool))), nb.WF → (normClauses nb lines cnf cls).1.Ext nbF →
      ((∀ c ∈ (normClauses nb lines cnf cls).2.2.toList, CNF.Clause.eval τ c = true)
        ↔ ((∀ c ∈ cnf.toList, CNF.Clause.eval τ c = true) ∧
            ∀ cl ∈ cls, ∃ b ∈ cl, b.denote f = true))
  | [], nb, lines, cnf, _, _ => by rw [normClauses]; simp
  | cl :: cls, nb, lines, cnf, hwf, hext => by
    rw [normClauses] at hext ⊢
    simp only [] at hext ⊢
    have hwf' : (normLits nb false #[] cl).2.2.WF := normLits_wf cl nb false #[] hwf
    by_cases hsat : (normLits nb false #[] cl).1 = true
    · rw [if_pos hsat] at hext ⊢
      have hextL : (normLits nb false #[] cl).2.2.Ext nbF :=
        (normClauses_ext cls _ lines cnf).trans hext
      have hcl : ∃ b ∈ cl, b.denote f = true := by
        have := (normLits_spec hcorr cl nb false #[] hwf hextL).mp (Or.inl hsat)
        rcases this with h | h | h
        · simp at h
        · obtain ⟨p, hp, _⟩ := h; simp at hp
        · exact h
      rw [normClauses_spec hcorr cls _ lines cnf hwf' hext]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact hcl
          · exact h2 c hc'⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun c hc => h2 c (by simp [hc])⟩
    · rw [if_neg hsat] at hext ⊢
      have hextL : (normLits nb false #[] cl).2.2.Ext nbF :=
        (normClauses_ext cls _ _ _).trans hext
      have hcl : (CNF.Clause.eval τ
          ((normLits nb false #[] cl).2.1.toList.map (fun p => (p.1 - 1, p.2))) = true)
          ↔ ∃ b ∈ cl, b.denote f = true := by
        rw [clause_eval_iff]
        have := normLits_spec hcorr cl nb false #[] hwf hextL
        constructor
        · intro h
          rcases this.mp (Or.inr h) with h' | h' | h'
          · simp at h'
          · obtain ⟨p, hp, _⟩ := h'; simp at hp
          · exact h'
        · intro h
          rcases this.mpr (Or.inr (Or.inr h)) with h' | h'
          · exact absurd h' hsat
          · exact h'
      rw [normClauses_spec hcorr cls _ _ _ hwf' hext]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun c hc => h1 c (by simp [hc]), fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact hcl.mp (h1 _ (by simp))
        · exact h2 c hc'
      · rintro ⟨h1, h2⟩
        refine ⟨fun c hc => ?_, fun c hc => h2 c (by simp [hc])⟩
        rcases (by simpa using hc : c ∈ cnf.toList ∨
            c = (normLits nb false #[] cl).2.1.toList.map (fun p => (p.1 - 1, p.2))) with h | rfl
        · exact h1 c h
        · exact hcl.mpr (h2 cl (by simp))

/-- **Normalization and numbering preserve satisfiability**, in both
directions: the CNF handed to cadical has a model exactly when the clause
array the encoder built has one. Dropping tautologies and repeated
literals — `EQCHECK_SPEC.md` §Deviations, forced on us by cadical's parser
— is therefore inside the claim, not beside it. -/
theorem toDimacs_unsat_iff (clauses : Array BClause) :
    CNF.Unsat (toDimacs clauses).cnf ↔
      ∀ f : Var → Bool, ¬ (∀ cl ∈ clauses.toList, ∃ b ∈ cl, b.denote f = true) := by
  have hwf0 : Numbering.WF {} := by
    intro v i h
    simp [Numbering.idx] at h
  set nbF := (normClauses {} #[] #[] clauses.toList).1 with hnbF
  have hcnf : (toDimacs clauses).cnf = (normClauses {} #[] #[] clauses.toList).2.2.toList := rfl
  constructor
  · -- UNSAT ⇒ the two sides agree
    intro hun f hsat
    -- read the model of the clause array off as a DIMACS model
    set τ : Nat → Bool := fun k => f (nbF.vars[k]!) with hτ
    have hcorr : Corr nbF f τ := by
      intro v i hi
      obtain ⟨hlt, hpos, hv⟩ := normClauses_wf clauses.toList {} #[] #[] hwf0 v i hi
      simp only [hτ]
      rw [getElem_bang _ _ hlt, hv]
    have := (normClauses_spec hcorr clauses.toList {} #[] #[] hwf0
      (Numbering.Ext.refl _)).mpr ⟨by simp, fun cl hcl => hsat cl hcl⟩
    have huneval := hun τ
    rw [hcnf] at huneval
    have : CNF.eval τ (normClauses {} #[] #[] clauses.toList).2.2.toList = true := by
      simp only [CNF.eval, List.all_eq_true]
      intro c hc
      exact this c hc
    rw [this] at huneval
    simp at huneval
  · -- a model of the CNF ⇒ a state where they differ
    intro hag τ
    rcases Bool.eq_false_or_eq_true (CNF.eval τ (toDimacs clauses).cnf) with hev | hev
    · exfalso
      set f : Var → Bool := fun v =>
        match nbF.idx[v]? with
        | some i => τ (i - 1)
        | none => false with hf
      have hcorr : Corr nbF f τ := by
        intro v i hi
        simp only [hf, hi]
      refine hag f ?_
      refine ((normClauses_spec hcorr clauses.toList {} #[] #[] hwf0
        (Numbering.Ext.refl _)).mp (fun c hc => ?_)).2
      rw [hcnf] at hev
      simp only [CNF.eval, List.all_eq_true] at hev
      exact hev c hc
    · exact hev

/-! ## The miter: `encode_sound`

Everything above is assembled here. `sigMiter` is what `coneMiter` (and,
bit for bit, `outMiter`) runs: the constant-folding assumptions, side A
blasted from the µVerilog expression, side B from whatever encoder the
caller supplies, and the assertion that the two differ. -/

/-- The per-bit differences, as a value. -/
def diffVal (a b : Array Bit) (f : Var → Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => ((a[k]!).denote f ^^ (b[k]!).denote f) :: diffVal a b f k

theorem Enc_differAcc {n₀ : Nat} (a b : Array Bit)
    (hwa : ∀ i : Nat, BitWF n₀ (a[i]!)) (hwb : ∀ i : Nat, BitWF n₀ (b[i]!)) :
    ∀ k : Nat, Enc n₀ (differAcc a b k) (fun f => diffVal a b f k)
  | 0 => Enc.pure (fun b hb => absurd hb (by simp)) (fun f => by simp [diffVal])
  | k + 1 => by
    rw [differAcc]
    refine Enc.bind (α := List Bit) (α' := List Bit)
      (valA := fun f => diffVal a b f k)
      (valB := fun lv f => ((a[k]!).denote f ^^ (b[k]!).denote f) :: lv) ?_
      (Enc_differAcc a b hwa hwb k) ?_
    · intro f g ha
      induction k with
      | zero => rfl
      | succ m ih =>
        simp only [diffVal, List.cons.injEq]
        exact ⟨by rw [(hwa m).denote_congr ha, (hwb m).denote_congr ha], ih⟩
    · intro l n hn hwl
      refine Enc.bind (α := Bit) (α' := List Bit) (valA := fun f =>
          (a[k]!).denote f ^^ (b[k]!).denote f)
        (valB := fun t f => t :: (l.map (·.denote f)))
        (Stable.bop (n₀ := n₀) hn (fun _ _ => Stable.const _)
          (BitWF.mono hn (hwa k)) (BitWF.mono hn (hwb k)))
        (Enc.mono hn (Enc_mkXor (hwa k) (hwb k))) ?_
      intro t n' hn' hwt
      exact Enc.pure (by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact hwt
        · exact BitWF.mono hn' (hwl c hc')) (fun f => rfl)

theorem diffVal_any (a b : Array Bit) (f : Var → Bool) :
    ∀ k : Nat, ((diffVal a b f k).any id = true ↔
      ∃ i, i < k ∧ (a[i]!).denote f ≠ (b[i]!).denote f)
  | 0 => by simp [diffVal]
  | k + 1 => by
    simp only [diffVal, List.any_cons, id, Bool.or_eq_true, diffVal_any a b f k]
    constructor
    · rintro (h | ⟨i, hi, hne⟩)
      · exact ⟨k, by omega, by
          cases hx : (a[k]!).denote f <;> cases hy : (b[k]!).denote f <;> simp_all⟩
      · exact ⟨i, by omega, hne⟩
    · rintro ⟨i, hi, hne⟩
      rcases Nat.lt_or_ge i k with h | h
      · exact Or.inr ⟨i, h, hne⟩
      · have : i = k := by omega
        subst this
        exact Or.inl (by
          cases hx : (a[i]!).denote f <;> cases hy : (b[i]!).denote f <;> simp_all)

theorem run_assertAll : ∀ (l : List Bit) (s : St),
    M.run (assertAll l) s = (.ok (), { s with clauses := s.clauses ++ (l.map (fun b => [b])).toArray })
  | [], s => by simp [assertAll, run_pure]
  | b :: bs, s => by
    show M.run (assert b >>= fun _ => assertAll bs) s = _
    rw [run_bind]
    show (match M.run (addCl [b]) s with
      | (.ok a, s') => M.run (assertAll bs) s'
      | (.error e, s') => (.error e, s')) = _
    rw [run_addCl]
    simp only []
    rw [run_assertAll bs]
    simp

/-- The miter's output bit: "some bit position differs". -/
def differOr (a b : Array Bit) (k : Nat) : M Bit := do
  let xs ← differAcc a b k
  mkOrList xs

theorem Enc_differOr {n₀ : Nat} (a b : Array Bit)
    (hwa : ∀ i : Nat, BitWF n₀ (a[i]!)) (hwb : ∀ i : Nat, BitWF n₀ (b[i]!)) (k : Nat) :
    Enc n₀ (differOr a b k) (fun f => (diffVal a b f k).any id) := by
  refine Enc.bind (α := List Bit) (α' := Bit) (valA := fun f => diffVal a b f k)
    (valB := fun lv _ => lv.any id) ?_ (Enc_differAcc a b hwa hwb k) ?_
  · intro f g ha
    induction k with
    | zero => rfl
    | succ m ih =>
      simp only [diffVal, List.cons.injEq]
      exact ⟨by rw [(hwa m).denote_congr ha, (hwb m).denote_congr ha], ih⟩
  · intro l n hn hwl
    refine Enc.congr (α := Bit) (β := Bool) (val := fun f => l.any (fun x => x.denote f))
      (fun f => by simp) (Enc_mkOrList l hwl)

theorem run_assert (b : Bit) (s : St) :
    M.run (assert b) s = (.ok (), { s with clauses := s.clauses.push [b] }) := rfl

/-- **`encode_sound`** — the theorem D32 asks for.

For one signal's miter (`sigMiter`, which is exactly what `coneMiter` and
`outMiter` run): the CNF handed to the solver is unsatisfiable **iff** the
µVerilog expression and side B's encoder agree on every valuation that
satisfies the constant-folding assumptions.

* left to right: an UNSAT verdict *means* the two transition functions
  agree — the "if the encoding is faithful" caveat is discharged;
* right to left: a SAT verdict *means* they differ, so the countermodel the
  tool prints is a genuine disagreement.

`toDimacs`' clause normalization (dropping repeated literals and
tautologies, EQCHECK_SPEC.md §Deviations) is inside the statement, not
beside it. Side B enters as a hypothesis `EncA 0 w actB valB`: for the
netlist cone walk (`evalSig`/`evalBits`) that hypothesis is *not* proved —
see the partition recorded in EQCHECK_SPEC.md. -/
theorem encode_sound {w : Nat} (assumps : List Bit) (syms : List (String × Nat))
    (e : Expr w) (hfrag : encVerified e = true)
    (actB : M (Array Bit)) (valB : (Var → Bool) → BitVec w) (hB : EncA 0 w actB valB)
    (hwfA : ∀ b ∈ assumps, BitWF 0 b) {s : St}
    (hrun : M.run (sigMiter assumps syms e actB) {} = (.ok (), s)) :
    CNF.Unsat (toDimacs s.clauses).cnf ↔
      ∀ f : Var → Bool, (∀ b ∈ assumps, b.denote f = true) → e.eval (stOf f) = valB f := by
  obtain ⟨hszA, hstA, hencA⟩ := Enc_blastE syms e hfrag
  obtain ⟨hszB, hstB, hencB⟩ := hB
  -- Step 0: the assumptions.
  set s0 : St := { clauses := (assumps.map (fun b => [b])).toArray : St } with hs0
  have hs0cl : s0.clauses.toList = assumps.map (fun b => [b]) := by simp [hs0]
  have hs0next : s0.next = 0 := rfl
  have hWF0 : StWF s0 := by
    intro cl hcl
    rw [hs0cl] at hcl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hcl
    intro c hc
    rcases List.mem_cons.mp hc with h' | hc'
    · rw [h']; exact hwfA b hb
    · exact absurd hc' (by simp)
  have hsat0 : ∀ f : Var → Bool, SatSt f s0 ↔ ∀ b ∈ assumps, b.denote f = true := by
    intro f
    constructor
    · intro h b hb
      obtain ⟨c, hc, hcv⟩ := h [b] (by rw [hs0cl]; exact List.mem_map_of_mem hb)
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hcv
      · exact absurd hc' (by simp)
    · intro h cl hcl
      rw [hs0cl] at hcl
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hcl
      exact ⟨b, by simp, h b hb⟩
  -- Run the three stages.
  have hrun' : M.run (blastE syms e >>= fun a => actB >>= fun b => assertDiffer a b) s0
      = (.ok (), s) := by
    rw [show sigMiter assumps syms e actB
        = (assertAll assumps >>= fun _ => blastE syms e >>= fun a =>
            actB >>= fun b => assertDiffer a b) from rfl, run_bind, run_assertAll] at hrun
    simp only [] at hrun
    rw [hs0]
    simpa using hrun
  clear hrun
  rw [run_bind] at hrun'
  revert hrun'
  cases hAr : M.run (blastE syms e) s0 with
  | mk rA s1 =>
    cases rA with
    | error e' => intro h; simp at h
    | ok bitsA =>
      simp only []
      rw [run_bind]
      cases hBr : M.run actB s1 with
      | mk rB s2 =>
        cases rB with
        | error e' => intro h; simp at h
        | ok bitsB =>
          simp only []
          intro hrun'
          obtain ⟨hWF1, hn1, hwbitsA, hpre1, hbackA, hfwdA⟩ :=
            hencA s0 bitsA s1 hWF0 (by omega) hAr
          obtain ⟨hWF2, hn2, hwbitsB, hpre2, hbackB, hfwdB⟩ :=
            hencB s1 bitsB s2 hWF1 (by omega) hBr
          have hsA : bitsA.size = w := hszA s0 bitsA s1 hAr
          have hsB : bitsB.size = w := hszB s1 bitsB s2 hBr
          -- assertDiffer: sizes match, so it is `differOr` followed by `assert`.
          rw [show assertDiffer bitsA bitsB
              = (differOr bitsA bitsB bitsA.size >>= fun o => assert o) by
            simp [assertDiffer, differOr, hsA, hsB]] at hrun'
          rw [run_bind] at hrun'
          revert hrun'
          cases hOr : M.run (differOr bitsA bitsB bitsA.size) s2 with
          | mk rO s3 =>
            cases rO with
            | error e' => intro h; simp at h
            | ok o =>
              simp only [run_assert]
              intro hrun'
              have hwa : ∀ i : Nat, BitWF s2.next (bitsA[i]!) := by
                intro i
                rcases Nat.lt_or_ge i bitsA.size with h | h
                · rw [getElem_bang bitsA i h]
                  exact BitWF.mono hn2 (hwbitsA _ (Array.getElem_mem h))
                · rw [getElem!_neg _ _ (by omega)]
                  trivial
              have hwb : ∀ i : Nat, BitWF s2.next (bitsB[i]!) := by
                intro i
                rcases Nat.lt_or_ge i bitsB.size with h | h
                · rw [getElem_bang bitsB i h]
                  exact hwbitsB _ (Array.getElem_mem h)
                · rw [getElem!_neg _ _ (by omega)]
                  trivial
              obtain ⟨hWF3, hn3, hwo, hpre3, hbackO, hfwdO⟩ :=
                Enc_differOr bitsA bitsB hwa hwb bitsA.size s2 o s3 hWF2 (Nat.le_refl _) hOr
              cases hrun'
              -- The final clause set: `s3` plus the unit clause `[o]`.
              set sF : St := { s3 with clauses := s3.clauses.push [o] } with hsF
              have hsFcl : sF.clauses.toList = s3.clauses.toList ++ [[o]] := by simp [hsF]
              have hsatF : ∀ f : Var → Bool,
                  SatSt f sF ↔ (SatSt f s3 ∧ o.denote f = true) := by
                intro f
                constructor
                · intro h
                  refine ⟨fun cl hcl => h cl (by rw [hsFcl]; exact List.mem_append_left _ hcl), ?_⟩
                  obtain ⟨c, hc, hcv⟩ := h [o] (by rw [hsFcl]; simp)
                  rcases List.mem_cons.mp hc with rfl | hc'
                  · exact hcv
                  · exact absurd hc' (by simp)
                · rintro ⟨h1, h2⟩ cl hcl
                  rw [hsFcl] at hcl
                  rcases List.mem_append.mp hcl with h | h
                  · exact h1 cl h
                  · rcases List.mem_singleton.mp h with rfl
                    exact ⟨o, by simp, h2⟩
              rw [toDimacs_unsat_iff]
              constructor
              · -- UNSAT ⇒ they agree
                intro hun f hass
                rcases Classical.em (e.eval (stOf f) = valB f) with h | hne
                · exact h
                exfalso
                -- build a model from `f`
                have hsat0f : SatSt f s0 := (hsat0 f).mpr hass
                obtain ⟨g1, hag1, hsg1, hdg1⟩ := hfwdA f hsat0f
                obtain ⟨g2, hag2, hsg2, hdg2⟩ := hfwdB g1 hsg1
                obtain ⟨g3, hag3, hsg3, hdg3⟩ := hfwdO g2 hsg2
                have hstf1 : stOf f = stOf g1 := stOf_congr (hag1.antitone (Nat.zero_le _))
                have hstf2 : stOf g1 = stOf g2 := stOf_congr (hag2.antitone (Nat.zero_le _))
                have hstf3 : stOf g2 = stOf g3 := stOf_congr (hag3.antitone (Nat.zero_le _))
                have hvB2 : valB g1 = valB g2 := hstB g1 g2 (hag2.antitone (Nat.zero_le _))
                have hvB3 : valB g2 = valB g3 := hstB g2 g3 (hag3.antitone (Nat.zero_le _))
                have hvB1 : valB f = valB g1 := hstB f g1 (hag1.antitone (Nat.zero_le _))
                -- both sides' bits, read under g3
                have hdenA : ∀ i, i < w → (bitsA[i]!).denote g3 = (e.eval (stOf g3)).getLsbD i := by
                  intro i hi
                  have h1 : (bitsA[i]!).denote g1 = (e.eval (stOf g1)).getLsbD i :=
                    den_pointwise hsA hdg1 i hi
                  have h2 : (bitsA[i]!).denote g1 = (bitsA[i]!).denote g3 := by
                    refine BitWF.denote_congr (n := s1.next) ?_ (hag2.trans hag3 hn2)
                    rcases Nat.lt_or_ge i bitsA.size with h | h
                    · rw [getElem_bang bitsA i h]; exact hwbitsA _ (Array.getElem_mem h)
                    · rw [getElem!_neg _ _ (by omega)]; trivial
                  rw [← h2, h1, hstf2, hstf3]
                have hdenB : ∀ i, i < w → (bitsB[i]!).denote g3 = (valB g3).getLsbD i := by
                  intro i hi
                  have h1 : (bitsB[i]!).denote g2 = (valB g2).getLsbD i :=
                    den_pointwise hsB hdg2 i hi
                  have h2 : (bitsB[i]!).denote g2 = (bitsB[i]!).denote g3 := by
                    refine BitWF.denote_congr (n := s2.next) ?_ hag3
                    rcases Nat.lt_or_ge i bitsB.size with h | h
                    · rw [getElem_bang bitsB i h]; exact hwbitsB _ (Array.getElem_mem h)
                    · rw [getElem!_neg _ _ (by omega)]; trivial
                  rw [← h2, h1, hvB3]
                -- they differ somewhere
                have hdiff : ∃ i, i < w ∧
                    (bitsA[i]!).denote g3 ≠ (bitsB[i]!).denote g3 := by
                  rcases Classical.em (∃ i, i < w ∧
                      (e.eval (stOf g3)).getLsbD i ≠ (valB g3).getLsbD i) with ⟨i, hi, hne'⟩ | hall
                  · exact ⟨i, hi, by rw [hdenA i hi, hdenB i hi]; exact hne'⟩
                  · exfalso
                    refine hne ?_
                    rw [hstf1, hstf2, hstf3, hvB1, hvB2, hvB3]
                    refine BitVec.eq_of_getLsbD_eq (fun i hi => ?_)
                    rcases Classical.em ((e.eval (stOf g3)).getLsbD i = (valB g3).getLsbD i) with
                      h | h
                    · exact h
                    · exact absurd ⟨i, hi, h⟩ hall
                have hoTrue : o.denote g3 = true := by
                  rw [show o.denote g3 = (Deno.den g3 o : Bool) from rfl, hdg3]
                  refine (diffVal_any bitsA bitsB g3 bitsA.size).mpr ?_
                  obtain ⟨i, hi, hne'⟩ := hdiff
                  exact ⟨i, by omega, hne'⟩
                exact absurd ((hsatF g3).mpr ⟨hsg3, hoTrue⟩) (hun g3)
              · -- they agree ⇒ UNSAT
                intro hag f hsatf
                have hf3 : SatSt f s3 := ((hsatF f).mp hsatf).1
                have hoT : o.denote f = true := ((hsatF f).mp hsatf).2
                have hf2 : SatSt f s2 := SatSt.of_prefix hpre3 hf3
                have hf1 : SatSt f s1 := SatSt.of_prefix hpre2 hf2
                have hf0 : SatSt f s0 := SatSt.of_prefix hpre1 hf1
                have heq := hag f ((hsat0 f).mp hf0)
                have : (diffVal bitsA bitsB f bitsA.size).any id = true := by
                  have := hbackO f hf3
                  simp only [den_bit] at this
                  rw [← this]; exact hoT
                obtain ⟨i, hi, hne'⟩ := (diffVal_any bitsA bitsB f bitsA.size).mp this
                refine hne' ?_
                rw [den_pointwise hsA (hbackA f hf1) i (by omega),
                  den_pointwise hsB (hbackB f hf2) i (by omega)]
                exact congrArg (fun v => BitVec.getLsbD v i) heq

end Loom.Netlist
