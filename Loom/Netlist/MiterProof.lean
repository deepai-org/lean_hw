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
  | _, .add _ _ => false
  | _, .sub _ _ => false
  | _, .shl _ _ => false
  | _, .shr _ _ => false
  | _, .eq _ _ => false
  | _, .ult _ _ => false
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

/-! ## The main theorem

`blastE` encodes exactly `Expr.eval`, for every expression in the verified
fragment, in both directions. -/
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
  | _, .memRead _ _ _, h => by simp [encVerified] at h
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
  | _, .add _ _, h => by simp [encVerified] at h
  | _, .sub _ _, h => by simp [encVerified] at h
  | _, .shl _ _, h => by simp [encVerified] at h
  | _, .shr _ _, h => by simp [encVerified] at h
  | _, .eq _ _, h => by simp [encVerified] at h
  | _, .ult _ _, h => by simp [encVerified] at h
  | _, .slt _ _, h => by simp [encVerified] at h
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

end Loom.Netlist
