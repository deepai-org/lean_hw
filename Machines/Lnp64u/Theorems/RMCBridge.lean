-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCFrames
import Machines.Lnp64u.Theorems.RMCEnc

/-!
# R-MC support: expression-level evaluation bridges

The workhorse evaluation lemmas connecting `Hw/Enc.lean`'s `Expr`
combinators to their spec-side meanings:

* `muxFin_eval` — a `muxFin` selection tree evaluates to the selected
  branch (**the** workhorse: every dynamic register-file/cap-table/gate
  lookup in the design goes through it). Requires the index width to be
  exact (`2 ^ iw = n`), which holds for every `Fin`-indexed family in the
  µ design.
* `orAll_eval` / `andAll_eval` — the OR/AND trees as existential/universal
  quantification over the branch list.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-! ## Boolean-vector helpers -/

private theorem bv1_or_eq_one (a b : BitVec 1) :
    (a ||| b = 1#1) ↔ (a = 1#1 ∨ b = 1#1) := by
  revert a b; decide

private theorem bv1_and_eq_one (a b : BitVec 1) :
    (a &&& b = 1#1) ↔ (a = 1#1 ∧ b = 1#1) := by
  revert a b; decide

/-! ## The `muxFin` selection tree -/

/-- Chain step: walking the mux chain over a list `l`, the result is the
branch of the selected index provided it occurs in `l`. -/
private theorem muxChain_eval {n iw w : Nat} (h : 2 ^ iw = n)
    (f : Fin n → Expr w) (idx : Expr iw) (σ : Loom.Hw.St) :
    ∀ (l : List (Fin n)) (dflt : Expr w),
      finOfBv h (idx.eval σ) ∈ l →
      (l.foldr (fun i acc =>
          Expr.mux (.eq idx (.lit (BitVec.ofNat iw i.val))) (f i) acc)
        dflt).eval σ = (f (finOfBv h (idx.eval σ))).eval σ
  | [], _, hmem => absurd hmem (List.not_mem_nil)
  | i :: t, dflt, hmem => by
      simp only [List.foldr]
      show (if (if idx.eval σ = BitVec.ofNat iw i.val then 1#1 else 0#1) = 1#1
        then (f i).eval σ else _) = _
      by_cases heq : idx.eval σ = BitVec.ofNat iw i.val
      · have : finOfBv h (idx.eval σ) = i := by
          apply Fin.ext
          show (idx.eval σ).toNat = i.val
          rw [heq, BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
        rw [this]
        simp [heq]
      · have hne : finOfBv h (idx.eval σ) ≠ i := by
          intro hcon
          apply heq
          have : (idx.eval σ).toNat = i.val := congrArg Fin.val hcon
          apply BitVec.eq_of_toNat_eq
          rw [this, BitVec.toNat_ofNat]
          exact (Nat.mod_eq_of_lt (by have := i.isLt; omega)).symm
      -- the head test is false; recurse into the tail
        have hmem' : finOfBv h (idx.eval σ) ∈ t := by
          rcases List.mem_cons.mp hmem with hh | ht
          · exact absurd hh hne
          · exact ht
        simp only [heq, if_false]
        exact muxChain_eval h f idx σ t dflt hmem'

/-- **The `muxFin` evaluation workhorse**: with an exact index width, the
selection tree evaluates to the branch at the decoded index. -/
theorem muxFin_eval {n iw w : Nat} (h : 2 ^ iw = n)
    (f : Fin n → Expr w) (idx : Expr iw) (σ : Loom.Hw.St) :
    (Hw.muxFin f idx).eval σ = (f (finOfBv h (idx.eval σ))).eval σ :=
  muxChain_eval h f idx σ (List.finRange n) (.lit 0)
    (List.mem_finRange _)

/-! ## OR / AND trees -/

theorem orAll_eval (σ : Loom.Hw.St) :
    ∀ (l : List (Expr 1)),
      ((Hw.orAll l).eval σ = 1#1) ↔ (∃ e ∈ l, e.eval σ = 1#1)
  | [] => by simp [Hw.orAll, Expr.eval]
  | [e] => by simp [Hw.orAll]
  | e :: e' :: t => by
      show ((e.eval σ ||| (Hw.orAll (e' :: t)).eval σ) = 1#1) ↔ _
      rw [bv1_or_eq_one, orAll_eval σ (e' :: t)]
      simp

theorem andAll_eval (σ : Loom.Hw.St) :
    ∀ (l : List (Expr 1)),
      ((Hw.andAll l).eval σ = 1#1) ↔ (∀ e ∈ l, e.eval σ = 1#1)
  | [] => by simp [Hw.andAll, Expr.eval]
  | [e] => by simp [Hw.andAll]
  | e :: e' :: t => by
      show ((e.eval σ &&& (Hw.andAll (e' :: t)).eval σ) = 1#1) ↔ _
      rw [bv1_and_eq_one, andAll_eval σ (e' :: t)]
      simp

/-- A 1-bit expression evaluates to `0` or `1`; `≠ 1 ↔ = 0`. -/
theorem bv1_ne_one {b : BitVec 1} : b ≠ 1#1 ↔ b = 0#1 := by
  revert b; decide

/-- `neqE` evaluates to disequality. -/
theorem neqE_eval {w : Nat} (a b : Expr w) (σ : Loom.Hw.St) :
    ((Hw.neqE a b).eval σ = 1#1) ↔ a.eval σ ≠ b.eval σ := by
  show ((~~~(if a.eval σ = b.eval σ then 1#1 else 0#1)) = 1#1) ↔ _
  by_cases h : a.eval σ = b.eval σ <;> simp [h]

/-! ## Bit-field helpers -/

private theorem bv1_eq_one_iff_getLsb (b : BitVec 1) :
    (b = 1#1) ↔ b.getLsbD 0 = true := by
  revert b; decide

/-- A 1-bit slice equals `1` iff the source bit is set. -/
theorem extract1_eq_one {n : Nat} (w : BitVec n) (i : Nat) :
    (w.extractLsb' i 1 = 1#1) ↔ w.getLsbD i = true := by
  rw [bv1_eq_one_iff_getLsb]
  simp

/-- A 1-bit slice equals `0` iff the source bit is clear. -/
theorem extract1_eq_zero {n : Nat} (w : BitVec n) (i : Nat) :
    (w.extractLsb' i 1 = 0#1) ↔ w.getLsbD i = false := by
  constructor
  · intro h
    by_contra hb
    have := (extract1_eq_one w i).mpr (by revert hb; cases w.getLsbD i <;> simp)
    rw [h] at this
    exact absurd this (by decide)
  · intro h
    have : ¬(w.extractLsb' i 1 = 1#1) := by
      rw [extract1_eq_one, h]; simp
    exact bv1_ne_one.mp this

/-! ## The machine-wide node index (`idx6` = dom ∥ slot) -/

private theorem idx6_toNat (dv : BitVec 2) (sv : BitVec 4) :
    ((dv.setWidth 6 <<< (4 : Nat)) ||| sv.setWidth 6).toNat
      = dv.toNat * 16 + sv.toNat := by
  revert dv sv; decide

private theorem idx6_eval (domE : Expr 2) (slotE : Expr 4) (σ : Loom.Hw.St) :
    ((Hw.idx6 domE slotE).eval σ).toNat
      = (domE.eval σ).toNat * 16 + (slotE.eval σ).toNat := by
  show (((domE.eval σ).setWidth 6 <<< ((Expr.lit (4:BitVec 6)).eval σ).toNat)
      ||| (slotE.eval σ).setWidth 6).toNat = _
  rw [show ((Expr.lit (4:BitVec 6)).eval σ).toNat = 4 from rfl]
  exact idx6_toNat _ _

/-- Node lookup decomposition: reading a per-node register family at a
packed `idx6` index is reading it at the decoded (domain, slot). -/
theorem nodeAt_eval {w : Nat} (f : Hw.NodeId → Expr w)
    (domE : Expr 2) (slotE : Expr 4) (σ : Loom.Hw.St) :
    ((Hw.muxFin f (Hw.idx6 domE slotE)).eval σ) =
      (f ⟨(domE.eval σ).toNat * 16 + (slotE.eval σ).toNat, by
        have h2 := (domE.eval σ).isLt
        have h4 := (slotE.eval σ).isLt
        show _ < numDomains * numSlots
        simp only [numDomains, numSlots]
        omega⟩).eval σ := by
  rw [muxFin_eval (by decide : 2 ^ 6 = numDomains * numSlots)]
  have heq : (finOfBv (by decide : 2 ^ 6 = numDomains * numSlots)
      ((Hw.idx6 domE slotE).eval σ)) =
      (⟨(domE.eval σ).toNat * 16 + (slotE.eval σ).toNat, by
        have h2 := (domE.eval σ).isLt
        have h4 := (slotE.eval σ).isLt
        show _ < numDomains * numSlots
        simp only [numDomains, numSlots]
        omega⟩ : Hw.NodeId) :=
    Fin.ext (idx6_eval domE slotE σ)
  rw [heq]

/-- `nDom`/`nSlot` of the packed node. -/
theorem nDom_pack (dn sn : Nat) (h2 : dn < 4) (h4 : sn < 16) :
    Hw.nDom ⟨dn * 16 + sn, by show _ < numDomains * numSlots; simp only [numDomains, numSlots]; omega⟩
        = ⟨dn, h2⟩ ∧
    Hw.nSlot ⟨dn * 16 + sn, by show _ < numDomains * numSlots; simp only [numDomains, numSlots]; omega⟩
        = ⟨sn, h4⟩ := by
  constructor
  · apply Fin.ext
    show (dn * 16 + sn) / 16 = dn
    omega
  · apply Fin.ext
    show (dn * 16 + sn) % 16 = sn
    omega

/-! ## Capability liveness (`liveRefE` ↔ `MachineState.liveRef`) -/

/-- Spec-side unfolding of `liveRef` through the abstraction. -/
theorem abs_liveRef (σ : Loom.Hw.St) (c : DomainId) (s : Slot) (g : Gen) :
    ((Hw.abs σ).liveRef ⟨c, s, g⟩ = true) ↔
      (σ.regs (Hw.dcapV c s) 1 = 1#1 ∧ σ.regs (Hw.dgen c s) 8 = g ∧ g ≠ 0) := by
  show ((((Hw.abs σ).doms c).liveCap s g).isSome = true) ↔ _
  rw [DomainState.liveCap]
  show ((match (if σ.regs (Hw.dcapV c s) 1 = 1#1 then _ else none : Option CapEntry) with
    | some e => if σ.regs (Hw.dgen c s) 8 = g && g != 0 then some e else none
    | none => none).isSome = true) ↔ _
  by_cases hv : σ.regs (Hw.dcapV c s) 1 = 1#1
  · rw [if_pos hv]
    by_cases hg : σ.regs (Hw.dgen c s) 8 = g
    · by_cases hz : g = 0
      · simp [hg, hz]
      · simp [hg, hv]
    · simp [hg, hv]
  · rw [if_neg hv]
    simp [hv]

/-- `Expr.eq` evaluates to equality. -/
theorem eqE_eval {w : Nat} (a b : Expr w) (σ : Loom.Hw.St) :
    ((Expr.eq a b).eval σ = 1#1) ↔ a.eval σ = b.eval σ := by
  show ((if a.eval σ = b.eval σ then 1#1 else 0#1) = 1#1) ↔ _
  by_cases h : a.eval σ = b.eval σ <;> simp [h]

/-- The machine-wide liveness circuit decodes to the spec's `liveRef` on
the abstraction. -/
theorem liveRefE_eval (σ : Loom.Hw.St) (domE : Expr 2) (slotE : Expr 4)
    (genE : Expr 8) (c : DomainId) (s : Slot)
    (hc : c.val = (domE.eval σ).toNat) (hs : s.val = (slotE.eval σ).toNat) :
    ((Hw.liveRefE domE slotE genE).eval σ = 1#1) ↔
      (Hw.abs σ).liveRef ⟨c, s, genE.eval σ⟩ = true := by
  have hnode := nDom_pack (domE.eval σ).toNat (slotE.eval σ).toNat
    (domE.eval σ).isLt (slotE.eval σ).isLt
  have hcfin : (⟨(domE.eval σ).toNat, (domE.eval σ).isLt⟩ : DomainId) = c :=
    Fin.ext hc.symm
  have hsfin : (⟨(slotE.eval σ).toNat, (slotE.eval σ).isLt⟩ : Slot) = s :=
    Fin.ext hs.symm
  have hcapV : (Hw.capVAt (Hw.idx6 domE slotE)).eval σ =
      σ.regs (Hw.dcapV c s) 1 := by
    rw [Hw.capVAt, nodeAt_eval]
    show σ.regs (Hw.dcapV (Hw.nDom _) (Hw.nSlot _)) 1 = _
    rw [hnode.1, hnode.2, hcfin, hsfin]
  have hgen : (Hw.genAt (Hw.idx6 domE slotE)).eval σ =
      σ.regs (Hw.dgen c s) 8 := by
    rw [Hw.genAt, nodeAt_eval]
    show σ.regs (Hw.dgen (Hw.nDom _) (Hw.nSlot _)) 8 = _
    rw [hnode.1, hnode.2, hcfin, hsfin]
  rw [show (Hw.liveRefE domE slotE genE).eval σ =
      ((Hw.capVAt (Hw.idx6 domE slotE)).eval σ &&&
       ((Expr.eq (Hw.genAt (Hw.idx6 domE slotE)) genE).eval σ &&&
        (Hw.neqE genE (.lit 0)).eval σ)) from rfl,
    bv1_and_eq_one, bv1_and_eq_one, abs_liveRef, hcapV]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · rw [eqE_eval, hgen]
  · rw [neqE_eval]
    show genE.eval σ ≠ (0 : BitVec 8) ↔ _
    rfl


/-! ## Small evaluators -/

/-- 1-bit `not` flips `= 1` to `= 0`. -/
theorem notE_eval (e : Expr 1) (σ : Loom.Hw.St) :
    ((Expr.not e).eval σ = 1#1) ↔ e.eval σ = 0#1 := by
  show (~~~(e.eval σ) = 1#1) ↔ _
  constructor
  · intro h
    have := e.eval σ
    revert h
    generalize e.eval σ = b
    revert b; decide
  · intro h; rw [h]; decide

/-- `Expr.ult` through `toNat`. -/
theorem ultE_eval {w : Nat} (a b : Expr w) (σ : Loom.Hw.St) :
    ((Expr.ult a b).eval σ = 1#1) ↔ (a.eval σ).toNat < (b.eval σ).toNat := by
  show ((if (a.eval σ).ult (b.eval σ) then 1#1 else 0#1) = 1#1) ↔ _
  rw [BitVec.ult]
  by_cases h : (a.eval σ).toNat < (b.eval σ).toNat <;> simp [h]

/-- Widening preserves `toNat`. -/
theorem toNat_setWidth_le {n m : Nat} (h : n ≤ m) (x : BitVec n) :
    (x.setWidth m).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h))

/-! ## Kind-word coverage (`kCovers` ↔ `CapKind.covers ∘ decKind`) -/

/-- `kIsMem` reads the tag bit. -/
theorem kIsMem_eval (kw : Expr 32) (σ : Loom.Hw.St) :
    ((Hw.kIsMem kw).eval σ = 1#1) ↔ (kw.eval σ).getLsbD 0 = false := by
  rw [Hw.kIsMem, eqE_eval]
  show (kw.eval σ).extractLsb' 0 1 = (Expr.lit 0#1).eval σ ↔ _
  exact extract1_eq_zero (kw.eval σ) 0

/-- The permission bits of the decoded kind word. -/
theorem decPerms_bits (w : BitVec 32) :
    (Hw.decPerms (w.extractLsb' 26 3)).r = w.getLsbD 26 ∧
    (Hw.decPerms (w.extractLsb' 26 3)).w = w.getLsbD 27 ∧
    (Hw.decPerms (w.extractLsb' 26 3)).x = w.getLsbD 28 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Hw.decPerms]

/-- The coverage circuit against a kind word decodes to `CapKind.covers`
of the decoded kind. -/
theorem kCovers_eval (kw : Expr 32) (a : Expr 12) (need : Perms)
    (σ : Loom.Hw.St) :
    ((Hw.kCovers kw a need).eval σ = 1#1) ↔
      (Hw.decKind (kw.eval σ)).covers (a.eval σ) need = true := by
  obtain ⟨hr, hw, hx⟩ := decPerms_bits (kw.eval σ)
  rw [Hw.kCovers, andAll_eval]
  by_cases h0 : (kw.eval σ).getLsbD 0
  · -- gate kind: both sides false
    constructor
    · intro hall
      have h1 : (Hw.kIsMem kw).eval σ = 1#1 := hall _ (by simp)
      rw [kIsMem_eval, h0] at h1
      exact absurd h1 (by simp)
    · intro hcov
      exfalso
      rw [Hw.decKind, if_pos h0] at hcov
      exact absurd hcov (by simp [CapKind.covers])
  · -- memory kind
    rw [Hw.decKind, if_neg h0]
    have hbase : ((Expr.not (.ult a (Hw.kBase kw))).eval σ = 1#1) ↔
        ((kw.eval σ).extractLsb' 1 12).toNat ≤ (a.eval σ).toNat := by
      have hkb : (Hw.kBase kw).eval σ = (kw.eval σ).extractLsb' 1 12 := rfl
      rw [notE_eval]
      constructor
      · intro h
        have hn : ¬((Expr.ult a (Hw.kBase kw)).eval σ = 1#1) := by
          rw [h]; decide
        rw [ultE_eval, hkb] at hn
        omega
      · intro h
        apply bv1_ne_one.mp
        intro hlt
        rw [ultE_eval, hkb] at hlt
        omega
    have hlen : ((Expr.ult (.zext a 14)
        (.add (.zext (Hw.kBase kw) 14) (.zext (Hw.kLen kw) 14))).eval σ = 1#1) ↔
        (a.eval σ).toNat <
          ((kw.eval σ).extractLsb' 1 12).toNat +
          ((kw.eval σ).extractLsb' 13 13).toNat := by
      rw [ultE_eval]
      show ((a.eval σ).setWidth 14).toNat <
          ((((kw.eval σ).extractLsb' 1 12).setWidth 14) +
           (((kw.eval σ).extractLsb' 13 13).setWidth 14)).toNat ↔ _
      rw [toNat_setWidth_le (by omega), BitVec.toNat_add,
        toNat_setWidth_le (by omega), toNat_setWidth_le (by omega)]
      have hb := ((kw.eval σ).extractLsb' 1 12).isLt
      have hl := ((kw.eval σ).extractLsb' 13 13).isLt
      rw [Nat.mod_eq_of_lt (by omega)]
    have hKR : ((Hw.kR kw).eval σ = 1#1) ↔ (kw.eval σ).getLsbD 26 = true :=
      extract1_eq_one (kw.eval σ) 26
    have hKW : ((Hw.kW kw).eval σ = 1#1) ↔ (kw.eval σ).getLsbD 27 = true :=
      extract1_eq_one (kw.eval σ) 27
    have hKX : ((Hw.kX kw).eval σ = 1#1) ↔ (kw.eval σ).getLsbD 28 = true :=
      extract1_eq_one (kw.eval σ) 28
    rcases need with ⟨nr, nw, nx⟩
    cases nr <;> cases nw <;> cases nx <;>
    · simp only [reduceIte, List.cons_append, List.nil_append,
        List.forall_mem_cons]
      rw [kIsMem_eval, hbase, hlen]
      simp only [CapKind.covers, Perms.le, Bool.and_eq_true,
        decide_eq_true_eq, Bool.not_true, Bool.not_false, Bool.false_or,
        Bool.true_or, Bool.true_and, Bool.and_true, hr, hw, hx,
        hKR, hKW, hKX, h0, true_and,
        Bool.false_eq_true, if_false, List.nil_append,
        List.append_nil, List.cons_append,
        List.forall_mem_cons, and_assoc]
      try simp


/-! ## Region coverage (`coversE` ↔ `Region.covers ∘ decRegion`) -/

/-- The permission bits of a decoded region value. -/
theorem decRegion_perm_bits (v : BitVec 42) :
    (Hw.decRegion v).perms.r = v.getLsbD 0 ∧
    (Hw.decRegion v).perms.w = v.getLsbD 1 ∧
    (Hw.decRegion v).perms.x = v.getLsbD 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Hw.decRegion, Hw.decPerms]

/-- The per-region coverage circuit decodes to validity plus
`Region.covers` of the decoded region. -/
theorem coversE_eval (σ : Loom.Hw.St) (d : DomainId) (r : RegionId)
    (a : Expr 12) (need : Perms) :
    ((Hw.coversE d r a need).eval σ = 1#1) ↔
      (σ.regs (Hw.drgnV d r) 1 = 1#1 ∧
       (Hw.decRegion (σ.regs (Hw.drgn d r) 42)).covers (a.eval σ) need
         = true) := by
  obtain ⟨hr, hw, hx⟩ := decRegion_perm_bits (σ.regs (Hw.drgn d r) 42)
  set v := σ.regs (Hw.drgn d r) 42 with hv
  have hfb : (Hw.field (.reg 42 (Hw.drgn d r)) 16 12).eval σ
      = v.extractLsb' 16 12 := rfl
  have hbase : ((Expr.not (.ult a (Hw.field (.reg 42 (Hw.drgn d r)) 16 12))).eval σ
        = 1#1) ↔ (v.extractLsb' 16 12).toNat ≤ (a.eval σ).toNat := by
    rw [notE_eval]
    constructor
    · intro h
      have hn : ¬((Expr.ult a (Hw.field (.reg 42 (Hw.drgn d r)) 16 12)).eval σ
          = 1#1) := by rw [h]; decide
      rw [ultE_eval, hfb] at hn
      omega
    · intro h
      apply bv1_ne_one.mp
      intro hlt
      rw [ultE_eval, hfb] at hlt
      omega
  have hlen : ((Expr.ult (.zext a 14)
      (.add (.zext (Hw.field (.reg 42 (Hw.drgn d r)) 16 12) 14)
            (.zext (Hw.field (.reg 42 (Hw.drgn d r)) 3 13) 14))).eval σ = 1#1) ↔
      (a.eval σ).toNat <
        (v.extractLsb' 16 12).toNat + (v.extractLsb' 3 13).toNat := by
    rw [ultE_eval]
    show ((a.eval σ).setWidth 14).toNat <
        (((v.extractLsb' 16 12).setWidth 14) +
         ((v.extractLsb' 3 13).setWidth 14)).toNat ↔ _
    rw [toNat_setWidth_le (by omega), BitVec.toNat_add,
      toNat_setWidth_le (by omega), toNat_setWidth_le (by omega)]
    have hb := (v.extractLsb' 16 12).isLt
    have hl := (v.extractLsb' 3 13).isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  have hPR : ((Hw.field (.reg 42 (Hw.drgn d r)) 0 1).eval σ = 1#1) ↔
      v.getLsbD 0 = true := extract1_eq_one v 0
  have hPW : ((Hw.field (.reg 42 (Hw.drgn d r)) 1 1).eval σ = 1#1) ↔
      v.getLsbD 1 = true := extract1_eq_one v 1
  have hPX : ((Hw.field (.reg 42 (Hw.drgn d r)) 2 1).eval σ = 1#1) ↔
      v.getLsbD 2 = true := extract1_eq_one v 2
  rw [Hw.coversE, andAll_eval]
  rcases need with ⟨nr, nw, nx⟩
  cases nr <;> cases nw <;> cases nx <;>
  · simp only [reduceIte, List.cons_append, List.nil_append,
      List.forall_mem_cons]
    rw [hbase, hlen]
    simp only [Region.covers, Perms.le, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or,
      Bool.true_and, Bool.and_true, hr, hw, hx, hPR, hPW, hPX,
      Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
      List.cons_append, List.forall_mem_cons, and_assoc]
    try simp
    try (show (_ ∧ _) ↔ _ ; rfl)

/-- Decoded regions of the abstraction. -/
theorem abs_regions (σ : Loom.Hw.St) (d : DomainId) (r : RegionId) :
    ((Hw.abs σ).doms d).regions r =
      (if σ.regs (Hw.drgnV d r) 1 = 1#1
       then some (Hw.decRegion (σ.regs (Hw.drgn d r) 42)) else none) := rfl

/-- The domain-coverage OR-tree decodes to `MachineState.domCovers`. -/
theorem domCoversE_eval (σ : Loom.Hw.St) (d : DomainId) (a : Expr 12)
    (need : Perms) :
    ((Hw.domCoversE d a need).eval σ = 1#1) ↔
      (Hw.abs σ).domCovers d (a.eval σ) need = true := by
  rw [Hw.domCoversE, orAll_eval]
  rw [show ((Hw.abs σ).domCovers d (a.eval σ) need = true) ↔
      (∃ r : RegionId, ∃ rg, ((Hw.abs σ).doms d).regions r = some rg ∧
        rg.covers (a.eval σ) need = true) from by
    rw [MachineState.domCovers]
    simp]
  constructor
  · rintro ⟨e, hmem, heval⟩
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨hval, hcov⟩ := (coversE_eval σ d r a need).mp heval
    refine ⟨r, Hw.decRegion (σ.regs (Hw.drgn d r) 42), ?_, hcov⟩
    rw [abs_regions, if_pos hval]
  · rintro ⟨r, rg, hsome, hcov⟩
    refine ⟨Hw.coversE d r a need, List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩, ?_⟩
    rw [abs_regions] at hsome
    by_cases hval : σ.regs (Hw.drgnV d r) 1 = 1#1
    · rw [if_pos hval] at hsome
      obtain rfl := Option.some.inj hsome
      exact (coversE_eval σ d r a need).mpr ⟨hval, hcov⟩
    · rw [if_neg hval] at hsome
      exact absurd hsome (by simp)

end Machines.Lnp64u.Theorems.RMC
