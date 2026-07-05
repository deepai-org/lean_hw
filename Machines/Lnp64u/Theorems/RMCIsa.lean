-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCBridge
import Machines.Lnp64u.Isa

/-!
# R-MC support: the decode/cost bridge

The circuits dispatch on the raw opcode field through `isa`-derived
tables (`knownE`, `costE`, `isMn`); the spec decodes through
`Loom.Isa.decode`. Both are projections of the same 25-entry array, so:

* `decode_eq_find` — `decode` as a first-match scan of `isa.toList`;
* `knownE_eval` — the known-opcode OR-tree is decode success;
* `costE_eval_of_decode` — the cost mux returns the decoded
  instruction's WCET charge;
* `isMn_eval` — mnemonic dispatch tests the opcode field.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

private theorem list_findFinIdx_get {α : Type} (p : α → Bool) :
    ∀ (l : List α), (List.findFinIdx? p l).map (fun i => l[i]) = l.find? p := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      by_cases hx : p x
      · simp [List.findFinIdx?_cons, hx]
      · simp only [List.findFinIdx?_cons, List.find?_cons, hx, if_false,
          Bool.false_eq_true]
        rw [← ih]
        cases h : List.findFinIdx? p t
        · simp
        · simp

private theorem arr_findFinIdx_get {α : Type} (p : α → Bool) (a : Array α) :
    (a.findFinIdx? p).map (fun i => a[i]) = a.find? p := by
  rw [← Array.find?_toList, ← list_findFinIdx_get p a.toList,
    Array.findFinIdx?_toList]
  cases h : a.findFinIdx? p <;> simp

/-- `decode` is the first-match scan of the declaration list. -/
theorem decode_eq_find (w : Loom.Word32) :
    Loom.Isa.decode isa w
      = isa.find? (fun d => d.opcode == Machines.Lnp64u.sig.opcodeOf w) := by
  rw [Loom.Isa.decode, Loom.Isa.decodeIdx, arr_findFinIdx_get]

/-- The cost mux returns the first matching declaration's WCET charge. -/
private theorem costE_fold_eval (σ : Loom.Hw.St) (opcE : Expr 6) :
    ∀ (L : List Machines.Lnp64u.Instr) (d : Machines.Lnp64u.Instr),
      L.find? (fun x => x.opcode == opcE.eval σ) = some d →
      (((L.map (fun i => (i.opcode, i.cost.cost))).foldr
        (fun oc acc => Expr.mux (.eq opcE (.lit oc.1))
          (.lit (BitVec.ofNat 8 oc.2)) acc)
        (.lit 0)).eval σ) = BitVec.ofNat 8 d.cost.cost
  | [], d, h => by simp at h
  | x :: t, d, h => by
      show (if (Expr.eq opcE (.lit x.opcode)).eval σ = 1#1
        then BitVec.ofNat 8 x.cost.cost else _) = _
      by_cases hx : opcE.eval σ = x.opcode
      · rw [if_pos (by rw [eqE_eval]; exact hx)]
        have hd : x = d := by
          rw [List.find?_cons, show (x.opcode == opcE.eval σ) = true
            from by simp [hx.symm]] at h
          exact Option.some.inj h
        rw [hd]
      · rw [if_neg (by rw [eqE_eval]; exact hx)]
        have ht : t.find? (fun y => y.opcode == opcE.eval σ) = some d := by
          rw [List.find?_cons, show (x.opcode == opcE.eval σ) = false
            from by simp; exact fun hc => hx hc.symm] at h
          exact h
        exact costE_fold_eval σ opcE t d ht


/-- The known-opcode OR-tree is decode success. -/
theorem knownE_eval (σ : Loom.Hw.St) (opcE : Expr 6) :
    ((Hw.knownE opcE).eval σ = 1#1) ↔
      (∃ d ∈ isa, d.opcode = opcE.eval σ) := by
  rw [Hw.knownE, orAll_eval]
  constructor
  · rintro ⟨e, hmem, he⟩
    rw [Hw.opCosts, List.mem_map] at hmem
    obtain ⟨oc, hoc, rfl⟩ := hmem
    rw [List.mem_map] at hoc
    obtain ⟨i, hi, rfl⟩ := hoc
    rw [eqE_eval] at he
    exact ⟨i, by rwa [Array.mem_def], he.symm ▸ rfl⟩
  · rintro ⟨d, hd, hop⟩
    refine ⟨Expr.eq opcE (.lit d.opcode), ?_, ?_⟩
    · rw [Hw.opCosts, List.mem_map]
      exact ⟨(d.opcode, d.cost.cost), List.mem_map.mpr
        ⟨d, by rwa [← Array.mem_def], rfl⟩, rfl⟩
    · rw [eqE_eval]
      exact hop.symm ▸ rfl

/-- Decode failure is the known-opcode tree reading `0`. -/
theorem decode_none_iff (σ : Loom.Hw.St) (opcE : Expr 6) (w : Loom.Word32)
    (hopc : Machines.Lnp64u.sig.opcodeOf w = opcE.eval σ) :
    (Loom.Isa.decode isa w = none) ↔ ¬((Hw.knownE opcE).eval σ = 1#1) := by
  rw [knownE_eval]
  constructor
  · intro h hc
    have := (Loom.Isa.isSome_decode_iff isa w).mpr
      (by obtain ⟨d, hd, hop⟩ := hc; exact ⟨d, hd, by rw [hop, hopc]⟩)
    rw [h] at this
    exact absurd this (by simp)
  · intro h
    cases hd : Loom.Isa.decode isa w with
    | none => rfl
    | some d =>
        exfalso
        apply h
        have := (Loom.Isa.isSome_decode_iff isa w).mp (by rw [hd]; rfl)
        obtain ⟨d', hd', hop⟩ := this
        exact ⟨d', hd', by rw [hop, hopc]⟩

/-- The cost mux returns the decoded instruction's WCET charge. -/
theorem costE_eval_of_decode (σ : Loom.Hw.St) (opcE : Expr 6)
    (w : Loom.Word32) (d : Machines.Lnp64u.Instr)
    (hopc : Machines.Lnp64u.sig.opcodeOf w = opcE.eval σ)
    (hdec : Loom.Isa.decode isa w = some d) :
    (Hw.costE opcE).eval σ = BitVec.ofNat 8 d.cost.cost := by
  rw [decode_eq_find, ← Array.find?_toList] at hdec
  rw [hopc] at hdec
  exact costE_fold_eval σ opcE isa.toList d hdec

/-- Mnemonic dispatch tests the opcode field of the in-flight word. -/
theorem isMn_eval (σ : Loom.Hw.St) (mn : String) :
    ((Hw.isMn mn).eval σ = 1#1) ↔
      (σ.regs "if_word" 32).extractLsb' 0 6 = Hw.opcodeOf mn := by
  rw [Hw.isMn, eqE_eval]
  rfl

end Machines.Lnp64u.Theorems.RMC
