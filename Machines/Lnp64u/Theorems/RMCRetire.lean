-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCIssue

/-!
# R-MC support: the retirement dispatch skeleton

On a retiring cycle (`if_v = 1`, `if_cl < 2`) the core rule runs
`retireAct`: clear the latch, dispatch on the owning domain, run exactly
one opcode circuit (mnemonic conditions are mutually exclusive — opcodes
are distinct), and commit the ops' single muxed port-0 memory write.
This file reduces that composite to the selected op's act, one arm at a
time, so the per-op proofs see only their own circuit.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## Branch selection into `retireAct` -/

/-- A retiring cycle selects the retirement branch of the core rule. -/
theorem coreAct_run_retire_eq (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2) :
    (Hw.coreAct m).run σ acc = Hw.retireAct.run σ acc := by
  show (if (Expr.reg 1 "if_v").eval σ = 1#1 then _ else _) = _
  rw [if_pos (show (Expr.reg 1 "if_v").eval σ = 1#1 from hifv)]
  show (if (Expr.ult (.reg 8 "if_cl") (.lit 2)).eval σ = 1#1 then _ else _) = _
  rw [if_pos (show (Expr.ult (.reg 8 "if_cl") (.lit 2)).eval σ = 1#1 from by
    rw [ultE_eval]
    have h2 : ((Expr.lit (2 : BitVec 8)).eval σ).toNat = 2 := rfl
    have h3 : (Expr.reg 8 "if_cl").eval σ = σ.regs "if_cl" 8 := rfl
    rw [h3]
    omega)]

/-- The per-domain dispatch condition selects the latch's owner. -/
theorem ifDomIs_sel (σ : Loom.Hw.St) (e : DomainId)
    (he : e.val = (σ.regs "if_dom" 2).toNat) :
    ((Hw.ifDomIs e).eval σ = 1#1) ∧
    (∀ d : DomainId, d ≠ e → (Hw.ifDomIs d).eval σ ≠ 1#1) := by
  constructor
  · rw [Hw.ifDomIs, eqE_eval]
    show σ.regs "if_dom" 2 = BitVec.ofNat 2 e.val
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← he]
    exact (Nat.mod_eq_of_lt (by have := e.isLt; omega)).symm
  · intro d hd hc
    rw [Hw.ifDomIs, eqE_eval] at hc
    apply hd
    apply Fin.ext
    have : σ.regs "if_dom" 2 = BitVec.ofNat 2 d.val := hc
    rw [he, this, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := d.isLt; omega)).symm

private theorem retireAct_shape :
    Hw.retireAct =
      (let (en, ad, da) := (List.finRange numDomains).foldr
        (fun d (acc : Expr 1 × Expr 12 × Expr 32) =>
          let (en_d, ad_d, da_d) := Hw.retireMemFor d
          let g := Expr.and (Hw.ifDomIs d) en_d
          (.or g acc.1, .mux g ad_d acc.2.1, .mux g da_d acc.2.2))
        ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))
      .seq (.write 1 "if_v" (.lit 0)) <|
      .seq (Hw.seqAll <| (List.finRange numDomains).map fun d =>
          .ite (Hw.ifDomIs d) (Hw.retireFor d) .skip)
        (.ite en (.memWrite 12 32 "mem" 0 ad da) .skip)) := rfl

/-- Register reads pass through the committed memory write. -/
private theorem ite_memWrite_regs (σ st : Loom.Hw.St) (c : Expr 1)
    (ad : Expr 12) (da : Expr 32) (rn : String) (w : Nat) :
    ((Act.ite c (.memWrite 12 32 "mem" 0 ad da) .skip).run σ st).regs rn w
      = st.regs rn w := by
  show (if c.eval σ = 1#1 then _ else st).regs rn w = _
  rw [regs_ite]
  show (if c.eval σ = 1#1 then st.regs rn w else st.regs rn w) = _
  rw [ite_self]

/-- **Skeleton, register face**: after a retiring cycle, every register
read is the owner's op dispatch over the cleared latch. -/
theorem retireAct_run_regs (σ acc : Loom.Hw.St) (e : DomainId)
    (he : e.val = (σ.regs "if_dom" 2).toNat) (rn : String) (w : Nat) :
    (Hw.retireAct.run σ acc).regs rn w
      = ((Hw.retireFor e).run σ
          ((Act.write 1 "if_v" (.lit 0)).run σ acc)).regs rn w := by
  obtain ⟨hsel, hexcl⟩ := ifDomIs_sel σ e he
  rw [retireAct_shape]
  show ((Act.ite _ (.memWrite 12 32 "mem" 0 _ _) .skip).run σ
    ((Hw.seqAll ((List.finRange numDomains).map fun d =>
      Act.ite (Hw.ifDomIs d) (Hw.retireFor d) .skip)).run σ
      ((Act.write 1 "if_v" (.lit 0)).run σ acc))).regs rn w = _
  rw [ite_memWrite_regs]
  rw [seqAll_ite_run_unique σ _ _ _ e hsel (fun j hj => hexcl j hj) _
    (List.mem_finRange e) (List.nodup_finRange _)]

/-- **Skeleton, memory face**: the dispatch writes no memory, so the
result memory is the accumulator overlaid with the (possibly disabled)
muxed port-0 commit. -/
theorem retireAct_run_mems (σ acc : Loom.Hw.St) (ad' w' : Nat) :
    (Hw.retireAct.run σ acc).mems "mem" ad' w'
      = ((Act.ite ((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))).1
        (.memWrite 12 32 "mem" 0
          ((List.finRange numDomains).foldr
            (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
              let (en_d, ad_d, da_d) := Hw.retireMemFor d
              let g := Expr.and (Hw.ifDomIs d) en_d
              (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
            ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))).2.1
          ((List.finRange numDomains).foldr
            (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
              let (en_d, ad_d, da_d) := Hw.retireMemFor d
              let g := Expr.and (Hw.ifDomIs d) en_d
              (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
            ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))).2.2)
        .skip).run σ acc).mems "mem" ad' w' := by
  have hdm : ∀ (ad w : Nat),
      ((Hw.seqAll ((List.finRange numDomains).map fun d =>
        Act.ite (Hw.ifDomIs d) (Hw.retireFor d) .skip)).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ acc)).mems "mem" ad w
      = acc.mems "mem" ad w := by
    intro ad w
    rw [Loom.Hw.Compile.run_mems_notin "mem" _ (of_decide_eq_true rfl) σ _
      ad w]
    rfl
  rw [retireAct_shape]
  set T := (List.finRange numDomains).foldr
    (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
      let (en_d, ad_d, da_d) := Hw.retireMemFor d
      let g := Expr.and (Hw.ifDomIs d) en_d
      (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
    ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32)) with hT
  set DST := (Hw.seqAll ((List.finRange numDomains).map fun d =>
    Act.ite (Hw.ifDomIs d) (Hw.retireFor d) .skip)).run σ
    ((Act.write 1 "if_v" (.lit 0)).run σ acc) with hDST
  have hL : ((Act.ite T.1 (.memWrite 12 32 "mem" 0 T.2.1 T.2.2) .skip).run σ
      DST).mems "mem" ad' w'
      = if (T.1).eval σ = 1#1
        then (DST.mems.set "mem" ((T.2.1).eval σ).toNat ((T.2.2).eval σ))
          "mem" ad' w'
        else DST.mems "mem" ad' w' := by
    show (if (T.1).eval σ = 1#1 then _ else DST).mems "mem" ad' w' = _
    rw [mems_ite]
    rfl
  have hR : ((Act.ite T.1 (.memWrite 12 32 "mem" 0 T.2.1 T.2.2) .skip).run σ
      acc).mems "mem" ad' w'
      = if (T.1).eval σ = 1#1
        then (acc.mems.set "mem" ((T.2.1).eval σ).toNat ((T.2.2).eval σ))
          "mem" ad' w'
        else acc.mems "mem" ad' w' := by
    show (if (T.1).eval σ = 1#1 then _ else acc).mems "mem" ad' w' = _
    rw [mems_ite]
    rfl
  show ((Act.ite T.1 (.memWrite 12 32 "mem" 0 T.2.1 T.2.2) .skip).run σ
    DST).mems "mem" ad' w' = _
  rw [hL, hR]
  by_cases hen : (T.1).eval σ = 1#1
  · rw [if_pos hen, if_pos hen]
    show (_root_.Loom.Hw.MemEnv.set DST.mems "mem" ((T.2.1).eval σ).toNat
      ((T.2.2).eval σ)) "mem" ad' w' = _
    simp only [MemEnv.set]
    split
    · by_cases hw32 : (32 : Nat) = w'
      · rw [dif_pos hw32, dif_pos hw32]
      · rw [dif_neg hw32, dif_neg hw32]
        exact hdm ad' w'
    · exact hdm ad' w'
  · rw [if_neg hen, if_neg hen]
    exact hdm ad' w'

end Machines.Lnp64u.Theorems.RMC
