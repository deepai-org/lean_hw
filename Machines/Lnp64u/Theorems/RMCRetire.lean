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


/-! ## Per-op selection inside `retireFor` -/

/-- The op fold picks the first matching mnemonic; conditions are opcode
tests, mutually exclusive by opcode distinctness. -/
private theorem opFold_run_sel (σ acc : Loom.Hw.St) (fb : Act) :
    ∀ (l : List (String × Hw.OpCirc)) (mn : String) (c : Hw.OpCirc),
      (mn, c) ∈ l →
      ((Hw.isMn mn).eval σ = 1#1) →
      (∀ p ∈ l, p.1 ≠ mn → (Hw.isMn p.1).eval σ ≠ 1#1) →
      (∀ p ∈ l, p.1 = mn → p.2 = c) →
      ((l.foldr (fun p acc' => Act.ite (Hw.isMn p.1) p.2.act acc') fb).run σ
        acc) = c.act.run σ acc
  | [], _, _, hmem, _, _, _ => absurd hmem (List.not_mem_nil)
  | (mn', c') :: t, mn, c, hmem, hsel, hexcl, huniq => by
      show (if (Hw.isMn mn').eval σ = 1#1 then _ else _) = _
      by_cases hm : mn' = mn
      · rw [if_pos (hm ▸ hsel)]
        rw [huniq (mn', c') (List.mem_cons_self ..) hm]
      · rw [if_neg (hexcl (mn', c') (List.mem_cons_self ..) hm)]
        have hmem' : (mn, c) ∈ t := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd (congrArg Prod.fst h).symm hm
          · exact h
        exact opFold_run_sel σ acc fb t mn c hmem' hsel
          (fun p hp => hexcl p (List.mem_cons_of_mem _ hp))
          (fun p hp => huniq p (List.mem_cons_of_mem _ hp))

/-- No mnemonic matches: the fold falls through to the fallback. -/
private theorem opFold_run_none (σ acc : Loom.Hw.St) (fb : Act) :
    ∀ (l : List (String × Hw.OpCirc)),
      (∀ p ∈ l, (Hw.isMn p.1).eval σ ≠ 1#1) →
      ((l.foldr (fun p acc' => Act.ite (Hw.isMn p.1) p.2.act acc') fb).run σ
        acc) = fb.run σ acc
  | [], _ => rfl
  | (mn', c') :: t, hnone => by
      show (if (Hw.isMn mn').eval σ = 1#1 then _ else _) = _
      rw [if_neg (hnone (mn', c') (List.mem_cons_self ..))]
      exact opFold_run_none σ acc fb t
        (fun p hp => hnone p (List.mem_cons_of_mem _ hp))

/-- `retireFor` runs exactly the matching op circuit. -/
theorem retireFor_run_sel (σ acc : Loom.Hw.St) (e : DomainId) (mn : String)
    (c : Hw.OpCirc) (hmem : (mn, c) ∈ Hw.opCircs e)
    (hsel : (Hw.isMn mn).eval σ = 1#1)
    (hexcl : ∀ p ∈ Hw.opCircs e, p.1 ≠ mn → (Hw.isMn p.1).eval σ ≠ 1#1)
    (huniq : ∀ p ∈ Hw.opCircs e, p.1 = mn → p.2 = c) :
    (Hw.retireFor e).run σ acc = c.act.run σ acc :=
  opFold_run_sel σ acc _ (Hw.opCircs e) mn c hmem hsel hexcl huniq

/-- No declared opcode matches: `retireFor` falls through to the
illegal-instruction fault. -/
theorem retireFor_run_none (σ acc : Loom.Hw.St) (e : DomainId)
    (hnone : ∀ p ∈ Hw.opCircs e, (Hw.isMn p.1).eval σ ≠ 1#1) :
    (Hw.retireFor e).run σ acc
      = (Hw.haltFault e .illegalInstruction).run σ acc :=
  opFold_run_none σ acc _ (Hw.opCircs e) hnone

/-! ## Spec-side unfolding of the retirement -/

/-- An in-flight instruction on its last cycle retires. -/
theorem corePhase_retire (m : Manifest) (τ : MachineState)
    (fl : InFlight) (hfl : τ.inflight = some fl) (h1 : fl.cyclesLeft ≤ 1) :
    corePhase m τ = retire { τ with inflight := none } fl.dom fl.word := by
  unfold corePhase
  rw [hfl]
  show (if fl.cyclesLeft ≤ 1 then _ else _) = _
  rw [if_pos h1]

/-- Decode failure retires as an illegal-instruction fault (unreachable
for issued words; kept total). -/
theorem retire_of_decode_none (σ : MachineState) (d : DomainId)
    (w : Loom.Word32) (hdec : Loom.Isa.decode isa w = none) :
    retire σ d w = haltWith σ d .illegalInstruction := by
  unfold retire
  rw [hdec]

/-- Retirement of a decoded instruction: `pc` advance, `exec` on the
current state, the T6 outcome triage. -/
theorem retire_of_decode_some (σ : MachineState) (d : DomainId)
    (w : Loom.Word32) (instr : Instr)
    (hdec : Loom.Isa.decode isa w = some instr) :
    retire σ d w =
      (match instr.sem.exec
          { d := d, pc := (σ.doms d).pc, op := operandsOf w }
          (σ.setDom d fun ds => { ds with pc := ds.pc + 1 }) with
      | .ok _ σ' => σ'
      | .err e σ' =>
          σ'.setDom d fun ds => ds.setReg (operandsOf w).rd e.toWord
      | .fault f => haltWith σ d f) := by
  unfold retire
  rw [hdec]
  rfl

/-- The latch decodes to the in-flight record. -/
theorem absInflight_some (σ : Loom.Hw.St) (hifv : σ.regs "if_v" 1 = 1#1) :
    Hw.absInflight σ = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := σ.regs "if_word" 32
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
  rw [Hw.absInflight]
  rw [if_pos (show σ.regs "if_v" 1 = 1 from hifv)]

/-- The dispatch's opcode expression reads the latched word's opcode. -/
theorem opcE_opcodeOf (σ : Loom.Hw.St) :
    Machines.Lnp64u.sig.opcodeOf (σ.regs "if_word" 32)
      = Hw.opcE.eval σ := rfl

end Machines.Lnp64u.Theorems.RMC
