-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCHalt
import Machines.Lnp64u.Theorems.RMCSched
import Machines.Lnp64u.Theorems.RMCIdle
import Machines.Lnp64u.Logic.Authority
import Machines.Lnp64u.Logic.SlotGen
import Machines.Lnp64u.Logic.Inflight

/-!
# R-MC support: the issue arm's condition bridges

The idle-core issue path (`issueFor`): fetch under execute authority,
decode, upfront payer charge (with the serving-chain donation draw), and
the in-flight latch — or one of the fault/burn outcomes. This file
bridges the branch conditions to the spec's issue path on the
post-refill state; the arm assembly sits on top.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## Fetch -/

/-- The fetch-authority test decodes to `Step.fetch` success, and the
fetched word is the memory read at the domain's PC. -/
theorem fetch_bridge (σ : Loom.Hw.St) (e : DomainId)
    (τ : MachineState)
    (hrgn : ∀ x, (τ.doms x).regions = ((Hw.abs σ).doms x).regions)
    (hpc : (τ.doms e).pc = σ.regs (Hw.dpc e) 12)
    (hmem : ∀ b : Addr, τ.mem b = σ.mems "mem" b.toNat 32) :
    ((Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1 →
      Machines.Lnp64u.fetch τ e
        = some (σ.mems "mem" (σ.regs (Hw.dpc e) 12).toNat 32)) ∧
    (¬((Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1) →
      Machines.Lnp64u.fetch τ e = none) := by
  have hdc : τ.domCovers e (τ.doms e).pc ⟨false, false, true⟩
      = (Hw.abs σ).domCovers e (σ.regs (Hw.dpc e) 12) ⟨false, false, true⟩ := by
    rw [MachineState.domCovers, MachineState.domCovers, hrgn, hpc]
  have heval := domCoversE_eval σ e (Hw.rPc e) ⟨false, false, true⟩
  constructor
  · intro h
    rw [Machines.Lnp64u.fetch, if_pos (by
      rw [hdc]
      exact heval.mp h)]
    rw [MachineState.read, hmem, hpc]
  · intro h
    rw [Machines.Lnp64u.fetch, if_neg (by
      rw [hdc]
      intro hc
      exact h (heval.mpr hc))]

/-! ## The effective (post-refill) budget -/

/-- The `effBudgetE` mux at the decoded payer reads the post-refill
budget. Standalone form of the computation inside `eligE_eval`. -/
theorem effBudget_eval (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (p : DomainId) :
    ((Hw.effBudgetE m p).eval σ).toNat
      = ((refillPhase m (Hw.abs σ)).doms p).budget := by
  show (if (Hw.refillCondE p).eval σ = 1#1
    then (BitVec.ofNat 32 (m.doms p).budgetQ)
    else σ.regs (Hw.dbudget p) 32).toNat = _
  rw [refillPhase_dbudget]
  have hQ : (m.doms p).budgetQ < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (hwf.budget_le p) (hfit.period_lt p)
  have hzero : ((Hw.refillCondE p).eval σ = 1#1) ↔
      ((Hw.abs σ).cycle.toNat % (m.doms p).periodP = 0) := by
    show ((if σ.regs (Hw.drctr p) 32 = (Expr.lit (0 : BitVec 32)).eval σ
      then (1 : BitVec 1) else 0) = 1) ↔ _
    rw [bv1_ite_eq_one]
    constructor
    · intro h
      have := hsync p
      rw [show (Expr.lit (0:BitVec 32)).eval σ = 0#32 from rfl] at h
      rw [h] at this
      simpa [Hw.abs] using this.symm
    · intro h
      show σ.regs (Hw.drctr p) 32 = 0#32
      apply BitVec.eq_of_toNat_eq
      rw [hsync p]
      simpa [Hw.abs] using h
  by_cases hb : (Hw.refillCondE p).eval σ = 1#1
  · rw [if_pos hb, if_pos (hzero.mp hb)]
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [if_neg hb, if_neg (fun hc => hb (hzero.mpr hc))]
    rfl


/-! ## The issue circuit's branch skeleton -/

/-- The fetched word (pre-cycle memory at the domain's PC). -/
def wE (e : DomainId) : Expr 32 := .memRead 32 "mem" (Hw.rPc e)

/-- The fetched opcode field. -/
def opcEx (e : DomainId) : Expr 6 := Hw.field (wE e) 0 6

/-- The 32-bit upfront charge. -/
def cost32E (e : DomainId) : Expr 32 := .zext (Hw.costE (opcEx e)) 32

/-- The payer's effective budget. -/
def effBE (m : Manifest) (e : DomainId) : Expr 32 :=
  Hw.muxFin (fun q => Hw.effBudgetE m q) (Hw.payerE e)

/-- The serving gate id / activation-valid / donation reads. -/
def gidE (e : DomainId) : Expr 2 := .reg 2 (Hw.dsrv e)
def actvE (e : DomainId) : Expr 1 :=
  Hw.muxFin (fun g => .reg 1 (Hw.gactV g)) (gidE e)
def donE (e : DomainId) : Expr 32 :=
  Hw.muxFin (fun g => .reg 32 (Hw.gdon g)) (gidE e)

/-- The upfront charge onto the payer. -/
def chargeA (m : Manifest) (e : DomainId) : Act :=
  Hw.seqAll <| (List.finRange numDomains).map fun q =>
    .ite (.eq (Hw.payerE e) (.lit (BitVec.ofNat 2 q.val)))
      (.write 32 (Hw.dbudget q) (.sub (Hw.effBudgetE m q) (cost32E e))) .skip

/-- Residual burn of an underfunded non-serving payer. -/
def burnA (e : DomainId) : Act :=
  Hw.seqAll <| (List.finRange numDomains).map fun q =>
    .ite (.eq (Hw.payerE e) (.lit (BitVec.ofNat 2 q.val)))
      (.write 32 (Hw.dbudget q) (.lit 0)) .skip

/-- The in-flight latch. -/
def latchA (e : DomainId) : Act :=
  .seq (.write 1 "if_v" (.lit 1)) <|
  .seq (.write 2 "if_dom" (.lit (BitVec.ofNat 2 e.val))) <|
  .seq (.write 32 "if_word" (wE e)) (.write 8 "if_cl" (Hw.costE (opcEx e)))

/-- The donation draw-down. -/
def drawDonA (e : DomainId) : Act :=
  Hw.seqAll <| (List.finRange numGates).map fun g =>
    .ite (.eq (gidE e) (.lit (BitVec.ofNat 2 g.val)))
      (.write 32 (Hw.gdon g) (.sub (donE e) (cost32E e))) .skip

private theorem issueFor_shape (m : Manifest) (e : DomainId) :
    Hw.issueFor m e =
      .ite (.not (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩))
        (Hw.haltFault e .memoryAuthority)
      (.ite (.not (Hw.knownE (opcEx e)))
        (Hw.haltFault e .illegalInstruction)
      (.ite (.ult (effBE m e) (cost32E e))
        (.ite (.reg 1 (Hw.dsrvV e)) (Hw.haltFault e .budget) (burnA e))
      (.ite (.reg 1 (Hw.dsrvV e))
        (.ite (.not (actvE e)) (Hw.haltFault e .protocol)
          (.ite (.ult (donE e) (cost32E e)) (Hw.haltFault e .budget)
            (.seq (chargeA m e) (.seq (drawDonA e) (latchA e)))))
        (.seq (chargeA m e) (latchA e))))) := rfl

/-! ## Branch selections -/

theorem issueFor_run_fetchFault (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (h : ¬((Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)) :
    (Hw.issueFor m e).run σ acc
      = (Hw.haltFault e .memoryAuthority).run σ acc := by
  rw [issueFor_shape]
  show (if (Expr.not (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩)).eval σ
    = 1#1 then _ else _) = _
  rw [if_pos (notE_eval _ σ |>.mpr (bv1_ne_one.mp h))]

theorem issueFor_run_decodeFault (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (h : ¬((Hw.knownE (opcEx e)).eval σ = 1#1)) :
    (Hw.issueFor m e).run σ acc
      = (Hw.haltFault e .illegalInstruction).run σ acc := by
  rw [issueFor_shape]
  show (if (Expr.not (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩)).eval σ
    = 1#1 then _ else _) = _
  rw [if_neg (show ¬_ from fun hc => by
    rw [notE_eval] at hc
    rw [hcov] at hc
    exact absurd hc (by decide))]
  show (if (Expr.not (Hw.knownE (opcEx e))).eval σ = 1#1 then _ else _) = _
  rw [if_pos (notE_eval _ σ |>.mpr (bv1_ne_one.mp h))]

private theorem issueFor_past_decode (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (hkn : (Hw.knownE (opcEx e)).eval σ = 1#1) :
    (Hw.issueFor m e).run σ acc =
      (Act.ite (.ult (effBE m e) (cost32E e))
        (.ite (.reg 1 (Hw.dsrvV e)) (Hw.haltFault e .budget) (burnA e))
      (.ite (.reg 1 (Hw.dsrvV e))
        (.ite (.not (actvE e)) (Hw.haltFault e .protocol)
          (.ite (.ult (donE e) (cost32E e)) (Hw.haltFault e .budget)
            (.seq (chargeA m e) (.seq (drawDonA e) (latchA e)))))
        (.seq (chargeA m e) (latchA e)))).run σ acc := by
  rw [issueFor_shape]
  show (if (Expr.not (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩)).eval σ
    = 1#1 then _ else _) = _
  rw [if_neg (show ¬_ from fun hc => by
    rw [notE_eval] at hc
    rw [hcov] at hc
    exact absurd hc (by decide))]
  show (if (Expr.not (Hw.knownE (opcEx e))).eval σ = 1#1 then _ else _) = _
  rw [if_neg (show ¬_ from fun hc => by
    rw [notE_eval] at hc
    rw [hkn] at hc
    exact absurd hc (by decide))]


theorem issueFor_run_budgetFault (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (hkn : (Hw.knownE (opcEx e)).eval σ = 1#1)
    (hshort : (Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1)
    (hsrv : σ.regs (Hw.dsrvV e) 1 = 1#1) :
    (Hw.issueFor m e).run σ acc = (Hw.haltFault e .budget).run σ acc := by
  rw [issueFor_past_decode m σ acc e hcov hkn]
  show (if (Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1 then _ else _) = _
  rw [if_pos hshort]
  show (if (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 then _ else _) = _
  rw [if_pos (show (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 from hsrv)]

theorem issueFor_run_burn (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (hkn : (Hw.knownE (opcEx e)).eval σ = 1#1)
    (hshort : (Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1)
    (hsrv : ¬(σ.regs (Hw.dsrvV e) 1 = 1#1)) :
    (Hw.issueFor m e).run σ acc = (burnA e).run σ acc := by
  rw [issueFor_past_decode m σ acc e hcov hkn]
  show (if (Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1 then _ else _) = _
  rw [if_pos hshort]
  show (if (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 then _ else _) = _
  rw [if_neg (show ¬((Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1) from hsrv)]

private theorem issueFor_past_budget (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (hkn : (Hw.knownE (opcEx e)).eval σ = 1#1)
    (hfund : ¬((Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1)) :
    (Hw.issueFor m e).run σ acc =
      (Act.ite (.reg 1 (Hw.dsrvV e))
        (.ite (.not (actvE e)) (Hw.haltFault e .protocol)
          (.ite (.ult (donE e) (cost32E e)) (Hw.haltFault e .budget)
            (.seq (chargeA m e) (.seq (drawDonA e) (latchA e)))))
        (.seq (chargeA m e) (latchA e))).run σ acc := by
  rw [issueFor_past_decode m σ acc e hcov hkn]
  show (if (Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1 then _ else _) = _
  rw [if_neg hfund]

theorem issueFor_run_plain (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (hkn : (Hw.knownE (opcEx e)).eval σ = 1#1)
    (hfund : ¬((Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1))
    (hsrv : ¬(σ.regs (Hw.dsrvV e) 1 = 1#1)) :
    (Hw.issueFor m e).run σ acc
      = ((chargeA m e).seq (latchA e)).run σ acc := by
  rw [issueFor_past_budget m σ acc e hcov hkn hfund]
  show (if (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 then _ else _) = _
  rw [if_neg (show ¬((Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1) from hsrv)]

theorem issueFor_run_protoFault (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (hkn : (Hw.knownE (opcEx e)).eval σ = 1#1)
    (hfund : ¬((Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1))
    (hsrv : σ.regs (Hw.dsrvV e) 1 = 1#1)
    (hact : ¬((actvE e).eval σ = 1#1)) :
    (Hw.issueFor m e).run σ acc
      = (Hw.haltFault e .protocol).run σ acc := by
  rw [issueFor_past_budget m σ acc e hcov hkn hfund]
  show (if (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 then _ else _) = _
  rw [if_pos (show (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 from hsrv)]
  show (if (Expr.not (actvE e)).eval σ = 1#1 then _ else _) = _
  rw [if_pos (notE_eval _ σ |>.mpr (bv1_ne_one.mp hact))]

theorem issueFor_run_donFault (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (hkn : (Hw.knownE (opcEx e)).eval σ = 1#1)
    (hfund : ¬((Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1))
    (hsrv : σ.regs (Hw.dsrvV e) 1 = 1#1)
    (hact : (actvE e).eval σ = 1#1)
    (hdshort : (Expr.ult (donE e) (cost32E e)).eval σ = 1#1) :
    (Hw.issueFor m e).run σ acc = (Hw.haltFault e .budget).run σ acc := by
  rw [issueFor_past_budget m σ acc e hcov hkn hfund]
  show (if (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 then _ else _) = _
  rw [if_pos (show (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 from hsrv)]
  show (if (Expr.not (actvE e)).eval σ = 1#1 then _ else _) = _
  rw [if_neg (show ¬_ from fun hc => by
    rw [notE_eval] at hc
    rw [hact] at hc
    exact absurd hc (by decide))]
  show (if (Expr.ult (donE e) (cost32E e)).eval σ = 1#1 then _ else _) = _
  rw [if_pos hdshort]

theorem issueFor_run_serve (m : Manifest) (σ acc : Loom.Hw.St)
    (e : DomainId)
    (hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1)
    (hkn : (Hw.knownE (opcEx e)).eval σ = 1#1)
    (hfund : ¬((Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1))
    (hsrv : σ.regs (Hw.dsrvV e) 1 = 1#1)
    (hact : (actvE e).eval σ = 1#1)
    (hdon : ¬((Expr.ult (donE e) (cost32E e)).eval σ = 1#1)) :
    (Hw.issueFor m e).run σ acc
      = ((chargeA m e).seq ((drawDonA e).seq (latchA e))).run σ acc := by
  rw [issueFor_past_budget m σ acc e hcov hkn hfund]
  show (if (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 then _ else _) = _
  rw [if_pos (show (Expr.reg 1 (Hw.dsrvV e)).eval σ = 1#1 from hsrv)]
  show (if (Expr.not (actvE e)).eval σ = 1#1 then _ else _) = _
  rw [if_neg (show ¬_ from fun hc => by
    rw [notE_eval] at hc
    rw [hact] at hc
    exact absurd hc (by decide))]
  show (if (Expr.ult (donE e) (cost32E e)).eval σ = 1#1 then _ else _) = _
  rw [if_neg hdon]


/-! ## Sub-circuit run characterizations -/

private theorem payer_cond_iff (σ : Loom.Hw.St) (e q : DomainId) :
    ((Expr.eq (Hw.payerE e) (.lit (BitVec.ofNat 2 q.val))).eval σ = 1#1)
      ↔ (Hw.abs σ).payer e = q := by
  rw [eqE_eval, ← payerE_eval σ e]
  show ((Hw.payerE e).eval σ = BitVec.ofNat 2 q.val) ↔ _
  exact bv2_lit_iff _ q

/-- Generic payer-indexed fold selection (the payer expression stays
opaque, so nothing forces the huge unrolled walk to reduce). -/
private theorem payerFold_run (σ acc : Loom.Hw.St) (pe : Expr 2)
    (body : DomainId → Act) (p : DomainId)
    (hp : (pe.eval σ).toNat = p.val) :
    (Hw.seqAll ((List.finRange numDomains).map fun q =>
      Act.ite (.eq pe (.lit (BitVec.ofNat 2 q.val))) (body q) .skip)).run σ acc
    = (body p).run σ acc := by
  refine seqAll_ite_run_unique σ acc _ body p ?_ ?_ _
    (List.mem_finRange p) (List.nodup_finRange _)
  · rw [eqE_eval]
    show pe.eval σ = BitVec.ofNat 2 p.val
    apply BitVec.eq_of_toNat_eq
    rw [hp, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := p.isLt; omega)).symm
  · intro j hj hc
    rw [eqE_eval] at hc
    apply hj
    apply Fin.ext
    have hce : pe.eval σ = BitVec.ofNat 2 j.val := hc
    rw [← hp, hce, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := j.isLt; omega)).symm

private theorem finOfBv_val {w n : Nat} (h : 2 ^ w = n) (x : BitVec w) :
    (finOfBv h x).val = x.toNat := rfl

/-- The payer's decoded index (kept `toNat`-level to stay opaque). -/
theorem payer_toNat (σ : Loom.Hw.St) (e : DomainId) (p : DomainId)
    (hp : (Hw.abs σ).payer e = p) :
    ((Hw.payerE e).eval σ).toNat = p.val := by
  rw [← hp, ← payerE_eval σ e, finOfBv_val]

/-- The charge fold writes exactly the payer's budget register. -/
theorem chargeA_run (m : Manifest) (σ acc : Loom.Hw.St) (e : DomainId)
    (p : DomainId) (hp : (Hw.abs σ).payer e = p) :
    (chargeA m e).run σ acc
      = (Act.write 32 (Hw.dbudget p)
          (.sub (Hw.effBudgetE m p) (cost32E e))).run σ acc :=
  payerFold_run σ acc (Hw.payerE e)
    (fun q => Act.write 32 (Hw.dbudget q)
      (.sub (Hw.effBudgetE m q) (cost32E e)))
    p (payer_toNat σ e p hp)

/-- The burn fold writes exactly the payer's budget register. -/
theorem burnA_run (σ acc : Loom.Hw.St) (e : DomainId)
    (p : DomainId) (hp : (Hw.abs σ).payer e = p) :
    (burnA e).run σ acc
      = (Act.write 32 (Hw.dbudget p) (.lit 0)).run σ acc :=
  payerFold_run σ acc (Hw.payerE e)
    (fun q => Act.write 32 (Hw.dbudget q) (.lit 0))
    p (payer_toNat σ e p hp)

/-- The donation fold writes exactly the served gate's donation. -/
theorem drawDonA_run (σ acc : Loom.Hw.St) (e : DomainId) (g : GateId)
    (hg : g.val = (σ.regs (Hw.dsrv e) 2).toNat) :
    (drawDonA e).run σ acc
      = (Act.write 32 (Hw.gdon g) (.sub (donE e) (cost32E e))).run σ acc := by
  show (Hw.seqAll ((List.finRange numGates).map fun g' =>
    Act.ite (.eq (gidE e) (.lit (BitVec.ofNat 2 g'.val)))
      (.write 32 (Hw.gdon g') (.sub (donE e) (cost32E e))) .skip)).run σ acc = _
  rw [seqAll_ite_run_unique σ acc _ _ g ?_ ?_ _ (List.mem_finRange g)
    (List.nodup_finRange _)]
  · rw [eqE_eval]
    show σ.regs (Hw.dsrv e) 2 = BitVec.ofNat 2 g.val
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← hg]
    exact (Nat.mod_eq_of_lt (by have := g.isLt; omega)).symm
  · intro j hj hc
    rw [eqE_eval] at hc
    apply hj
    apply Fin.ext
    have : σ.regs (Hw.dsrv e) 2 = BitVec.ofNat 2 j.val := hc
    rw [hg, this, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := j.isLt; omega)).symm


/-! ## Spec-side issue-path selections -/

section SpecSel

variable (m : Manifest) (τ : MachineState) (e : DomainId)

private theorem corePhase_idle_shape (hif : τ.inflight = none)
    (hs : schedule m τ = some e) :
    corePhase m τ =
      (match Machines.Lnp64u.fetch τ e with
        | none => haltWith τ e .memoryAuthority
        | some w =>
          match Loom.Isa.decode isa w with
          | none => haltWith τ e .illegalInstruction
          | some instr =>
            let cost := instr.cost.cost
            let p := τ.payer e
            if cost ≤ (τ.doms p).budget then
              match (τ.doms e).serving with
              | some g =>
                  match (τ.gates g).act with
                  | some a =>
                      if cost ≤ a.donated then
                        let σ' := τ.setDom p fun ds =>
                          { ds with budget := ds.budget - cost }
                        let gs' : GateState :=
                          { (σ'.gates g) with
                            act := some { a with donated := a.donated - cost } }
                        let σ'' := { σ' with
                          gates := Loom.Fun.update σ'.gates g gs' }
                        { σ'' with inflight := some ⟨e, w, cost⟩ }
                      else haltWith τ e .budget
                  | none => haltWith τ e .protocol
              | none =>
                  let σ' := τ.setDom p fun ds =>
                    { ds with budget := ds.budget - cost }
                  { σ' with inflight := some ⟨e, w, cost⟩ }
            else
              match (τ.doms e).serving with
              | some _ => haltWith τ e .budget
              | none => τ.setDom p fun ds => { ds with budget := 0 }) := by
  unfold corePhase
  rw [hif]
  show (match schedule m τ with
    | none => τ
    | some d => _) = _
  rw [hs]
  rfl

theorem corePhase_fetchFault (hif : τ.inflight = none)
    (hs : schedule m τ = some e)
    (hf : Machines.Lnp64u.fetch τ e = none) :
    corePhase m τ = haltWith τ e .memoryAuthority := by
  rw [corePhase_idle_shape m τ e hif hs, hf]

theorem corePhase_decodeFault (hif : τ.inflight = none)
    (hs : schedule m τ = some e) (w : Loom.Word32)
    (hf : Machines.Lnp64u.fetch τ e = some w)
    (hdec : Loom.Isa.decode isa w = none) :
    corePhase m τ = haltWith τ e .illegalInstruction := by
  rw [corePhase_idle_shape m τ e hif hs, hf]
  show (match Loom.Isa.decode isa w with
    | none => haltWith τ e .illegalInstruction
    | some instr => _) = _
  rw [hdec]

theorem corePhase_budgetFault (hif : τ.inflight = none)
    (hs : schedule m τ = some e) (w : Loom.Word32)
    (instr : Machines.Lnp64u.Instr)
    (hf : Machines.Lnp64u.fetch τ e = some w)
    (hdec : Loom.Isa.decode isa w = some instr)
    (hb : ¬(instr.cost.cost ≤ (τ.doms (τ.payer e)).budget))
    (g : GateId) (hsg : (τ.doms e).serving = some g) :
    corePhase m τ = haltWith τ e .budget := by
  rw [corePhase_idle_shape m τ e hif hs, hf]
  show (match Loom.Isa.decode isa w with
    | none => haltWith τ e .illegalInstruction
    | some instr => _) = _
  rw [hdec]
  show (if instr.cost.cost ≤ (τ.doms (τ.payer e)).budget then _ else _) = _
  rw [if_neg hb]
  show (match (τ.doms e).serving with
    | some _ => haltWith τ e .budget
    | none => _) = _
  rw [hsg]

theorem corePhase_burn (hif : τ.inflight = none)
    (hs : schedule m τ = some e) (w : Loom.Word32)
    (instr : Machines.Lnp64u.Instr)
    (hf : Machines.Lnp64u.fetch τ e = some w)
    (hdec : Loom.Isa.decode isa w = some instr)
    (hb : ¬(instr.cost.cost ≤ (τ.doms (τ.payer e)).budget))
    (hsg : (τ.doms e).serving = none) :
    corePhase m τ = τ.setDom (τ.payer e) (fun ds => { ds with budget := 0 }) := by
  rw [corePhase_idle_shape m τ e hif hs, hf]
  show (match Loom.Isa.decode isa w with
    | none => haltWith τ e .illegalInstruction
    | some instr => _) = _
  rw [hdec]
  show (if instr.cost.cost ≤ (τ.doms (τ.payer e)).budget then _ else _) = _
  rw [if_neg hb]
  show (match (τ.doms e).serving with
    | some _ => haltWith τ e .budget
    | none => τ.setDom (τ.payer e) (fun ds => { ds with budget := 0 })) = _
  rw [hsg]

theorem corePhase_protoFault (hif : τ.inflight = none)
    (hs : schedule m τ = some e) (w : Loom.Word32)
    (instr : Machines.Lnp64u.Instr)
    (hf : Machines.Lnp64u.fetch τ e = some w)
    (hdec : Loom.Isa.decode isa w = some instr)
    (hb : instr.cost.cost ≤ (τ.doms (τ.payer e)).budget)
    (g : GateId) (hsg : (τ.doms e).serving = some g)
    (ha : (τ.gates g).act = none) :
    corePhase m τ = haltWith τ e .protocol := by
  rw [corePhase_idle_shape m τ e hif hs, hf]
  show (match Loom.Isa.decode isa w with
    | none => haltWith τ e .illegalInstruction
    | some instr => _) = _
  rw [hdec]
  show (if instr.cost.cost ≤ (τ.doms (τ.payer e)).budget then _ else _) = _
  rw [if_pos hb]
  show (match (τ.doms e).serving with
    | some g => _
    | none => _) = _
  rw [hsg]
  show (match (τ.gates g).act with
    | some a => _
    | none => haltWith τ e .protocol) = _
  rw [ha]

theorem corePhase_donFault (hif : τ.inflight = none)
    (hs : schedule m τ = some e) (w : Loom.Word32)
    (instr : Machines.Lnp64u.Instr)
    (hf : Machines.Lnp64u.fetch τ e = some w)
    (hdec : Loom.Isa.decode isa w = some instr)
    (hb : instr.cost.cost ≤ (τ.doms (τ.payer e)).budget)
    (g : GateId) (hsg : (τ.doms e).serving = some g)
    (a : Activation) (ha : (τ.gates g).act = some a)
    (hd : ¬(instr.cost.cost ≤ a.donated)) :
    corePhase m τ = haltWith τ e .budget := by
  rw [corePhase_idle_shape m τ e hif hs, hf]
  show (match Loom.Isa.decode isa w with
    | none => haltWith τ e .illegalInstruction
    | some instr => _) = _
  rw [hdec]
  show (if instr.cost.cost ≤ (τ.doms (τ.payer e)).budget then _ else _) = _
  rw [if_pos hb]
  show (match (τ.doms e).serving with
    | some g => _
    | none => _) = _
  rw [hsg]
  show (match (τ.gates g).act with
    | some a => _
    | none => haltWith τ e .protocol) = _
  rw [ha]
  show (if instr.cost.cost ≤ a.donated then _ else _) = _
  rw [if_neg hd]

theorem corePhase_serveIssue (hif : τ.inflight = none)
    (hs : schedule m τ = some e) (w : Loom.Word32)
    (instr : Machines.Lnp64u.Instr)
    (hf : Machines.Lnp64u.fetch τ e = some w)
    (hdec : Loom.Isa.decode isa w = some instr)
    (hb : instr.cost.cost ≤ (τ.doms (τ.payer e)).budget)
    (g : GateId) (hsg : (τ.doms e).serving = some g)
    (a : Activation) (ha : (τ.gates g).act = some a)
    (hd : instr.cost.cost ≤ a.donated) :
    corePhase m τ =
      (let σ' := τ.setDom (τ.payer e) fun ds =>
        { ds with budget := ds.budget - instr.cost.cost }
      let gs' : GateState := { (σ'.gates g) with
        act := some { a with donated := a.donated - instr.cost.cost } }
      let σ'' := { σ' with gates := Loom.Fun.update σ'.gates g gs' }
      { σ'' with inflight := some ⟨e, w, instr.cost.cost⟩ }) := by
  rw [corePhase_idle_shape m τ e hif hs, hf]
  show (match Loom.Isa.decode isa w with
    | none => haltWith τ e .illegalInstruction
    | some instr => _) = _
  rw [hdec]
  show (if instr.cost.cost ≤ (τ.doms (τ.payer e)).budget then _ else _) = _
  rw [if_pos hb]
  show (match (τ.doms e).serving with
    | some g => _
    | none => _) = _
  rw [hsg]
  show (match (τ.gates g).act with
    | some a => _
    | none => haltWith τ e .protocol) = _
  rw [ha]
  show (if instr.cost.cost ≤ a.donated then _ else _) = _
  rw [if_pos hd]

theorem corePhase_plainIssue (hif : τ.inflight = none)
    (hs : schedule m τ = some e) (w : Loom.Word32)
    (instr : Machines.Lnp64u.Instr)
    (hf : Machines.Lnp64u.fetch τ e = some w)
    (hdec : Loom.Isa.decode isa w = some instr)
    (hb : instr.cost.cost ≤ (τ.doms (τ.payer e)).budget)
    (hsg : (τ.doms e).serving = none) :
    corePhase m τ =
      (let σ' := τ.setDom (τ.payer e) fun ds =>
        { ds with budget := ds.budget - instr.cost.cost }
      { σ' with inflight := some ⟨e, w, instr.cost.cost⟩ }) := by
  rw [corePhase_idle_shape m τ e hif hs, hf]
  show (match Loom.Isa.decode isa w with
    | none => haltWith τ e .illegalInstruction
    | some instr => _) = _
  rw [hdec]
  show (if instr.cost.cost ≤ (τ.doms (τ.payer e)).budget then _ else _) = _
  rw [if_pos hb]
  show (match (τ.doms e).serving with
    | some g => _
    | none => _) = _
  rw [hsg]

end SpecSel


/-! ## Spec-side halt preservation (missing field forms) -/

private theorem haltDom_regions' (τ : MachineState) (d : DomainId)
    (c : Loom.Word32) (x : DomainId) :
    ((τ.haltDom d c).doms x).regions = (τ.doms x).regions := by
  unfold MachineState.haltDom
  split
  · exact haltBase_regions τ d c x
  · split
    · exact haltBase_regions τ d c x
    · rw [unwindGate_regions, haltBase_regions]

private theorem haltDom_caps' (τ : MachineState) (d : DomainId)
    (c : Loom.Word32) (x : DomainId) :
    ((τ.haltDom d c).doms x).caps = (τ.doms x).caps := by
  funext s
  exact haltDom_caps τ d c x s

private theorem haltDom_slotGen' (τ : MachineState) (d : DomainId)
    (c : Loom.Word32) (x : DomainId) :
    ((τ.haltDom d c).doms x).slotGen = (τ.doms x).slotGen := by
  funext s
  exact haltDom_slotGen τ d c x s

private theorem haltDom_mover' (τ : MachineState) (d : DomainId)
    (c : Loom.Word32) : (τ.haltDom d c).mover = τ.mover := by
  unfold MachineState.haltDom
  split
  · rfl
  · split
    · rfl
    · rw [unwindGate_mover, haltBase_mover]

private theorem haltDom_mem' (τ : MachineState) (d : DomainId)
    (c : Loom.Word32) : (τ.haltDom d c).mem = τ.mem := by
  unfold MachineState.haltDom
  split
  · rfl
  · split
    · rfl
    · rfl

/-! ## The shared fault-arm assembly -/

/-- **Any idle-cycle fault outcome squares**: when the core rule reduces
to `haltFault e f` and the spec's core phase to `haltWith τ1 e f`, the
whole cycle squares — the halt bridge carries domains and gates, and
everything else is the quiescent refill/Mover/tick composition. -/
theorem square_issue_fault (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1)
    (e : DomainId) (f : Fault)
    (hcore : (Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)
      = (Hw.haltFault e f).run σ ((Hw.refillAct m).run σ σ))
    (hspec : corePhase m (refillPhase m (Hw.abs σ))
      = haltWith (refillPhase m (Hw.abs σ)) e f) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hnr := retiringE_eval_idle σ hifv0
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  -- the halt bridge, against the post-refill pair
  have hdoms1 : ∀ x, Hw.absDom σ1 x = τ1.doms x := fun x => by
    rw [← habs1]; rfl
  have hgates1 : ∀ g, Hw.absGate σ1 g = τ1.gates g := fun g => by
    rw [← habs1]; rfl
  obtain ⟨hHD, hHG⟩ := abs_haltAct σ σ1 τ1 e (BitVec.ofNat 32 f.code)
    hdoms1 hgates1
    (by rw [hσ1, refill_pres m σ (by fin_cases e <;> decide)])
    (by rw [hσ1, refill_pres m σ (by fin_cases e <;> decide)])
    (fun g => by rw [hσ1, refill_pres m σ (by fin_cases g <;> decide)])
    (fun g => by rw [hσ1, refill_pres m σ (by fin_cases g <;> decide)])
    (fun g => by rw [hσ1, refill_pres m σ (by fin_cases g <;> decide)])
  -- bridge hypotheses for the Mover
  have hcaps : ∀ x, ((corePhase m τ1).doms x).caps
      = ((Hw.abs σ).doms x).caps := by
    intro x
    rw [hspec]
    show ((τ1.haltDom e _).doms x).caps = _
    rw [haltDom_caps' τ1 e _ x, hτ1, refillPhase_caps]
  have hgen : ∀ x, ((corePhase m τ1).doms x).slotGen
      = ((Hw.abs σ).doms x).slotGen := by
    intro x
    rw [hspec]
    show ((τ1.haltDom e _).doms x).slotGen = _
    rw [haltDom_slotGen' τ1 e _ x, hτ1, refillPhase_slotGen]
  have hrgn : ∀ x, ((corePhase m τ1).doms x).regions
      = ((Hw.abs σ).doms x).regions := by
    intro x
    rw [hspec]
    show ((τ1.haltDom e _).doms x).regions = _
    rw [haltDom_regions' τ1 e _ x, hτ1, refillPhase_regions]
  have hjob : (corePhase m τ1).mover = Hw.absMover σ := by
    rw [hspec]
    show (τ1.haltDom e _).mover = _
    rw [haltDom_mover' τ1 e _, hτ1, refillPhase_mover]
    rfl
  have hmem2 : ∀ ad, ((Hw.coreAct m).run σ σ1).mems "mem" ad 32
      = σ.mems "mem" ad 32 := by
    intro ad
    rw [hcore]
    rw [Loom.Hw.Compile.run_mems_notin "mem" _
      (by fin_cases e <;> exact of_decide_eq_true rfl) σ σ1 ad 32]
    rw [hσ1]
    exact Loom.Hw.Compile.run_mems_notin "mem" _
      (by rw [refillAct_memWrites]; simp) σ σ ad 32
  have hτm : ∀ b : Addr, (corePhase m τ1).mem b
      = σ.mems "mem" b.toNat 32 := by
    intro b
    rw [hspec]
    show (τ1.haltDom e _).mem b = _
    rw [haltDom_mem' τ1 e _, hτ1]
    rfl
  -- register frame down to the post-core accumulator
  have hp : ∀ (rn : String) (w : Nat),
      rn.startsWith "mov_" = false → ¬(rn = "cycle" ∧ w = 32) →
      ((Hw.core m).cycle σ).regs rn w
        = ((Hw.coreAct m).run σ σ1).regs rn w := by
    intro rn w h2 h4
    rw [core_cycle_unfold]
    rw [frame (show (rn, w) ∉ Hw.tickAct.regWrites from by
      intro hmem
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem
      exact h4 hmem)]
    rw [run_WritesPrefixed h2 w _ mover_prefixed]
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hspec]
    show _ = (τ1.haltDom e _).cycle + 1
    rw [haltDom_cycle]
    rfl
  · funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    exact moverAct_mem_quiescent σ _ (corePhase m τ1) hnr hcaps hgen hrgn
      hjob hmem2 hτm a
  · funext x
    have hRHS : (moverPhase (corePhase m τ1)).doms x
        = (τ1.haltDom e (BitVec.ofNat 32 f.code)).doms x := by
      rw [moverPhase_doms, hspec]
      rfl
    show Hw.absDom ((Hw.core m).cycle σ) x = _
    rw [hRHS, ← hHD x]
    have hmovfree : ∀ q ∈ domReadNames x, q.1.startsWith "mov_" = false := by
      fin_cases x <;> decide +kernel
    have hcycfree : ∀ q ∈ domReadNames x, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases x <;> exact of_decide_eq_true rfl
    apply absDom_congr
    intro p hp'
    rw [show Act.run σ (Hw.haltAct e (BitVec.ofNat 32 f.code)) σ1
      = Act.run σ (Hw.haltFault e f) σ1 from rfl, ← hcore]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g
        = (τ1.haltDom e (BitVec.ofNat 32 f.code)).gates g := by
      rw [moverPhase_gates, hspec]
      rfl
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS, ← hHG g]
    have hmovfree : ∀ q ∈ gateReadNames g, q.1.startsWith "mov_" = false := by
      fin_cases g <;> decide +kernel
    have hcycfree : ∀ q ∈ gateReadNames g, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases g <;> exact of_decide_eq_true rfl
    apply absGate_congr
    intro p hp'
    rw [show Act.run σ (Hw.haltAct e (BitVec.ofNat 32 f.code)) σ1
      = Act.run σ (Hw.haltFault e f) σ1 from rfl, ← hcore]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · show Hw.absMover ((Hw.core m).cycle σ)
      = (moverPhase (corePhase m τ1)).mover
    rw [core_cycle_unfold]
    have htick : ∀ (rn : String) (w : Nat), ¬(rn = "cycle" ∧ w = 32) →
        (Hw.tickAct.run σ (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))).regs
          rn w = (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)).regs rn w := by
      intro rn w h4
      exact frame (by
        intro hmem
        simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
          Prod.mk.injEq] at hmem
        exact h4 hmem) σ _
    rw [show Hw.absMover (Hw.tickAct.run σ
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)))
        = Hw.absMover (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)) from by
      unfold Hw.absMover
      rw [htick "mov_v" 1 (by decide), htick "mov_owner" 2 (by decide),
        htick "mov_src" 14 (by decide), htick "mov_dst" 14 (by decide),
        htick "mov_srccur" 12 (by decide), htick "mov_dstcur" 12 (by decide),
        htick "mov_rem" 13 (by decide), htick "mov_status" 12 (by decide)]]
    exact absMover_moverAct_quiescent σ _ (corePhase m τ1) hnr
      (fun x => hcaps x) (fun x => hgen x) hjob
  · have hRHS : (moverPhase (corePhase m τ1)).inflight = none := by
      rw [moverPhase_inflight, hspec]
      show (τ1.haltDom e _).inflight = none
      rw [haltDom_inflight]
      show Hw.absInflight σ = none
      rw [Hw.absInflight, if_neg (show ¬(σ.regs "if_v" 1 = 1) from hifv0)]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    rw [hp "if_v" 1 (by decide +kernel) (by decide), hcore,
      frame (show ("if_v", 1) ∉ (Hw.haltFault e f).regWrites from by
        fin_cases e <;> exact of_decide_eq_true rfl) σ σ1,
      hσ1, refill_pres m σ (by decide)]
    rw [if_neg (show ¬(σ.regs "if_v" 1 = 1) from hifv0)]


/-! ## Condition glue -/

/-- The effective-budget mux at the payer reads the post-refill payer
budget (`eligE_eval`'s core, standalone). -/
theorem effB_at_payer (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP) (e : DomainId) :
    ((effBE m e).eval σ).toNat
      = ((refillPhase m (Hw.abs σ)).doms
          ((refillPhase m (Hw.abs σ)).payer e)).budget := by
  show ((Hw.muxFin (fun q => Hw.effBudgetE m q) (Hw.payerE e)).eval σ).toNat = _
  rw [muxFin_eval (by decide : 2 ^ 2 = numDomains)]
  rw [show finOfBv (by decide : 2 ^ 2 = numDomains) ((Hw.payerE e).eval σ)
    = (Hw.abs σ).payer e from payerE_eval σ e]
  rw [refillPhase_payer]
  exact effBudget_eval m hwf hfit σ hsync ((Hw.abs σ).payer e)

/-- Costs fit the 8-bit charge register. -/
private theorem cost_lt_256 (instr : Machines.Lnp64u.Instr)
    (h : instr ∈ isa) : instr.cost.cost < 256 := by
  rw [Array.mem_def] at h
  fin_cases h <;> decide

/-! ## The remaining outcome assemblies (staged) -/

/-- Burn outcome: the payer's residual budget zeroed, nothing latched. -/
theorem square_issue_burn (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1)
    (e : DomainId) (p : DomainId) (hpay : (Hw.abs σ).payer e = p)
    (hcore : (Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)
      = (burnA e).run σ ((Hw.refillAct m).run σ σ))
    (hspec : corePhase m (refillPhase m (Hw.abs σ))
      = (refillPhase m (Hw.abs σ)).setDom p
          (fun ds => { ds with budget := 0 })) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hnr := retiringE_eval_idle σ hifv0
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  have hburn : (Hw.coreAct m).run σ σ1
      = (Act.write 32 (Hw.dbudget p) (.lit 0)).run σ σ1 := by
    rw [hcore]
    exact burnA_run σ σ1 e p hpay
  have hdoms1 : ∀ x, Hw.absDom σ1 x = τ1.doms x := fun x => by
    rw [← habs1]; rfl
  have hgates1 : ∀ g, Hw.absGate σ1 g = τ1.gates g := fun g => by
    rw [← habs1]; rfl
  -- one-write read helper
  have hread : ∀ (rn : String) (w : Nat), rn ≠ Hw.dbudget p →
      ((Hw.coreAct m).run σ σ1).regs rn w = σ1.regs rn w := by
    intro rn w hne
    rw [hburn]
    show (σ1.regs.set (Hw.dbudget p) ((Expr.lit (0:BitVec 32)).eval σ)) rn w = _
    simp only [RegEnv.set]
    rw [if_neg hne]
  -- spec-side field facts
  have hspecdoms : ∀ x, (corePhase m τ1).doms x
      = if x = p then { (τ1.doms p) with budget := 0 } else τ1.doms x := by
    intro x
    rw [hspec]
    show (Loom.Fun.update τ1.doms p _) x = _
    by_cases hxp : x = p
    · subst hxp
      rw [Loom.Fun.update_same, if_pos rfl]
    · rw [Loom.Fun.update_ne _ _ _ _ hxp, if_neg hxp]
  -- Mover-bridge hypotheses
  have hcaps : ∀ x, ((corePhase m τ1).doms x).caps
      = ((Hw.abs σ).doms x).caps := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).caps = _
      rw [hτ1, refillPhase_caps]
    · rw [if_neg hxp, hτ1, refillPhase_caps]
  have hgen : ∀ x, ((corePhase m τ1).doms x).slotGen
      = ((Hw.abs σ).doms x).slotGen := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).slotGen = _
      rw [hτ1, refillPhase_slotGen]
    · rw [if_neg hxp, hτ1, refillPhase_slotGen]
  have hrgn : ∀ x, ((corePhase m τ1).doms x).regions
      = ((Hw.abs σ).doms x).regions := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).regions = _
      rw [hτ1, refillPhase_regions]
    · rw [if_neg hxp, hτ1, refillPhase_regions]
  have hjob : (corePhase m τ1).mover = Hw.absMover σ := by
    rw [hspec]
    show τ1.mover = _
    rw [hτ1, refillPhase_mover]
    rfl
  have hmem2 : ∀ ad, ((Hw.coreAct m).run σ σ1).mems "mem" ad 32
      = σ.mems "mem" ad 32 := by
    intro ad
    rw [hburn]
    show σ1.mems "mem" ad 32 = _
    rw [hσ1]
    exact Loom.Hw.Compile.run_mems_notin "mem" _
      (by rw [refillAct_memWrites]; simp) σ σ ad 32
  have hτm : ∀ b : Addr, (corePhase m τ1).mem b
      = σ.mems "mem" b.toNat 32 := by
    intro b
    rw [hspec]
    show τ1.mem b = _
    rw [hτ1]
    rfl
  have hp : ∀ (rn : String) (w : Nat),
      rn.startsWith "mov_" = false → ¬(rn = "cycle" ∧ w = 32) →
      ((Hw.core m).cycle σ).regs rn w
        = ((Hw.coreAct m).run σ σ1).regs rn w := by
    intro rn w h2 h4
    rw [core_cycle_unfold]
    rw [frame (show (rn, w) ∉ Hw.tickAct.regWrites from by
      intro hmem
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem
      exact h4 hmem)]
    rw [run_WritesPrefixed h2 w _ mover_prefixed]
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hspec]
    rfl
  · funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    exact moverAct_mem_quiescent σ _ (corePhase m τ1) hnr hcaps hgen hrgn
      hjob hmem2 hτm a
  · funext x
    have hRHS : (moverPhase (corePhase m τ1)).doms x
        = (corePhase m τ1).doms x := congrFun (moverPhase_doms _) x
    show Hw.absDom ((Hw.core m).cycle σ) x = _
    rw [hRHS, hspecdoms x]
    have hmovfree : ∀ q ∈ domReadNames x, q.1.startsWith "mov_" = false := by
      fin_cases x <;> decide +kernel
    have hcycfree : ∀ q ∈ domReadNames x, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases x <;> exact of_decide_eq_true rfl
    by_cases hxp : x = p
    · rw [if_pos hxp, ← hxp, ← hdoms1 x]
      apply domainState_ext'
      · funext r
        show ((Hw.core m).cycle σ).regs (Hw.dreg x r) 32 = _
        rw [hp _ _ (by fin_cases x <;> fin_cases r <;> decide +kernel)
          (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl)]
        rfl
      · show ((Hw.core m).cycle σ).regs (Hw.dpc x) 12 = _
        rw [hp _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)]
        rfl
      · funext s
        show (if ((Hw.core m).cycle σ).regs (Hw.dcapV x s) 1 = 1
          then _ else _) = _
        rw [hp (Hw.dcapV x s) 1
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl),
          hp (Hw.dcapKind x s) 32
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl),
          hp (Hw.dcapLinV x s) 1
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl),
          hp (Hw.dcapLin x s) 4
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)]
        rfl
      · funext s
        show ((Hw.core m).cycle σ).regs (Hw.dgen x s) 8 = _
        rw [hp _ _ (by fin_cases x <;> fin_cases s <;> decide +kernel)
          (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)]
        rfl
      · funext l
        show (if ((Hw.core m).cycle σ).regs (Hw.dcellV x l) 1 = 1
          then _ else _) = _
        rw [hp (Hw.dcellV x l) 1
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases l <;>
            exact of_decide_eq_true rfl),
          hp (Hw.dcellPar x l) 14
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases l <;>
            exact of_decide_eq_true rfl)]
        rfl
      · funext r
        show (if ((Hw.core m).cycle σ).regs (Hw.drgnV x r) 1 = 1
          then _ else _) = _
        rw [hp (Hw.drgnV x r) 1
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl),
          hp (Hw.drgn x r) 42
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl)]
        rfl
      · show Hw.decRun _ _ = _
        rw [hp (Hw.drun x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl),
          hp (Hw.drunG x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)]
        rfl
      · show (if ((Hw.core m).cycle σ).regs (Hw.dsrvV x) 1 = 1
          then _ else _) = _
        rw [hp (Hw.dsrvV x) 1 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl),
          hp (Hw.dsrv x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)]
        rfl
      · show ((Hw.core m).cycle σ).regs (Hw.dcause x) 32 = _
        rw [hp _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)]
        rfl
      · show (((Hw.core m).cycle σ).regs (Hw.dbudget x) 32).toNat = _
        rw [hp _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hburn, hxp]
        show ((σ1.regs.set (Hw.dbudget p)
          ((Expr.lit (0:BitVec 32)).eval σ)) (Hw.dbudget p) 32).toNat = _
        simp [RegEnv.set, Expr.eval]
      · show (((Hw.core m).cycle σ).regs (Hw.dmaxdon x) 32).toNat = _
        rw [hp _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)]
        rfl
    · rw [if_neg hxp, ← hdoms1 x]
      apply absDom_congr
      intro q hq
      rw [hp q.1 q.2 (hmovfree q hq) (hcycfree q hq)]
      apply hread
      exact (show ∀ r ∈ domReadNames x, r.1 ≠ Hw.dbudget p from by
        fin_cases x <;> fin_cases p <;>
          first
            | exact absurd rfl hxp
            | exact of_decide_eq_true rfl) q hq
  · funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g = τ1.gates g := by
      rw [moverPhase_gates, hspec]
      rfl
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS, ← hgates1 g]
    have hmovfree : ∀ q ∈ gateReadNames g, q.1.startsWith "mov_" = false := by
      fin_cases g <;> decide +kernel
    have hcycfree : ∀ q ∈ gateReadNames g, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases g <;> exact of_decide_eq_true rfl
    apply absGate_congr
    intro q hq
    rw [hp q.1 q.2 (hmovfree q hq) (hcycfree q hq)]
    apply hread
    exact (show ∀ r ∈ gateReadNames g, r.1 ≠ Hw.dbudget p from by
      fin_cases g <;> fin_cases p <;> exact of_decide_eq_true rfl) q hq
  · show Hw.absMover ((Hw.core m).cycle σ)
      = (moverPhase (corePhase m τ1)).mover
    rw [core_cycle_unfold]
    have htick : ∀ (rn : String) (w : Nat), ¬(rn = "cycle" ∧ w = 32) →
        (Hw.tickAct.run σ (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))).regs
          rn w = (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)).regs rn w := by
      intro rn w h4
      exact frame (by
        intro hmem
        simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
          Prod.mk.injEq] at hmem
        exact h4 hmem) σ _
    rw [show Hw.absMover (Hw.tickAct.run σ
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)))
        = Hw.absMover (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)) from by
      unfold Hw.absMover
      rw [htick "mov_v" 1 (by decide), htick "mov_owner" 2 (by decide),
        htick "mov_src" 14 (by decide), htick "mov_dst" 14 (by decide),
        htick "mov_srccur" 12 (by decide), htick "mov_dstcur" 12 (by decide),
        htick "mov_rem" 13 (by decide), htick "mov_status" 12 (by decide)]]
    exact absMover_moverAct_quiescent σ _ (corePhase m τ1) hnr hcaps hgen hjob
  · have hRHS : (moverPhase (corePhase m τ1)).inflight = none := by
      rw [moverPhase_inflight, hspec]
      show τ1.inflight = none
      show Hw.absInflight σ = none
      rw [Hw.absInflight, if_neg (show ¬(σ.regs "if_v" 1 = 1) from hifv0)]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    rw [hp "if_v" 1 (by decide +kernel) (by decide),
      hread "if_v" 1 (by fin_cases p <;> exact of_decide_eq_true rfl),
      hσ1, refill_pres m σ (by decide)]
    rw [if_neg (show ¬(σ.regs "if_v" 1 = 1) from hifv0)]

private theorem toNat_sub_of_le32 (a b : BitVec 32) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- Plain (non-serving) issue: charge + latch. -/
theorem square_issue_plain (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1)
    (e : DomainId) (w : Loom.Word32) (instr : Machines.Lnp64u.Instr)
    (p : DomainId) (hpay : (Hw.abs σ).payer e = p)
    (hw : (wE e).eval σ = w)
    (hcost : ((Hw.costE (opcEx e)).eval σ).toNat = instr.cost.cost)
    (hble : instr.cost.cost ≤ ((refillPhase m (Hw.abs σ)).doms p).budget)
    (hcore : (Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)
      = ((chargeA m e).seq (latchA e)).run σ ((Hw.refillAct m).run σ σ))
    (hspec : corePhase m (refillPhase m (Hw.abs σ))
      = (let τ1 := refillPhase m (Hw.abs σ)
        let σ' := τ1.setDom p fun ds =>
          { ds with budget := ds.budget - instr.cost.cost }
        { σ' with inflight := some ⟨e, w, instr.cost.cost⟩ })) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hnr := retiringE_eval_idle σ hifv0
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  have hdoms1 : ∀ x, Hw.absDom σ1 x = τ1.doms x := fun x => by
    rw [← habs1]; rfl
  have hgates1 : ∀ g, Hw.absGate σ1 g = τ1.gates g := fun g => by
    rw [← habs1]; rfl
  -- the concrete write chain
  have hchain : (Hw.coreAct m).run σ σ1
      = (latchA e).run σ
          ((Act.write 32 (Hw.dbudget p)
            (.sub (Hw.effBudgetE m p) (cost32E e))).run σ σ1) := by
    rw [hcore]
    show (latchA e).run σ ((chargeA m e).run σ σ1) = _
    rw [chargeA_run m σ σ1 e p hpay]
  have hread : ∀ (rn : String) (w' : Nat), rn ≠ Hw.dbudget p →
      rn ≠ "if_v" → rn ≠ "if_dom" → rn ≠ "if_word" → rn ≠ "if_cl" →
      ((Hw.coreAct m).run σ σ1).regs rn w' = σ1.regs rn w' := by
    intro rn w' h1 h2 h3 h4 h5
    rw [hchain]
    show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word" ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ)) : _root_.Loom.Hw.RegEnv) rn w' = _
    simp only [RegEnv.set]
    rw [if_neg h5, if_neg h4, if_neg h3, if_neg h2, if_neg h1]
  -- spec-side doms
  have hspecdoms : ∀ x, (corePhase m τ1).doms x
      = if x = p then { (τ1.doms p) with
          budget := (τ1.doms p).budget - instr.cost.cost }
        else τ1.doms x := by
    intro x
    rw [hspec]
    show (Loom.Fun.update τ1.doms p _) x = _
    by_cases hxp : x = p
    · subst hxp
      rw [Loom.Fun.update_same, if_pos rfl]
    · rw [Loom.Fun.update_ne _ _ _ _ hxp, if_neg hxp]
  have hcaps : ∀ x, ((corePhase m τ1).doms x).caps
      = ((Hw.abs σ).doms x).caps := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).caps = _
      rw [hτ1, refillPhase_caps]
    · rw [if_neg hxp, hτ1, refillPhase_caps]
  have hgen : ∀ x, ((corePhase m τ1).doms x).slotGen
      = ((Hw.abs σ).doms x).slotGen := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).slotGen = _
      rw [hτ1, refillPhase_slotGen]
    · rw [if_neg hxp, hτ1, refillPhase_slotGen]
  have hrgn : ∀ x, ((corePhase m τ1).doms x).regions
      = ((Hw.abs σ).doms x).regions := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).regions = _
      rw [hτ1, refillPhase_regions]
    · rw [if_neg hxp, hτ1, refillPhase_regions]
  have hjob : (corePhase m τ1).mover = Hw.absMover σ := by
    rw [hspec]
    show τ1.mover = _
    rw [hτ1, refillPhase_mover]
    rfl
  have hmem2 : ∀ ad, ((Hw.coreAct m).run σ σ1).mems "mem" ad 32
      = σ.mems "mem" ad 32 := by
    intro ad
    rw [hchain]
    show σ1.mems "mem" ad 32 = _
    rw [hσ1]
    exact Loom.Hw.Compile.run_mems_notin "mem" _
      (by rw [refillAct_memWrites]; simp) σ σ ad 32
  have hτm : ∀ b : Addr, (corePhase m τ1).mem b
      = σ.mems "mem" b.toNat 32 := by
    intro b
    rw [hspec]
    show τ1.mem b = _
    rw [hτ1]
    rfl
  have hp : ∀ (rn : String) (w' : Nat),
      rn.startsWith "mov_" = false → ¬(rn = "cycle" ∧ w' = 32) →
      ((Hw.core m).cycle σ).regs rn w'
        = ((Hw.coreAct m).run σ σ1).regs rn w' := by
    intro rn w' h2 h4
    rw [core_cycle_unfold]
    rw [frame (show (rn, w') ∉ Hw.tickAct.regWrites from by
      intro hmem
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem
      exact h4 hmem)]
    rw [run_WritesPrefixed h2 w' _ mover_prefixed]
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hspec]
    rfl
  · funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    exact moverAct_mem_quiescent σ _ (corePhase m τ1) hnr hcaps hgen hrgn
      hjob hmem2 hτm a
  · funext x
    have hRHS : (moverPhase (corePhase m τ1)).doms x
        = (corePhase m τ1).doms x := congrFun (moverPhase_doms _) x
    show Hw.absDom ((Hw.core m).cycle σ) x = _
    rw [hRHS, hspecdoms x]
    have hmovfree : ∀ q ∈ domReadNames x, q.1.startsWith "mov_" = false := by
      fin_cases x <;> decide +kernel
    have hcycfree : ∀ q ∈ domReadNames x, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases x <;> exact of_decide_eq_true rfl
    by_cases hxp : x = p
    · rw [if_pos hxp, ← hxp, ← hdoms1 x]
      apply domainState_ext'
      · funext r
        show ((Hw.core m).cycle σ).regs (Hw.dreg x r) 32 = _
        rw [hp _ _ (by fin_cases x <;> fin_cases r <;> decide +kernel)
          (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)]
        rfl
      · show ((Hw.core m).cycle σ).regs (Hw.dpc x) 12 = _
        rw [hp _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
      · funext s
        show (if ((Hw.core m).cycle σ).regs (Hw.dcapV x s) 1 = 1
          then _ else _) = _
        rw [hp (Hw.dcapV x s) 1
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
          hp (Hw.dcapKind x s) 32
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
          hp (Hw.dcapLinV x s) 1
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
          hp (Hw.dcapLin x s) 4
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)]
        rfl
      · funext s
        show ((Hw.core m).cycle σ).regs (Hw.dgen x s) 8 = _
        rw [hp _ _ (by fin_cases x <;> fin_cases s <;> decide +kernel)
          (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)]
        rfl
      · funext l
        show (if ((Hw.core m).cycle σ).regs (Hw.dcellV x l) 1 = 1
          then _ else _) = _
        rw [hp (Hw.dcellV x l) 1
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases l <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl),
          hp (Hw.dcellPar x l) 14
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases l <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)]
        rfl
      · funext r
        show (if ((Hw.core m).cycle σ).regs (Hw.drgnV x r) 1 = 1
          then _ else _) = _
        rw [hp (Hw.drgnV x r) 1
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl),
          hp (Hw.drgn x r) 42
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)]
        rfl
      · show Hw.decRun _ _ = _
        rw [hp (Hw.drun x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl),
          hp (Hw.drunG x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
      · show (if ((Hw.core m).cycle σ).regs (Hw.dsrvV x) 1 = 1
          then _ else _) = _
        rw [hp (Hw.dsrvV x) 1 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl),
          hp (Hw.dsrv x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
      · show ((Hw.core m).cycle σ).regs (Hw.dcause x) 32 = _
        rw [hp _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
      · -- the charged budget
        show (((Hw.core m).cycle σ).regs (Hw.dbudget x) 32).toNat = _
        rw [hp _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hchain]
        rw [show ((latchA e).run σ
            ((Act.write 32 (Hw.dbudget p)
              (.sub (Hw.effBudgetE m p) (cost32E e))).run σ σ1)).regs
            (Hw.dbudget x) 32
          = ((Act.write 32 (Hw.dbudget p)
              (.sub (Hw.effBudgetE m p) (cost32E e))).run σ σ1).regs
            (Hw.dbudget x) 32 from by
          show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word" ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ)) : _root_.Loom.Hw.RegEnv) (Hw.dbudget x) 32 = _
          simp only [RegEnv.set]
          rw [if_neg (by fin_cases x <;> exact of_decide_eq_true rfl :
              Hw.dbudget x ≠ "if_cl"),
            if_neg (by fin_cases x <;> exact of_decide_eq_true rfl :
              Hw.dbudget x ≠ "if_word"),
            if_neg (by fin_cases x <;> exact of_decide_eq_true rfl :
              Hw.dbudget x ≠ "if_dom"),
            if_neg (by fin_cases x <;> exact of_decide_eq_true rfl :
              Hw.dbudget x ≠ "if_v")]
          rfl]
        rw [hxp]
        show ((σ1.regs.set (Hw.dbudget p)
          ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ))
          (Hw.dbudget p) 32).toNat = _
        simp only [RegEnv.set, dite_true]
        show (((Hw.effBudgetE m p).eval σ - (cost32E e).eval σ)).toNat = _
        have hEb : ((Hw.effBudgetE m p).eval σ).toNat
            = (τ1.doms p).budget := effBudget_eval m hwf hfit σ hsync p
        have hC32 : ((cost32E e).eval σ).toNat = instr.cost.cost := by
          show (((Hw.costE (opcEx e)).eval σ).setWidth 32).toNat = _
          rw [toNat_setWidth_le (by omega)]
          exact hcost
        rw [toNat_sub_of_le32 _ _ (by rw [hEb, hC32]; exact hble)]
        rw [hEb, hC32, hdoms1 p]
      · show (((Hw.core m).cycle σ).regs (Hw.dmaxdon x) 32).toNat = _
        rw [hp _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
    · rw [if_neg hxp, ← hdoms1 x]
      apply absDom_congr
      intro q hq
      rw [hp q.1 q.2 (hmovfree q hq) (hcycfree q hq)]
      apply hread
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ Hw.dbudget p from by
          fin_cases x <;> fin_cases p <;>
            first
              | exact absurd rfl hxp
              | exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ "if_v" from by
          fin_cases x <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ "if_dom" from by
          fin_cases x <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ "if_word" from by
          fin_cases x <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ "if_cl" from by
          fin_cases x <;> exact of_decide_eq_true rfl) q hq
  · funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g = τ1.gates g := by
      rw [moverPhase_gates, hspec]
      rfl
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS, ← hgates1 g]
    have hmovfree : ∀ q ∈ gateReadNames g, q.1.startsWith "mov_" = false := by
      fin_cases g <;> decide +kernel
    have hcycfree : ∀ q ∈ gateReadNames g, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases g <;> exact of_decide_eq_true rfl
    apply absGate_congr
    intro q hq
    rw [hp q.1 q.2 (hmovfree q hq) (hcycfree q hq)]
    apply hread
    · exact (show ∀ r ∈ gateReadNames g, r.1 ≠ Hw.dbudget p from by
        fin_cases g <;> fin_cases p <;> exact of_decide_eq_true rfl) q hq
    · exact (show ∀ r ∈ gateReadNames g, r.1 ≠ "if_v" from by
        fin_cases g <;> exact of_decide_eq_true rfl) q hq
    · exact (show ∀ r ∈ gateReadNames g, r.1 ≠ "if_dom" from by
        fin_cases g <;> exact of_decide_eq_true rfl) q hq
    · exact (show ∀ r ∈ gateReadNames g, r.1 ≠ "if_word" from by
        fin_cases g <;> exact of_decide_eq_true rfl) q hq
    · exact (show ∀ r ∈ gateReadNames g, r.1 ≠ "if_cl" from by
        fin_cases g <;> exact of_decide_eq_true rfl) q hq
  · show Hw.absMover ((Hw.core m).cycle σ)
      = (moverPhase (corePhase m τ1)).mover
    rw [core_cycle_unfold]
    have htick : ∀ (rn : String) (w' : Nat), ¬(rn = "cycle" ∧ w' = 32) →
        (Hw.tickAct.run σ (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))).regs
          rn w' = (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)).regs rn w' := by
      intro rn w' h4
      exact frame (by
        intro hmem
        simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
          Prod.mk.injEq] at hmem
        exact h4 hmem) σ _
    rw [show Hw.absMover (Hw.tickAct.run σ
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)))
        = Hw.absMover (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)) from by
      unfold Hw.absMover
      rw [htick "mov_v" 1 (by decide), htick "mov_owner" 2 (by decide),
        htick "mov_src" 14 (by decide), htick "mov_dst" 14 (by decide),
        htick "mov_srccur" 12 (by decide), htick "mov_dstcur" 12 (by decide),
        htick "mov_rem" 13 (by decide), htick "mov_status" 12 (by decide)]]
    exact absMover_moverAct_quiescent σ _ (corePhase m τ1) hnr hcaps hgen hjob
  · -- the latched instruction
    have hRHS : (moverPhase (corePhase m τ1)).inflight
        = some ⟨e, w, instr.cost.cost⟩ := by
      rw [moverPhase_inflight, hspec]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    have hifv1 : ((Hw.core m).cycle σ).regs "if_v" 1 = 1#1 := by
      rw [hp "if_v" 1 (by decide +kernel) (by decide), hchain]
      show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word" ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ)) : _root_.Loom.Hw.RegEnv) "if_v" 1 = 1#1
      simp only [RegEnv.set]
      rw [if_neg (by decide : ("if_v":String) ≠ "if_cl"),
        if_neg (by decide : ("if_v":String) ≠ "if_word"),
        if_neg (by decide : ("if_v":String) ≠ "if_dom")]
      simp [Expr.eval]
    rw [if_pos (show ((Hw.core m).cycle σ).regs "if_v" 1 = 1 from hifv1)]
    have hifd : ((Hw.core m).cycle σ).regs "if_dom" 2
        = BitVec.ofNat 2 e.val := by
      rw [hp "if_dom" 2 (by decide +kernel) (by decide), hchain]
      show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word" ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ)) : _root_.Loom.Hw.RegEnv) "if_dom" 2 = _
      simp only [RegEnv.set]
      rw [if_neg (by decide : ("if_dom":String) ≠ "if_cl"),
        if_neg (by decide : ("if_dom":String) ≠ "if_word")]
      simp [Expr.eval]
    have hifw : ((Hw.core m).cycle σ).regs "if_word" 32 = w := by
      rw [hp "if_word" 32 (by decide +kernel) (by decide), hchain]
      show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word" ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ)) : _root_.Loom.Hw.RegEnv) "if_word" 32 = _
      simp only [RegEnv.set]
      rw [if_neg (by decide : ("if_word":String) ≠ "if_cl")]
      simp [hw]
    have hifcl : ((Hw.core m).cycle σ).regs "if_cl" 8
        = (Hw.costE (opcEx e)).eval σ := by
      rw [hp "if_cl" 8 (by decide +kernel) (by decide), hchain]
      show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word" ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ)) : _root_.Loom.Hw.RegEnv) "if_cl" 8 = _
      simp [RegEnv.set]
    rw [hifd, hifw, hifcl]
    congr 1
    show (⟨finOfBv (by decide) (BitVec.ofNat 2 e.val), w,
      ((Hw.costE (opcEx e)).eval σ).toNat⟩ : InFlight) = _
    rw [show (finOfBv (by decide : 2 ^ 2 = numDomains)
        (BitVec.ofNat 2 e.val)) = e from by
      apply Fin.ext
      rw [finOfBv_val, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := e.isLt; omega)]
    rw [hcost]

/-- Serving issue: charge + donation draw + latch. -/
theorem square_issue_serve (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1)
    (e : DomainId) (w : Loom.Word32) (instr : Machines.Lnp64u.Instr)
    (p : DomainId) (hpay : (Hw.abs σ).payer e = p)
    (g : GateId) (hg : g.val = (σ.regs (Hw.dsrv e) 2).toNat)
    (a : Activation)
    (ha : ((refillPhase m (Hw.abs σ)).gates g).act = some a)
    (hw : (wE e).eval σ = w)
    (hcost : ((Hw.costE (opcEx e)).eval σ).toNat = instr.cost.cost)
    (hble : instr.cost.cost ≤ ((refillPhase m (Hw.abs σ)).doms p).budget)
    (hdble : instr.cost.cost ≤ a.donated)
    (hdon : ((donE e).eval σ).toNat = a.donated)
    (hcore : (Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)
      = ((chargeA m e).seq ((drawDonA e).seq (latchA e))).run σ
          ((Hw.refillAct m).run σ σ))
    (hspec : corePhase m (refillPhase m (Hw.abs σ))
      = (let τ1 := refillPhase m (Hw.abs σ)
        let σ' := τ1.setDom p fun ds =>
          { ds with budget := ds.budget - instr.cost.cost }
        let gs' : GateState := { (σ'.gates g) with
          act := some { a with donated := a.donated - instr.cost.cost } }
        let σ'' := { σ' with gates := Loom.Fun.update σ'.gates g gs' }
        { σ'' with inflight := some ⟨e, w, instr.cost.cost⟩ })) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hnr := retiringE_eval_idle σ hifv0
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  have hdoms1 : ∀ x, Hw.absDom σ1 x = τ1.doms x := fun x => by
    rw [← habs1]; rfl
  have hgates1 : ∀ h, Hw.absGate σ1 h = τ1.gates h := fun h => by
    rw [← habs1]; rfl
  have hchain : (Hw.coreAct m).run σ σ1
      = (latchA e).run σ
          ((Act.write 32 (Hw.gdon g) (.sub (donE e) (cost32E e))).run σ
            ((Act.write 32 (Hw.dbudget p)
              (.sub (Hw.effBudgetE m p) (cost32E e))).run σ σ1)) := by
    rw [hcore]
    show (latchA e).run σ ((drawDonA e).run σ ((chargeA m e).run σ σ1)) = _
    rw [chargeA_run m σ σ1 e p hpay, drawDonA_run σ _ e g hg]
  have hread : ∀ (rn : String) (w' : Nat), rn ≠ Hw.dbudget p →
      rn ≠ Hw.gdon g → rn ≠ "if_v" → rn ≠ "if_dom" → rn ≠ "if_word" →
      rn ≠ "if_cl" →
      ((Hw.coreAct m).run σ σ1).regs rn w' = σ1.regs rn w' := by
    intro rn w' h1 h1g h2 h3 h4 h5
    rw [hchain]
    show ((((((σ1.regs.set (Hw.dbudget p)
      ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set (Hw.gdon g)
      ((Expr.sub (donE e) (cost32E e)).eval σ)).set "if_v"
      ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom"
      ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word"
      ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ) :
      _root_.Loom.Hw.RegEnv) rn w' = _
    simp only [RegEnv.set]
    rw [if_neg h5, if_neg h4, if_neg h3, if_neg h2, if_neg h1g, if_neg h1]
  have hC32 : ((cost32E e).eval σ).toNat = instr.cost.cost := by
    show (((Hw.costE (opcEx e)).eval σ).setWidth 32).toNat = _
    rw [toNat_setWidth_le (by omega)]
    exact hcost
  -- spec-side facts
  have hspecdoms : ∀ x, (corePhase m τ1).doms x
      = if x = p then { (τ1.doms p) with
          budget := (τ1.doms p).budget - instr.cost.cost }
        else τ1.doms x := by
    intro x
    rw [hspec]
    show (Loom.Fun.update τ1.doms p _) x = _
    by_cases hxp : x = p
    · subst hxp
      rw [Loom.Fun.update_same, if_pos rfl]
    · rw [Loom.Fun.update_ne _ _ _ _ hxp, if_neg hxp]
  have hspecgates : ∀ h, (corePhase m τ1).gates h
      = if h = g then { (τ1.gates g) with
          act := some { a with donated := a.donated - instr.cost.cost } }
        else τ1.gates h := by
    intro h
    rw [hspec]
    show (Loom.Fun.update τ1.gates g _) h = _
    by_cases hhg : h = g
    · subst hhg
      rw [Loom.Fun.update_same, if_pos rfl]
      rfl
    · rw [Loom.Fun.update_ne _ _ _ _ hhg, if_neg hhg]
  have hcaps : ∀ x, ((corePhase m τ1).doms x).caps
      = ((Hw.abs σ).doms x).caps := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).caps = _
      rw [hτ1, refillPhase_caps]
    · rw [if_neg hxp, hτ1, refillPhase_caps]
  have hgen : ∀ x, ((corePhase m τ1).doms x).slotGen
      = ((Hw.abs σ).doms x).slotGen := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).slotGen = _
      rw [hτ1, refillPhase_slotGen]
    · rw [if_neg hxp, hτ1, refillPhase_slotGen]
  have hrgn : ∀ x, ((corePhase m τ1).doms x).regions
      = ((Hw.abs σ).doms x).regions := by
    intro x
    rw [hspecdoms x]
    by_cases hxp : x = p
    · subst hxp
      rw [if_pos rfl]
      show (τ1.doms x).regions = _
      rw [hτ1, refillPhase_regions]
    · rw [if_neg hxp, hτ1, refillPhase_regions]
  have hjob : (corePhase m τ1).mover = Hw.absMover σ := by
    rw [hspec]
    show τ1.mover = _
    rw [hτ1, refillPhase_mover]
    rfl
  have hmem2 : ∀ ad, ((Hw.coreAct m).run σ σ1).mems "mem" ad 32
      = σ.mems "mem" ad 32 := by
    intro ad
    rw [hchain]
    show σ1.mems "mem" ad 32 = _
    rw [hσ1]
    exact Loom.Hw.Compile.run_mems_notin "mem" _
      (by rw [refillAct_memWrites]; simp) σ σ ad 32
  have hτm : ∀ b : Addr, (corePhase m τ1).mem b
      = σ.mems "mem" b.toNat 32 := by
    intro b
    rw [hspec]
    show τ1.mem b = _
    rw [hτ1]
    rfl
  have hp' : ∀ (rn : String) (w' : Nat),
      rn.startsWith "mov_" = false → ¬(rn = "cycle" ∧ w' = 32) →
      ((Hw.core m).cycle σ).regs rn w'
        = ((Hw.coreAct m).run σ σ1).regs rn w' := by
    intro rn w' h2 h4
    rw [core_cycle_unfold]
    rw [frame (show (rn, w') ∉ Hw.tickAct.regWrites from by
      intro hmem
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem
      exact h4 hmem)]
    rw [run_WritesPrefixed h2 w' _ mover_prefixed]
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hspec]
    rfl
  · funext b
    show ((Hw.core m).cycle σ).mems "mem" b.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ b.toNat 32]
    exact moverAct_mem_quiescent σ _ (corePhase m τ1) hnr hcaps hgen hrgn
      hjob hmem2 hτm b
  · funext x
    have hRHS : (moverPhase (corePhase m τ1)).doms x
        = (corePhase m τ1).doms x := congrFun (moverPhase_doms _) x
    show Hw.absDom ((Hw.core m).cycle σ) x = _
    rw [hRHS, hspecdoms x]
    have hmovfree : ∀ q ∈ domReadNames x, q.1.startsWith "mov_" = false := by
      fin_cases x <;> decide +kernel
    have hcycfree : ∀ q ∈ domReadNames x, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases x <;> exact of_decide_eq_true rfl
    by_cases hxp : x = p
    · rw [if_pos hxp, ← hxp, ← hdoms1 x]
      apply domainState_ext'
      · funext r
        show ((Hw.core m).cycle σ).regs (Hw.dreg x r) 32 = _
        rw [hp' _ _ (by fin_cases x <;> fin_cases r <;> decide +kernel)
          (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)]
        rfl
      · show ((Hw.core m).cycle σ).regs (Hw.dpc x) 12 = _
        rw [hp' _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
      · funext s
        show (if ((Hw.core m).cycle σ).regs (Hw.dcapV x s) 1 = 1
          then _ else _) = _
        rw [hp' (Hw.dcapV x s) 1
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
          hp' (Hw.dcapKind x s) 32
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
          hp' (Hw.dcapLinV x s) 1
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl),
          hp' (Hw.dcapLin x s) 4
            (by fin_cases x <;> fin_cases s <;> decide +kernel)
            (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)]
        rfl
      · funext s
        show ((Hw.core m).cycle σ).regs (Hw.dgen x s) 8 = _
        rw [hp' _ _ (by fin_cases x <;> fin_cases s <;> decide +kernel)
          (by fin_cases x <;> fin_cases s <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases s <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases s <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases s <;> exact of_decide_eq_true rfl)]
        rfl
      · funext l
        show (if ((Hw.core m).cycle σ).regs (Hw.dcellV x l) 1 = 1
          then _ else _) = _
        rw [hp' (Hw.dcellV x l) 1
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases l <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases l <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl),
          hp' (Hw.dcellPar x l) 14
            (by fin_cases x <;> fin_cases l <;> decide +kernel)
            (by fin_cases x <;> fin_cases l <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases l <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases l <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases l <;> exact of_decide_eq_true rfl)]
        rfl
      · funext r
        show (if ((Hw.core m).cycle σ).regs (Hw.drgnV x r) 1 = 1
          then _ else _) = _
        rw [hp' (Hw.drgnV x r) 1
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl),
          hp' (Hw.drgn x r) 42
            (by fin_cases x <;> fin_cases r <;> decide +kernel)
            (by fin_cases x <;> fin_cases r <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;> fin_cases r <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> fin_cases r <;>
              exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases r <;> exact of_decide_eq_true rfl)]
        rfl
      · show Hw.decRun _ _ = _
        rw [hp' (Hw.drun x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl),
          hp' (Hw.drunG x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
      · show (if ((Hw.core m).cycle σ).regs (Hw.dsrvV x) 1 = 1
          then _ else _) = _
        rw [hp' (Hw.dsrvV x) 1 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl),
          hp' (Hw.dsrv x) 2 (by fin_cases x <;> decide +kernel)
            (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
      · show ((Hw.core m).cycle σ).regs (Hw.dcause x) 32 = _
        rw [hp' _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
      · show (((Hw.core m).cycle σ).regs (Hw.dbudget x) 32).toNat = _
        rw [hp' _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hchain]
        rw [show ((latchA e).run σ
            ((Act.write 32 (Hw.gdon g) (.sub (donE e) (cost32E e))).run σ
              ((Act.write 32 (Hw.dbudget p)
                (.sub (Hw.effBudgetE m p) (cost32E e))).run σ σ1))).regs
            (Hw.dbudget x) 32
          = (((Act.write 32 (Hw.dbudget p)
              (.sub (Hw.effBudgetE m p) (cost32E e))).run σ σ1)).regs
            (Hw.dbudget x) 32 from by
          show ((((((σ1.regs.set (Hw.dbudget p)
            ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set
            (Hw.gdon g) ((Expr.sub (donE e) (cost32E e)).eval σ)).set
            "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom"
            ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word"
            ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ) :
            _root_.Loom.Hw.RegEnv) (Hw.dbudget x) 32 = _
          simp only [RegEnv.set]
          rw [if_neg (by fin_cases x <;> exact of_decide_eq_true rfl :
              Hw.dbudget x ≠ "if_cl"),
            if_neg (by fin_cases x <;> exact of_decide_eq_true rfl :
              Hw.dbudget x ≠ "if_word"),
            if_neg (by fin_cases x <;> exact of_decide_eq_true rfl :
              Hw.dbudget x ≠ "if_dom"),
            if_neg (by fin_cases x <;> exact of_decide_eq_true rfl :
              Hw.dbudget x ≠ "if_v"),
            if_neg (by fin_cases x <;> fin_cases g <;>
              exact of_decide_eq_true rfl : Hw.dbudget x ≠ Hw.gdon g)]
          rfl]
        rw [hxp]
        show ((σ1.regs.set (Hw.dbudget p)
          ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ))
          (Hw.dbudget p) 32).toNat = _
        simp only [RegEnv.set, dite_true]
        show (((Hw.effBudgetE m p).eval σ - (cost32E e).eval σ)).toNat = _
        have hEb : ((Hw.effBudgetE m p).eval σ).toNat
            = (τ1.doms p).budget := effBudget_eval m hwf hfit σ hsync p
        rw [toNat_sub_of_le32 _ _ (by rw [hEb, hC32]; exact hble)]
        rw [hEb, hC32, hdoms1 p]
      · show (((Hw.core m).cycle σ).regs (Hw.dmaxdon x) 32).toNat = _
        rw [hp' _ _ (by fin_cases x <;> decide +kernel)
          (by fin_cases x <;> decide +kernel),
          hread _ _ (by rw [← hxp]; fin_cases x <;>
            exact of_decide_eq_true rfl)
            (by fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)
            (by fin_cases x <;> exact of_decide_eq_true rfl)]
        rfl
    · rw [if_neg hxp, ← hdoms1 x]
      apply absDom_congr
      intro q hq
      rw [hp' q.1 q.2 (hmovfree q hq) (hcycfree q hq)]
      apply hread
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ Hw.dbudget p from by
          fin_cases x <;> fin_cases p <;>
            first
              | exact absurd rfl hxp
              | exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ Hw.gdon g from by
          fin_cases x <;> fin_cases g <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ "if_v" from by
          fin_cases x <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ "if_dom" from by
          fin_cases x <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ "if_word" from by
          fin_cases x <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ domReadNames x, r.1 ≠ "if_cl" from by
          fin_cases x <;> exact of_decide_eq_true rfl) q hq
  · funext h
    have hRHS : (moverPhase (corePhase m τ1)).gates h
        = (corePhase m τ1).gates h := congrFun (moverPhase_gates _) h
    show Hw.absGate ((Hw.core m).cycle σ) h = _
    rw [hRHS, hspecgates h]
    have hmovfree : ∀ q ∈ gateReadNames h, q.1.startsWith "mov_" = false := by
      fin_cases h <;> decide +kernel
    have hcycfree : ∀ q ∈ gateReadNames h, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases h <;> exact of_decide_eq_true rfl
    by_cases hhg : h = g
    · -- the served gate: donation drawn down
      rw [if_pos hhg, ← hhg]
      have hact1 : σ1.regs (Hw.gactV h) 1 = 1#1 := by
        by_contra hc
        have hnone : (τ1.gates h).act = none := by
          rw [← hgates1 h]
          show (if σ1.regs (Hw.gactV h) 1 = 1#1 then _ else none) = none
          rw [if_neg hc]
        rw [hhg] at hnone
        rw [hnone] at ha
        exact absurd ha (by simp)
      -- identify `a` with the decoded activation
      have hah : (τ1.gates h).act = some a := by rw [hhg]; exact ha
      have hasome : some a =
          some { caller := finOfBv (by decide) (σ1.regs (Hw.gcaller h) 2)
                 callerRd := finOfBv (by decide) (σ1.regs (Hw.gcallerRd h) 3)
                 savedRegs := fun r => σ1.regs (Hw.gsreg h r) 32
                 savedPc := σ1.regs (Hw.gspc h) 12
                 savedServing :=
                   if σ1.regs (Hw.gssrvV h) 1 = 1#1 then
                     some (finOfBv (by decide) (σ1.regs (Hw.gssrv h) 2))
                   else none
                 depth := (σ1.regs (Hw.gdepth h) 3).toNat
                 donated := (σ1.regs (Hw.gdon h) 32).toNat } := by
        rw [← hah, ← hgates1 h]
        show (Hw.absGate σ1 h).act = _
        show (if σ1.regs (Hw.gactV h) 1 = 1#1 then _ else none) = _
        rw [if_pos hact1]
        rfl
      have haact := Option.some.inj hasome
      -- the run-side reads of the gate block
      have hgread : ∀ (rn : String) (w' : Nat), rn ≠ Hw.gdon h →
          (rn, w') ∈ gateReadNames h →
          ((Hw.core m).cycle σ).regs rn w' = σ1.regs rn w' := by
        intro rn w' hnd hmem
        rw [hp' rn w'
          ((show ∀ q ∈ gateReadNames h, q.1.startsWith "mov_" = false from by
            fin_cases h <;> decide +kernel) (rn, w') hmem)
          (fun hc => ((show ∀ q ∈ gateReadNames h, ¬(q.1 = "cycle" ∧
              q.2 = 32) from by
            fin_cases h <;> exact of_decide_eq_true rfl) (rn, w') hmem) hc)]
        apply hread
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.dbudget p from by
            fin_cases h <;> fin_cases p <;>
              exact of_decide_eq_true rfl) (rn, w') hmem
        · rw [hhg] at hnd
          exact hnd
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ "if_v" from by
            fin_cases h <;> exact of_decide_eq_true rfl) (rn, w') hmem
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ "if_dom" from by
            fin_cases h <;> exact of_decide_eq_true rfl) (rn, w') hmem
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ "if_word" from by
            fin_cases h <;> exact of_decide_eq_true rfl) (rn, w') hmem
        · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ "if_cl" from by
            fin_cases h <;> exact of_decide_eq_true rfl) (rn, w') hmem
      have hgdonr : ((Hw.core m).cycle σ).regs (Hw.gdon h) 32
          = (donE e).eval σ - (cost32E e).eval σ := by
        rw [hp' (Hw.gdon h) 32 (by fin_cases h <;> decide +kernel)
          (by fin_cases h <;> decide +kernel), hchain, hhg]
        show ((((((σ1.regs.set (Hw.dbudget p)
          ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set
          (Hw.gdon g) ((Expr.sub (donE e) (cost32E e)).eval σ)).set
          "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom"
          ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word"
          ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ) :
          _root_.Loom.Hw.RegEnv) (Hw.gdon g) 32 = _
        simp only [RegEnv.set]
        rw [if_neg (by fin_cases g <;> exact of_decide_eq_true rfl :
            Hw.gdon g ≠ "if_cl"),
          if_neg (by fin_cases g <;> exact of_decide_eq_true rfl :
            Hw.gdon g ≠ "if_word"),
          if_neg (by fin_cases g <;> exact of_decide_eq_true rfl :
            Hw.gdon g ≠ "if_dom"),
          if_neg (by fin_cases g <;> exact of_decide_eq_true rfl :
            Hw.gdon g ≠ "if_v")]
        simp [Expr.eval]
      unfold Hw.absGate
      rw [hgread (Hw.gcallee h) 2
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgread (Hw.gentry h) 12
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgread (Hw.gactV h) 1
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgread (Hw.gcaller h) 2
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgread (Hw.gcallerRd h) 3
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgread (Hw.gspc h) 12
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgread (Hw.gssrvV h) 1
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgread (Hw.gssrv h) 2
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgread (Hw.gdepth h) 3
          (by fin_cases h <;> exact of_decide_eq_true rfl) (by simp [gateReadNames]),
        hgdonr]
      have hsreg : ∀ r : RegId, ((Hw.core m).cycle σ).regs (Hw.gsreg h r) 32
          = σ1.regs (Hw.gsreg h r) 32 := fun r =>
        hgread (Hw.gsreg h r) 32
          (by fin_cases h <;> fin_cases r <;> exact of_decide_eq_true rfl)
          (by simp [gateReadNames])
      simp only [hsreg]
      -- assemble: config from the decode, activation record fieldwise
      rw [if_pos (show σ1.regs (Hw.gactV h) 1 = 1 from hact1)]
      have hcfg : (τ1.gates h).config = GateConfig.mk
          (finOfBv (by decide) (σ1.regs (Hw.gcallee h) 2))
          (σ1.regs (Hw.gentry h) 12) := by
        rw [← hgates1 h]
        rfl
      congr 1
      · rw [hcfg]
      · rw [haact] at hdon hdble ⊢
        congr 1
        rw [toNat_sub_of_le32 _ _ (by rw [hdon, hC32]; exact hdble),
          hdon, hC32]
        rfl
    · rw [if_neg hhg, ← hgates1 h]
      apply absGate_congr
      intro q hq
      rw [hp' q.1 q.2 (hmovfree q hq) (hcycfree q hq)]
      apply hread
      · exact (show ∀ r ∈ gateReadNames h, r.1 ≠ Hw.dbudget p from by
          fin_cases h <;> fin_cases p <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ gateReadNames h, r.1 ≠ Hw.gdon g from by
          fin_cases h <;> fin_cases g <;>
            first
              | exact absurd rfl hhg
              | exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ gateReadNames h, r.1 ≠ "if_v" from by
          fin_cases h <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ gateReadNames h, r.1 ≠ "if_dom" from by
          fin_cases h <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ gateReadNames h, r.1 ≠ "if_word" from by
          fin_cases h <;> exact of_decide_eq_true rfl) q hq
      · exact (show ∀ r ∈ gateReadNames h, r.1 ≠ "if_cl" from by
          fin_cases h <;> exact of_decide_eq_true rfl) q hq
  · show Hw.absMover ((Hw.core m).cycle σ)
      = (moverPhase (corePhase m τ1)).mover
    rw [core_cycle_unfold]
    have htick : ∀ (rn : String) (w' : Nat), ¬(rn = "cycle" ∧ w' = 32) →
        (Hw.tickAct.run σ (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))).regs
          rn w' = (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)).regs rn w' := by
      intro rn w' h4
      exact frame (by
        intro hmem
        simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
          Prod.mk.injEq] at hmem
        exact h4 hmem) σ _
    rw [show Hw.absMover (Hw.tickAct.run σ
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)))
        = Hw.absMover (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)) from by
      unfold Hw.absMover
      rw [htick "mov_v" 1 (by decide), htick "mov_owner" 2 (by decide),
        htick "mov_src" 14 (by decide), htick "mov_dst" 14 (by decide),
        htick "mov_srccur" 12 (by decide), htick "mov_dstcur" 12 (by decide),
        htick "mov_rem" 13 (by decide), htick "mov_status" 12 (by decide)]]
    exact absMover_moverAct_quiescent σ _ (corePhase m τ1) hnr hcaps hgen hjob
  · have hRHS : (moverPhase (corePhase m τ1)).inflight
        = some ⟨e, w, instr.cost.cost⟩ := by
      rw [moverPhase_inflight, hspec]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    have hchainR : ∀ (rn : String) (w' : Nat) (v : BitVec w'),
        True := fun _ _ _ => trivial
    have hifv1 : ((Hw.core m).cycle σ).regs "if_v" 1 = 1#1 := by
      rw [hp' "if_v" 1 (by decide +kernel) (by decide), hchain]
      show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set (Hw.gdon g)
        ((Expr.sub (donE e) (cost32E e)).eval σ)).set "if_v"
        ((Expr.lit (1 : BitVec 1)).eval σ)).set "if_dom"
        ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set "if_word"
        ((wE e).eval σ)).set "if_cl" ((Hw.costE (opcEx e)).eval σ) :
        _root_.Loom.Hw.RegEnv) "if_v" 1 = 1#1
      simp only [RegEnv.set]
      rw [if_neg (by decide : ("if_v":String) ≠ "if_cl"),
        if_neg (by decide : ("if_v":String) ≠ "if_word"),
        if_neg (by decide : ("if_v":String) ≠ "if_dom")]
      simp [Expr.eval]
    rw [if_pos (show ((Hw.core m).cycle σ).regs "if_v" 1 = 1 from hifv1)]
    have hifd : ((Hw.core m).cycle σ).regs "if_dom" 2
        = BitVec.ofNat 2 e.val := by
      rw [hp' "if_dom" 2 (by decide +kernel) (by decide), hchain]
      show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set (Hw.gdon g)
        ((Expr.sub (donE e) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set
        "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set
        "if_word" ((wE e).eval σ)).set "if_cl"
        ((Hw.costE (opcEx e)).eval σ) :
        _root_.Loom.Hw.RegEnv) "if_dom" 2 = _
      simp only [RegEnv.set]
      rw [if_neg (by decide : ("if_dom":String) ≠ "if_cl"),
        if_neg (by decide : ("if_dom":String) ≠ "if_word")]
      simp [Expr.eval]
    have hifw : ((Hw.core m).cycle σ).regs "if_word" 32 = w := by
      rw [hp' "if_word" 32 (by decide +kernel) (by decide), hchain]
      show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set (Hw.gdon g)
        ((Expr.sub (donE e) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set
        "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set
        "if_word" ((wE e).eval σ)).set "if_cl"
        ((Hw.costE (opcEx e)).eval σ) :
        _root_.Loom.Hw.RegEnv) "if_word" 32 = _
      simp only [RegEnv.set]
      rw [if_neg (by decide : ("if_word":String) ≠ "if_cl")]
      simp [hw]
    have hifcl : ((Hw.core m).cycle σ).regs "if_cl" 8
        = (Hw.costE (opcEx e)).eval σ := by
      rw [hp' "if_cl" 8 (by decide +kernel) (by decide), hchain]
      show ((((((σ1.regs.set (Hw.dbudget p) ((Expr.sub (Hw.effBudgetE m p) (cost32E e)).eval σ)).set (Hw.gdon g)
        ((Expr.sub (donE e) (cost32E e)).eval σ)).set "if_v" ((Expr.lit (1 : BitVec 1)).eval σ)).set
        "if_dom" ((Expr.lit (BitVec.ofNat 2 e.val)).eval σ)).set
        "if_word" ((wE e).eval σ)).set "if_cl"
        ((Hw.costE (opcEx e)).eval σ) :
        _root_.Loom.Hw.RegEnv) "if_cl" 8 = _
      simp [RegEnv.set]
    rw [hifd, hifw, hifcl]
    congr 1
    show (⟨finOfBv (by decide) (BitVec.ofNat 2 e.val), w,
      ((Hw.costE (opcEx e)).eval σ).toNat⟩ : InFlight) = _
    rw [show (finOfBv (by decide : 2 ^ 2 = numDomains)
        (BitVec.ofNat 2 e.val)) = e from by
      apply Fin.ext
      rw [finOfBv_val, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := e.isLt; omega)]
    rw [hcost]


/-! ## The issue-arm dispatcher -/

/-- **The idle-issue arm of the square**: idle core, a domain scheduled —
dispatch over the issue circuit's ladder, matching each outcome with its
spec equation and proven assembly. -/
theorem square_idle_issue (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrc : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hifv0 : ¬ σ.regs "if_v" 1 = 1#1)
    (e : DomainId)
    (hsched : schedule m (refillPhase m (Hw.abs σ)) = some e) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  -- the scheduled domain wins the circuit's fold
  have helig : (Hw.eligE m e).eval σ = 1#1 :=
    (eligE_eval m hwf hfit σ hsync hrc e).mpr (schedule_eligible m τ1 e hsched)
  have htop : ∀ e' : DomainId, (Hw.eligE m e').eval σ = 1#1 →
      (m.doms e').priority ≤ (m.doms e).priority := fun e' he' =>
    schedule_priority_le m τ1 e' e
      ((eligE_eval m hwf hfit σ hsync hrc e').mp he') hsched
  have hsel : (Hw.coreAct m).run σ σ1 = (Hw.issueFor m e).run σ σ1 :=
    coreAct_run_idle_issue m hwf σ σ1 e hifv0 helig htop
  have hifl : τ1.inflight = none := by
    show Hw.absInflight σ = none
    rw [Hw.absInflight, if_neg (show ¬(σ.regs "if_v" 1 = 1) from hifv0)]
  -- fetch bridge inputs
  have hrgnτ : ∀ x, (τ1.doms x).regions = ((Hw.abs σ).doms x).regions :=
    fun x => refillPhase_regions m _ x
  have hpcτ : (τ1.doms e).pc = σ.regs (Hw.dpc e) 12 := by
    rw [refillPhase_dpc]
    rfl
  have hmemτ : ∀ b : Addr, τ1.mem b = σ.mems "mem" b.toNat 32 := fun b => rfl
  obtain ⟨hfok, hfnone⟩ := fetch_bridge σ e τ1 hrgnτ hpcτ hmemτ
  by_cases hcov : (Hw.domCoversE e (Hw.rPc e) ⟨false, false, true⟩).eval σ = 1#1
  case neg =>
    -- fetch fault
    refine square_issue_fault m hwf hfit σ hsync hifv0 e .memoryAuthority ?_ ?_
    · rw [hsel]
      exact issueFor_run_fetchFault m σ σ1 e hcov
    · exact corePhase_fetchFault m τ1 e hifl hsched (hfnone hcov)
  case pos =>
  set W : Loom.Word32 := σ.mems "mem" (σ.regs (Hw.dpc e) 12).toNat 32 with hW
  have hfetch : Machines.Lnp64u.fetch τ1 e = some W := hfok hcov
  have hwE : (wE e).eval σ = W := rfl
  have hopc : Machines.Lnp64u.sig.opcodeOf W = (opcEx e).eval σ := rfl
  by_cases hkn : (Hw.knownE (opcEx e)).eval σ = 1#1
  case neg =>
    -- decode fault
    refine square_issue_fault m hwf hfit σ hsync hifv0 e .illegalInstruction
      ?_ ?_
    · rw [hsel]
      exact issueFor_run_decodeFault m σ σ1 e hcov hkn
    · exact corePhase_decodeFault m τ1 e hifl hsched W hfetch
        ((decode_none_iff σ (opcEx e) W hopc).mpr hkn)
  case pos =>
  -- decode succeeds
  have hdecs : (Loom.Isa.decode isa W).isSome := by
    rw [Loom.Isa.isSome_decode_iff]
    obtain ⟨d, hd, hop⟩ := (knownE_eval σ (opcEx e)).mp hkn
    exact ⟨d, hd, by rw [hop, hopc]⟩
  obtain ⟨instr, hdec⟩ := Option.isSome_iff_exists.mp hdecs
  have hcost8 : (Hw.costE (opcEx e)).eval σ = BitVec.ofNat 8 instr.cost.cost :=
    costE_eval_of_decode σ (opcEx e) W instr hopc hdec
  have hcost : ((Hw.costE (opcEx e)).eval σ).toNat = instr.cost.cost := by
    rw [hcost8, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (cost_lt_256 instr (Loom.Isa.decode_mem isa hdec)) (by norm_num))
  have hC32' : ((cost32E e).eval σ).toNat = instr.cost.cost := by
    show (((Hw.costE (opcEx e)).eval σ).setWidth 32).toNat = _
    rw [toNat_setWidth_le (by omega)]
    exact hcost
  set p : DomainId := (Hw.abs σ).payer e with hpdef
  have hpp : τ1.payer e = p := refillPhase_payer m _ e
  have hEb : ((effBE m e).eval σ).toNat = (τ1.doms p).budget := by
    have := effB_at_payer m hwf hfit σ hsync e
    rw [hpp] at this
    exact this
  have hshort_iff : ((Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1) ↔
      ¬(instr.cost.cost ≤ (τ1.doms (τ1.payer e)).budget) := by
    rw [ultE_eval, hEb, hC32', hpp]
    omega
  -- serving decode
  have hserv_iff : ∀ (hv : σ.regs (Hw.dsrvV e) 1 = 1#1),
      (τ1.doms e).serving
        = some (finOfBv (by decide) (σ.regs (Hw.dsrv e) 2)) := by
    intro hv
    rw [refillPhase_serving]
    show (if σ.regs (Hw.dsrvV e) 1 = 1#1 then _ else none) = _
    rw [if_pos hv]
  have hserv_none : ∀ (hv : ¬(σ.regs (Hw.dsrvV e) 1 = 1#1)),
      (τ1.doms e).serving = none := by
    intro hv
    rw [refillPhase_serving]
    show (if σ.regs (Hw.dsrvV e) 1 = 1#1 then _ else none) = _
    rw [if_neg hv]
  by_cases hshort : (Expr.ult (effBE m e) (cost32E e)).eval σ = 1#1
  case pos =>
    by_cases hsv : σ.regs (Hw.dsrvV e) 1 = 1#1
    · -- budget fault
      refine square_issue_fault m hwf hfit σ hsync hifv0 e .budget ?_ ?_
      · rw [hsel]
        exact issueFor_run_budgetFault m σ σ1 e hcov hkn hshort hsv
      · exact corePhase_budgetFault m τ1 e hifl hsched W instr hfetch hdec
          (hshort_iff.mp hshort) _ (hserv_iff hsv)
    · -- residual burn
      refine square_issue_burn m hwf hfit σ hsync hifv0 e p hpdef.symm ?_ ?_
      · rw [hsel]
        exact issueFor_run_burn m σ σ1 e hcov hkn hshort hsv
      · rw [corePhase_burn m τ1 e hifl hsched W instr hfetch hdec
          (hshort_iff.mp hshort) (hserv_none hsv), hpp]
  case neg =>
  have hble : instr.cost.cost ≤ (τ1.doms p).budget := by
    have := hshort_iff.not.mp hshort
    rw [hpp] at this
    omega
  by_cases hsv : σ.regs (Hw.dsrvV e) 1 = 1#1
  case neg =>
    -- plain issue
    refine square_issue_plain m hwf hfit σ hsync hifv0 e W instr p
      hpdef.symm hwE hcost hble ?_ ?_
    · rw [hsel]
      exact issueFor_run_plain m σ σ1 e hcov hkn hshort hsv
    · rw [corePhase_plainIssue m τ1 e hifl hsched W instr hfetch hdec
        (by rw [hpp]; exact hble) (hserv_none hsv), hpp]
  case pos =>
  set g : GateId := finOfBv (by decide) (σ.regs (Hw.dsrv e) 2) with hgdef
  have hgv : g.val = (σ.regs (Hw.dsrv e) 2).toNat := rfl
  have hsg : (τ1.doms e).serving = some g := hserv_iff hsv
  have hactv_eval : (actvE e).eval σ = σ.regs (Hw.gactV g) 1 := by
    show (Hw.muxFin (fun g' => Expr.reg 1 (Hw.gactV g')) (gidE e)).eval σ = _
    rw [muxFin_eval (by decide : 2 ^ 2 = numGates)]
    rfl
  by_cases hactv : (actvE e).eval σ = 1#1
  case neg =>
    -- protocol fault
    have hact_none : (τ1.gates g).act = none := by
      show (Hw.absGate σ g).act = none
      show (if σ.regs (Hw.gactV g) 1 = 1#1 then _ else none) = none
      rw [if_neg (fun hc => hactv (by rw [hactv_eval]; exact hc))]
    refine square_issue_fault m hwf hfit σ hsync hifv0 e .protocol ?_ ?_
    · rw [hsel]
      exact issueFor_run_protoFault m σ σ1 e hcov hkn hshort hsv hactv
    · exact corePhase_protoFault m τ1 e hifl hsched W instr hfetch hdec
        (by rw [hpp]; exact hble) g hsg hact_none
  case pos =>
  -- the live activation, decoded
  have hact1 : σ.regs (Hw.gactV g) 1 = 1#1 := by
    rw [← hactv_eval]
    exact hactv
  set a : Activation :=
    { caller := finOfBv (by decide) (σ.regs (Hw.gcaller g) 2)
      callerRd := finOfBv (by decide) (σ.regs (Hw.gcallerRd g) 3)
      savedRegs := fun r => σ.regs (Hw.gsreg g r) 32
      savedPc := σ.regs (Hw.gspc g) 12
      savedServing :=
        if σ.regs (Hw.gssrvV g) 1 = 1#1 then
          some (finOfBv (by decide) (σ.regs (Hw.gssrv g) 2))
        else none
      depth := (σ.regs (Hw.gdepth g) 3).toNat
      donated := (σ.regs (Hw.gdon g) 32).toNat } with hadef
  have ha : (τ1.gates g).act = some a := by
    show (Hw.absGate σ g).act = some a
    show (if σ.regs (Hw.gactV g) 1 = 1#1 then _ else none) = some a
    rw [if_pos hact1, hadef]
    rfl
  have hdon : ((donE e).eval σ).toNat = a.donated := by
    show ((Hw.muxFin (fun g' => Expr.reg 32 (Hw.gdon g')) (gidE e)).eval
      σ).toNat = _
    rw [muxFin_eval (by decide : 2 ^ 2 = numGates)]
    rfl
  have hdshort_iff : ((Expr.ult (donE e) (cost32E e)).eval σ = 1#1) ↔
      ¬(instr.cost.cost ≤ a.donated) := by
    rw [ultE_eval, hdon, hC32']
    omega
  by_cases hdshort : (Expr.ult (donE e) (cost32E e)).eval σ = 1#1
  case pos =>
    -- donation fault
    refine square_issue_fault m hwf hfit σ hsync hifv0 e .budget ?_ ?_
    · rw [hsel]
      exact issueFor_run_donFault m σ σ1 e hcov hkn hshort hsv hactv hdshort
    · exact corePhase_donFault m τ1 e hifl hsched W instr hfetch hdec
        (by rw [hpp]; exact hble) g hsg a ha (hdshort_iff.mp hdshort)
  case neg =>
    -- serving issue
    refine square_issue_serve m hwf hfit σ hsync hifv0 e W instr p
      hpdef.symm g hgv a ha hwE hcost hble
      (by have := hdshort_iff.not.mp hdshort; omega) hdon ?_ ?_
    · rw [hsel]
      exact issueFor_run_serve m σ σ1 e hcov hkn hshort hsv hactv hdshort
    · rw [corePhase_serveIssue m τ1 e hifl hsched W instr hfetch hdec
        (by rw [hpp]; exact hble) g hsg a ha
        (by have := hdshort_iff.not.mp hdshort; omega), hpp]

end Machines.Lnp64u.Theorems.RMC
