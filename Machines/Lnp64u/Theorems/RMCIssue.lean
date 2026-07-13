-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCHalt
import Machines.Lnp64u.Theorems.RMCSched

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

end Machines.Lnp64u.Theorems.RMC
