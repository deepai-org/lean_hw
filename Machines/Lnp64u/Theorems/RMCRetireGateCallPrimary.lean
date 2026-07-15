-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCall
import Machines.Lnp64u.Theorems.RMCRetireGateTransferOutcomes

/-!
# R-MC gate-call primary selector context

Proof-only packaging for the exact gate capability selected after the first
two `gate_call` checks pass.  Keeping this bridge separate gives the branch
assembler a small incremental build target.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

/-- Semantic payload exposed once the first two gate-call checks pass. -/
def CallPrimary (σ : Loom.Hw.St) (τ : MachineState)
    (d : DomainId) (c : Ctx) : Prop :=
  ∃ slot : Slot, ∃ gen : Gen, ∃ entry : CapEntry, ∃ gate : GateId,
    Machines.Lnp64u.Isa.capLive c.d
        ((τ.doms c.d).reg c.op.rs1) τ = .ok (slot, gen, entry) τ ∧
      entry.kind = .gate gate ∧
      finOfBv (by decide : 2 ^ 2 = numGates)
        ((Hw.callGid d).eval σ) = gate

/-- Construct the shared primary-gate context directly from passing hardware
selector checks and the exact post-PC-advance specification view. -/
theorem callPrimary_of_pass (σ : Loom.Hw.St) (τ : MachineState)
    (d : DomainId) (c : Ctx)
    (hcd : c.d = d)
    (hword : (τ.doms c.d).reg c.op.rs1 =
      (Hw.readReg d Hw.rs1E).eval σ)
    (hbridge : ∀ (S : Slot) (G : Gen),
      (τ.doms d).liveCap S G = ((Hw.abs σ).doms d).liveCap S G)
    (hkc : KindCanon σ)
    (hlive : (Hw.callSel d).live.eval σ = 1#1)
    (hprimary : (Expr.not (Expr.and (Hw.callSel d).clsOk
      (Expr.not (Hw.kIsMem (Hw.callSel d).kindW)))).eval σ ≠ 1#1) :
    CallPrimary σ τ d c := by
  obtain ⟨e, hliveτ, hcap⟩ := capSel_entry_of_live σ τ d
    (Hw.readReg d Hw.rs1E) hbridge hlive
  let S := (Handle.decode ((Hw.readReg d Hw.rs1E).eval σ)).slot
  let G := (Handle.decode ((Hw.readReg d Hw.rs1E).eval σ)).gen
  have hslot : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.readReg d Hw.rs1E).eval σ).extractLsb' 0 4)).val =
      (((Hw.readReg d Hw.rs1E).eval σ).extractLsb' 0 4).toNat := rfl
  have hclsIff := capSel_clsOk_iff_some σ d (Hw.readReg d Hw.rs1E)
    (finOfBv (by decide)
      (((Hw.readReg d Hw.rs1E).eval σ).extractLsb' 0 4)) e
    hkc hslot hcap
  have hmemIff := capSel_isMem_iff_some σ d (Hw.readReg d Hw.rs1E)
    (finOfBv (by decide)
      (((Hw.readReg d Hw.rs1E).eval σ).extractLsb' 0 4)) e
    hkc hslot hcap
  have hlogic : (Hw.callSel d).clsOk.eval σ = 1#1 ∧
      (Hw.kIsMem (Hw.callSel d).kindW).eval σ = 0#1 := by
    apply (by decide : ∀ a b : BitVec 1,
      ~~~(a &&& ~~~b) ≠ 1#1 → a = 1#1 ∧ b = 0#1)
    exact hprimary
  have hcls := hclsIff.mp hlogic.1
  obtain ⟨g, hkind⟩ : ∃ g : GateId, e.kind = .gate g := by
    cases hk : e.kind with
    | mem base len perms =>
        exfalso
        have hm := hmemIff.mpr ⟨base, len, perms, hk⟩
        have hm0 : (Hw.kIsMem
            (Hw.capSel d (Hw.readReg d Hw.rs1E)).kindW).eval σ = 0#1 := by
          simpa [Hw.callSel] using hlogic.2
        rw [hm0] at hm
        contradiction
    | gate g => exact ⟨g, rfl⟩
  have hkw : (Hw.callSel d).kindW.eval σ = Hw.encKind (.gate g) := by
    have hk := capSel_kind_of_some σ d (Hw.readReg d Hw.rs1E)
      (finOfBv (by decide)
        (((Hw.readReg d Hw.rs1E).eval σ).extractLsb' 0 4)) e
      hkc hslot hcap
    simpa [Hw.callSel, hkind] using hk
  have hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g :=
    kGid_encGate_eval σ (Hw.callSel d).kindW g hkw
  have hcapLive : Machines.Lnp64u.Isa.capLive c.d
      ((τ.doms c.d).reg c.op.rs1) τ = .ok (S, G, e) τ := by
    apply capLive_eq_selected
    · rw [hword]
      cases hd : Handle.decode ((Hw.readReg d Hw.rs1E).eval σ) with
      | mk S' G' cls =>
          simp only [S, G, hd] at hcls ⊢
          rw [hcls]
    · simpa [S, G, hcd] using hliveτ
  exact ⟨S, G, e, g, hcapLive, hkind, hgid⟩

/-- Semantic payload after the selected gate is idle and its callee differs
from the caller.  This is the common prefix for run-state, serving-state,
depth, argument-transfer, and successful-call branches. -/
def CallCallee (σ : Loom.Hw.St) (τ : MachineState)
    (d : DomainId) (c : Ctx) : Prop :=
  ∃ slot : Slot, ∃ gen : Gen, ∃ entry : CapEntry, ∃ gate : GateId,
    ∃ callee : DomainId,
      Machines.Lnp64u.Isa.capLive c.d
          ((τ.doms c.d).reg c.op.rs1) τ = .ok (slot, gen, entry) τ ∧
        entry.kind = .gate gate ∧
        (τ.gates gate).act = none ∧
        (τ.gates gate).config.callee = callee ∧
        callee ≠ c.d ∧
        finOfBv (by decide : 2 ^ 2 = numGates)
          ((Hw.callGid d).eval σ) = gate ∧
        finOfBv (by decide : 2 ^ 2 = numDomains)
          ((Hw.callCal d).eval σ) = callee

/-- Extend a passing primary selector with the idle/non-self state checks. -/
theorem callCallee_of_pass (σ : Loom.Hw.St) (τ : MachineState)
    (d : DomainId) (c : Ctx)
    (hcd : c.d = d)
    (hgates : τ.gates = (Hw.abs σ).gates)
    (hprimary : CallPrimary σ τ d c)
    (hidle : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
      (Hw.callGid d)).eval σ ≠ 1#1)
    (hself : (Expr.eq (Hw.callCal d) (Hw.dLit d)).eval σ ≠ 1#1) :
    CallCallee σ τ d c := by
  obtain ⟨S, G, e, g, hlive, hkind, hgid⟩ := hprimary
  have hactAbs : ((Hw.abs σ).gates g).act = none := by
    cases ha : ((Hw.abs σ).gates g).act with
    | none => rfl
    | some a =>
        exfalso
        apply hidle
        apply (callGateActive_eval σ d g hgid).mpr
        simp [ha]
  have hact : (τ.gates g).act = none := by
    rw [hgates]
    exact hactAbs
  let cal : DomainId := ((Hw.abs σ).gates g).config.callee
  have hcalSel : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal :=
    callCal_eval_selected σ d g hgid
  have hneD : cal ≠ d := by
    intro heq
    apply hself
    apply (callSameCallee_eval σ d cal hcalSel).mpr
    exact heq
  have hne : cal ≠ c.d := by simpa [hcd] using hneD
  have hcal : (τ.gates g).config.callee = cal := by
    rw [hgates]
  exact ⟨S, G, e, g, cal, hlive, hkind, hact, hcal, hne,
    hgid, hcalSel⟩

/-- Semantic payload after all five gate/callee/depth checks pass. -/
def CallReady (σ : Loom.Hw.St) (τ : MachineState)
    (d : DomainId) (c : Ctx) : Prop :=
  ∃ slot : Slot, ∃ gen : Gen, ∃ entry : CapEntry, ∃ gate : GateId,
    ∃ callee : DomainId,
      Machines.Lnp64u.Isa.capLive c.d
          ((τ.doms c.d).reg c.op.rs1) τ = .ok (slot, gen, entry) τ ∧
        entry.kind = .gate gate ∧
        (τ.gates gate).act = none ∧
        (τ.gates gate).config.callee = callee ∧
        callee ≠ c.d ∧
        (τ.doms callee).run = .running ∧
        (τ.doms callee).serving = none ∧
        Machines.Lnp64u.Isa.Wip.gateDepth c τ ≤ maxChainDepth ∧
        finOfBv (by decide : 2 ^ 2 = numGates)
          ((Hw.callGid d).eval σ) = gate ∧
        finOfBv (by decide : 2 ^ 2 = numDomains)
          ((Hw.callCal d).eval σ) = callee

/-- Extend the idle/non-self context through the running, non-serving, and
bounded-depth checks.  State-view bridges are explicit so this lemma is
reusable after either gate operation's PC-only retirement prefix. -/
theorem callReady_of_pass (σ : Loom.Hw.St) (τ : MachineState)
    (d : DomainId) (c : Ctx)
    (hcd : c.d = d)
    (hwf : Wf (Hw.abs σ))
    (hrc : ∀ x : DomainId, σ.regs (Hw.drun x) 2 ≠ 3#2)
    (hrunBridge : ∀ x : DomainId,
      (τ.doms x).run = ((Hw.abs σ).doms x).run)
    (hservBridge : ∀ x : DomainId,
      (τ.doms x).serving = ((Hw.abs σ).doms x).serving)
    (hgates : τ.gates = (Hw.abs σ).gates)
    (hcallee : CallCallee σ τ d c)
    (hrunning : (Hw.neqE
      (Hw.muxFin (fun x => .reg 2 (Hw.drun x)) (Hw.callCal d))
      (.lit 0)).eval σ ≠ 1#1)
    (hnotServing : (Hw.muxFin (fun x => .reg 1 (Hw.dsrvV x))
      (Hw.callCal d)).eval σ ≠ 1#1)
    (hdepthPass : (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth d)).eval σ ≠ 1#1) :
    CallReady σ τ d c := by
  obtain ⟨S, G, e, g, cal, hlive, hkind, hact, hcal, hne,
      hgid, hcalSel⟩ := hcallee
  have hrunAbs : ((Hw.abs σ).doms cal).run = .running := by
    by_contra hn
    exact hrunning ((callCalleeNotRunning_eval σ d cal (hrc cal)
      hcalSel).mpr hn)
  have hrun : (τ.doms cal).run = .running :=
    (hrunBridge cal).trans hrunAbs
  have hservAbs : ((Hw.abs σ).doms cal).serving = none := by
    cases hs : ((Hw.abs σ).doms cal).serving with
    | none => rfl
    | some served =>
        exfalso
        apply hnotServing
        apply (callCalleeServing_eval σ d cal hcalSel).mpr
        simp [hs]
  have hserv : (τ.doms cal).serving = none :=
    (hservBridge cal).trans hservAbs
  have hdepthAbs : Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) ≤
      maxChainDepth := by
    by_contra hn
    apply hdepthPass
    have hover := (callDepthOverflow_eval σ c hwf).mpr hn
    simpa [hcd] using hover
  have hdepthEq : Machines.Lnp64u.Isa.Wip.gateDepth c τ =
      Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) := by
    unfold Machines.Lnp64u.Isa.Wip.gateDepth
    rw [hservBridge c.d, hgates]
  have hdepth : Machines.Lnp64u.Isa.Wip.gateDepth c τ ≤
      maxChainDepth := by
    rw [hdepthEq]
    exact hdepthAbs
  exact ⟨S, G, e, g, cal, hlive, hkind, hact, hcal, hne, hrun,
    hserv, hdepth, hgid, hcalSel⟩

end Machines.Lnp64u.Theorems.RMC
