-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateCall

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

end Machines.Lnp64u.Theorems.RMC
