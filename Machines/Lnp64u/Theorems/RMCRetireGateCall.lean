-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateTransfer

/-!
# R-MC retirement: gate-call semantic bridges

Decode and bounded-depth facts for the `gate_call` retirement arm. These
lemmas connect the muxed hardware view of the selected gate and callee to
the structured specification state before the success-action abstraction.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 3200000
set_option maxRecDepth 200000

/-- The dynamically selected gate's callee expression decodes to the
callee stored in the corresponding abstract gate configuration. -/
theorem callCal_eval_selected (σ : Loom.Hw.St) (d : DomainId) (g : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    finOfBv (by decide : 2 ^ 2 = numDomains) ((Hw.callCal d).eval σ) =
      ((Hw.abs σ).gates g).config.callee := by
  unfold Hw.callCal
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates)]
  rw [hgid]
  rfl

/-- The selected gate's entry register is exactly its abstract entry
address. -/
theorem gateEntry_selected (σ : Loom.Hw.St) (g : GateId) :
    σ.regs (Hw.gentry g) 12 = ((Hw.abs σ).gates g).config.entry := by
  rfl

/-- The hardware null-argument predicate is equivalent to the argument
word being nonzero. -/
theorem argNZ_eval_iff (σ : Loom.Hw.St) (d : DomainId) :
    (Hw.argNZ d).eval σ = 1#1 ↔ (Hw.argW d).eval σ ≠ 0#32 := by
  unfold Hw.argNZ Hw.neqE
  change (~~~(if (Hw.argW d).eval σ = 0#32 then 1#1 else 0#1) = 1#1) ↔ _
  by_cases h : (Hw.argW d).eval σ = 0#32 <;> simp [h]

/-- A non-serving domain produces the hardware/spec call depth `1`. -/
theorem callDepth_eval_not_serving (σ : Loom.Hw.St) (d : DomainId)
    (hserv : ((Hw.abs σ).doms d).serving = none) :
    ((Hw.callDepth d).eval σ).toNat = 1 := by
  have hv : σ.regs (Hw.dsrvV d) 1 ≠ 1#1 := by
    intro hv
    change (if σ.regs (Hw.dsrvV d) 1 = 1#1 then
      some (finOfBv (by decide) (σ.regs (Hw.dsrv d) 2)) else none) = none
      at hserv
    rw [if_pos hv] at hserv
    contradiction
  have hz : σ.regs (Hw.dsrvV d) 1 = 0#1 := bv1_ne_one.mp hv
  unfold Hw.callDepth
  change (if σ.regs (Hw.dsrvV d) 1 &&& _ = 1#1 then _ else 1#3).toNat = 1
  rw [hz]
  simp

/-- For a serving domain, Wf makes the selected activation live and bounds
its depth tightly enough that the three-bit hardware increment cannot wrap.
The computed hardware depth is therefore the specification activation depth
plus one. -/
theorem callDepth_eval_serving (σ : Loom.Hw.St) (d : DomainId) (g : GateId)
    (hwf : Wf (Hw.abs σ))
    (hserv : ((Hw.abs σ).doms d).serving = some g) :
    ((Hw.callDepth d).eval σ).toNat =
      (((Hw.abs σ).gates g).act.getD
        { caller := 0, callerRd := 0, savedRegs := fun _ => 0,
          savedPc := 0, savedServing := none, depth := 0, donated := 0 }).depth
        + 1 := by
  have hsv : σ.regs (Hw.dsrvV d) 1 = 1#1 := by
    change (if σ.regs (Hw.dsrvV d) 1 = 1#1 then
      some (finOfBv (by decide) (σ.regs (Hw.dsrv d) 2)) else none) = some g
      at hserv
    by_cases hv : σ.regs (Hw.dsrvV d) 1 = 1#1
    · exact hv
    · rw [if_neg hv] at hserv
      contradiction
  have hsg : finOfBv (by decide : 2 ^ 2 = numGates)
      (σ.regs (Hw.dsrv d) 2) = g := by
    change (if σ.regs (Hw.dsrvV d) 1 = 1#1 then
      some (finOfBv (by decide) (σ.regs (Hw.dsrv d) 2)) else none) = some g
      at hserv
    rw [if_pos hsv] at hserv
    exact Option.some.inj hserv
  have hisSome : ((Hw.abs σ).gates g).act.isSome :=
    (hwf.serving_gate d g hserv).2
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hisSome
  have hgv : σ.regs (Hw.gactV g) 1 = 1#1 := by
    change (if σ.regs (Hw.gactV g) 1 = 1#1 then some _ else none) = some a
      at ha
    by_cases hv : σ.regs (Hw.gactV g) 1 = 1#1
    · exact hv
    · rw [if_neg hv] at ha
      contradiction
  have hdepth : (σ.regs (Hw.gdepth g) 3).toNat = a.depth := by
    change (if σ.regs (Hw.gactV g) 1 = 1#1 then some _ else none) = some a
      at ha
    rw [if_pos hgv] at ha
    exact congrArg Activation.depth (Option.some.inj ha)
  have hle : a.depth ≤ maxChainDepth :=
    (hwf.gate_serving g a ha).2.2.2
  have hnowrap : (σ.regs (Hw.gdepth g) 3).toNat + 1 < 2 ^ 3 := by
    rw [hdepth]
    change a.depth + 1 < 8
    change a.depth ≤ 4 at hle
    omega
  simp only [Hw.callDepth, Expr.eval]
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates),
    muxFin_eval (by decide : 2 ^ 2 = numGates)]
  change (if σ.regs (Hw.dsrvV d) 1 &&&
      σ.regs (Hw.gactV (finOfBv (by decide) (σ.regs (Hw.dsrv d) 2))) 1 = 1#1
    then σ.regs (Hw.gdepth
      (finOfBv (by decide) (σ.regs (Hw.dsrv d) 2))) 3 + 1#3 else 1#3).toNat = _
  rw [hsg]
  rw [hsv, hgv, if_pos (show 1#1 &&& 1#1 = 1#1 by decide),
    BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hnowrap, hdepth]
  rw [ha]
  rfl

/-- Unified hardware/spec depth bridge. -/
theorem callDepth_eval (σ : Loom.Hw.St) (c : Ctx)
    (hwf : Wf (Hw.abs σ)) :
    ((Hw.callDepth c.d).eval σ).toNat =
      Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) := by
  unfold Machines.Lnp64u.Isa.Wip.gateDepth
  cases hserv : ((Hw.abs σ).doms c.d).serving with
  | none => exact callDepth_eval_not_serving σ c.d hserv
  | some g =>
      rw [callDepth_eval_serving σ c.d g hwf hserv]
      have hisSome := (hwf.serving_gate c.d g hserv).2
      cases hact : ((Hw.abs σ).gates g).act with
      | none => simp [hact] at hisSome
      | some a => simp [hact]

end Machines.Lnp64u.Theorems.RMC
