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

/-- The selected gate-active check is exactly abstract activation presence. -/
theorem callGateActive_eval (σ : Loom.Hw.St) (d : DomainId) (g : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    (Hw.muxFin (fun h => .reg 1 (Hw.gactV h))
      (Hw.callGid d)).eval σ = 1#1 ↔
      ((Hw.abs σ).gates g).act.isSome := by
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
  change σ.regs (Hw.gactV g) 1 = 1#1 ↔
    (if σ.regs (Hw.gactV g) 1 = 1#1 then some _ else none).isSome
  by_cases hv : σ.regs (Hw.gactV g) 1 = 1#1 <;> simp [hv]

/-- The selected callee-serving check is exactly abstract serving presence. -/
theorem callCalleeServing_eval (σ : Loom.Hw.St) (d cal : DomainId)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal) :
    (Hw.muxFin (fun c => .reg 1 (Hw.dsrvV c))
      (Hw.callCal d)).eval σ = 1#1 ↔
      ((Hw.abs σ).doms cal).serving.isSome := by
  rw [muxFin_eval (by decide : 2 ^ 2 = numDomains), hcal]
  change σ.regs (Hw.dsrvV cal) 1 = 1#1 ↔
    (if σ.regs (Hw.dsrvV cal) 1 = 1#1 then some _ else none).isSome
  by_cases hv : σ.regs (Hw.dsrvV cal) 1 = 1#1 <;> simp [hv]

/-- The self-call check fires exactly when the selected callee is the caller. -/
theorem callSameCallee_eval (σ : Loom.Hw.St) (d cal : DomainId)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal) :
    (Expr.eq (Hw.callCal d) (Hw.dLit d)).eval σ = 1#1 ↔ cal = d := by
  rw [eqE_eval, bv2_lit_iff]
  exact ⟨fun h => h.symm.trans hcal, fun h => h ▸ hcal.symm⟩

/-- Under the canonical run-state invariant, the selected callee's raw
nonzero check is exactly failure to be abstractly running. -/
theorem callCalleeNotRunning_eval (σ : Loom.Hw.St) (d cal : DomainId)
    (hrc : σ.regs (Hw.drun cal) 2 ≠ 3#2)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal) :
    (Hw.neqE (Hw.muxFin (fun c => .reg 2 (Hw.drun c)) (Hw.callCal d))
      (.lit 0)).eval σ = 1#1 ↔
      ((Hw.abs σ).doms cal).run ≠ .running := by
  rw [neqE_eval, muxFin_eval (by decide : 2 ^ 2 = numDomains), hcal]
  change σ.regs (Hw.drun cal) 2 ≠ 0#2 ↔
    Hw.decRun (σ.regs (Hw.drun cal) 2) (σ.regs (Hw.drunG cal) 2) ≠ .running
  rcases (show σ.regs (Hw.drun cal) 2 = 0#2 ∨
      σ.regs (Hw.drun cal) 2 = 1#2 ∨ σ.regs (Hw.drun cal) 2 = 2#2 ∨
      σ.regs (Hw.drun cal) 2 = 3#2 by omega) with h | h | h | h
  · simp [h, Hw.decRun]
  · simp [h, Hw.decRun]
  · simp [h, Hw.decRun]
  · exact absurd h hrc

/-- The hardware chain-overflow check is the negation of the specification's
bounded-depth requirement. -/
theorem callDepthOverflow_eval (σ : Loom.Hw.St) (c : Ctx)
    (hwf : Wf (Hw.abs σ)) :
    (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
      (Hw.callDepth c.d)).eval σ = 1#1 ↔
      ¬Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) ≤ maxChainDepth := by
  rw [ultE_eval, callDepth_eval σ c hwf]
  change maxChainDepth < Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) ↔ _
  omega

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

/-- The five gate/callee/depth predicates all pass under the corresponding
abstract successful-call preconditions. -/
theorem callStateChecks_pass (σ : Loom.Hw.St) (c : Ctx)
    (g : GateId) (cal : DomainId)
    (hwf : Wf (Hw.abs σ))
    (hrc : σ.regs (Hw.drun cal) 2 ≠ 3#2)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid c.d).eval σ) = g)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal c.d).eval σ) = cal)
    (hgate : ((Hw.abs σ).gates g).act = none)
    (hne : cal ≠ c.d)
    (hrun : ((Hw.abs σ).doms cal).run = .running)
    (hserv : ((Hw.abs σ).doms cal).serving = none)
    (hdepth : Machines.Lnp64u.Isa.Wip.gateDepth c (Hw.abs σ) ≤
      maxChainDepth) :
    (Hw.muxFin (fun h => .reg 1 (Hw.gactV h))
        (Hw.callGid c.d)).eval σ ≠ 1#1 ∧
    (Expr.eq (Hw.callCal c.d) (Hw.dLit c.d)).eval σ ≠ 1#1 ∧
    (Hw.neqE (Hw.muxFin (fun x => .reg 2 (Hw.drun x))
        (Hw.callCal c.d)) (.lit 0)).eval σ ≠ 1#1 ∧
    (Hw.muxFin (fun x => .reg 1 (Hw.dsrvV x))
        (Hw.callCal c.d)).eval σ ≠ 1#1 ∧
    (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
        (Hw.callDepth c.d)).eval σ ≠ 1#1 := by
  constructor
  · intro h
    have := (callGateActive_eval σ c.d g hgid).mp h
    simp [hgate] at this
  constructor
  · exact fun h => hne ((callSameCallee_eval σ c.d cal hcal).mp h)
  constructor
  · exact fun h => (callCalleeNotRunning_eval σ c.d cal hrc hcal).mp h hrun
  constructor
  · intro h
    have := (callCalleeServing_eval σ c.d cal hcal).mp h
    simp [hserv] at this
  · exact fun h => (callDepthOverflow_eval σ c hwf).mp h hdepth

/-- A live, class-matching gate capability discharges the first two call
checks and yields the selected gate identifier. -/
theorem callSelector_pass (σ : Loom.Hw.St) (d : DomainId)
    (S : Slot) (e : CapEntry) (g : GateId)
    (hkc : KindCanon σ)
    (hslot : S.val = ((Hw.readReg d Hw.rs1E).eval σ).extractLsb' 0 4 |>.toNat)
    (hlive : (Hw.abs σ).liveRef
      ⟨d, S, ((Hw.readReg d Hw.rs1E).eval σ).extractLsb' 4 8⟩ = true)
    (hcap : ((Hw.abs σ).doms d).caps S = some e)
    (hcls : (Handle.decode ((Hw.readReg d Hw.rs1E).eval σ)).cls = e.kind.cls)
    (hkind : e.kind = .gate g) :
    (Expr.not (Hw.callSel d).live).eval σ ≠ 1#1 ∧
    (Expr.not (.and (Hw.callSel d).clsOk
      (.not (Hw.kIsMem (Hw.callSel d).kindW))).eval σ ≠ 1#1 ∧
    finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g := by
  have hliveE : (Hw.callSel d).live.eval σ = 1#1 := by
    exact capSel_live_of_liveRef σ d (Hw.readReg d Hw.rs1E) S hslot hlive
  have hclsE : (Hw.callSel d).clsOk.eval σ = 1#1 := by
    exact capSel_clsOk_of_some σ d (Hw.readReg d Hw.rs1E) S e hkc hslot hcap hcls
  have hkw : (Hw.callSel d).kindW.eval σ = Hw.encKind (.gate g) := by
    rw [capSel_kind_of_some σ d (Hw.readReg d Hw.rs1E) S e hkc hslot hcap,
      hkind]
  have hmem : (Hw.kIsMem (Hw.callSel d).kindW).eval σ = 0#1 := by
    rw [show (Hw.kIsMem (Hw.callSel d).kindW).eval σ =
      if ((Hw.callSel d).kindW.eval σ).extractLsb' 0 1 = 0#1 then 1#1
      else 0#1 from rfl, hkw]
    fin_cases g <;> decide
  constructor
  · show ¬(~~~((Hw.callSel d).live.eval σ) = 1#1)
    rw [hliveE]
    decide
  constructor
  · show ¬(~~~((Hw.callSel d).clsOk.eval σ &&&
      ~~~((Hw.kIsMem (Hw.callSel d).kindW).eval σ)) = 1#1)
    rw [hclsE, hmem]
    decide
  · exact kGid_encGate_eval σ (Hw.callSel d).kindW g hkw

/-- A null argument vacuously passes all three transfer-related checks. -/
theorem callArgumentChecks_zero (σ : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argW d).eval σ = 0#32) :
    (Expr.and (Hw.argNZ d) (.not (Hw.argSel d).live)).eval σ ≠ 1#1 ∧
    (Expr.and (Hw.argNZ d) (.not (Hw.argSel d).clsOk)).eval σ ≠ 1#1 ∧
    (Expr.and (Hw.argNZ d)
      (Hw.transferBlocked d (Hw.callCal d) (Hw.argSel d))).eval σ ≠ 1#1 := by
  have hnz : (Hw.argNZ d).eval σ = 0#1 := by
    apply bv1_ne_one.mp
    intro h
    exact (argNZ_eval_iff σ d).mp h hz
  simp only [Expr.eval, hnz]
  decide

/-- A non-null live, class-matching argument discharges the liveness and
class checks and exposes its canonical kind word. -/
theorem callArgumentSelector_pass (σ : Loom.Hw.St) (d : DomainId)
    (S : Slot) (e : CapEntry) (hkc : KindCanon σ)
    (hnz : (Hw.argW d).eval σ ≠ 0#32)
    (hslot : S.val = ((Hw.argW d).eval σ).extractLsb' 0 4 |>.toNat)
    (hlive : (Hw.abs σ).liveRef
      ⟨d, S, ((Hw.argW d).eval σ).extractLsb' 4 8⟩ = true)
    (hcap : ((Hw.abs σ).doms d).caps S = some e)
    (hcls : (Handle.decode ((Hw.argW d).eval σ)).cls = e.kind.cls) :
    (Expr.and (Hw.argNZ d) (.not (Hw.argSel d).live)).eval σ ≠ 1#1 ∧
    (Expr.and (Hw.argNZ d) (.not (Hw.argSel d).clsOk)).eval σ ≠ 1#1 ∧
    (Hw.argSel d).kindW.eval σ = Hw.encKind e.kind := by
  have hnzE : (Hw.argNZ d).eval σ = 1#1 :=
    (argNZ_eval_iff σ d).mpr hnz
  have hliveE : (Hw.argSel d).live.eval σ = 1#1 :=
    capSel_live_of_liveRef σ d (Hw.argW d) S hslot hlive
  have hclsE : (Hw.argSel d).clsOk.eval σ = 1#1 :=
    capSel_clsOk_of_some σ d (Hw.argW d) S e hkc hslot hcap hcls
  constructor
  · show ¬((Hw.argNZ d).eval σ &&& ~~~((Hw.argSel d).live.eval σ) = 1#1)
    rw [hnzE, hliveE]
    decide
  constructor
  · show ¬((Hw.argNZ d).eval σ &&& ~~~((Hw.argSel d).clsOk.eval σ) = 1#1)
    rw [hnzE, hclsE]
    decide
  · exact capSel_kind_of_some σ d (Hw.argW d) S e hkc hslot hcap

/-- Assemble the ten individual pass facts into the hardware's combined
successful-call predicate. -/
theorem callOkE_of_passes (σ : Loom.Hw.St) (d : DomainId)
    (hsel :
      (Expr.not (Hw.callSel d).live).eval σ ≠ 1#1 ∧
      (Expr.not (.and (Hw.callSel d).clsOk
        (.not (Hw.kIsMem (Hw.callSel d).kindW))).eval σ ≠ 1#1)
    (hstate :
      (Hw.muxFin (fun h => .reg 1 (Hw.gactV h))
          (Hw.callGid d)).eval σ ≠ 1#1 ∧
      (Expr.eq (Hw.callCal d) (Hw.dLit d)).eval σ ≠ 1#1 ∧
      (Hw.neqE (Hw.muxFin (fun x => .reg 2 (Hw.drun x))
          (Hw.callCal d)) (.lit 0)).eval σ ≠ 1#1 ∧
      (Hw.muxFin (fun x => .reg 1 (Hw.dsrvV x))
          (Hw.callCal d)).eval σ ≠ 1#1 ∧
      (Expr.ult (.lit (BitVec.ofNat 3 maxChainDepth))
          (Hw.callDepth d)).eval σ ≠ 1#1)
    (harg :
      (Expr.and (Hw.argNZ d) (.not (Hw.argSel d).live)).eval σ ≠ 1#1 ∧
      (Expr.and (Hw.argNZ d) (.not (Hw.argSel d).clsOk)).eval σ ≠ 1#1 ∧
      (Expr.and (Hw.argNZ d)
        (Hw.transferBlocked d (Hw.callCal d) (Hw.argSel d))).eval σ ≠ 1#1) :
    (Hw.callOkE d).eval σ = 1#1 := by
  apply (okOf_eval_iff σ (Hw.callChecks d)).mpr
  intro c hc
  rcases hsel with ⟨h0, h1⟩
  rcases hstate with ⟨h2, h3, h4, h5, h6⟩
  rcases harg with ⟨h7, h8, h9⟩
  simp only [Hw.callChecks, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

/-! ## Whole-core kill selection -/

/-- With a non-null argument, the call kill predicate is exactly equality
with the caller and the selected argument slot. -/
theorem callKilled_nonzero_eval (σ : Loom.Hw.St) (d : DomainId)
    (hnz : (Hw.argNZ d).eval σ = 1#1) (dm : Expr 2) (sl : Expr 4) :
    (Hw.callKilled d dm sl).eval σ =
      (Expr.and (.eq dm (Hw.dLit d))
        (.eq sl (Hw.argSel d).slot)).eval σ := by
  unfold Hw.callKilled Hw.andAll
  change (Hw.argNZ d).eval σ &&&
      ((Expr.eq dm (Hw.dLit d)).eval σ &&&
        (Expr.eq sl (Hw.argSel d).slot).eval σ) = _
  rw [hnz]
  decide

/-- A null argument gives the successful call an empty kill footprint. -/
theorem callKilled_zero_eval (σ : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argNZ d).eval σ = 0#1) (dm : Expr 2) (sl : Expr 4) :
    (Hw.callKilled d dm sl).eval σ = 0#1 := by
  unfold Hw.callKilled Hw.andAll
  change (Hw.argNZ d).eval σ &&& _ = 0#1
  rw [hz]
  decide

/-- On a successful retiring `gate_call`, the global core kill tree selects
exactly that call's optional-transfer predicate. -/
theorem killedByCoreE_call_eval (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ = 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1)
    (hok : ∀ d : DomainId, d = E → (Hw.callOkE d).eval σ = 1#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = (Hw.callKilled E dm sl).eval σ := by
  have hdrop0 : (Hw.isMn "cap_drop").eval σ = 0#1 := bv1_ne_one.mp hdrop
  have hrev0 : (Hw.isMn "cap_revoke").eval σ = 0#1 := bv1_ne_one.mp hrev
  have hreturn0 : (Hw.isMn "gate_return").eval σ = 0#1 :=
    bv1_ne_one.mp hreturn
  have honeAnd : ∀ x : BitVec 1, 1#1 &&& x = x := by decide
  have hzeroAnd : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
  have hzeroOr : ∀ x : BitVec 1, 0#1 ||| x = x := by decide
  have horZero : ∀ x : BitVec 1, x ||| 0#1 = x := by decide
  unfold Hw.killedByCoreE
  fin_cases E <;>
    simp [Hw.orAll, List.finRange, Expr.eval, Fin.ext_iff, hret, hif,
      hdrop0, hrev0, hcall, hok, hreturn0, honeAnd, hzeroAnd, hzeroOr,
      horZero] <;>
    congr 2

/-- A failed call has no kill footprint; `callOkE` gates the optional
transfer out of the Mover rule as well as out of the retirement action. -/
theorem killedByCoreE_call_failed (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ = 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1)
    (hbad : ∀ d : DomainId, d = E → (Hw.callOkE d).eval σ = 0#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = 0#1 := by
  have hdrop0 : (Hw.isMn "cap_drop").eval σ = 0#1 := bv1_ne_one.mp hdrop
  have hrev0 : (Hw.isMn "cap_revoke").eval σ = 0#1 := bv1_ne_one.mp hrev
  have hreturn0 : (Hw.isMn "gate_return").eval σ = 0#1 :=
    bv1_ne_one.mp hreturn
  have honeAnd : ∀ x : BitVec 1, 1#1 &&& x = x := by decide
  have hzeroAnd : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
  have hzeroOr : ∀ x : BitVec 1, 0#1 ||| x = x := by decide
  have horZero : ∀ x : BitVec 1, x ||| 0#1 = x := by decide
  unfold Hw.killedByCoreE
  fin_cases E <;>
    simp [Hw.orAll, List.finRange, Expr.eval, Fin.ext_iff, hret, hif,
      hdrop0, hrev0, hcall, hbad, hreturn0, honeAnd, hzeroAnd, hzeroOr,
      horZero]

/-- Failed calls are Mover-inert once the unrelated job-install gate is
known off. -/
theorem Inert.of_failed_call (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdrop : (Hw.isMn "cap_drop").eval σ ≠ 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ = 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1)
    (hbad : ∀ d : DomainId, d = E → (Hw.callOkE d).eval σ = 0#1)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1) : Inert σ where
  killed := killedByCoreE_call_failed σ E hret hif hdrop hrev hcall
    hreturn hbad
  newJob := hnew

/-- Successful non-null call specialization of the shared one-source-slot
Mover-state bridge. -/
theorem absMover_moverAct_call (σ acc : Loom.Hw.St) (τ : MachineState)
    (E : DomainId) (S : Slot)
    (hslot : (Hw.argSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.argNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.callKilled E dm sl).eval σ)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hkind : ∀ d s g, ¬(d = E ∧ s = S) →
      Option.map CapEntry.kind ((τ.doms d).liveCap s g) =
        Option.map CapEntry.kind (((Hw.abs σ).doms d).liveCap s g))
    (hjob : τ.mover =
      match Hw.absMover σ with
      | none => none
      | some job =>
          if (job.src.dom = E ∧ job.src.slot = S) ∨
              (job.dst.dom = E ∧ job.dst.slot = S)
          then none else some job) :
    Hw.absMover (Hw.moverAct.run σ acc) = (moverPhase τ).mover := by
  apply absMover_moverAct_transfer σ acc τ E (Hw.argSel E).slot S hslot
  · intro dm sl
    rw [hkills]
    exact callKilled_nonzero_eval σ E hnz dm sl
  · exact hnew
  · exact hkind
  · exact hjob

/-- Successful non-null call specialization of the shared one-source-slot
Mover memory bridge. -/
theorem moverAct_mem_call (σ acc : Loom.Hw.St) (τ : MachineState)
    (E : DomainId) (S : Slot)
    (hslot : (Hw.argSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.argNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.callKilled E dm sl).eval σ)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hkind : ∀ d s g, ¬(d = E ∧ s = S) →
      Option.map CapEntry.kind ((τ.doms d).liveCap s g) =
        Option.map CapEntry.kind (((Hw.abs σ).doms d).liveCap s g))
    (hjob : τ.mover =
      match Hw.absMover σ with
      | none => none
      | some job =>
          if (job.src.dom = E ∧ job.src.slot = S) ∨
              (job.dst.dom = E ∧ job.dst.slot = S)
          then none else some job)
    (hauthτ : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
              Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true)
    (hmemτ : ∀ b : Addr, acc.mems "mem" b.toNat 32 = τ.mem b)
    (hswτ : ∀ job, Hw.absMover σ = some job →
      ¬((job.src.dom = E ∧ job.src.slot = S) ∨
        (job.dst.dom = E ∧ job.dst.slot = S)) →
      ∀ sc : Expr 12, Expr.eval σ
        (((List.finRange numDomains).foldr
          (fun d acc' =>
            Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                Hw.domCoversE d
                  (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                  ⟨false, true, false⟩,
                .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
              (Hw.readReg d Hw.rs2E) acc')
          (.memRead 32 "mem" sc))) = τ.mem (sc.eval σ))
    (a : Addr) :
    (Hw.moverAct.run σ acc).mems "mem" a.toNat 32 =
      (moverPhase τ).mem a := by
  apply moverAct_mem_transfer σ acc τ E (Hw.argSel E).slot S hslot
  · intro dm sl
    rw [hkills]
    exact callKilled_nonzero_eval σ E hnz dm sl
  · exact hnew
  · exact hkind
  · exact hjob
  · exact hauthτ
  · exact hmemτ
  · exact hswτ
  · exact a

/-- The status-authority tree for a successful non-null call decodes against
the post-transfer swept region table. -/
theorem sAuth_call_eval (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (τ : MachineState)
    (hslot : (Hw.argSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hnz : (Hw.argNZ E).eval σ = 1#1)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.callKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hregions : ∀ c : DomainId,
      (τ.doms c).regions = ((Hw.abs σ).doms c).regions)
    (hlive : ∀ ref : CapRef, τ.liveRef ref =
      if ref.dom = E ∧ ref.slot = S then false
      else (Hw.abs σ).liveRef ref)
    (hwf : Wf (Hw.abs σ)) (ow : Expr 2) (sa : Expr 12) :
    ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
      τ.sweepRegions.domCovers (finOfBv (by decide) (ow.eval σ))
        (sa.eval σ) ⟨false, true, false⟩ = true := by
  apply sAuth_transfer_eval σ E (Hw.argSel E).slot S τ hslot
  · intro dm sl
    rw [hkills]
    exact callKilled_nonzero_eval σ E hnz dm sl
  · exact hmapz
  · exact hunmapz
  · exact hregions
  · exact hlive
  · exact hwf

/-! ## Activation-record writer -/

/-- The gate-indexed activation-record fold from the successful call arm. -/
def callActivateA (d : DomainId) : Act :=
  Hw.seqAll ((List.finRange numGates).map fun g =>
    .ite (.eq (Hw.callGid d) (Hw.gLit g)) (Hw.seqAll <|
      [ .write 1 (Hw.gactV g) (.lit 1),
        .write 2 (Hw.gcaller g) (Hw.dLit d),
        .write 3 (Hw.gcallerRd g) Hw.rdE ]
      ++ ((List.finRange numRegs).map fun r =>
          .write 32 (Hw.gsreg g r)
            (Hw.muxFin (fun c => .reg 32 (Hw.dreg c r)) (Hw.callCal d)))
      ++ [ .write 12 (Hw.gspc g)
            (Hw.muxFin (fun c => .reg 12 (Hw.dpc c)) (Hw.callCal d)),
           .write 1 (Hw.gssrvV g)
            (Hw.muxFin (fun c => .reg 1 (Hw.dsrvV c)) (Hw.callCal d)),
           .write 2 (Hw.gssrv g)
            (Hw.muxFin (fun c => .reg 2 (Hw.dsrv c)) (Hw.callCal d)),
           .write 3 (Hw.gdepth g) (Hw.callDepth d),
           .write 32 (Hw.gdon g) (.reg 32 (Hw.dmaxdon d)) ]) .skip)

/-- The concrete activation writer after selecting gate `g`. -/
def callActivateChosenA (d : DomainId) (g : GateId) : Act :=
  Hw.seqAll <|
    [ .write 1 (Hw.gactV g) (.lit 1),
      .write 2 (Hw.gcaller g) (Hw.dLit d),
      .write 3 (Hw.gcallerRd g) Hw.rdE ]
    ++ ((List.finRange numRegs).map fun r =>
        .write 32 (Hw.gsreg g r)
          (Hw.muxFin (fun c => .reg 32 (Hw.dreg c r)) (Hw.callCal d)))
    ++ [ .write 12 (Hw.gspc g)
          (Hw.muxFin (fun c => .reg 12 (Hw.dpc c)) (Hw.callCal d)),
         .write 1 (Hw.gssrvV g)
          (Hw.muxFin (fun c => .reg 1 (Hw.dsrvV c)) (Hw.callCal d)),
         .write 2 (Hw.gssrv g)
          (Hw.muxFin (fun c => .reg 2 (Hw.dsrv c)) (Hw.callCal d)),
         .write 3 (Hw.gdepth g) (Hw.callDepth d),
         .write 32 (Hw.gdon g) (.reg 32 (Hw.dmaxdon d)) ]

/-- The activation-record fold selects exactly the decoded gate id. -/
theorem callActivateA_run_selected (σ acc : Loom.Hw.St) (d : DomainId)
    (g : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    (callActivateA d).run σ acc = (callActivateChosenA d g).run σ acc := by
  have hsel : (Expr.eq (Hw.callGid d) (Hw.gLit g)).eval σ = 1#1 :=
    by rw [eqE_eval]; exact (bv2_lit_iff _ g).mpr hgid
  have hexcl : ∀ j : GateId, j ≠ g →
      (Expr.eq (Hw.callGid d) (Hw.gLit j)).eval σ ≠ 1#1 := by
    intro j hne hj
    rw [eqE_eval] at hj
    exact hne ((bv2_lit_iff _ j).mp hj |>.symm.trans hgid)
  exact seqAll_ite_run_unique σ acc
    (fun j : GateId => Expr.eq (Hw.callGid d) (Hw.gLit j))
    (fun j => callActivateChosenA d j) g hsel hexcl
    (List.finRange numGates) (List.mem_finRange g) (List.nodup_finRange _)

private theorem seqAll_write_frame {I : Type} {w qW : Nat}
    (σ acc : Loom.Hw.St) (rn : I → String) (v : I → Expr w)
    (l : List I) (q : String) (hne : ∀ i ∈ l, q ≠ rn i) :
    ((Hw.seqAll (l.map fun i => Act.write w (rn i) (v i))).run σ acc).regs
      q qW = acc.regs q qW := by
  induction l generalizing acc with
  | nil => rfl
  | cons i t ih =>
      change ((Hw.seqAll (t.map fun j => Act.write w (rn j) (v j))).run σ
        ((Act.write w (rn i) (v i)).run σ acc)).regs q qW = _
      rw [ih _ (fun j hj => hne j (List.mem_cons_of_mem i hj))]
      simp only [Act.run, RegEnv.set]
      rw [if_neg (hne i (List.mem_cons_self ..))]

private theorem seqAll_write_at {I : Type} {w : Nat}
    (σ acc : Loom.Hw.St) (rn : I → String) (v : I → Expr w)
    (l : List I) (i : I) (hi : i ∈ l) (hnd : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, rn a = rn b → a = b) :
    ((Hw.seqAll (l.map fun j => Act.write w (rn j) (v j))).run σ acc).regs
      (rn i) w = (v i).eval σ := by
  induction l generalizing acc with
  | nil => exact absurd hi List.not_mem_nil
  | cons a t ih =>
      have hnd' := List.nodup_cons.mp hnd
      by_cases hai : a = i
      · subst a
        change ((Hw.seqAll (t.map fun j => Act.write w (rn j) (v j))).run σ
          ((Act.write w (rn i) (v i)).run σ acc)).regs (rn i) w = _
        rw [seqAll_write_frame σ _ rn v t (rn i)
          (fun j hj hname => hnd'.1
            ((hinj i (List.mem_cons_self ..) j
              (List.mem_cons_of_mem i hj) hname).symm ▸ hj))]
        simp [Act.run, RegEnv.set]
      · have hit : i ∈ t := (List.mem_cons.mp hi).resolve_left
          (fun h => hai h.symm)
        exact ih _ hit hnd'.2 (fun x hx y hy =>
          hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))

/-- Decoding the chosen activation writer yields exactly the specification
activation record, expressed over the sampled pre-call state. -/
theorem absGate_callActivateChosen_selected (σ acc : Loom.Hw.St)
    (d cal : DomainId) (g : GateId)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal) :
    Hw.absGate ((callActivateChosenA d g).run σ acc) g =
      { Hw.absGate acc g with
        act := some
          { caller := d
            callerRd := finOfBv (by decide) (Hw.rdE.eval σ)
            savedRegs := ((Hw.abs σ).doms cal).regs
            savedPc := ((Hw.abs σ).doms cal).pc
            savedServing := ((Hw.abs σ).doms cal).serving
            depth := ((Hw.callDepth d).eval σ).toNat
            donated := ((Hw.abs σ).doms d).maxDonation } } := by
  have hreg : ∀ r : RegId,
      (Hw.muxFin (fun c => .reg 32 (Hw.dreg c r))
        (Hw.callCal d)).eval σ = σ.regs (Hw.dreg cal r) 32 := by
    intro r
    rw [muxFin_eval (by decide : 2 ^ 2 = numDomains), hcal]
    rfl
  have hpc : (Hw.muxFin (fun c => .reg 12 (Hw.dpc c))
      (Hw.callCal d)).eval σ = σ.regs (Hw.dpc cal) 12 := by
    rw [muxFin_eval (by decide : 2 ^ 2 = numDomains), hcal]
    rfl
  have hsv : (Hw.muxFin (fun c => .reg 1 (Hw.dsrvV c))
      (Hw.callCal d)).eval σ = σ.regs (Hw.dsrvV cal) 1 := by
    rw [muxFin_eval (by decide : 2 ^ 2 = numDomains), hcal]
    rfl
  have hsg : (Hw.muxFin (fun c => .reg 2 (Hw.dsrv c))
      (Hw.callCal d)).eval σ = σ.regs (Hw.dsrv cal) 2 := by
    rw [muxFin_eval (by decide : 2 ^ 2 = numDomains), hcal]
    rfl
  let pre : List Act :=
    [ .write 1 (Hw.gactV g) (.lit 1),
      .write 2 (Hw.gcaller g) (Hw.dLit d),
      .write 3 (Hw.gcallerRd g) Hw.rdE ]
  let saves : List Act := (List.finRange numRegs).map fun r =>
    .write 32 (Hw.gsreg g r)
      (Hw.muxFin (fun c => .reg 32 (Hw.dreg c r)) (Hw.callCal d))
  let tail : List Act :=
    [ .write 12 (Hw.gspc g)
        (Hw.muxFin (fun c => .reg 12 (Hw.dpc c)) (Hw.callCal d)),
      .write 1 (Hw.gssrvV g)
        (Hw.muxFin (fun c => .reg 1 (Hw.dsrvV c)) (Hw.callCal d)),
      .write 2 (Hw.gssrv g)
        (Hw.muxFin (fun c => .reg 2 (Hw.dsrv c)) (Hw.callCal d)),
      .write 3 (Hw.gdepth g) (Hw.callDepth d),
      .write 32 (Hw.gdon g) (.reg 32 (Hw.dmaxdon d)) ]
  let a0 := (Hw.seqAll pre).run σ acc
  let a1 := (Hw.seqAll saves).run σ a0
  have hrun : (callActivateChosenA d g).run σ acc =
      (Hw.seqAll tail).run σ a1 := by
    unfold callActivateChosenA a1 a0 pre saves tail
    rw [seqAll_append_run, seqAll_append_run]
  have hcfg1 : ((callActivateChosenA d g).run σ acc).regs
      (Hw.gcallee g) 2 = acc.regs (Hw.gcallee g) 2 := by
    apply frame
    fin_cases g <;> exact of_decide_eq_true rfl
  have hcfg2 : ((callActivateChosenA d g).run σ acc).regs
      (Hw.gentry g) 12 = acc.regs (Hw.gentry g) 12 := by
    apply frame
    fin_cases g <;> exact of_decide_eq_true rfl
  have hprefix : ∀ q ∈ [(Hw.gactV g, 1), (Hw.gcaller g, 2),
      (Hw.gcallerRd g, 3)],
      ((callActivateChosenA d g).run σ acc).regs q.1 q.2 = a0.regs q.1 q.2 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq <;> subst q
    all_goals
      rw [hrun, frame (by
        unfold tail
        fin_cases g <;> exact of_decide_eq_true rfl) σ a1]
      apply seqAll_write_frame σ a0 (fun r => Hw.gsreg g r)
        (fun r => Hw.muxFin (fun c => .reg 32 (Hw.dreg c r)) (Hw.callCal d))
        (List.finRange numRegs) _
      intro r _
      fin_cases g <;> fin_cases r <;> exact of_decide_eq_true rfl
  have hactV : ((callActivateChosenA d g).run σ acc).regs
      (Hw.gactV g) 1 = 1#1 := by
    rw [hprefix (Hw.gactV g, 1) (by simp)]
    simp [a0, pre, Hw.seqAll, Act.run, RegEnv.set]
    rfl
  have hcaller : finOfBv (by decide)
      (((callActivateChosenA d g).run σ acc).regs (Hw.gcaller g) 2) = d := by
    rw [hprefix (Hw.gcaller g, 2) (by simp)]
    simpa [a0, pre, Hw.seqAll, Act.run, RegEnv.set, Hw.dLit, Expr.eval] using
      finOfBv_dLit d
  have hcallerRd : finOfBv (by decide : 2 ^ 3 = numRegs)
      (((callActivateChosenA d g).run σ acc).regs (Hw.gcallerRd g) 3) =
      finOfBv (by decide : 2 ^ 3 = numRegs) (Hw.rdE.eval σ) := by
    rw [hprefix (Hw.gcallerRd g, 3) (by simp)]
    simp [a0, pre, Hw.seqAll, Act.run, RegEnv.set]
  have hsaves : ∀ r : RegId,
      ((callActivateChosenA d g).run σ acc).regs (Hw.gsreg g r) 32 =
        σ.regs (Hw.dreg cal r) 32 := by
    intro r
    rw [hrun]
    rw [show ((Hw.seqAll tail).run σ a1).regs (Hw.gsreg g r) 32 =
        a1.regs (Hw.gsreg g r) 32 from frame (by
          fin_cases g <;> fin_cases r <;>
            exact of_decide_eq_true rfl) σ a1]
    unfold a1 saves
    rw [seqAll_write_at σ a0 (fun r => Hw.gsreg g r)
      (fun r => Hw.muxFin (fun c => .reg 32 (Hw.dreg c r)) (Hw.callCal d))
      (List.finRange numRegs) r (List.mem_finRange r) (List.nodup_finRange _)
      (by
        intro x _ y _ heq
        fin_cases g <;> fin_cases x <;> fin_cases y <;>
          first | rfl | exact absurd heq (by decide +kernel))]
    exact hreg r
  have hspc : ((callActivateChosenA d g).run σ acc).regs
      (Hw.gspc g) 12 = σ.regs (Hw.dpc cal) 12 := by
    rw [hrun]
    simp [tail, Hw.seqAll, Act.run, RegEnv.set, hpc]
  have hssrvV : ((callActivateChosenA d g).run σ acc).regs
      (Hw.gssrvV g) 1 = σ.regs (Hw.dsrvV cal) 1 := by
    rw [hrun]
    simp [tail, Hw.seqAll, Act.run, RegEnv.set, hsv]
  have hssrv : ((callActivateChosenA d g).run σ acc).regs
      (Hw.gssrv g) 2 = σ.regs (Hw.dsrv cal) 2 := by
    rw [hrun]
    simp [tail, Hw.seqAll, Act.run, RegEnv.set, hsg]
  have hdepth : ((callActivateChosenA d g).run σ acc).regs
      (Hw.gdepth g) 3 = (Hw.callDepth d).eval σ := by
    rw [hrun]
    simp [tail, Hw.seqAll, Act.run, RegEnv.set]
  have hdon : ((callActivateChosenA d g).run σ acc).regs
      (Hw.gdon g) 32 = σ.regs (Hw.dmaxdon d) 32 := by
    rw [hrun]
    simp [tail, Hw.seqAll, Act.run, RegEnv.set]
    rfl
  unfold Hw.absGate
  rw [hcfg1, hcfg2, hactV]
  simp only [if_pos (show (1#1 : BitVec 1) = 1 from rfl)]
  rw [hcaller, hcallerRd, hspc,
    hssrvV, hssrv, hdepth, hdon]
  simp only [hsaves]
  simp [Hw.abs, Hw.absDom]

/-- A chosen activation writer leaves every other abstract gate unchanged. -/
theorem absGate_callActivateChosen_other (σ acc : Loom.Hw.St)
    (d : DomainId) (g h : GateId) (hne : h ≠ g) :
    Hw.absGate ((callActivateChosenA d g).run σ acc) h =
      Hw.absGate acc h := by
  apply absGate_congr
  intro q hq
  apply frame
  have hquiet : ∀ q ∈ gateReadNames h,
      q ∉ (callActivateChosenA d g).regWrites := by
    fin_cases g <;> fin_cases h <;>
      first | exact absurd rfl hne | decide +kernel +revert
  exact hquiet q hq

/-- The gate-indexed activation fold updates exactly its decoded gate. -/
theorem absGate_callActivateA (σ acc : Loom.Hw.St)
    (d cal : DomainId) (g h : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal) :
    Hw.absGate ((callActivateA d).run σ acc) h =
      if h = g then
        { Hw.absGate acc g with
          act := some
            { caller := d
              callerRd := finOfBv (by decide) (Hw.rdE.eval σ)
              savedRegs := ((Hw.abs σ).doms cal).regs
              savedPc := ((Hw.abs σ).doms cal).pc
              savedServing := ((Hw.abs σ).doms cal).serving
              depth := ((Hw.callDepth d).eval σ).toNat
              donated := ((Hw.abs σ).doms d).maxDonation } }
      else Hw.absGate acc h := by
  rw [callActivateA_run_selected σ acc d g hgid]
  by_cases hh : h = g
  · subst h
    rw [if_pos rfl]
    exact absGate_callActivateChosen_selected σ acc d cal g hcal
  · rw [if_neg hh]
    exact absGate_callActivateChosen_other σ acc d g h hh

/-- Gate activation writes do not change any abstract domain. -/
theorem absDom_callActivateA_frame (σ acc : Loom.Hw.St)
    (d : DomainId) (x : DomainId) :
    Hw.absDom ((callActivateA d).run σ acc) x = Hw.absDom acc x := by
  apply absDom_congr
  intro q hq
  apply frame
  have hquiet : ∀ q ∈ domReadNames x, q ∉ (callActivateA d).regWrites := by
    fin_cases x <;> exact of_decide_eq_true rfl
  exact hquiet q hq

/-! ## Callee scrub and entry writer -/

/-- The successful call's argument value as installed in callee register 1. -/
def callArgHandle (d : DomainId) : Expr 32 :=
  .mux (Hw.argNZ d) (Hw.transferHandleAt (Hw.callCal d) (Hw.argSel d)) (.lit 0)

/-- A null call argument installs the null handle. -/
theorem callArgHandle_eval_zero (σ : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.argW d).eval σ = 0#32) :
    (callArgHandle d).eval σ = 0#32 := by
  have hnz : (Hw.argNZ d).eval σ ≠ 1#1 := by
    intro h
    exact (argNZ_eval_iff σ d).mp h hz
  have hzero := bv1_ne_one.mp hnz
  simp only [callArgHandle, Expr.eval]
  rw [hzero, if_neg (by decide)]
  rfl

/-- A non-null call argument installs the recipient-relative handle selected
by the shared transfer machinery. -/
theorem callArgHandle_eval_nonzero (σ : Loom.Hw.St) (d : DomainId)
    (cls : CapClass) (hnz : (Hw.argW d).eval σ ≠ 0#32)
    (hcls : (Hw.field (Hw.argSel d).kindW 0 1).eval σ =
      if cls = .gate then 1#1 else 0#1) :
    (callArgHandle d).eval σ =
      let cal : DomainId := finOfBv (by decide) ((Hw.callCal d).eval σ)
      Handle.encode
        ⟨finOfBv (by decide) ((Hw.freeSlotIdx cal).eval σ),
          (Hw.genOfE cal (Hw.freeSlotIdx cal)).eval σ, cls⟩ := by
  have harg : (Hw.argNZ d).eval σ = 1#1 :=
    (argNZ_eval_iff σ d).mpr hnz
  simp only [callArgHandle, Expr.eval]
  rw [harg, if_pos rfl]
  exact transferHandleAt_eval σ (Hw.callCal d) (Hw.argSel d) cls hcls

/-- The domain-indexed callee scrub and entry fold. -/
def callCalleeA (d : DomainId) : Act :=
  Hw.seqAll ((List.finRange numDomains).map fun c =>
    .ite (.eq (Hw.callCal d) (Hw.dLit c)) (Hw.seqAll <|
      ((List.finRange numRegs).map fun r =>
        .write 32 (Hw.dreg c r)
          (if r.val = 1 then callArgHandle d else .lit 0))
      ++ [ .write 12 (Hw.dpc c)
            (Hw.muxFin (fun g => .reg 12 (Hw.gentry g)) (Hw.callGid d)),
           .write 1 (Hw.dsrvV c) (.lit 1),
           .write 2 (Hw.dsrv c) (Hw.callGid d) ]) .skip)

/-- The concrete scrub and entry writer after selecting callee `cal`. -/
def callCalleeChosenA (d cal : DomainId) : Act :=
  Hw.seqAll <|
    ((List.finRange numRegs).map fun r =>
      .write 32 (Hw.dreg cal r)
        (if r.val = 1 then callArgHandle d else .lit 0))
    ++ [ .write 12 (Hw.dpc cal)
          (Hw.muxFin (fun g => .reg 12 (Hw.gentry g)) (Hw.callGid d)),
         .write 1 (Hw.dsrvV cal) (.lit 1),
         .write 2 (Hw.dsrv cal) (Hw.callGid d) ]

/-- The callee fold selects exactly the decoded callee domain. -/
theorem callCalleeA_run_selected (σ acc : Loom.Hw.St) (d cal : DomainId)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal) :
    (callCalleeA d).run σ acc = (callCalleeChosenA d cal).run σ acc := by
  have hsel : (Expr.eq (Hw.callCal d) (Hw.dLit cal)).eval σ = 1#1 :=
    by rw [eqE_eval]; exact (bv2_lit_iff _ cal).mpr hcal
  have hexcl : ∀ c : DomainId, c ≠ cal →
      (Expr.eq (Hw.callCal d) (Hw.dLit c)).eval σ ≠ 1#1 := by
    intro c hne hc
    rw [eqE_eval] at hc
    exact hne ((bv2_lit_iff _ c).mp hc |>.symm.trans hcal)
  exact seqAll_ite_run_unique σ acc
    (fun c : DomainId => Expr.eq (Hw.callCal d) (Hw.dLit c))
    (fun c => callCalleeChosenA d c) cal hsel hexcl
    (List.finRange numDomains) (List.mem_finRange cal) (List.nodup_finRange _)

/-- The chosen callee writer scrubs the register file, enters the gate, and
marks the domain as serving that gate, preserving all other domain fields. -/
theorem absDom_callCalleeChosen_selected (σ acc : Loom.Hw.St)
    (d cal : DomainId) (g : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    Hw.absDom ((callCalleeChosenA d cal).run σ acc) cal =
      { Hw.absDom acc cal with
        regs := fun r => if r.val = 1 then (callArgHandle d).eval σ else 0
        pc := ((Hw.abs σ).gates g).config.entry
        serving := some g } := by
  let writes : List Act := (List.finRange numRegs).map fun r =>
    .write 32 (Hw.dreg cal r)
      (if r.val = 1 then callArgHandle d else .lit 0)
  let tail : List Act :=
    [ .write 12 (Hw.dpc cal)
        (Hw.muxFin (fun g => .reg 12 (Hw.gentry g)) (Hw.callGid d)),
      .write 1 (Hw.dsrvV cal) (.lit 1),
      .write 2 (Hw.dsrv cal) (Hw.callGid d) ]
  let mid := (Hw.seqAll writes).run σ acc
  have hrun : (callCalleeChosenA d cal).run σ acc =
      (Hw.seqAll tail).run σ mid := by
    unfold callCalleeChosenA mid writes tail
    rw [seqAll_append_run]
  have hframe {rn : String} {w : Nat}
      (hn : (rn, w) ∉ (callCalleeChosenA d cal).regWrites) :
      ((callCalleeChosenA d cal).run σ acc).regs rn w = acc.regs rn w :=
    frame hn σ acc
  have hregs : ∀ r : RegId,
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dreg cal r) 32 =
        (if r.val = 1 then (callArgHandle d).eval σ else 0) := by
    intro r
    rw [hrun]
    rw [show ((Hw.seqAll tail).run σ mid).regs (Hw.dreg cal r) 32 =
        mid.regs (Hw.dreg cal r) 32 from frame (by
          unfold tail
          fin_cases cal <;> fin_cases r <;> exact of_decide_eq_true rfl) σ mid]
    unfold mid writes
    rw [seqAll_write_at σ acc (fun r => Hw.dreg cal r)
      (fun r => if r.val = 1 then callArgHandle d else .lit 0)
      (List.finRange numRegs) r (List.mem_finRange r) (List.nodup_finRange _)
      (by
        intro x _ y _ heq
        fin_cases cal <;> fin_cases x <;> fin_cases y <;>
          first | rfl | exact absurd heq (by decide +kernel))]
    split <;> rfl
  have hpc : ((callCalleeChosenA d cal).run σ acc).regs
      (Hw.dpc cal) 12 = ((Hw.abs σ).gates g).config.entry := by
    rw [hrun]
    simp [tail, Hw.seqAll, Act.run, RegEnv.set]
    rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
    rfl
  have hsrvV : ((callCalleeChosenA d cal).run σ acc).regs
      (Hw.dsrvV cal) 1 = 1#1 := by
    rw [hrun]
    simp [tail, Hw.seqAll, Act.run, RegEnv.set]
    rfl
  have hsrv : finOfBv (by decide : 2 ^ 2 = numGates)
      (((callCalleeChosenA d cal).run σ acc).regs (Hw.dsrv cal) 2) = g := by
    rw [hrun]
    simp [tail, Hw.seqAll, Act.run, RegEnv.set]
    exact hgid
  have hcapV (s : Slot) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dcapV cal s) 1 =
        acc.regs (Hw.dcapV cal s) 1 := hframe (by
    fin_cases cal <;> fin_cases s <;>
      exact of_decide_eq_true rfl)
  have hcapK (s : Slot) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dcapKind cal s) 32 =
        acc.regs (Hw.dcapKind cal s) 32 := hframe (by
    fin_cases cal <;> fin_cases s <;>
      exact of_decide_eq_true rfl)
  have hcapLV (s : Slot) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dcapLinV cal s) 1 =
        acc.regs (Hw.dcapLinV cal s) 1 := hframe (by
    fin_cases cal <;> fin_cases s <;>
      exact of_decide_eq_true rfl)
  have hcapL (s : Slot) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dcapLin cal s) 4 =
        acc.regs (Hw.dcapLin cal s) 4 := hframe (by
    fin_cases cal <;> fin_cases s <;>
      exact of_decide_eq_true rfl)
  have hgen (s : Slot) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dgen cal s) 8 =
        acc.regs (Hw.dgen cal s) 8 := hframe (by
    fin_cases cal <;> fin_cases s <;>
      exact of_decide_eq_true rfl)
  have hcellV (l : LineageId) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dcellV cal l) 1 =
        acc.regs (Hw.dcellV cal l) 1 := hframe (by
    fin_cases cal <;> fin_cases l <;>
      exact of_decide_eq_true rfl)
  have hcellP (l : LineageId) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dcellPar cal l) 14 =
        acc.regs (Hw.dcellPar cal l) 14 := hframe (by
    fin_cases cal <;> fin_cases l <;>
      exact of_decide_eq_true rfl)
  have hrgnV (r : RegionId) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.drgnV cal r) 1 =
        acc.regs (Hw.drgnV cal r) 1 := hframe (by
    fin_cases cal <;> fin_cases r <;>
      exact of_decide_eq_true rfl)
  have hrgn (r : RegionId) :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.drgn cal r) 42 =
        acc.regs (Hw.drgn cal r) 42 := hframe (by
    fin_cases cal <;> fin_cases r <;>
      exact of_decide_eq_true rfl)
  have hrunV :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.drun cal) 2 =
        acc.regs (Hw.drun cal) 2 := hframe (by
    fin_cases cal <;> exact of_decide_eq_true rfl)
  have hrunG :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.drunG cal) 2 =
        acc.regs (Hw.drunG cal) 2 := hframe (by
    fin_cases cal <;> exact of_decide_eq_true rfl)
  have hcause :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dcause cal) 32 =
        acc.regs (Hw.dcause cal) 32 := hframe (by
    fin_cases cal <;> exact of_decide_eq_true rfl)
  have hbudget :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dbudget cal) 32 =
        acc.regs (Hw.dbudget cal) 32 := hframe (by
    fin_cases cal <;> exact of_decide_eq_true rfl)
  have hmaxdon :
      ((callCalleeChosenA d cal).run σ acc).regs (Hw.dmaxdon cal) 32 =
        acc.regs (Hw.dmaxdon cal) 32 := hframe (by
    fin_cases cal <;> exact of_decide_eq_true rfl)
  apply domainState_ext'
  · funext r
    exact hregs r
  · exact hpc
  · funext s
    change (Hw.absDom ((callCalleeChosenA d cal).run σ acc) cal).caps s =
      (Hw.absDom acc cal).caps s
    unfold Hw.absDom
    simp only
    rw [hcapV, hcapK, hcapLV, hcapL]
  · funext s
    change _ = acc.regs (Hw.dgen cal s) 8
    exact hgen s
  · funext l
    change (if _ = 1#1 then some _ else none) = _
    rw [hcellV, hcellP]
    rfl
  · funext r
    change (if _ = 1#1 then some _ else none) = _
    rw [hrgnV, hrgn]
    rfl
  · change Hw.decRun _ _ = Hw.decRun (acc.regs (Hw.drun cal) 2)
      (acc.regs (Hw.drunG cal) 2)
    rw [hrunV, hrunG]
  · change (if _ = 1#1 then some _ else none) = some g
    rw [hsrvV, if_pos rfl, hsrv]
  · change _ = acc.regs (Hw.dcause cal) 32
    exact hcause
  · change (((callCalleeChosenA d cal).run σ acc).regs
      (Hw.dbudget cal) 32).toNat = (acc.regs (Hw.dbudget cal) 32).toNat
    rw [hbudget]
  · change (((callCalleeChosenA d cal).run σ acc).regs
      (Hw.dmaxdon cal) 32).toNat = (acc.regs (Hw.dmaxdon cal) 32).toNat
    rw [hmaxdon]

/-- The chosen callee writer leaves every other abstract domain unchanged. -/
theorem absDom_callCalleeChosen_other (σ acc : Loom.Hw.St)
    (d cal x : DomainId) (hne : x ≠ cal) :
    Hw.absDom ((callCalleeChosenA d cal).run σ acc) x = Hw.absDom acc x := by
  apply absDom_congr
  intro q hq
  apply frame
  have hquiet : ∀ q ∈ domReadNames x,
      q ∉ (callCalleeChosenA d cal).regWrites := by
    fin_cases cal <;> fin_cases x <;>
      first | exact absurd rfl hne | exact of_decide_eq_true rfl
  exact hquiet q hq

/-- The domain-indexed callee fold updates exactly its decoded callee. -/
theorem absDom_callCalleeA (σ acc : Loom.Hw.St)
    (d cal : DomainId) (g : GateId) (x : DomainId)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    Hw.absDom ((callCalleeA d).run σ acc) x =
      if x = cal then
        { Hw.absDom acc cal with
          regs := fun r => if r.val = 1 then (callArgHandle d).eval σ else 0
          pc := ((Hw.abs σ).gates g).config.entry
          serving := some g }
      else Hw.absDom acc x := by
  rw [callCalleeA_run_selected σ acc d cal hcal]
  by_cases hx : x = cal
  · subst x
    rw [if_pos rfl]
    exact absDom_callCalleeChosen_selected σ acc d cal g hgid
  · rw [if_neg hx]
    exact absDom_callCalleeChosen_other σ acc d cal x hx

/-- Callee scrub and entry writes do not change any abstract gate. -/
theorem absGate_callCalleeA_frame (σ acc : Loom.Hw.St)
    (d : DomainId) (h : GateId) :
    Hw.absGate ((callCalleeA d).run σ acc) h = Hw.absGate acc h := by
  apply absGate_congr
  intro q hq
  apply frame
  have hquiet : ∀ q ∈ gateReadNames h, q ∉ (callCalleeA d).regWrites := by
    fin_cases h <;> exact of_decide_eq_true rfl
  exact hquiet q hq

/-! ## Caller block writer -/

/-- The final successful-call writes to the caller domain. -/
def callCallerA (d : DomainId) : Act :=
  Hw.seqAll
    [ .write 2 (Hw.drun d) (.lit 2),
      .write 2 (Hw.drunG d) (Hw.callGid d),
      Hw.pcAdvA d ]

/-- A read disjoint from the caller status and PC writes is preserved. -/
private theorem callCaller_read (σ acc : Loom.Hw.St) (d : DomainId)
    (rn : String) (w : Nat)
    (hpc : rn ≠ Hw.dpc d) (hrunG : rn ≠ Hw.drunG d)
    (hrun : rn ≠ Hw.drun d) :
    ((callCallerA d).run σ acc).regs rn w = acc.regs rn w := by
  unfold callCallerA Hw.pcAdvA Hw.seqAll
  simp only [Act.run, RegEnv.set]
  rw [if_neg hpc, if_neg hrunG, if_neg hrun]

/-- The caller writer advances the sampled PC and blocks on the selected
gate, preserving the rest of the caller's abstract domain state. -/
theorem absDom_callCaller_selected (σ acc : Loom.Hw.St)
    (d : DomainId) (g : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    Hw.absDom ((callCallerA d).run σ acc) d =
      { Hw.absDom acc d with
        pc := σ.regs (Hw.dpc d) 12 + 1
        run := .blocked g } := by
  have hgidRaw : (Hw.callGid d).eval σ = BitVec.ofNat 2 g.val :=
    (bv2_lit_iff _ g).mpr hgid
  have hpc : ((callCallerA d).run σ acc).regs (Hw.dpc d) 12 =
      σ.regs (Hw.dpc d) 12 + 1 := by
    simp [callCallerA, Hw.pcAdvA, Hw.seqAll, Act.run, RegEnv.set]
  have hrun : Hw.decRun (((callCallerA d).run σ acc).regs (Hw.drun d) 2)
      (((callCallerA d).run σ acc).regs (Hw.drunG d) 2) = .blocked g := by
    simp [callCallerA, Hw.pcAdvA, Hw.seqAll, Act.run, RegEnv.set,
      Hw.decRun, hgidRaw]
    exact finOfBv_dLit g
  apply domainState_ext'
  · funext r
    exact callCaller_read σ acc d _ _
      (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl)
  · exact hpc
  · funext s
    change (if _ = 1#1 then some _ else none) = _
    rw [callCaller_read σ acc d _ _
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl),
      callCaller_read σ acc d _ _
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl),
      callCaller_read σ acc d _ _
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl),
      callCaller_read σ acc d _ _
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)]
    rfl
  · funext s
    exact callCaller_read σ acc d _ _
      (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> fin_cases s <;> exact of_decide_eq_true rfl)
  · funext l
    change (if _ = 1#1 then some _ else none) = _
    rw [callCaller_read σ acc d _ _
          (by fin_cases d <;> fin_cases l <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases l <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases l <;> exact of_decide_eq_true rfl),
      callCaller_read σ acc d _ _
          (by fin_cases d <;> fin_cases l <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases l <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases l <;> exact of_decide_eq_true rfl)]
    rfl
  · funext r
    change (if _ = 1#1 then some _ else none) = _
    rw [callCaller_read σ acc d _ _
          (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl),
      callCaller_read σ acc d _ _
          (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl)]
    rfl
  · exact hrun
  · change (if _ = 1#1 then some _ else none) = _
    rw [callCaller_read σ acc d _ _
          (by fin_cases d <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> exact of_decide_eq_true rfl),
      callCaller_read σ acc d _ _
          (by fin_cases d <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> exact of_decide_eq_true rfl)
          (by fin_cases d <;> exact of_decide_eq_true rfl)]
    rfl
  · exact callCaller_read σ acc d _ _
      (by fin_cases d <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> exact of_decide_eq_true rfl)
  · rw [callCaller_read σ acc d _ _
      (by fin_cases d <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> exact of_decide_eq_true rfl)]
  · rw [callCaller_read σ acc d _ _
      (by fin_cases d <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> exact of_decide_eq_true rfl)
      (by fin_cases d <;> exact of_decide_eq_true rfl)]

/-- Blocking the caller leaves every other abstract domain unchanged. -/
theorem absDom_callCaller_other (σ acc : Loom.Hw.St)
    (d x : DomainId) (hne : x ≠ d) :
    Hw.absDom ((callCallerA d).run σ acc) x = Hw.absDom acc x := by
  apply absDom_congr
  intro q hq
  apply callCaller_read
  · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.dpc d from by
      fin_cases x <;> fin_cases d <;>
        first | exact absurd rfl hne | exact of_decide_eq_true rfl) q hq
  · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.drunG d from by
      fin_cases x <;> fin_cases d <;>
        first | exact absurd rfl hne | exact of_decide_eq_true rfl) q hq
  · exact (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.drun d from by
      fin_cases x <;> fin_cases d <;>
        first | exact absurd rfl hne | exact of_decide_eq_true rfl) q hq

/-- Caller status and PC writes do not change any abstract gate. -/
theorem absGate_callCaller_frame (σ acc : Loom.Hw.St)
    (d : DomainId) (h : GateId) :
    Hw.absGate ((callCallerA d).run σ acc) h = Hw.absGate acc h := by
  apply absGate_congr
  intro q hq
  apply callCaller_read
  · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.dpc d from by
      fin_cases h <;> fin_cases d <;> exact of_decide_eq_true rfl) q hq
  · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.drunG d from by
      fin_cases h <;> fin_cases d <;> exact of_decide_eq_true rfl) q hq
  · exact (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.drun d from by
      fin_cases h <;> fin_cases d <;> exact of_decide_eq_true rfl) q hq

/-! ## Successful call action -/

/-- Optional structural argument transfer at the head of a successful call. -/
def callTransferA (d : DomainId) : Act :=
  .ite (Hw.argNZ d) (Hw.transferA d (Hw.callCal d) (Hw.argSel d)) .skip

/-- The successful action payload factored out of `Hw.callCirc`. -/
def callSuccessA (d : DomainId) : Act :=
  Hw.seqAll
    [ callTransferA d,
      callActivateA d,
      callCalleeA d,
      .write 2 (Hw.drun d) (.lit 2),
      .write 2 (Hw.drunG d) (Hw.callGid d),
      Hw.pcAdvA d ]

/-- Pure abstract state assembled by a successful call after the optional
argument transfer.  `source` is the sampled pre-cycle architectural state;
`base` is the state after that transfer. -/
def callAbstractSuccess (source base : MachineState)
    (d cal : DomainId) (g : GateId) (rd : RegId)
    (argHandle : Loom.Word32) (depth : Nat) : MachineState :=
  { base with
    doms := fun x =>
      if x = d then
        { base.doms d with
          pc := (source.doms d).pc + 1
          run := .blocked g }
      else if x = cal then
        { base.doms cal with
          regs := fun r => if r.val = 1 then argHandle else 0
          pc := (source.gates g).config.entry
          serving := some g }
      else base.doms x
    gates := fun h =>
      if h = g then
        { base.gates g with
          act := some
            { caller := d
              callerRd := rd
              savedRegs := (source.doms cal).regs
              savedPc := (source.doms cal).pc
              savedServing := (source.doms cal).serving
              depth := depth
              donated := (source.doms d).maxDonation } }
      else base.gates h }

/-- Register faces outside domains and gates that the successful-call tail
must frame. -/
private def callQuietNames : List (String × Nat) :=
  [ ("cycle", 32),
    ("mov_v", 1), ("mov_owner", 2), ("mov_src", 14), ("mov_dst", 14),
    ("mov_srccur", 12), ("mov_dstcur", 12), ("mov_rem", 13),
    ("mov_status", 12),
    ("if_v", 1), ("if_dom", 2), ("if_word", 32), ("if_cl", 8) ]

/-- The factored successful payload is definitionally the body selected by
the hardware call check ladder. -/
theorem callCirc_act_eq (d : DomainId) :
    (Hw.callCirc d).act = Hw.ladder d (Hw.callChecks d) (callSuccessA d) := by
  rfl

/-- Retirement dispatch selects the gate-call circuit on opcode 22. -/
theorem retireFor_gateCall_run (σ acc : Loom.Hw.St) (d : DomainId)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6) :
    (Hw.retireFor d).run σ acc =
      (Hw.ladder d (Hw.callChecks d) (callSuccessA d)).run σ acc := by
  rw [← callCirc_act_eq]
  exact retireFor_sel_of_opc σ d "gate_call" 22#6 hopc
    (by decide +kernel)
    (by decide +kernel)
    (Hw.callCirc d)
    (List.mem_append_right _ (by simp)) acc

/-- When the combined call predicate is true, dispatch runs the factored
successful payload directly. -/
theorem retireFor_gateCall_success (σ acc : Loom.Hw.St) (d : DomainId)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hok : (Hw.callOkE d).eval σ = 1#1) :
    (Hw.retireFor d).run σ acc = (callSuccessA d).run σ acc := by
  rw [retireFor_gateCall_run σ acc d hopc]
  apply ladder_run_all_pass
  exact (okOf_eval_iff σ (Hw.callChecks d)).mp hok

/-- Generic first-failure selector for the gate-call errno ladder. -/
theorem retireFor_gateCall_first_error (σ acc : Loom.Hw.St) (d : DomainId)
    (pre post : List Hw.Check) (c : Expr 1) (er : Errno)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6)
    (hchecks : Hw.callChecks d = pre ++ (c, .err er) :: post)
    (hpre : ∀ x ∈ pre, x.1.eval σ ≠ 1#1)
    (hfail : c.eval σ = 1#1) :
    (Hw.retireFor d).run σ acc =
      (Act.seq (Hw.pcAdvA d)
        (Hw.writeReg d Hw.rdE (.lit er.toWord))).run σ acc := by
  rw [retireFor_gateCall_run σ acc d hopc]
  rw [hchecks]
  exact ladder_run_first_failure σ acc d pre post c (.err er)
    (callSuccessA d) hpre hfail

/-- Operational decomposition of the successful call payload into its four
semantic stages. -/
theorem callSuccessA_run (σ acc : Loom.Hw.St) (d : DomainId) :
    (callSuccessA d).run σ acc =
      (callCallerA d).run σ
        ((callCalleeA d).run σ
          ((callActivateA d).run σ ((callTransferA d).run σ acc))) := by
  rfl

/-- After the optional transfer, the remainder of the call payload frames
the cycle, Mover, and in-flight encodings. -/
private theorem callSuccessA_frame_quiet (σ acc : Loom.Hw.St)
    (d : DomainId) (q : String × Nat) (hq : q ∈ callQuietNames) :
    ((callSuccessA d).run σ acc).regs q.1 q.2 =
      ((callTransferA d).run σ acc).regs q.1 q.2 := by
  rw [callSuccessA_run]
  rw [Loom.Hw.Compile.run_regs_notin q.1 q.2 (callCallerA d)]
  rw [Loom.Hw.Compile.run_regs_notin q.1 q.2 (callCalleeA d)]
  rw [Loom.Hw.Compile.run_regs_notin q.1 q.2 (callActivateA d)]
  all_goals
    exact (show ∀ p ∈ callQuietNames, p ∉ _ from by
      fin_cases d <;> decide +kernel) q hq

/-- Domain-map abstraction of the complete successful payload, relative to
the state produced by its optional structural transfer. -/
theorem absDom_callSuccessA (σ acc : Loom.Hw.St)
    (d cal : DomainId) (g : GateId) (x : DomainId)
    (hne : d ≠ cal)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    Hw.absDom ((callSuccessA d).run σ acc) x =
      let base := (callTransferA d).run σ acc
      if x = d then
        { Hw.absDom base d with
          pc := σ.regs (Hw.dpc d) 12 + 1
          run := .blocked g }
      else if x = cal then
        { Hw.absDom base cal with
          regs := fun r => if r.val = 1 then (callArgHandle d).eval σ else 0
          pc := ((Hw.abs σ).gates g).config.entry
          serving := some g }
      else Hw.absDom base x := by
  rw [callSuccessA_run]
  let base := (callTransferA d).run σ acc
  let activated := (callActivateA d).run σ base
  let entered := (callCalleeA d).run σ activated
  change Hw.absDom ((callCallerA d).run σ entered) x = _
  by_cases hxd : x = d
  · subst x
    rw [if_pos rfl, absDom_callCaller_selected σ entered d g hgid]
    have hdc : d ≠ cal := hne
    rw [show Hw.absDom entered d = Hw.absDom activated d from
      absDom_callCalleeA σ activated d cal g d hcal hgid |>.trans
        (if_neg hdc)]
    rw [absDom_callActivateA_frame σ base d d]
  · rw [if_neg hxd, absDom_callCaller_other σ entered d x hxd]
    by_cases hxc : x = cal
    · subst x
      rw [if_pos rfl]
      rw [absDom_callCalleeA σ activated d cal g cal hcal hgid,
        if_pos rfl]
      rw [absDom_callActivateA_frame σ base d cal]
    · rw [if_neg hxc]
      rw [absDom_callCalleeA σ activated d cal g x hcal hgid,
        if_neg hxc]
      rw [absDom_callActivateA_frame σ base d x]

/-- Gate-map abstraction of the complete successful payload. Only the
selected gate receives the new activation record. -/
theorem absGate_callSuccessA (σ acc : Loom.Hw.St)
    (d cal : DomainId) (g h : GateId)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    Hw.absGate ((callSuccessA d).run σ acc) h =
      let base := (callTransferA d).run σ acc
      if h = g then
        { Hw.absGate base g with
          act := some
            { caller := d
              callerRd := finOfBv (by decide) (Hw.rdE.eval σ)
              savedRegs := ((Hw.abs σ).doms cal).regs
              savedPc := ((Hw.abs σ).doms cal).pc
              savedServing := ((Hw.abs σ).doms cal).serving
              depth := ((Hw.callDepth d).eval σ).toNat
              donated := ((Hw.abs σ).doms d).maxDonation } }
      else Hw.absGate base h := by
  rw [callSuccessA_run]
  let base := (callTransferA d).run σ acc
  let activated := (callActivateA d).run σ base
  let entered := (callCalleeA d).run σ activated
  rw [absGate_callCaller_frame σ entered d h,
    absGate_callCalleeA_frame σ activated d h]
  exact absGate_callActivateA σ base d cal g h hgid hcal

/-- The successful call payload has no memory writes; its memory face is
therefore exactly the optional transfer's memory face. -/
private theorem callSuccessA_frame_mem (σ acc : Loom.Hw.St)
    (d : DomainId) (mn : String) (a w : Nat) :
    ((callSuccessA d).run σ acc).mems mn a w =
      ((callTransferA d).run σ acc).mems mn a w := by
  rw [callSuccessA_run]
  rw [Loom.Hw.Compile.run_mems_notin mn (callCallerA d)
    (by simp [callCallerA, Act.memWrites])]
  rw [Loom.Hw.Compile.run_mems_notin mn (callCalleeA d)
    (by simp [callCalleeA, callCalleeChosenA, Act.memWrites])]
  rw [Loom.Hw.Compile.run_mems_notin mn (callActivateA d)
    (by simp [callActivateA, callActivateChosenA, Act.memWrites])]

/-- Whole-machine abstraction of a successful call, relative only to the
state produced by its optional argument transfer.  This is the assembly
lemma consumed by the full retirement square. -/
theorem abs_callSuccessA (σ acc : Loom.Hw.St)
    (d cal : DomainId) (g : GateId)
    (hne : d ≠ cal)
    (hcal : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.callCal d).eval σ) = cal)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.callGid d).eval σ) = g) :
    Hw.abs ((callSuccessA d).run σ acc) =
      callAbstractSuccess (Hw.abs σ)
        (Hw.abs ((callTransferA d).run σ acc)) d cal g
        (finOfBv (by decide) (Hw.rdE.eval σ))
        ((callArgHandle d).eval σ) ((Hw.callDepth d).eval σ).toNat := by
  apply machineState_ext
  · exact callSuccessA_frame_quiet σ acc d ("cycle", 32)
      (by simp [callQuietNames])
  · funext a
    exact callSuccessA_frame_mem σ acc d "mem" a.toNat 32
  · funext x
    rw [absDom_callSuccessA σ acc d cal g x hne hcal hgid]
    rfl
  · funext h
    rw [absGate_callSuccessA σ acc d cal g h hcal hgid]
    rfl
  · change Hw.absMover ((callSuccessA d).run σ acc) =
      Hw.absMover ((callTransferA d).run σ acc)
    unfold Hw.absMover
    rw [callSuccessA_frame_quiet σ acc d ("mov_v", 1)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("mov_owner", 2)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("mov_src", 14)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("mov_dst", 14)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("mov_srccur", 12)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("mov_dstcur", 12)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("mov_rem", 13)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("mov_status", 12)
        (by simp [callQuietNames])]
  · change Hw.absInflight ((callSuccessA d).run σ acc) =
      Hw.absInflight ((callTransferA d).run σ acc)
    unfold Hw.absInflight
    rw [callSuccessA_frame_quiet σ acc d ("if_v", 1)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("if_dom", 2)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("if_word", 32)
        (by simp [callQuietNames]),
      callSuccessA_frame_quiet σ acc d ("if_cl", 8)
        (by simp [callQuietNames])]

/-! ## Successful specification execution -/

/-- A missing live capability is the first gate-call failure and leaves the
specification state unchanged. -/
theorem gateCallExec_stale (c : Ctx) (τ : MachineState)
    (hnone : (τ.doms c.d).liveCap
      (Handle.decode ((τ.doms c.d).reg c.op.rs1)).slot
      (Handle.decode ((τ.doms c.d).reg c.op.rs1)).gen = none) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err .staleHandle τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, Machines.Lnp64u.Isa.capLive, SpecM.get,
    hnone, SpecM.raise]

/-- A live capability whose class bit disagrees with its handle is the
second gate-call failure and likewise leaves the state unchanged. -/
theorem gateCallExec_badClass (c : Ctx) (τ : MachineState) (e : CapEntry)
    (hsome : (τ.doms c.d).liveCap
      (Handle.decode ((τ.doms c.d).reg c.op.rs1)).slot
      (Handle.decode ((τ.doms c.d).reg c.op.rs1)).gen = some e)
    (hcls : (Handle.decode ((τ.doms c.d).reg c.op.rs1)).cls ≠ e.kind.cls) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err .badCap τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, Machines.Lnp64u.Isa.capLive, SpecM.get,
    hsome, SpecM.require]
  rw [if_neg (by simpa using hcls)]
  rfl

/-- A class-correct memory capability cannot be called as a gate. -/
theorem gateCallExec_memCap (c : Ctx) (τ : MachineState) (e : CapEntry)
    (hsome : (τ.doms c.d).liveCap
      (Handle.decode ((τ.doms c.d).reg c.op.rs1)).slot
      (Handle.decode ((τ.doms c.d).reg c.op.rs1)).gen = some e)
    (hcls : (Handle.decode ((τ.doms c.d).reg c.op.rs1)).cls = e.kind.cls)
    (base : Addr) (len : BitVec 13) (perms : Perms)
    (hkind : e.kind = .mem base len perms) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err .badCap τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, Machines.Lnp64u.Isa.capLive, SpecM.get,
    hsome, SpecM.require]
  rw [if_pos (by simpa using hcls)]
  simp only [specM_pure, hkind, SpecM.raise]

/-- An already-active gate fails before any mutation. -/
theorem gateCallExec_active (c : Ctx) (τ : MachineState)
    (S : Slot) (G : Gen) (e : CapEntry) (g : GateId) (a : Activation)
    (hlive : Machines.Lnp64u.Isa.capLive c.d
      ((τ.doms c.d).reg c.op.rs1) τ = .ok (S, G, e) τ)
    (hkind : e.kind = .gate g)
    (hact : (τ.gates g).act = some a) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err .gateBusy τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, hlive, hkind, SpecM.get,
    SpecM.require, hact]
  rfl

/-- Self-call rejection after an idle gate. -/
theorem gateCallExec_self (c : Ctx) (τ : MachineState)
    (S : Slot) (G : Gen) (e : CapEntry) (g : GateId)
    (hlive : Machines.Lnp64u.Isa.capLive c.d
      ((τ.doms c.d).reg c.op.rs1) τ = .ok (S, G, e) τ)
    (hkind : e.kind = .gate g)
    (hact : (τ.gates g).act = none)
    (hcal : (τ.gates g).config.callee = c.d) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err .gateBusy τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, hlive, hkind, SpecM.get, hact,
    Option.isNone_none, SpecM.require, hcal]
  rfl

/-- A non-running callee is rejected before transfer. -/
theorem gateCallExec_calleeNotRunning (c : Ctx) (τ : MachineState)
    (S : Slot) (G : Gen) (e : CapEntry) (g : GateId) (cal : DomainId)
    (hlive : Machines.Lnp64u.Isa.capLive c.d
      ((τ.doms c.d).reg c.op.rs1) τ = .ok (S, G, e) τ)
    (hkind : e.kind = .gate g)
    (hact : (τ.gates g).act = none)
    (hcal : (τ.gates g).config.callee = cal)
    (hne : cal ≠ c.d)
    (hrun : (τ.doms cal).run ≠ .running) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err .gateBusy τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, hlive, hkind, SpecM.get, hact,
    Option.isNone_none, SpecM.require, hcal, hne, decide_true]
  rw [if_neg (by simpa using hrun)]
  rfl

/-- A callee already serving another activation is rejected. -/
theorem gateCallExec_calleeServing (c : Ctx) (τ : MachineState)
    (S : Slot) (G : Gen) (e : CapEntry) (g : GateId) (cal : DomainId)
    (served : GateId)
    (hlive : Machines.Lnp64u.Isa.capLive c.d
      ((τ.doms c.d).reg c.op.rs1) τ = .ok (S, G, e) τ)
    (hkind : e.kind = .gate g)
    (hact : (τ.gates g).act = none)
    (hcal : (τ.gates g).config.callee = cal)
    (hne : cal ≠ c.d)
    (hrun : (τ.doms cal).run = .running)
    (hserv : (τ.doms cal).serving = some served) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err .gateBusy τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, hlive, hkind, SpecM.get, hact,
    Option.isNone_none, SpecM.require, hcal, hne, decide_true, hrun, hserv]
  rfl

/-- A call that would exceed the bounded activation depth is rejected. -/
theorem gateCallExec_depthOverflow (c : Ctx) (τ : MachineState)
    (S : Slot) (G : Gen) (e : CapEntry) (g : GateId) (cal : DomainId)
    (hlive : Machines.Lnp64u.Isa.capLive c.d
      ((τ.doms c.d).reg c.op.rs1) τ = .ok (S, G, e) τ)
    (hkind : e.kind = .gate g)
    (hact : (τ.gates g).act = none)
    (hcal : (τ.gates g).config.callee = cal)
    (hne : cal ≠ c.d)
    (hrun : (τ.doms cal).run = .running)
    (hserv : (τ.doms cal).serving = none)
    (hdepth : ¬Machines.Lnp64u.Isa.Wip.gateDepth c τ ≤ maxChainDepth) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err .gateBusy τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, hlive, hkind, SpecM.get, hact,
    Option.isNone_none, SpecM.require, hcal, hne, decide_true, hrun, hserv]
  rw [if_neg (by simpa using hdepth)]
  rfl

/-- After all gate-state checks pass, an optional-transfer errno is returned
unchanged by the enclosing call. -/
theorem gateCallExec_transferErr (c : Ctx) (τ : MachineState)
    (S : Slot) (G : Gen) (e : CapEntry) (g : GateId) (cal : DomainId)
    (er : Errno)
    (hlive : Machines.Lnp64u.Isa.capLive c.d
      ((τ.doms c.d).reg c.op.rs1) τ = .ok (S, G, e) τ)
    (hkind : e.kind = .gate g)
    (hact : (τ.gates g).act = none)
    (hcal : (τ.gates g).config.callee = cal)
    (hne : cal ≠ c.d)
    (hrun : (τ.doms cal).run = .running)
    (hserv : (τ.doms cal).serving = none)
    (hdepth : Machines.Lnp64u.Isa.Wip.gateDepth c τ ≤ maxChainDepth)
    (htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ.doms c.d).reg c.op.rs2) τ = .err er τ) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ = .err er τ := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind, hlive, hkind, SpecM.get, hact,
    Option.isNone_none, SpecM.require, hcal, hne, decide_true, hrun, hserv,
    hdepth, htransfer]

/-- The named specification gate-call body reduces to the same pure state
transformer as `abs_callSuccessA` once all checks and the optional transfer
have succeeded.  The frame hypotheses are exactly the non-structural fields
preserved by `transferByHandle`. -/
theorem gateCallExec_eq_selected (c : Ctx) (τ τt : MachineState)
    (S : Slot) (G : Gen) (e : CapEntry) (g : GateId) (cal : DomainId)
    (argHandle : Loom.Word32)
    (hlive : Machines.Lnp64u.Isa.capLive c.d
      ((τ.doms c.d).reg c.op.rs1) τ = .ok (S, G, e) τ)
    (hkind : e.kind = .gate g)
    (hact : (τ.gates g).act = none)
    (hcal : (τ.gates g).config.callee = cal)
    (hne : cal ≠ c.d)
    (hrun : (τ.doms cal).run = .running)
    (hserv : (τ.doms cal).serving = none)
    (hdepth : Machines.Lnp64u.Isa.Wip.gateDepth c τ ≤ maxChainDepth)
    (htransfer : Machines.Lnp64u.Isa.transferByHandle c.d cal
      ((τ.doms c.d).reg c.op.rs2) τ = .ok argHandle τt)
    (hgates : τt.gates = τ.gates)
    (hcalRegs : (τt.doms cal).regs = (τ.doms cal).regs)
    (hcalPc : (τt.doms cal).pc = (τ.doms cal).pc)
    (hcalServing : (τt.doms cal).serving = (τ.doms cal).serving)
    (hcallerDonation : (τt.doms c.d).maxDonation =
      (τ.doms c.d).maxDonation) :
    Machines.Lnp64u.Isa.Wip.gateCallExec c τ =
      .ok () (callAbstractSuccess τ τt c.d cal g c.op.rd argHandle
        (Machines.Lnp64u.Isa.Wip.gateDepth c τ)) := by
  unfold Machines.Lnp64u.Isa.Wip.gateCallExec
  simp only [SpecM.reg, specM_bind]
  rw [hlive]
  simp only [hkind, SpecM.get, hact, Option.isNone_none, SpecM.require,
    hcal, hne, decide_true, hrun, hserv, hdepth, htransfer, SpecM.set,
    SpecM.updDom, SpecM.modify]
  unfold callAbstractSuccess
  rw [hgates, hcalRegs, hcalPc, hcalServing, hcallerDonation]
  rfl

end Machines.Lnp64u.Theorems.RMC
