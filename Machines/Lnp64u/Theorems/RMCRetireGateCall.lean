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

end Machines.Lnp64u.Theorems.RMC
