-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateReturnArm
import Machines.Lnp64u.Theorems.RMCReachableWf

/-!
# R-MC retirement: successful gate_return

Dynamic-selector reductions and whole-state abstraction for the successful
null and non-null reply-transfer paths.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

/-- The optional transfer is skipped when the reply handle is null. -/
theorem gateReturnTransferA_run_zero (σ acc : Loom.Hw.St) (d : DomainId)
    (hz : (Hw.retNZ d).eval σ = 0#1) :
    (gateReturnTransferA d).run σ acc = acc := by
  simp [gateReturnTransferA, Act.run, hz]

/-- A non-null reply selects the shared structural transfer action. -/
theorem gateReturnTransferA_run_nonzero (σ acc : Loom.Hw.St)
    (d : DomainId) (hnz : (Hw.retNZ d).eval σ = 1#1) :
    (gateReturnTransferA d).run σ acc =
      (Hw.transferA d (Hw.retCl d) (Hw.retSel d)).run σ acc := by
  simp [gateReturnTransferA, Act.run, hnz]

/-- The gate-clear fold selects exactly the serving gate. -/
theorem gateReturnClearA_run_selected (σ acc : Loom.Hw.St)
    (d : DomainId) (gid : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid) :
    (gateReturnClearA d).run σ acc =
      (Act.write 1 (Hw.gactV gid) (.lit 0)).run σ acc := by
  have hsel : (Expr.eq (Hw.retGid d) (Hw.gLit gid)).eval σ = 1#1 := by
    rw [eqE_eval]
    exact (bv2_lit_iff _ gid).mpr hgid
  have hexcl : ∀ g : GateId, g ≠ gid →
      (Expr.eq (Hw.retGid d) (Hw.gLit g)).eval σ ≠ 1#1 := by
    intro g hne hg
    rw [eqE_eval] at hg
    exact hne ((bv2_lit_iff _ g).mp hg |>.symm.trans hgid)
  exact seqAll_ite_run_unique σ acc
    (fun g : GateId => Expr.eq (Hw.retGid d) (Hw.gLit g))
    (fun g => Act.write 1 (Hw.gactV g) (.lit 0)) gid hsel hexcl
    (List.finRange numGates) (List.mem_finRange gid) (List.nodup_finRange _)

/-- The caller-resume fold selects exactly the active gate's caller. -/
theorem gateReturnResumeA_run_selected (σ acc : Loom.Hw.St)
    (d cl : DomainId)
    (hcl : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.retCl d).eval σ) = cl) :
    (gateReturnResumeA d).run σ acc =
      (Act.write 2 (Hw.drun cl) (.lit 0)).run σ acc := by
  have hsel : (Expr.eq (Hw.retCl d) (Hw.dLit cl)).eval σ = 1#1 := by
    rw [eqE_eval]
    exact (bv2_lit_iff _ cl).mpr hcl
  have hexcl : ∀ c : DomainId, c ≠ cl →
      (Expr.eq (Hw.retCl d) (Hw.dLit c)).eval σ ≠ 1#1 := by
    intro c hne hc
    rw [eqE_eval] at hc
    exact hne ((bv2_lit_iff _ c).mp hc |>.symm.trans hcl)
  exact seqAll_ite_run_unique σ acc
    (fun c : DomainId => Expr.eq (Hw.retCl d) (Hw.dLit c))
    (fun c => Act.write 2 (Hw.drun c) (.lit 0)) cl hsel hexcl
    (List.finRange numDomains) (List.mem_finRange cl)
    (List.nodup_finRange _)

/-- The reply-write fold selects exactly the active gate's caller. -/
theorem gateReturnReplyA_run_selected (σ acc : Loom.Hw.St)
    (d cl : DomainId)
    (hcl : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.retCl d).eval σ) = cl) :
    (gateReturnReplyA d).run σ acc =
      (Hw.writeReg cl
        (Hw.muxFin (fun g => .reg 3 (Hw.gcallerRd g)) (Hw.retGid d))
        (gateReturnReplyE d)).run σ acc := by
  have hsel : (Expr.eq (Hw.retCl d) (Hw.dLit cl)).eval σ = 1#1 := by
    rw [eqE_eval]
    exact (bv2_lit_iff _ cl).mpr hcl
  have hexcl : ∀ c : DomainId, c ≠ cl →
      (Expr.eq (Hw.retCl d) (Hw.dLit c)).eval σ ≠ 1#1 := by
    intro c hne hc
    rw [eqE_eval] at hc
    exact hne ((bv2_lit_iff _ c).mp hc |>.symm.trans hcl)
  exact seqAll_ite_run_unique σ acc
    (fun c : DomainId => Expr.eq (Hw.retCl d) (Hw.dLit c))
    (fun c => Hw.writeReg c
      (Hw.muxFin (fun g => .reg 3 (Hw.gcallerRd g)) (Hw.retGid d))
      (gateReturnReplyE d)) cl hsel hexcl
    (List.finRange numDomains) (List.mem_finRange cl)
    (List.nodup_finRange _)

/-! ## Sampled activation record -/

/-- A live abstract activation is exactly the record decoded from its gate
register bank in the sampled hardware state. -/
theorem gateReturn_activation_decode (σ : Loom.Hw.St) (gid : GateId)
    (act : Activation) (hact : ((Hw.abs σ).gates gid).act = some act) :
    act =
      { caller := finOfBv (by decide) (σ.regs (Hw.gcaller gid) 2)
        callerRd := finOfBv (by decide) (σ.regs (Hw.gcallerRd gid) 3)
        savedRegs := fun r => σ.regs (Hw.gsreg gid r) 32
        savedPc := σ.regs (Hw.gspc gid) 12
        savedServing := if σ.regs (Hw.gssrvV gid) 1 = 1#1 then
          some (finOfBv (by decide) (σ.regs (Hw.gssrv gid) 2)) else none
        depth := (σ.regs (Hw.gdepth gid) 3).toNat
        donated := (σ.regs (Hw.gdon gid) 32).toNat } := by
  change (if σ.regs (Hw.gactV gid) 1 = 1#1 then some _ else none) =
    some act at hact
  by_cases hv : σ.regs (Hw.gactV gid) 1 = 1#1
  · rw [if_pos hv] at hact
    exact (Option.some.inj hact).symm
  · rw [if_neg hv] at hact
    contradiction

/-- The sampled caller destination-register mux decodes to the activation's
saved `callerRd`. -/
theorem gateReturn_callerRd_eval (σ : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (act : Activation)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    finOfBv (by decide : 2 ^ 3 = numRegs)
      ((Hw.muxFin (fun g => .reg 3 (Hw.gcallerRd g))
        (Hw.retGid d)).eval σ) = act.callerRd := by
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
  rw [gateReturn_activation_decode σ gid act hact]
  rfl

/-- Every sampled saved-register mux agrees with the activation record. -/
theorem gateReturn_savedReg_eval (σ : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (act : Activation) (r : RegId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    (Hw.muxFin (fun g => .reg 32 (Hw.gsreg g r))
      (Hw.retGid d)).eval σ = act.savedRegs r := by
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
  rw [gateReturn_activation_decode σ gid act hact]
  rfl

/-- The sampled saved-PC mux agrees with the activation record. -/
theorem gateReturn_savedPc_eval (σ : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (act : Activation)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    (Hw.muxFin (fun g => .reg 12 (Hw.gspc g))
      (Hw.retGid d)).eval σ = act.savedPc := by
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
  rw [gateReturn_activation_decode σ gid act hact]
  rfl

/-- The sampled saved-serving mux pair agrees with the activation record. -/
theorem gateReturn_savedServing_eval (σ : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (act : Activation)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    (if (Hw.muxFin (fun g => .reg 1 (Hw.gssrvV g))
          (Hw.retGid d)).eval σ = 1#1 then
       some (finOfBv (by decide)
         ((Hw.muxFin (fun g => .reg 2 (Hw.gssrv g))
           (Hw.retGid d)).eval σ))
     else none) = act.savedServing := by
  rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid,
    muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
  rw [gateReturn_activation_decode σ gid act hact]
  rfl

/-! ## Gate-clear abstraction -/

/-- Clearing the selected activation bit removes exactly the selected
abstract activation. -/
theorem absGate_gateReturnClearA (σ acc : Loom.Hw.St) (d : DomainId)
    (gid h : GateId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid) :
    Hw.absGate ((gateReturnClearA d).run σ acc) h =
      if h = gid then { Hw.absGate acc gid with act := none }
      else Hw.absGate acc h := by
  rw [gateReturnClearA_run_selected σ acc d gid hgid]
  by_cases hh : h = gid
  · subst h
    rw [if_pos rfl]
    fin_cases gid <;>
      simp [Hw.absGate, Act.run, RegEnv.set, Expr.eval, Hw.gactV,
        Hw.gcallee, Hw.gentry, Hw.gcaller, Hw.gcallerRd, Hw.gsreg, Hw.gspc,
        Hw.gssrvV, Hw.gssrv, Hw.gdepth, Hw.gdon]
  · rw [if_neg hh]
    apply absGate_congr
    intro p hp
    exact frame (by
      intro hm
      simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
      have hn : p.1 ≠ Hw.gactV gid :=
        (show ∀ q ∈ gateReadNames h, q.1 ≠ Hw.gactV gid from by
          fin_cases h <;> fin_cases gid <;>
            first
              | exact absurd rfl hh
              | exact of_decide_eq_true rfl) p hp
      exact hn hm.1) σ acc

/-- The selected gate clear frames every abstract domain. -/
theorem absDom_gateReturnClearA (σ acc : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (x : DomainId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid) :
    Hw.absDom ((gateReturnClearA d).run σ acc) x = Hw.absDom acc x := by
  rw [gateReturnClearA_run_selected σ acc d gid hgid]
  apply absDom_congr
  intro p hp
  exact frame (by
    intro hm
    simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
    have hn : p.1 ≠ Hw.gactV gid :=
      (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.gactV gid from by
        fin_cases x <;> fin_cases gid <;> exact of_decide_eq_true rfl) p hp
    exact hn hm.1) σ acc

/-! ## Context-restore reads -/

/-- Domain registers whose decoding is unaffected by the return context
restore.  The restore owns only the architectural file, PC, and serving
pair. -/
private def returnRestoreQuietNames (d : DomainId) : List (String × Nat) :=
  ((List.finRange numSlots).flatMap fun s =>
      [(Hw.dcapV d s, 1), (Hw.dcapKind d s, 32), (Hw.dcapLinV d s, 1),
       (Hw.dcapLin d s, 4), (Hw.dgen d s, 8)])
  ++ ((List.finRange numLineage).flatMap fun l =>
      [(Hw.dcellV d l, 1), (Hw.dcellPar d l, 14)])
  ++ ((List.finRange numRegions).flatMap fun r =>
      [(Hw.drgnV d r, 1), (Hw.drgn d r, 42)])
  ++ [(Hw.drun d, 2), (Hw.drunG d, 2), (Hw.dcause d, 32),
      (Hw.dbudget d, 32), (Hw.dmaxdon d, 32)]

/-- Quiet-field abstraction when a hardware action changes only a domain's
architectural file, PC, and serving pair. -/
private theorem absDom_regpcserv {S1 S2 : Loom.Hw.St} (d : DomainId)
    (hq : ∀ q ∈ returnRestoreQuietNames d,
      S2.regs q.1 q.2 = S1.regs q.1 q.2) :
    Hw.absDom S2 d =
      { Hw.absDom S1 d with
        regs := fun r => S2.regs (Hw.dreg d r) 32
        pc := S2.regs (Hw.dpc d) 12
        serving := (Hw.absDom S2 d).serving } := by
  have hs : ∀ (s : Slot) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.dcapV d s, 1), (Hw.dcapKind d s, 32),
        (Hw.dcapLinV d s, 1), (Hw.dcapLin d s, 4), (Hw.dgen d s, 8)] →
      S2.regs rn w = S1.regs rn w := fun s rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨s, List.mem_finRange s, hp⟩))))
  have hl : ∀ (l : LineageId) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.dcellV d l, 1), (Hw.dcellPar d l, 14)] →
      S2.regs rn w = S1.regs rn w := fun l rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨l, List.mem_finRange l, hp⟩))))
  have hr : ∀ (r : RegionId) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.drgnV d r, 1), (Hw.drgn d r, 42)] →
      S2.regs rn w = S1.regs rn w := fun r rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨r, List.mem_finRange r, hp⟩)))
  have ht : ∀ (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.drun d, 2), (Hw.drunG d, 2), (Hw.dcause d, 32),
        (Hw.dbudget d, 32), (Hw.dmaxdon d, 32)] →
      S2.regs rn w = S1.regs rn w := fun rn w hp =>
    hq (rn, w) (List.mem_append_right _ hp)
  apply domainState_ext'
  · rfl
  · rfl
  · show (Hw.absDom S2 d).caps = (Hw.absDom S1 d).caps
    funext s
    show (if S2.regs (Hw.dcapV d s) 1 = 1 then _ else none) =
      (if S1.regs (Hw.dcapV d s) 1 = 1 then _ else none)
    rw [hs s (Hw.dcapV d s) 1 (by simp),
      hs s (Hw.dcapKind d s) 32 (by simp),
      hs s (Hw.dcapLinV d s) 1 (by simp),
      hs s (Hw.dcapLin d s) 4 (by simp)]
  · show (Hw.absDom S2 d).slotGen = (Hw.absDom S1 d).slotGen
    funext s
    exact hs s (Hw.dgen d s) 8 (by simp)
  · show (Hw.absDom S2 d).lineage = (Hw.absDom S1 d).lineage
    funext l
    show (if S2.regs (Hw.dcellV d l) 1 = 1 then _ else none) =
      (if S1.regs (Hw.dcellV d l) 1 = 1 then _ else none)
    rw [hl l (Hw.dcellV d l) 1 (by simp),
      hl l (Hw.dcellPar d l) 14 (by simp)]
  · show (Hw.absDom S2 d).regions = (Hw.absDom S1 d).regions
    funext r
    show (if S2.regs (Hw.drgnV d r) 1 = 1 then _ else none) =
      (if S1.regs (Hw.drgnV d r) 1 = 1 then _ else none)
    rw [hr r (Hw.drgnV d r) 1 (by simp), hr r (Hw.drgn d r) 42 (by simp)]
  · show Hw.decRun (S2.regs (Hw.drun d) 2) (S2.regs (Hw.drunG d) 2) =
      Hw.decRun (S1.regs (Hw.drun d) 2) (S1.regs (Hw.drunG d) 2)
    rw [ht (Hw.drun d) 2 (by simp), ht (Hw.drunG d) 2 (by simp)]
  · rfl
  · exact ht (Hw.dcause d) 32 (by simp)
  · change (S2.regs (Hw.dbudget d) 32).toNat =
      (S1.regs (Hw.dbudget d) 32).toNat
    rw [ht (Hw.dbudget d) 32 (by simp)]
  · change (S2.regs (Hw.dmaxdon d) 32).toNat =
      (S1.regs (Hw.dmaxdon d) 32).toNat
    rw [ht (Hw.dmaxdon d) 32 (by simp)]

private theorem return_seqAll_write_frame {I : Type} {w qW : Nat}
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

private theorem return_seqAll_write_at {I : Type} {w : Nat}
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
        rw [return_seqAll_write_frame σ _ rn v t (rn i)
          (fun j hj hname => hnd'.1
            ((hinj i (List.mem_cons_self ..) j
              (List.mem_cons_of_mem i hj) hname).symm ▸ hj))]
        simp [Act.run, RegEnv.set]
      · have hit : i ∈ t := (List.mem_cons.mp hi).resolve_left
          (fun h => hai h.symm)
        exact ih _ hit hnd'.2 (fun x hx y hy =>
          hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))

/-- The restore stage writes every architectural register from the sampled
activation record. -/
theorem gateReturnRestoreA_reg (σ acc : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (act : Activation) (r : RegId)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    ((gateReturnRestoreA d).run σ acc).regs (Hw.dreg d r) 32 =
      act.savedRegs r := by
  have hs := gateReturn_savedReg_eval σ d gid act r hgid hact
  change ((Act.write 2 (Hw.dsrv d)
      (Hw.muxFin (fun g => .reg 2 (Hw.gssrv g)) (Hw.retGid d))).run σ
    ((Act.write 1 (Hw.dsrvV d)
      (Hw.muxFin (fun g => .reg 1 (Hw.gssrvV g)) (Hw.retGid d))).run σ
    ((Act.write 12 (Hw.dpc d)
      (Hw.muxFin (fun g => .reg 12 (Hw.gspc g)) (Hw.retGid d))).run σ
    ((Hw.seqAll ((List.finRange numRegs).map fun r =>
      Act.write 32 (Hw.dreg d r)
        (Hw.muxFin (fun g => .reg 32 (Hw.gsreg g r))
          (Hw.retGid d)))).run σ acc)))).regs (Hw.dreg d r) 32 = _
  rw [frame (by
      intro hm
      simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
      exact (show Hw.dreg d r ≠ Hw.dsrv d from by
        fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl) hm.1) σ _,
    frame (by
      intro hm
      simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
      exact (show Hw.dreg d r ≠ Hw.dsrvV d from by
        fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl) hm.1) σ _,
    frame (by
      intro hm
      simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
      exact (show Hw.dreg d r ≠ Hw.dpc d from by
        fin_cases d <;> fin_cases r <;> exact of_decide_eq_true rfl) hm.1) σ _]
  rw [return_seqAll_write_at σ acc (Hw.dreg d)
    (fun r => Hw.muxFin (fun g => .reg 32 (Hw.gsreg g r)) (Hw.retGid d))
    (List.finRange numRegs) r (List.mem_finRange r) (List.nodup_finRange _)
    (fun a _ b _ hab => dreg_inj d a b hab)]
  exact hs

/-- The restore stage writes the sampled saved PC. -/
theorem gateReturnRestoreA_pc (σ acc : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (act : Activation)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    ((gateReturnRestoreA d).run σ acc).regs (Hw.dpc d) 12 =
      act.savedPc := by
  have hs := gateReturn_savedPc_eval σ d gid act hgid hact
  change ((Act.write 2 (Hw.dsrv d)
      (Hw.muxFin (fun g => .reg 2 (Hw.gssrv g)) (Hw.retGid d))).run σ
    ((Act.write 1 (Hw.dsrvV d)
      (Hw.muxFin (fun g => .reg 1 (Hw.gssrvV g)) (Hw.retGid d))).run σ
    ((Act.write 12 (Hw.dpc d)
      (Hw.muxFin (fun g => .reg 12 (Hw.gspc g)) (Hw.retGid d))).run σ
      _))).regs (Hw.dpc d) 12 = _
  rw [frame (by
      intro hm
      simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
      exact (show Hw.dpc d ≠ Hw.dsrv d from by
        fin_cases d <;> exact of_decide_eq_true rfl) hm.1) σ _,
    frame (by
      intro hm
      simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
      exact (show Hw.dpc d ≠ Hw.dsrvV d from by
        fin_cases d <;> exact of_decide_eq_true rfl) hm.1) σ _]
  simpa only [Act.run, RegEnv.set, if_true] using hs

/-- The restore stage's two serving registers decode to the sampled prior
serving tag. -/
theorem gateReturnRestoreA_serving (σ acc : Loom.Hw.St) (d : DomainId)
    (gid : GateId) (act : Activation)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    (if ((gateReturnRestoreA d).run σ acc).regs (Hw.dsrvV d) 1 = 1#1 then
       some (finOfBv (by decide)
         (((gateReturnRestoreA d).run σ acc).regs (Hw.dsrv d) 2))
     else none) = act.savedServing := by
  have hs := gateReturn_savedServing_eval σ d gid act hgid hact
  have hv : ((gateReturnRestoreA d).run σ acc).regs (Hw.dsrvV d) 1 =
      (Hw.muxFin (fun g => .reg 1 (Hw.gssrvV g)) (Hw.retGid d)).eval σ := by
    change ((Act.write 2 (Hw.dsrv d)
        (Hw.muxFin (fun g => .reg 2 (Hw.gssrv g)) (Hw.retGid d))).run σ
      ((Act.write 1 (Hw.dsrvV d)
        (Hw.muxFin (fun g => .reg 1 (Hw.gssrvV g)) (Hw.retGid d))).run σ
        _)).regs (Hw.dsrvV d) 1 = _
    rw [frame (by
      intro hm
      simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
      exact (show Hw.dsrvV d ≠ Hw.dsrv d from by
        fin_cases d <;> exact of_decide_eq_true rfl) hm.1) σ _]
    simp [Act.run, RegEnv.set]
  have hg : ((gateReturnRestoreA d).run σ acc).regs (Hw.dsrv d) 2 =
      (Hw.muxFin (fun g => .reg 2 (Hw.gssrv g)) (Hw.retGid d)).eval σ := by
    change ((Act.write 2 (Hw.dsrv d)
        (Hw.muxFin (fun g => .reg 2 (Hw.gssrv g)) (Hw.retGid d))).run σ
      _).regs (Hw.dsrv d) 2 = _
    simp [Act.run, RegEnv.set]
  rw [hv, hg]
  exact hs

/-! ## Context-restore abstraction -/

/-- The restore stage installs the complete saved context in the returning
domain and preserves every other abstract domain field. -/
theorem absDom_gateReturnRestoreA_selected (σ acc : Loom.Hw.St)
    (d : DomainId) (gid : GateId) (act : Activation)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    Hw.absDom ((gateReturnRestoreA d).run σ acc) d =
      { Hw.absDom acc d with
        regs := act.savedRegs
        pc := act.savedPc
        serving := act.savedServing } := by
  have hquiet : ∀ q ∈ returnRestoreQuietNames d,
      ((gateReturnRestoreA d).run σ acc).regs q.1 q.2 =
        acc.regs q.1 q.2 := by
    intro q hq
    exact frame (by
      have hn : ∀ q ∈ returnRestoreQuietNames d,
          q ∉ (gateReturnRestoreA d).regWrites := by
        fin_cases d <;> exact of_decide_eq_true rfl
      exact hn q hq) σ acc
  rw [absDom_regpcserv d hquiet]
  apply domainState_ext'
  · funext r
    exact gateReturnRestoreA_reg σ acc d gid act r hgid hact
  · exact gateReturnRestoreA_pc σ acc d gid act hgid hact
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact gateReturnRestoreA_serving σ acc d gid act hgid hact
  · rfl
  · rfl
  · rfl

/-- A return restore changes no other abstract domain. -/
theorem absDom_gateReturnRestoreA_other (σ acc : Loom.Hw.St)
    (d x : DomainId) (hne : x ≠ d) :
    Hw.absDom ((gateReturnRestoreA d).run σ acc) x = Hw.absDom acc x := by
  apply absDom_congr
  intro q hq
  exact frame (by
    have hn : ∀ q ∈ domReadNames x,
        q ∉ (gateReturnRestoreA d).regWrites := by
      fin_cases d <;> fin_cases x <;>
        first | exact absurd rfl hne | exact of_decide_eq_true rfl
    exact hn q hq) σ acc

/-- Whole-domain face of context restoration. -/
theorem absDom_gateReturnRestoreA (σ acc : Loom.Hw.St)
    (d x : DomainId) (gid : GateId) (act : Activation)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    Hw.absDom ((gateReturnRestoreA d).run σ acc) x =
      if x = d then
        { Hw.absDom acc d with
          regs := act.savedRegs
          pc := act.savedPc
          serving := act.savedServing }
      else Hw.absDom acc x := by
  by_cases hx : x = d
  · subst x
    rw [if_pos rfl]
    exact absDom_gateReturnRestoreA_selected σ acc d gid act hgid hact
  · rw [if_neg hx]
    exact absDom_gateReturnRestoreA_other σ acc d x hx

/-! ## Caller resume abstraction -/

/-- The resume stage changes exactly the selected caller's run state. -/
theorem absDom_gateReturnResumeA (σ acc : Loom.Hw.St)
    (d cl x : DomainId)
    (hcl : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.retCl d).eval σ) = cl) :
    Hw.absDom ((gateReturnResumeA d).run σ acc) x =
      if x = cl then { Hw.absDom acc cl with run := .running }
      else Hw.absDom acc x := by
  rw [gateReturnResumeA_run_selected σ acc d cl hcl]
  by_cases hx : x = cl
  · subst x
    rw [if_pos rfl]
    have hsrvrun : Hw.dsrv cl ≠ Hw.drun cl := by
      fin_cases cl <;> exact of_decide_eq_true rfl
    fin_cases cl <;>
      simp [Hw.absDom, Act.run, RegEnv.set, Expr.eval, Hw.decRun,
        Hw.dreg, Hw.dpc, Hw.dcapV, Hw.dcapKind, Hw.dcapLinV, Hw.dcapLin,
        Hw.dgen, Hw.dcellV, Hw.dcellPar, Hw.drgnV, Hw.drgn, Hw.drun,
        Hw.drunG, Hw.dsrvV, Hw.dsrv, Hw.dcause, Hw.dbudget, Hw.dmaxdon,
        hsrvrun] <;>
      split <;> simp_all <;> rw [if_neg (by decide)]
  · rw [if_neg hx]
    apply absDom_congr
    intro q hq
    exact frame (by
      intro hm
      simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
      have hn : q.1 ≠ Hw.drun cl :=
        (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.drun cl from by
          fin_cases x <;> fin_cases cl <;>
            first | exact absurd rfl hx | exact of_decide_eq_true rfl) q hq
      exact hn hm.1) σ acc

/-! ## Reply-register abstraction -/

/-- A decoded hardware `writeReg` is exactly the architectural `setReg`,
including the discarded `r0` case, and frames every other domain. -/
private theorem absDom_writeReg_eval (σ acc : Loom.Hw.St)
    (c x : DomainId) (rE : Expr 3) (vE : Expr 32)
    (rd : RegId) (V : Loom.Word32)
    (hrd : rd.val = (rE.eval σ).toNat) (hval : vE.eval σ = V) :
    Hw.absDom ((Hw.writeReg c rE vE).run σ acc) x =
      if x = c then (Hw.absDom acc c).setReg rd V
      else Hw.absDom acc x := by
  by_cases h0 : rd = (0 : RegId)
  · rw [writeReg_run_of_zero σ acc c rE vE (by rw [← hrd, h0]; rfl)]
    by_cases hx : x = c
    · subst x
      rw [if_pos rfl]
      simp [DomainState.setReg, h0]
    · rw [if_neg hx]
  · rw [writeReg_run_of_nz σ acc c rE vE rd hrd
      (fun hz => h0 (Fin.ext hz))]
    by_cases hx : x = c
    · subst x
      rw [if_pos rfl]
      have hquiet : ∀ q ∈ domQuietNames c,
          ((Act.write 32 (Hw.dreg c rd) vE).run σ acc).regs q.1 q.2 =
            acc.regs q.1 q.2 := by
        intro q hq
        exact frame (by
          intro hm
          simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
          have hn : q.1 ≠ Hw.dreg c rd :=
            (show ∀ q ∈ domQuietNames c, q.1 ≠ Hw.dreg c rd from by
              fin_cases c <;> fin_cases rd <;> exact of_decide_eq_true rfl) q hq
          exact hn hm.1) σ acc
      rw [absDom_regpc c hquiet]
      apply domainState_ext'
      · funext r
        rw [setReg_regs, if_neg h0]
        simp only [Act.run, RegEnv.set]
        by_cases hr : r = rd
        · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial, hval]
        · rw [if_neg (fun heq => hr (dreg_inj c r rd heq)), if_neg hr]
          rfl
      · rw [setReg_pc]
        change ((Act.write 32 (Hw.dreg c rd) vE).run σ acc).regs
          (Hw.dpc c) 12 = acc.regs (Hw.dpc c) 12
        exact frame (show ((Hw.dpc c : String), (12 : Nat)) ∉
          (Act.write 32 (Hw.dreg c rd) vE).regWrites from by
            fin_cases c <;> fin_cases rd <;> exact of_decide_eq_true rfl) σ acc
      · rw [setReg_caps]
      · rw [setReg_slotGen]
      · rw [setReg_lineage]
      · rw [setReg_regions]
      · rw [setReg_run]
      · rw [setReg_serving]
      · rw [setReg_cause]
      · rw [setReg_budget]
      · rw [setReg_maxDonation]
    · rw [if_neg hx]
      apply absDom_congr
      intro q hq
      exact frame (by
        intro hm
        simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
        have hn : q.1 ≠ Hw.dreg c rd :=
          (show ∀ q ∈ domReadNames x, q.1 ≠ Hw.dreg c rd from by
            fin_cases x <;> fin_cases c <;> fin_cases rd <;>
              first | exact absurd rfl hx | exact of_decide_eq_true rfl) q hq
        exact hn hm.1) σ acc

/-- The reply stage writes exactly the sampled reply destination in the
selected caller domain. -/
theorem absDom_gateReturnReplyA (σ acc : Loom.Hw.St)
    (d cl x : DomainId) (gid : GateId) (act : Activation)
    (reply : Loom.Word32)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hcl : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.retCl d).eval σ) = cl)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hreply : (gateReturnReplyE d).eval σ = reply) :
    Hw.absDom ((gateReturnReplyA d).run σ acc) x =
      if x = cl then (Hw.absDom acc cl).setReg act.callerRd reply
      else Hw.absDom acc x := by
  rw [gateReturnReplyA_run_selected σ acc d cl hcl]
  apply absDom_writeReg_eval σ acc cl x
  · rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid]
    rw [gateReturn_activation_decode σ gid act hact]
    rfl
  · exact hreply

/-! ## Successful payload abstraction -/

/-- Reads outside the return control tail.  These faces are inherited
unchanged from the optional structural transfer. -/
private def gateReturnQuietNames : List (String × Nat) :=
  [("cycle", 32), ("mov_v", 1), ("mov_owner", 2), ("mov_src", 14),
   ("mov_dst", 14), ("mov_srccur", 12), ("mov_dstcur", 12),
   ("mov_rem", 13), ("mov_status", 12), ("if_v", 1), ("if_dom", 2),
   ("if_word", 32), ("if_cl", 8)]

/-- The return control tail frames cycle, Mover, and in-flight reads relative
to the state produced by the optional reply transfer. -/
private theorem gateReturnSuccessA_frame_quiet (σ acc : Loom.Hw.St)
    (d : DomainId) (q : String × Nat) (hq : q ∈ gateReturnQuietNames) :
    ((gateReturnSuccessA d).run σ acc).regs q.1 q.2 =
      ((gateReturnTransferA d).run σ acc).regs q.1 q.2 := by
  rw [gateReturnSuccessA_run]
  rw [frame (by
      have hn : ∀ p ∈ gateReturnQuietNames,
          p ∉ (gateReturnReplyA d).regWrites := by
        fin_cases d <;> exact of_decide_eq_true rfl
      exact hn q hq) σ _]
  rw [frame (by
      have hn : ∀ p ∈ gateReturnQuietNames,
          p ∉ (gateReturnResumeA d).regWrites := by
        fin_cases d <;> exact of_decide_eq_true rfl
      exact hn q hq) σ _]
  rw [frame (by
      have hn : ∀ p ∈ gateReturnQuietNames,
          p ∉ (gateReturnRestoreA d).regWrites := by
        fin_cases d <;> exact of_decide_eq_true rfl
      exact hn q hq) σ _]
  exact frame (by
    have hn : ∀ p ∈ gateReturnQuietNames,
        p ∉ (gateReturnClearA d).regWrites := by
      fin_cases d <;> exact of_decide_eq_true rfl
    exact hn q hq) σ _

/-- The return tail has no memory writes; memory is exactly the optional
transfer's memory face. -/
private theorem gateReturnSuccessA_frame_mem (σ acc : Loom.Hw.St)
    (d : DomainId) (mn : String) (a w : Nat) :
    ((gateReturnSuccessA d).run σ acc).mems mn a w =
      ((gateReturnTransferA d).run σ acc).mems mn a w := by
  rw [gateReturnSuccessA_run]
  rw [Loom.Hw.Act.run_mems_notin mn (gateReturnReplyA d)
    (of_decide_eq_true rfl)]
  rw [Loom.Hw.Act.run_mems_notin mn (gateReturnResumeA d)
    (of_decide_eq_true rfl)]
  rw [Loom.Hw.Act.run_mems_notin mn (gateReturnRestoreA d)
    (of_decide_eq_true rfl)]
  rw [Loom.Hw.Act.run_mems_notin mn (gateReturnClearA d)
    (of_decide_eq_true rfl)]

/-- Domain-map face of the complete successful return payload. -/
theorem absDom_gateReturnSuccessA (σ acc : Loom.Hw.St)
    (d x : DomainId) (gid : GateId) (act : Activation)
    (reply : Loom.Word32) (hne : d ≠ act.caller)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hcl : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.retCl d).eval σ) = act.caller)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hreply : (gateReturnReplyE d).eval σ = reply) :
    Hw.absDom ((gateReturnSuccessA d).run σ acc) x =
      (returnAbstractSuccess
        (Hw.abs ((gateReturnTransferA d).run σ acc)) d gid act reply).doms x := by
  rw [gateReturnSuccessA_run]
  by_cases hxd : x = d
  · subst x
    rw [absDom_gateReturnReplyA σ _ d act.caller d gid act reply hgid hcl
        hact hreply, if_neg hne,
      absDom_gateReturnResumeA σ _ d act.caller d hcl, if_neg hne,
      absDom_gateReturnRestoreA σ _ d d gid act hgid hact, if_pos rfl,
      absDom_gateReturnClearA σ _ d gid d hgid]
    simp [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update, hne] <;>
      simp only [Hw.abs] <;> simp
  · by_cases hxc : x = act.caller
    · subst x
      rw [absDom_gateReturnReplyA σ _ d act.caller act.caller gid act reply
          hgid hcl hact hreply, if_pos rfl,
        absDom_gateReturnResumeA σ _ d act.caller act.caller hcl, if_pos rfl,
        absDom_gateReturnRestoreA σ _ d act.caller gid act hgid hact,
        if_neg hne.symm,
        absDom_gateReturnClearA σ _ d gid act.caller hgid]
      simp [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update,
        hne, hne.symm] <;> simp only [Hw.abs] <;> simp
    · rw [absDom_gateReturnReplyA σ _ d act.caller x gid act reply hgid hcl
          hact hreply, if_neg hxc,
        absDom_gateReturnResumeA σ _ d act.caller x hcl, if_neg hxc,
        absDom_gateReturnRestoreA σ _ d x gid act hgid hact, if_neg hxd,
        absDom_gateReturnClearA σ _ d gid x hgid]
      simp [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update, hxd,
        hxc] <;> simp only [Hw.abs] <;> simp

/-- Gate-map face of the complete successful return payload. -/
theorem absGate_gateReturnSuccessA (σ acc : Loom.Hw.St)
    (d : DomainId) (gid h : GateId) (act : Activation)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid) :
    Hw.absGate ((gateReturnSuccessA d).run σ acc) h =
      (returnAbstractSuccess
        (Hw.abs ((gateReturnTransferA d).run σ acc)) d gid act 0).gates h := by
  rw [gateReturnSuccessA_run]
  have hreplyFrame : Hw.absGate
      ((gateReturnReplyA d).run σ
        ((gateReturnResumeA d).run σ
          ((gateReturnRestoreA d).run σ
            ((gateReturnClearA d).run σ
              ((gateReturnTransferA d).run σ acc))))) h =
      Hw.absGate
        ((gateReturnResumeA d).run σ
          ((gateReturnRestoreA d).run σ
            ((gateReturnClearA d).run σ
              ((gateReturnTransferA d).run σ acc)))) h := by
    apply absGate_congr
    intro q hq
    exact frame (by
      have hn : ∀ q ∈ gateReadNames h,
          q ∉ (gateReturnReplyA d).regWrites := by
        fin_cases d <;> fin_cases h <;> exact of_decide_eq_true rfl
      exact hn q hq) σ _
  rw [hreplyFrame]
  have hresumeFrame : Hw.absGate
      ((gateReturnResumeA d).run σ
        ((gateReturnRestoreA d).run σ
          ((gateReturnClearA d).run σ
            ((gateReturnTransferA d).run σ acc)))) h =
      Hw.absGate
        ((gateReturnRestoreA d).run σ
          ((gateReturnClearA d).run σ
            ((gateReturnTransferA d).run σ acc))) h := by
    apply absGate_congr
    intro q hq
    exact frame (by
      have hn : ∀ q ∈ gateReadNames h,
          q ∉ (gateReturnResumeA d).regWrites := by
        fin_cases d <;> fin_cases h <;> exact of_decide_eq_true rfl
      exact hn q hq) σ _
  rw [hresumeFrame]
  have hrestoreFrame : Hw.absGate
      ((gateReturnRestoreA d).run σ
        ((gateReturnClearA d).run σ
          ((gateReturnTransferA d).run σ acc))) h =
      Hw.absGate
        ((gateReturnClearA d).run σ
          ((gateReturnTransferA d).run σ acc)) h := by
    apply absGate_congr
    intro q hq
    exact frame (by
      have hn : ∀ q ∈ gateReadNames h,
          q ∉ (gateReturnRestoreA d).regWrites := by
        fin_cases d <;> fin_cases h <;> exact of_decide_eq_true rfl
      exact hn q hq) σ _
  rw [hrestoreFrame, absGate_gateReturnClearA σ _ d gid h hgid]
  by_cases hh : h = gid <;>
    simp_all [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update] <;>
    rfl

/-- Whole-machine abstraction of a successful return, relative only to the
state produced by its optional reply transfer. -/
theorem abs_gateReturnSuccessA (σ acc : Loom.Hw.St)
    (d : DomainId) (gid : GateId) (act : Activation)
    (reply : Loom.Word32) (hne : d ≠ act.caller)
    (hgid : finOfBv (by decide : 2 ^ 2 = numGates)
      ((Hw.retGid d).eval σ) = gid)
    (hcl : finOfBv (by decide : 2 ^ 2 = numDomains)
      ((Hw.retCl d).eval σ) = act.caller)
    (hact : ((Hw.abs σ).gates gid).act = some act)
    (hreply : (gateReturnReplyE d).eval σ = reply) :
    Hw.abs ((gateReturnSuccessA d).run σ acc) =
      returnAbstractSuccess
        (Hw.abs ((gateReturnTransferA d).run σ acc)) d gid act reply := by
  apply machineState_ext'
  · exact gateReturnSuccessA_frame_quiet σ acc d ("cycle", 32)
      (by simp [gateReturnQuietNames])
  · funext a
    exact gateReturnSuccessA_frame_mem σ acc d "mem" a.toNat 32
  · funext x
    exact absDom_gateReturnSuccessA σ acc d x gid act reply hne hgid hcl
      hact hreply
  · funext h
    have hg := absGate_gateReturnSuccessA σ acc d gid h act hgid
    simpa [returnAbstractSuccess] using hg
  · change Hw.absMover ((gateReturnSuccessA d).run σ acc) =
      Hw.absMover ((gateReturnTransferA d).run σ acc)
    unfold Hw.absMover
    rw [gateReturnSuccessA_frame_quiet σ acc d ("mov_v", 1)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("mov_owner", 2)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("mov_src", 14)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("mov_dst", 14)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("mov_srccur", 12)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("mov_dstcur", 12)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("mov_rem", 13)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("mov_status", 12)
        (by simp [gateReturnQuietNames])]
  · change Hw.absInflight ((gateReturnSuccessA d).run σ acc) =
      Hw.absInflight ((gateReturnTransferA d).run σ acc)
    unfold Hw.absInflight
    rw [gateReturnSuccessA_frame_quiet σ acc d ("if_v", 1)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("if_dom", 2)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("if_word", 32)
        (by simp [gateReturnQuietNames]),
      gateReturnSuccessA_frame_quiet σ acc d ("if_cl", 8)
        (by simp [gateReturnQuietNames])]

/-! ## Specification-side normalization -/

/-- The successful return tail overwrites the retiring domain's PC, so the
specification's eager retirement increment is invisible after the tail. -/
theorem returnAbstractSuccess_setPc (base : MachineState)
    (d : DomainId) (gid : GateId) (act : Activation)
    (reply : Loom.Word32) (hne : d ≠ act.caller) :
    returnAbstractSuccess
        (base.setDom d fun ds => { ds with pc := ds.pc + 1 })
        d gid act reply =
      returnAbstractSuccess base d gid act reply := by
  unfold returnAbstractSuccess
  apply machineState_ext'
  · rfl
  · rfl
  · funext x
    by_cases hxd : x = d
    · subst x
      simp [MachineState.setDom, Loom.Fun.update, hne]
    · by_cases hxc : x = act.caller
      · subst x
        simp [MachineState.setDom, Loom.Fun.update, hne, hne.symm]
      · simp [MachineState.setDom, Loom.Fun.update, hxd, hxc]
  · rfl
  · rfl
  · rfl

/-- The return control tail preserves every structural table produced by
the optional transfer, as well as Mover and memory state. -/
theorem returnAbstractSuccess_structural_frames (base : MachineState)
    (d : DomainId) (gid : GateId) (act : Activation)
    (reply : Loom.Word32) :
    (∀ x, ((returnAbstractSuccess base d gid act reply).doms x).caps =
      (base.doms x).caps) ∧
    (∀ x, ((returnAbstractSuccess base d gid act reply).doms x).slotGen =
      (base.doms x).slotGen) ∧
    (∀ x, ((returnAbstractSuccess base d gid act reply).doms x).lineage =
      (base.doms x).lineage) ∧
    (∀ x, ((returnAbstractSuccess base d gid act reply).doms x).regions =
      (base.doms x).regions) ∧
    (returnAbstractSuccess base d gid act reply).mover = base.mover ∧
    (returnAbstractSuccess base d gid act reply).mem = base.mem := by
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = act.caller <;>
      simp_all [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update,
        setReg_caps]
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = act.caller <;>
      simp_all [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update,
        setReg_slotGen]
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = act.caller <;>
      simp_all [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update,
        setReg_lineage]
  constructor
  · intro x
    by_cases hxd : x = d <;> by_cases hxc : x = act.caller <;>
      simp_all [returnAbstractSuccess, MachineState.setDom, Loom.Fun.update,
        setReg_regions]
  · exact ⟨rfl, rfl⟩

/-- In a reachable return state, the running in-flight callee cannot also be
the blocked caller recorded by its active gate. -/
theorem gateReturnIssuer_ne_caller_of_reachable (m : Manifest) (hwf : m.WF)
    (σ : Loom.Hw.St) (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1) (gid : GateId) (act : Activation)
    (hact : ((Hw.abs σ).gates gid).act = some act) :
    finOfBv (by decide) (σ.regs "if_dom" 2) ≠ act.caller := by
  let E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2)
  let W := σ.regs "if_word" 32
  have hwfAbs : Wf (Hw.abs σ) := reachable_wf m hwf _ hsr
  have hfl : (Hw.abs σ).inflight = some
      { dom := E, word := W,
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    change Hw.absInflight σ = _
    simpa [E, W] using absInflight_some σ hifv
  change E ≠ act.caller
  exact Machines.Lnp64u.Theorems.RMC.Wf.inflight_ne_gateCaller
    hwfAbs _ hfl gid act hact

end Machines.Lnp64u.Theorems.RMC
