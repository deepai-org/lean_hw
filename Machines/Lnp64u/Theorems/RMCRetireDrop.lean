-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireDup

/-!
# R-MC retirement: `cap_drop` kill support

Selection bridges for the successful drop kill set.  These isolate the
non-inert core/Mover interaction shared by the region and Mover sweeps.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## Spec-side liveness through the structural drop updates -/

theorem regionBacking_live {σ : MachineState} (hwf : Wf σ)
    {d : DomainId} {r : RegionId} {rg : Region}
    (hr : (σ.doms d).regions r = some rg) : σ.liveRef rg.backing = true := by
  obtain ⟨e, he, -⟩ := hwf.region_backed d r rg hr
  unfold MachineState.liveRef
  rw [he]
  rfl

theorem moverEndpoints_live {σ : MachineState} (hwf : Wf σ)
    (job : MoverJob) (hj : σ.mover = some job) :
    σ.liveRef job.src = true ∧ σ.liveRef job.dst = true :=
  (hwf.mover_wf job hj).2.2

@[simp] theorem reparent_liveRef (σ : MachineState) (old new r : CapRef) :
    (σ.reparent old new).liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap
  rw [reparent_caps, reparent_slotGen]

@[simp] theorem orphanChildren_liveRef (σ : MachineState) (old r : CapRef) :
    (σ.orphanChildren old).liveRef r = σ.liveRef r := by
  unfold MachineState.liveRef
  apply liveCap_isSome_congr
  · exact orphanChildren_caps_isSome σ old r.dom r.slot
  · exact congrFun (orphanChildren_slotGen σ old r.dom) r.slot

/-- Clearing a slot removes exactly references at that domain/slot;
generation is irrelevant once the entry is absent. -/
theorem clearSlot_liveRef (σ : MachineState) (d : DomainId) (s : Slot)
    (r : CapRef) :
    (σ.clearSlot d s).liveRef r =
      if r.dom = d ∧ r.slot = s then false else σ.liveRef r := by
  unfold MachineState.liveRef DomainState.liveCap
  rw [clearSlot_caps, clearSlot_slotGen]
  by_cases h : r.dom = d ∧ r.slot = s
  · rw [if_pos h, if_pos h]
    simp [h]
  · rw [if_neg h, if_neg h]
    simp [h]

theorem reparent_clearSlot_liveRef (σ : MachineState) (old new : CapRef)
    (d : DomainId) (s : Slot) (r : CapRef) :
    ((σ.reparent old new).clearSlot d s).liveRef r =
      if r.dom = d ∧ r.slot = s then false else σ.liveRef r := by
  rw [clearSlot_liveRef]
  split <;> simp_all

theorem orphan_clearSlot_liveRef (σ : MachineState) (old : CapRef)
    (d : DomainId) (s : Slot) (r : CapRef) :
    ((σ.orphanChildren old).clearSlot d s).liveRef r =
      if r.dom = d ∧ r.slot = s then false else σ.liveRef r := by
  rw [clearSlot_liveRef]
  split <;> simp_all

/-- Given the exact post-clear liveness equation, `sweepRegions` removes
exactly regions backed by the cleared domain/slot. -/
theorem sweepRegions_drop_regions (σ τ : MachineState)
    (d : DomainId) (s : Slot)
    (hregions : ∀ c : DomainId, (τ.doms c).regions = (σ.doms c).regions)
    (hlive : ∀ r : CapRef, τ.liveRef r =
      if r.dom = d ∧ r.slot = s then false else σ.liveRef r)
    (hregionLive : ∀ c r rg, (σ.doms c).regions r = some rg →
      σ.liveRef rg.backing = true)
    (c : DomainId) (ri : RegionId) :
    (τ.sweepRegions.doms c).regions ri =
      match (σ.doms c).regions ri with
      | some rg =>
          if rg.backing.dom = d ∧ rg.backing.slot = s then none else some rg
      | none => none := by
  unfold MachineState.sweepRegions
  dsimp only
  rw [hregions]
  cases hr : (σ.doms c).regions ri with
  | none => rfl
  | some rg =>
      by_cases hk : rg.backing.dom = d ∧ rg.backing.slot = s
      · simp only
        rw [hlive, if_pos hk, if_pos hk]
        rfl
      · simp only
        rw [hlive, if_neg hk, hregionLive c ri rg hr, if_neg hk]
        rfl

/-- Under the same liveness equation, the spec Mover sweep clears exactly
jobs whose source or destination occupies the dropped slot. -/
theorem sweepMover_drop_mover (σ τ : MachineState)
    (d : DomainId) (s : Slot)
    (hmover : τ.mover = σ.mover)
    (hlive : ∀ r : CapRef, τ.liveRef r =
      if r.dom = d ∧ r.slot = s then false else σ.liveRef r)
    (hmoverLive : ∀ job, σ.mover = some job →
      σ.liveRef job.src = true ∧ σ.liveRef job.dst = true) :
    τ.sweepMover.mover =
      match σ.mover with
      | none => none
      | some job =>
          if (job.src.dom = d ∧ job.src.slot = s) ∨
              (job.dst.dom = d ∧ job.dst.slot = s)
          then none else some job := by
  unfold MachineState.sweepMover
  rw [hmover]
  cases hmov : σ.mover with
  | none =>
      simp only
      exact hmover.trans hmov
  | some job =>
      simp only
      have hl := hmoverLive job hmov
      by_cases hs : job.src.dom = d ∧ job.src.slot = s
      · rw [hlive, if_pos hs]
        simp [hs, MachineState.write]
        split <;> rfl
      · rw [hlive, if_neg hs, hl.1]
        by_cases hd : job.dst.dom = d ∧ job.dst.slot = s
        · rw [hlive, if_pos hd]
          simp [hs, hd, MachineState.write]
          split <;> rfl
        · rw [hlive, if_neg hd, hl.2]
          simp [hs, hd]
          exact hmover.trans hmov

/-- Memory face of the same sweep: a killed job writes `-ESTALE` to its
status word exactly when post-region authority still covers that word. -/
theorem sweepMover_drop_mem (σ τ : MachineState)
    (d : DomainId) (s : Slot)
    (hmover : τ.mover = σ.mover)
    (hlive : ∀ r : CapRef, τ.liveRef r =
      if r.dom = d ∧ r.slot = s then false else σ.liveRef r)
    (hmoverLive : ∀ job, σ.mover = some job →
      σ.liveRef job.src = true ∧ σ.liveRef job.dst = true)
    (b : Addr) :
    τ.sweepMover.mem b =
      match σ.mover with
      | none => τ.mem b
      | some job =>
          if (job.src.dom = d ∧ job.src.slot = s) ∨
              (job.dst.dom = d ∧ job.dst.slot = s) then
            if ({ τ with mover := none } : MachineState).domCovers job.owner
                job.statusAddr { r := false, w := true, x := false } then
              if b = job.statusAddr then Errno.staleHandle.toWord else τ.mem b
            else τ.mem b
          else τ.mem b := by
  unfold MachineState.sweepMover
  rw [hmover]
  cases hmov : σ.mover with
  | none => simp only
  | some job =>
      simp only
      have hl := hmoverLive job hmov
      by_cases hs : job.src.dom = d ∧ job.src.slot = s
      · rw [hlive, if_pos hs]
        simp only [Bool.false_and, Bool.false_eq_true, if_false]
        by_cases hc : ({ τ with mover := none } : MachineState).domCovers
            job.owner job.statusAddr { r := false, w := true, x := false }
        · rw [if_pos hc]
          by_cases hb : b = job.statusAddr
          · subst b
            rw [if_pos rfl]
            simp [hs, hc, MachineState.write, Loom.Fun.update_same]
          · rw [if_neg hb]
            simp [hs, hc, hb, MachineState.write,
              Loom.Fun.update_ne _ _ _ _ hb]
        · rw [if_neg hc]
          simp [hs, hc]
      · rw [hlive, if_neg hs, hl.1]
        by_cases hd : job.dst.dom = d ∧ job.dst.slot = s
        · rw [hlive, if_pos hd]
          simp only [Bool.true_and, Bool.false_eq_true, if_false]
          by_cases hc : ({ τ with mover := none } : MachineState).domCovers
              job.owner job.statusAddr { r := false, w := true, x := false }
          · rw [if_pos hc]
            by_cases hb : b = job.statusAddr
            · subst b
              rw [if_pos rfl]
              simp [hs, hd, hc, MachineState.write, Loom.Fun.update_same]
            · rw [if_neg hb]
              simp [hs, hd, hc, hb, MachineState.write,
                Loom.Fun.update_ne _ _ _ _ hb]
          · rw [if_neg hc]
            simp [hs, hd, hc]
        · rw [hlive, if_neg hd, hl.2]
          simp [hs, hd]

/-! ## Hardware structural walks -/

/-- A guarded write walk frames a register whose name is distinct from
every indexed target. -/
theorem seqAll_ite_write_frame {I : Type} {w qW : Nat}
    (σ acc : Loom.Hw.St) (cond : I → Expr 1) (rn : I → String)
    (v : I → Expr w) (l : List I) (q : String)
    (hne : ∀ i ∈ l, q ≠ rn i) :
    ((Hw.seqAll (l.map fun i => Act.ite (cond i)
      (Act.write w (rn i) (v i)) .skip)).run σ acc).regs q qW =
      acc.regs q qW := by
  induction l generalizing acc with
  | nil => rfl
  | cons i t ih =>
      change ((Hw.seqAll (t.map fun j => Act.ite (cond j)
        (Act.write w (rn j) (v j)) .skip)).run σ
          (if (cond i).eval σ = 1#1 then
            (Act.write w (rn i) (v i)).run σ acc else acc)).regs q qW = _
      rw [ih _ (fun j hj => hne j (List.mem_cons_of_mem i hj))]
      by_cases hc : (cond i).eval σ = 1#1
      · rw [if_pos hc]
        simp only [Act.run, RegEnv.set]
        rw [if_neg (hne i (List.mem_cons_self ..))]
      · rw [if_neg hc]

/-- Pointwise semantics of an injectively named guarded-write walk. -/
theorem seqAll_ite_write_at {I : Type} {w : Nat}
    (σ acc : Loom.Hw.St) (cond : I → Expr 1) (rn : I → String)
    (v : I → Expr w) (l : List I) (i : I) (hi : i ∈ l)
    (hnd : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, rn a = rn b → a = b) :
    ((Hw.seqAll (l.map fun j => Act.ite (cond j)
      (Act.write w (rn j) (v j)) .skip)).run σ acc).regs (rn i) w =
      if (cond i).eval σ = 1#1 then (v i).eval σ
      else acc.regs (rn i) w := by
  induction l generalizing acc with
  | nil => exact absurd hi List.not_mem_nil
  | cons a t ih =>
      have hnd' := List.nodup_cons.mp hnd
      by_cases hai : a = i
      · subst a
        change ((Hw.seqAll (t.map fun j => Act.ite (cond j)
          (Act.write w (rn j) (v j)) .skip)).run σ
            (if (cond i).eval σ = 1#1 then
              (Act.write w (rn i) (v i)).run σ acc else acc)).regs (rn i) w = _
        rw [seqAll_ite_write_frame σ _ cond rn v t (rn i)
          (fun j hj hname => hnd'.1
            ((hinj i (List.mem_cons_self ..) j
              (List.mem_cons_of_mem i hj) hname).symm ▸ hj))]
        by_cases hc : (cond i).eval σ = 1#1
        · rw [if_pos hc, if_pos hc]
          simp [Act.run, RegEnv.set]
        · rw [if_neg hc, if_neg hc]
      · have hit : i ∈ t := (List.mem_cons.mp hi).resolve_left
          (fun h => hai h.symm)
        let acc' := if (cond a).eval σ = 1#1 then
          (Act.write w (rn a) (v a)).run σ acc else acc
        change ((Hw.seqAll (t.map fun j => Act.ite (cond j)
          (Act.write w (rn j) (v j)) .skip)).run σ acc').regs (rn i) w = _
        rw [ih acc' hit hnd'.2
          (fun x hx y hy hxy => hinj x (List.mem_cons_of_mem a hx)
            y (List.mem_cons_of_mem a hy) hxy)]
        have hname : rn a ≠ rn i := fun h => hai
          (hinj a (List.mem_cons_self ..) i hi h)
        have hacc : acc'.regs (rn i) w = acc.regs (rn i) w := by
          dsimp only [acc']
          by_cases hc : (cond a).eval σ = 1#1
          · rw [if_pos hc]
            simp only [Act.run, RegEnv.set]
            rw [if_neg (fun h => hname h.symm)]
          · rw [if_neg hc]
        by_cases hc : (cond i).eval σ = 1#1
        · simp [hc]
        · simp [hc, hacc]

/-- Since action expressions read only the pre-cycle state, equality of one
accumulator register is preserved pointwise through any action. -/
theorem Act.run_regs_congr_acc (a : Act) (σ acc₁ acc₂ : Loom.Hw.St)
    (q : String) (qW : Nat)
    (h : acc₁.regs q qW = acc₂.regs q qW) :
    (a.run σ acc₁).regs q qW = (a.run σ acc₂).regs q qW := by
  induction a generalizing acc₁ acc₂ with
  | skip => exact h
  | seq a b iha ihb => exact ihb _ _ (iha _ _ h)
  | ite c t e iht ihe =>
      by_cases hc : c.eval σ = 1#1
      · simp [Act.run, hc, iht _ _ h]
      · simp [Act.run, hc, ihe _ _ h]
  | write w rn v =>
      simp only [Act.run, RegEnv.set]
      by_cases hr : q = rn
      · subst q
        simp only [if_pos]
        by_cases hw : w = qW
        · subst qW; simp
        · simp [hw, h]
      · simp [hr, h]
  | memWrite => exact h

/-- Memory-entry analogue of `Act.run_regs_congr_acc`. -/
theorem Act.run_mems_congr_acc (act : Act) (σ acc₁ acc₂ : Loom.Hw.St)
    (m : String) (a : Nat) (w : Nat)
    (h : acc₁.mems m a w = acc₂.mems m a w) :
    (act.run σ acc₁).mems m a w = (act.run σ acc₂).mems m a w := by
  induction act generalizing acc₁ acc₂ with
  | skip => exact h
  | seq x y ihx ihy => exact ihy _ _ (ihx _ _ h)
  | ite c t e iht ihe =>
      by_cases hc : c.eval σ = 1#1
      · simp [Act.run, hc, iht _ _ h]
      · simp [Act.run, hc, ihe _ _ h]
  | write => exact h
  | memWrite aw dw mn port addr data =>
      simp only [Act.run, MemEnv.set]
      by_cases hma : m = mn ∧ a = (addr.eval σ).toNat
      · rw [if_pos hma, if_pos hma]
        by_cases hw : dw = w
        · rw [dif_pos hw, dif_pos hw]
        · rw [dif_neg hw, dif_neg hw]
          exact h
      · rw [if_neg hma, if_neg hma]
        exact h

/-- The hardware generation bump is the kernel's saturating bump. -/
theorem bumpE_eval (σ : Loom.Hw.St) (g : Expr 8) :
    (Hw.bumpE g).eval σ = bumpGen (g.eval σ) := by
  unfold Hw.bumpE bumpGen
  rw [show genRetired = 255#8 from rfl]
  change (if (if g.eval σ = 255#8 then 1#1 else 0#1) = 1#1 then
    g.eval σ else g.eval σ + 1#8) = _
  by_cases h : g.eval σ = 255#8 <;> simp [h]

/-- `clearSlotA` clears exactly the selected capability-valid register. -/
theorem clearSlotA_capV (σ acc : Loom.Hw.St) (d : DomainId) (S s : Slot)
    (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val) :
    ((Hw.clearSlotA d sE linVE linE).run σ acc).regs (Hw.dcapV d s) 1 =
      if s = S then 0#1 else acc.regs (Hw.dcapV d s) 1 := by
  unfold Hw.clearSlotA
  simp only [Act.run]
  rw [frame (show ((Hw.dcapV d s : String), (1 : Nat)) ∉
      (Hw.seqAll ((List.finRange numLineage).map fun l =>
        Act.ite (.and linVE (.eq linE (Hw.lLit l)))
          (.write 1 (Hw.dcellV d l) (.lit 0)) .skip)).regWrites from by
      have hne : ∀ l : LineageId, Hw.dcapV d s ≠ Hw.dcellV d l := by
        intro l
        exact ((by native_decide +revert : ∀ (d : DomainId) (s : Slot)
          (l : LineageId), Hw.dcapV d s ≠ Hw.dcellV d l) d s l)
      generalize List.finRange numLineage = ls
      induction ls with
      | nil => simp [Hw.seqAll, Act.regWrites]
      | cons l ls ih =>
          simp [Hw.seqAll, Act.regWrites, hne l]
          simpa only [Hw.seqAll] using ih) σ _]
  rw [seqAll_ite_run_unique σ acc
    (fun s' : Slot => Expr.eq sE (Hw.sLit s'))
    (fun s' : Slot => Act.seq (.write 1 (Hw.dcapV d s') (.lit 0))
      (.write 8 (Hw.dgen d s')
        (Hw.bumpE (.reg 8 (Hw.dgen d s'))))) S]
  · simp only [Act.run, RegEnv.set]
    rw [if_neg ((by native_decide +revert : ∀ (d : DomainId) (s₁ s₂ : Slot),
      ¬(Hw.dcapV d s₁ = Hw.dgen d s₂)) d s S)]
    by_cases hs : s = S
    · subst s
      simp
      rfl
    · rw [if_neg (fun h => hs ((by native_decide +revert :
          ∀ (d : DomainId) (s₁ s₂ : Slot),
            Hw.dcapV d s₁ = Hw.dcapV d s₂ → s₁ = s₂) d s S h)), if_neg hs]
  · show (Expr.eq sE (Hw.sLit S)).eval σ = 1#1
    rw [eqE_eval, hslot]
    rfl
  · intro j hj hjeq
    rw [eqE_eval, hslot] at hjeq
    apply hj
    change BitVec.ofNat 4 S.val = BitVec.ofNat 4 j.val at hjeq
    apply Fin.ext
    have := congrArg BitVec.toNat hjeq
    simp [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show S.val < 2 ^ 4 by have := S.isLt; omega),
      Nat.mod_eq_of_lt (show j.val < 2 ^ 4 by have := j.isLt; omega)] at this
    omega
  · exact List.mem_finRange S
  · exact List.nodup_finRange _

/-- `clearSlotA` saturating-bumps exactly the selected slot generation. -/
theorem clearSlotA_gen (σ acc : Loom.Hw.St) (d : DomainId) (S s : Slot)
    (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val) :
    ((Hw.clearSlotA d sE linVE linE).run σ acc).regs (Hw.dgen d s) 8 =
      if s = S then bumpGen (σ.regs (Hw.dgen d S) 8)
      else acc.regs (Hw.dgen d s) 8 := by
  unfold Hw.clearSlotA
  simp only [Act.run]
  rw [frame (show ((Hw.dgen d s : String), (8 : Nat)) ∉
      (Hw.seqAll ((List.finRange numLineage).map fun l =>
        Act.ite (.and linVE (.eq linE (Hw.lLit l)))
          (.write 1 (Hw.dcellV d l) (.lit 0)) .skip)).regWrites from by
      have hne : ∀ l : LineageId, Hw.dgen d s ≠ Hw.dcellV d l := by
        intro l
        exact ((by native_decide +revert : ∀ (d : DomainId) (s : Slot)
          (l : LineageId), Hw.dgen d s ≠ Hw.dcellV d l) d s l)
      generalize List.finRange numLineage = ls
      induction ls with
      | nil => simp [Hw.seqAll, Act.regWrites]
      | cons l ls ih =>
          simp [Hw.seqAll, Act.regWrites, hne l]
          simpa only [Hw.seqAll] using ih) σ _]
  rw [seqAll_ite_run_unique σ acc
    (fun s' : Slot => Expr.eq sE (Hw.sLit s'))
    (fun s' : Slot => Act.seq (.write 1 (Hw.dcapV d s') (.lit 0))
      (.write 8 (Hw.dgen d s')
        (Hw.bumpE (.reg 8 (Hw.dgen d s'))))) S]
  · simp only [Act.run, RegEnv.set]
    by_cases hs : s = S
    · subst s
      rw [if_pos rfl, if_pos rfl, bumpE_eval]
      simp [Expr.eval]
    · rw [if_neg (fun h => hs ((by native_decide +revert :
          ∀ (d : DomainId) (s₁ s₂ : Slot),
            Hw.dgen d s₁ = Hw.dgen d s₂ → s₁ = s₂) d s S h)),
        if_neg ((by native_decide +revert : ∀ (d : DomainId) (s₁ s₂ : Slot),
          Hw.dgen d s₁ ≠ Hw.dcapV d s₂) d s S), if_neg hs]
  · show (Expr.eq sE (Hw.sLit S)).eval σ = 1#1
    rw [eqE_eval, hslot]
    rfl
  · intro j hj hjeq
    rw [eqE_eval, hslot] at hjeq
    apply hj
    change BitVec.ofNat 4 S.val = BitVec.ofNat 4 j.val at hjeq
    apply Fin.ext
    have := congrArg BitVec.toNat hjeq
    simp [Nat.mod_eq_of_lt (show S.val < 2 ^ 4 by have := S.isLt; omega),
      Nat.mod_eq_of_lt (show j.val < 2 ^ 4 by have := j.isLt; omega)] at this
    omega
  · exact List.mem_finRange S
  · exact List.nodup_finRange _

/-- For a derived entry, `clearSlotA` frees exactly its selected lineage
cell. -/
theorem clearSlotA_cellV_some (σ acc : Loom.Hw.St) (d : DomainId)
    (S : Slot) (L l : LineageId) (sE : Expr 4) (linVE : Expr 1)
    (linE : Expr 4)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (hlinV : linVE.eval σ = 1#1)
    (hlin : linE.eval σ = BitVec.ofNat 4 L.val) :
    ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
        (Hw.dcellV d l) 1 =
      if l = L then 0#1 else acc.regs (Hw.dcellV d l) 1 := by
  unfold Hw.clearSlotA
  simp only [Act.run]
  let slotAcc := (Hw.seqAll ((List.finRange numSlots).map fun s' =>
      Act.ite (.eq sE (Hw.sLit s'))
        (.seq (.write 1 (Hw.dcapV d s') (.lit 0))
          (.write 8 (Hw.dgen d s')
            (Hw.bumpE (.reg 8 (Hw.dgen d s'))))) .skip)).run σ acc
  have hacc : slotAcc.regs (Hw.dcellV d l) 1 =
      acc.regs (Hw.dcellV d l) 1 := by
    dsimp only [slotAcc]
    apply frame
    have hcap : ∀ s' : Slot, Hw.dcellV d l ≠ Hw.dcapV d s' := by
      intro s'; exact ((by native_decide +revert : ∀ (d : DomainId)
        (l : LineageId) (s : Slot), Hw.dcellV d l ≠ Hw.dcapV d s) d l s')
    have hgen : ∀ s' : Slot, Hw.dcellV d l ≠ Hw.dgen d s' := by
      intro s'; exact ((by native_decide +revert : ∀ (d : DomainId)
        (l : LineageId) (s : Slot), Hw.dcellV d l ≠ Hw.dgen d s) d l s')
    generalize List.finRange numSlots = ls
    induction ls with
    | nil => simp [Hw.seqAll, Act.regWrites]
    | cons s' ls ih =>
        simp [Hw.seqAll, Act.regWrites, hcap s', hgen s']
        simpa only [Hw.seqAll] using ih
  change ((Hw.seqAll ((List.finRange numLineage).map fun l' =>
    Act.ite (.and linVE (.eq linE (Hw.lLit l')))
      (.write 1 (Hw.dcellV d l') (.lit 0)) .skip)).run σ slotAcc).regs
      (Hw.dcellV d l) 1 = _
  rw [seqAll_ite_run_unique σ slotAcc
    (fun l' : LineageId => Expr.and linVE (Expr.eq linE (Hw.lLit l')))
    (fun l' : LineageId => Act.write 1 (Hw.dcellV d l') (.lit 0)) L]
  · simp only [Act.run, RegEnv.set]
    by_cases hl : l = L
    · subst l
      simp
      rfl
    · rw [if_neg (fun h => hl ((by native_decide +revert :
          ∀ (d : DomainId) (l₁ l₂ : LineageId),
            Hw.dcellV d l₁ = Hw.dcellV d l₂ → l₁ = l₂) d l L h)), if_neg hl,
        hacc]
  · show linVE.eval σ &&& (Expr.eq linE (Hw.lLit L)).eval σ = 1#1
    rw [hlinV]
    change 1#1 &&& (if linE.eval σ = BitVec.ofNat 4 L.val then 1#1 else 0#1) = 1#1
    rw [hlin]
    simp
  · intro j hj hcond
    change linVE.eval σ &&&
      (if linE.eval σ = BitVec.ofNat 4 j.val then 1#1 else 0#1) = 1#1 at hcond
    rw [bv1_and_eq_one] at hcond
    have heq : linE.eval σ = BitVec.ofNat 4 j.val := by
      by_cases heq : linE.eval σ = BitVec.ofNat 4 j.val
      · exact heq
      · rw [if_neg heq] at hcond
        exact absurd hcond.2 (by decide)
    rw [hlin] at heq
    apply hj
    change BitVec.ofNat 4 L.val = BitVec.ofNat 4 j.val at heq
    apply Fin.ext
    have := congrArg BitVec.toNat heq
    simp at this
    omega
  · exact List.mem_finRange L
  · exact List.nodup_finRange _

/-- A root entry owns no lineage cell, so the lineage half of
`clearSlotA` is inert. -/
theorem clearSlotA_cellV_none (σ acc : Loom.Hw.St) (d : DomainId)
    (S : Slot) (l : LineageId) (sE : Expr 4) (linVE : Expr 1)
    (linE : Expr 4)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (hlinV : linVE.eval σ = 0#1) :
    ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
        (Hw.dcellV d l) 1 = acc.regs (Hw.dcellV d l) 1 := by
  unfold Hw.clearSlotA
  simp only [Act.run]
  rw [seqAll_ite_run_none σ _
    (fun l' : LineageId => Expr.and linVE (Expr.eq linE (Hw.lLit l')))
    (fun l' : LineageId => Act.write 1 (Hw.dcellV d l') (.lit 0))]
  · apply frame
    have hcap : ∀ s' : Slot, Hw.dcellV d l ≠ Hw.dcapV d s' := by
      intro s'; exact ((by native_decide +revert : ∀ (d : DomainId)
        (l : LineageId) (s : Slot), Hw.dcellV d l ≠ Hw.dcapV d s) d l s')
    have hgen : ∀ s' : Slot, Hw.dcellV d l ≠ Hw.dgen d s' := by
      intro s'; exact ((by native_decide +revert : ∀ (d : DomainId)
        (l : LineageId) (s : Slot), Hw.dcellV d l ≠ Hw.dgen d s) d l s')
    generalize List.finRange numSlots = ls
    induction ls with
    | nil => simp [Hw.seqAll, Act.regWrites]
    | cons s' ls ih =>
        simp [Hw.seqAll, Act.regWrites, hcap s', hgen s']
        simpa only [Hw.seqAll] using ih
  · intro l' _ h
    change linVE.eval σ &&&
      (if linE.eval σ = BitVec.ofNat 4 l'.val then 1#1 else 0#1) = 1#1 at h
    rw [hlinV] at h
    have hz : ∀ x : BitVec 1, ¬(0#1 &&& x = 1#1) := by decide
    exact hz _ h

/-- `clearSlotA` frames registers outside capability-valid, generation,
and lineage-valid banks. -/
theorem clearSlotA_frame (σ acc : Loom.Hw.St) (d : DomainId)
    (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (q : String) (qW : Nat)
    (hcap : ∀ s : Slot, q ≠ Hw.dcapV d s)
    (hgen : ∀ s : Slot, q ≠ Hw.dgen d s)
    (hcell : ∀ l : LineageId, q ≠ Hw.dcellV d l) :
    ((Hw.clearSlotA d sE linVE linE).run σ acc).regs q qW =
      acc.regs q qW := by
  apply frame
  unfold Hw.clearSlotA
  simp only [Act.regWrites, List.mem_append, not_or]
  constructor
  · generalize List.finRange numSlots = ls
    induction ls with
    | nil => simp [Hw.seqAll, Act.regWrites]
    | cons s ls ih =>
        simp [Hw.seqAll, Act.regWrites, hcap s, hgen s]
        simpa only [Hw.seqAll] using ih
  · generalize List.finRange numLineage = ls
    induction ls with
    | nil => simp [Hw.seqAll, Act.regWrites]
    | cons l ls ih =>
        simp [Hw.seqAll, Act.regWrites, hcell l]
        simpa only [Hw.seqAll] using ih

/-- Pointwise parent-register semantics of the hardware reparent walk. -/
theorem reparentA_cellPar (σ acc : Loom.Hw.St) (oldE newE : Expr 14)
    (c : DomainId) (l : LineageId) :
    ((Hw.reparentA oldE newE).run σ acc).regs (Hw.dcellPar c l) 14 =
      if (Expr.and (.reg 1 (Hw.dcellV c l))
          (Expr.eq (.reg 14 (Hw.dcellPar c l)) oldE)).eval σ = 1#1 then
        newE.eval σ else acc.regs (Hw.dcellPar c l) 14 := by
  let cells : List (DomainId × LineageId) :=
    (List.finRange numDomains).product (List.finRange numLineage)
  have hacts :
      cells.map (fun p => Act.ite
        (.and (.reg 1 (Hw.dcellV p.1 p.2))
          (.eq (.reg 14 (Hw.dcellPar p.1 p.2)) oldE))
        (.write 14 (Hw.dcellPar p.1 p.2) newE) .skip) =
      (List.finRange numDomains).flatMap fun c' =>
        (List.finRange numLineage).map fun l' =>
          Act.ite (.and (.reg 1 (Hw.dcellV c' l'))
            (.eq (.reg 14 (Hw.dcellPar c' l')) oldE))
            (.write 14 (Hw.dcellPar c' l') newE) .skip := by
    rfl
  unfold Hw.reparentA
  rw [← hacts]
  apply seqAll_ite_write_at σ acc
    (fun p : DomainId × LineageId =>
      Expr.and (.reg 1 (Hw.dcellV p.1 p.2))
        (Expr.eq (.reg 14 (Hw.dcellPar p.1 p.2)) oldE))
    (fun p => Hw.dcellPar p.1 p.2) (fun _ => newE) cells (c, l)
  · simp [cells, List.product, List.mem_flatMap]
  · dsimp only [cells]
    decide +kernel
  · intro a _ b _ hab
    rcases a with ⟨ca, la⟩
    rcases b with ⟨cb, lb⟩
    have h := ((by native_decide +revert : ∀ (ca cb : DomainId)
      (la lb : LineageId), Hw.dcellPar ca la = Hw.dcellPar cb lb →
        ca = cb ∧ la = lb) ca cb la lb hab)
    exact Prod.ext h.1 h.2

/-- `reparentA` frames every register outside the lineage-parent bank. -/
theorem reparentA_frame (σ acc : Loom.Hw.St) (oldE newE : Expr 14)
    (q : String) (qW : Nat)
    (hne : ∀ c : DomainId, ∀ l : LineageId, q ≠ Hw.dcellPar c l) :
    ((Hw.reparentA oldE newE).run σ acc).regs q qW = acc.regs q qW := by
  let cells : List (DomainId × LineageId) :=
    (List.finRange numDomains).product (List.finRange numLineage)
  have hacts :
      cells.map (fun p => Act.ite
        (.and (.reg 1 (Hw.dcellV p.1 p.2))
          (.eq (.reg 14 (Hw.dcellPar p.1 p.2)) oldE))
        (.write 14 (Hw.dcellPar p.1 p.2) newE) .skip) =
      (List.finRange numDomains).flatMap fun c' =>
        (List.finRange numLineage).map fun l' =>
          Act.ite (.and (.reg 1 (Hw.dcellV c' l'))
            (.eq (.reg 14 (Hw.dcellPar c' l')) oldE))
            (.write 14 (Hw.dcellPar c' l') newE) .skip := by
    rfl
  unfold Hw.reparentA
  rw [← hacts]
  apply seqAll_ite_write_frame
  intro p _
  exact hne p.1 p.2

private abbrev OrphanIx :=
  Sum (DomainId × LineageId) (DomainId × Slot)

private def orphanIndices : List OrphanIx :=
  (List.finRange numDomains).flatMap fun c =>
    ((List.finRange numLineage).map fun l => Sum.inl (c, l)) ++
    ((List.finRange numSlots).map fun s => Sum.inr (c, s))

private def orphanCond (oldE : Expr 14) : OrphanIx → Expr 1
  | .inl (c, l) =>
      .and (.reg 1 (Hw.dcellV c l))
        (.eq (.reg 14 (Hw.dcellPar c l)) oldE)
  | .inr (c, s) =>
      Hw.andAll [.reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
        Hw.muxFin (fun l => .and (.reg 1 (Hw.dcellV c l))
          (.eq (.reg 14 (Hw.dcellPar c l)) oldE))
          (.reg 4 (Hw.dcapLin c s))]

private def orphanRn : OrphanIx → String
  | .inl (c, l) => Hw.dcellV c l
  | .inr (c, s) => Hw.dcapLinV c s

private theorem orphan_actions (oldE : Expr 14) :
    orphanIndices.map (fun i => Act.ite (orphanCond oldE i)
      (.write 1 (orphanRn i) (.lit 0)) .skip) =
    (List.finRange numDomains).flatMap fun c =>
      ((List.finRange numLineage).map fun l =>
        Act.ite (.and (.reg 1 (Hw.dcellV c l))
          (.eq (.reg 14 (Hw.dcellPar c l)) oldE))
          (.write 1 (Hw.dcellV c l) (.lit 0)) .skip) ++
      ((List.finRange numSlots).map fun s =>
        Act.ite (Hw.andAll [.reg 1 (Hw.dcapV c s),
          .reg 1 (Hw.dcapLinV c s),
          Hw.muxFin (fun l => .and (.reg 1 (Hw.dcellV c l))
            (.eq (.reg 14 (Hw.dcellPar c l)) oldE))
            (.reg 4 (Hw.dcapLin c s))])
          (.write 1 (Hw.dcapLinV c s) (.lit 0)) .skip) := by
  simp [orphanIndices, orphanCond, orphanRn, List.map_flatMap,
    Function.comp_def]

/-- The two-part orphan walk has uniform pointwise guarded-write
semantics over both register banks. -/
private theorem orphanA_at (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (i : OrphanIx) (hi : i ∈ orphanIndices) :
    ((Hw.orphanA oldE).run σ acc).regs (orphanRn i) 1 =
      if (orphanCond oldE i).eval σ = 1#1 then 0#1
      else acc.regs (orphanRn i) 1 := by
  simp only [Hw.orphanA]
  rw [← orphan_actions]
  apply seqAll_ite_write_at σ acc (orphanCond oldE) orphanRn
    (fun _ => (.lit 0 : Expr 1)) orphanIndices i hi
  · decide +kernel
  · intro a _ b _ hab
    rcases a with ⟨ca, la⟩ | ⟨ca, sa⟩ <;>
      rcases b with ⟨cb, lb⟩ | ⟨cb, sb⟩
    · have h := ((by native_decide +revert : ∀ (ca cb : DomainId)
        (la lb : LineageId), Hw.dcellV ca la = Hw.dcellV cb lb →
          ca = cb ∧ la = lb) ca cb la lb hab)
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · exact absurd hab ((by native_decide +revert : ∀ (ca cb : DomainId)
        (la : LineageId) (sb : Slot),
          Hw.dcellV ca la ≠ Hw.dcapLinV cb sb) ca cb la sb)
    · exact absurd hab ((by native_decide +revert : ∀ (ca cb : DomainId)
        (sa : Slot) (lb : LineageId),
          Hw.dcapLinV ca sa ≠ Hw.dcellV cb lb) ca cb sa lb)
    · have h := ((by native_decide +revert : ∀ (ca cb : DomainId)
        (sa sb : Slot), Hw.dcapLinV ca sa = Hw.dcapLinV cb sb →
          ca = cb ∧ sa = sb) ca cb sa sb hab)
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- `orphanA` clears a lineage cell exactly when it is a live child of
the removed reference. -/
theorem orphanA_cellV (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (c : DomainId) (l : LineageId) :
    ((Hw.orphanA oldE).run σ acc).regs (Hw.dcellV c l) 1 =
      if (Expr.and (.reg 1 (Hw.dcellV c l))
          (Expr.eq (.reg 14 (Hw.dcellPar c l)) oldE)).eval σ = 1#1 then
        0#1 else acc.regs (Hw.dcellV c l) 1 := by
  exact orphanA_at σ acc oldE (.inl (c, l)) (by
    simp [orphanIndices, List.mem_flatMap])

/-- `orphanA` clears an entry's lineage-valid bit exactly when its
selected cell is a child being orphaned. -/
theorem orphanA_capLinV (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (c : DomainId) (s : Slot) :
    ((Hw.orphanA oldE).run σ acc).regs (Hw.dcapLinV c s) 1 =
      if (Hw.andAll [.reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
          Hw.muxFin (fun l => .and (.reg 1 (Hw.dcellV c l))
            (.eq (.reg 14 (Hw.dcellPar c l)) oldE))
            (.reg 4 (Hw.dcapLin c s))]).eval σ = 1#1 then
        0#1 else acc.regs (Hw.dcapLinV c s) 1 := by
  exact orphanA_at σ acc oldE (.inr (c, s)) (by
    simp [orphanIndices, List.mem_flatMap])

/-- `orphanA` frames every register outside its two valid-bit banks. -/
theorem orphanA_frame (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (q : String) (qW : Nat)
    (hcell : ∀ c : DomainId, ∀ l : LineageId, q ≠ Hw.dcellV c l)
    (hcap : ∀ c : DomainId, ∀ s : Slot, q ≠ Hw.dcapLinV c s) :
    ((Hw.orphanA oldE).run σ acc).regs q qW = acc.regs q qW := by
  simp only [Hw.orphanA]
  rw [← orphan_actions]
  apply seqAll_ite_write_frame
  intro i _
  rcases i with ⟨c, l⟩ | ⟨c, s⟩
  · exact hcell c l
  · exact hcap c s

/-! ## Region-sweep hardware walk -/

private def regionIndices : List (DomainId × RegionId) :=
  (List.finRange numDomains).product (List.finRange numRegions)

private def regionKillCond
    (killed : Expr 2 → Expr 4 → Expr 1) (i : DomainId × RegionId) : Expr 1 :=
  let rg : Expr 42 := .reg 42 (Hw.drgn i.1 i.2)
  .and (.reg 1 (Hw.drgnV i.1 i.2))
    (killed (Hw.field rg 40 2) (Hw.field rg 36 4))

private theorem sweepRegions_actions
    (killed : Expr 2 → Expr 4 → Expr 1) :
    regionIndices.map (fun i => Act.ite (regionKillCond killed i)
      (.write 1 (Hw.drgnV i.1 i.2) (.lit 0)) .skip) =
      (List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          let rg : Expr 42 := .reg 42 (Hw.drgn c r)
          Act.ite (.and (.reg 1 (Hw.drgnV c r))
            (killed (Hw.field rg 40 2) (Hw.field rg 36 4)))
            (.write 1 (Hw.drgnV c r) (.lit 0)) .skip := by
  rfl

/-- The sweep walk clears exactly a region-valid bit whose pre-cycle
backing is killed. -/
theorem sweepRegionsA_rgnV (σ acc : Loom.Hw.St)
    (killed : Expr 2 → Expr 4 → Expr 1) (c : DomainId) (r : RegionId) :
    ((Hw.sweepRegionsA killed).run σ acc).regs (Hw.drgnV c r) 1 =
      if (regionKillCond killed (c, r)).eval σ = 1#1 then 0#1
      else acc.regs (Hw.drgnV c r) 1 := by
  unfold Hw.sweepRegionsA
  rw [← sweepRegions_actions]
  apply seqAll_ite_write_at σ acc (regionKillCond killed)
    (fun i => Hw.drgnV i.1 i.2) (fun _ => (.lit 0 : Expr 1))
    regionIndices (c, r)
  · simp [regionIndices]
  · decide +kernel
  · intro a _ b _ hab
    have h := ((by native_decide +revert : ∀ (ca cb : DomainId)
      (ra rb : RegionId), Hw.drgnV ca ra = Hw.drgnV cb rb →
        ca = cb ∧ ra = rb) a.1 b.1 a.2 b.2 hab)
    exact Prod.ext h.1 h.2

/-- The sweep walk frames every register outside the region-valid bank. -/
theorem sweepRegionsA_frame (σ acc : Loom.Hw.St)
    (killed : Expr 2 → Expr 4 → Expr 1) (q : String) (qW : Nat)
    (hne : ∀ c : DomainId, ∀ r : RegionId, q ≠ Hw.drgnV c r) :
    ((Hw.sweepRegionsA killed).run σ acc).regs q qW = acc.regs q qW := by
  unfold Hw.sweepRegionsA
  rw [← sweepRegions_actions]
  apply seqAll_ite_write_frame
  intro i _
  exact hne i.1 i.2

/-- In particular, the packed region payload is unchanged by the valid-bit
sweep. -/
theorem sweepRegionsA_rgn (σ acc : Loom.Hw.St)
    (killed : Expr 2 → Expr 4 → Expr 1) (c : DomainId) (r : RegionId) :
    ((Hw.sweepRegionsA killed).run σ acc).regs (Hw.drgn c r) 42 =
      acc.regs (Hw.drgn c r) 42 := by
  apply sweepRegionsA_frame
  intro c' r'
  exact ((by native_decide +revert : ∀ (c c' : DomainId) (r r' : RegionId),
    Hw.drgn c r ≠ Hw.drgnV c' r') c c' r r')

/-! ## Structural abstraction bridges -/

theorem domainState_ext {a b : DomainState}
    (hregs : a.regs = b.regs) (hpc : a.pc = b.pc)
    (hcaps : a.caps = b.caps) (hgen : a.slotGen = b.slotGen)
    (hlin : a.lineage = b.lineage) (hrgn : a.regions = b.regions)
    (hrun : a.run = b.run) (hsrv : a.serving = b.serving)
    (hcause : a.cause = b.cause) (hbud : a.budget = b.budget)
    (hmax : a.maxDonation = b.maxDonation) : a = b := by
  cases a
  cases b
  simp_all

theorem machineState_ext {a b : MachineState}
    (hcycle : a.cycle = b.cycle) (hmem : a.mem = b.mem)
    (hdoms : a.doms = b.doms) (hgates : a.gates = b.gates)
    (hmover : a.mover = b.mover) (hif : a.inflight = b.inflight) : a = b := by
  cases a
  cases b
  simp_all

/-- The hardware reparent walk decodes to the spec reparent operation on
each lineage-table entry, provided the accumulator still carries the
pre-cycle lineage bank. -/
theorem abs_reparentA_lineage (σ acc : Loom.Hw.St) (oldE newE : Expr 14)
    (c : DomainId) (l : LineageId)
    (hV : acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14) :
    ((Hw.abs ((Hw.reparentA oldE newE).run σ acc)).doms c).lineage l =
      (((Hw.abs acc).reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))).doms c).lineage l := by
  rw [reparent_lineage]
  change (if ((Hw.reparentA oldE newE).run σ acc).regs
      (Hw.dcellV c l) 1 = 1#1 then
      some (⟨Hw.decRef (((Hw.reparentA oldE newE).run σ acc).regs
        (Hw.dcellPar c l) 14)⟩ : LineageCell) else none) =
    match (if acc.regs (Hw.dcellV c l) 1 = 1#1 then
      some (⟨Hw.decRef (acc.regs (Hw.dcellPar c l) 14)⟩ : LineageCell) else none) with
    | some cell => some (if cell.parent = Hw.decRef (oldE.eval σ) then
        { parent := Hw.decRef (newE.eval σ) } else cell)
    | none => none
  rw [reparentA_frame σ acc oldE newE (Hw.dcellV c l) 1
    (fun c' l' => by
      clear * - c l c' l'
      revert c l c' l'
      native_decide), hV,
    reparentA_cellPar σ acc oldE newE c l]
  by_cases hv : σ.regs (Hw.dcellV c l) 1 = 1#1
  · rw [if_pos hv]
    rw [hP]
    by_cases hp : σ.regs (Hw.dcellPar c l) 14 = oldE.eval σ
    · simp [Expr.eval, hv, hp]
    · have hp' : oldE.eval σ ≠ σ.regs (Hw.dcellPar c l) 14 :=
        fun h => hp h.symm
      have hdec : Hw.decRef (σ.regs (Hw.dcellPar c l) 14) ≠
          Hw.decRef (oldE.eval σ) := by
        intro h
        apply hp
        rw [← encRef_decRef (σ.regs (Hw.dcellPar c l) 14), h,
          encRef_decRef]
      simp [Expr.eval, hv, hp, hp', hdec]
  · rw [if_neg hv]
    simp [Expr.eval, hv]

/-- Reparenting does not change decoded capability entries. -/
theorem abs_reparentA_caps (σ acc : Loom.Hw.St) (oldE newE : Expr 14)
    (c : DomainId) (s : Slot) :
    ((Hw.abs ((Hw.reparentA oldE newE).run σ acc)).doms c).caps s =
      (((Hw.abs acc).reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))).doms c).caps s := by
  rw [reparent_caps]
  change (if ((Hw.reparentA oldE newE).run σ acc).regs
      (Hw.dcapV c s) 1 = 1#1 then
      some ({
        kind := Hw.decKind (((Hw.reparentA oldE newE).run σ acc).regs
          (Hw.dcapKind c s) 32)
        lineage := if ((Hw.reparentA oldE newE).run σ acc).regs
            (Hw.dcapLinV c s) 1 = 1#1 then
          some (finOfBv (by decide) (((Hw.reparentA oldE newE).run σ acc).regs
            (Hw.dcapLin c s) 4)) else none
      } : CapEntry) else none) = _
  rw [reparentA_frame σ acc oldE newE (Hw.dcapV c s) 1
      (fun c' l' => by
      clear * - c s c' l'
      revert c s c' l'
      native_decide),
    reparentA_frame σ acc oldE newE (Hw.dcapKind c s) 32
      (fun c' l' => by
      clear * - c s c' l'
      revert c s c' l'
      native_decide),
    reparentA_frame σ acc oldE newE (Hw.dcapLinV c s) 1
      (fun c' l' => by
      clear * - c s c' l'
      revert c s c' l'
      native_decide),
    reparentA_frame σ acc oldE newE (Hw.dcapLin c s) 4
      (fun c' l' => by
      clear * - c s c' l'
      revert c s c' l'
      native_decide)]
  rfl

/-- Reparenting does not change decoded slot generations. -/
theorem abs_reparentA_slotGen (σ acc : Loom.Hw.St) (oldE newE : Expr 14)
    (c : DomainId) (s : Slot) :
    ((Hw.abs ((Hw.reparentA oldE newE).run σ acc)).doms c).slotGen s =
      (((Hw.abs acc).reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))).doms c).slotGen s := by
  rw [reparent_slotGen]
  change ((Hw.reparentA oldE newE).run σ acc).regs (Hw.dgen c s) 8 = _
  exact reparentA_frame σ acc oldE newE (Hw.dgen c s) 8
    (fun c' l' => by
      clear * - c s c' l'
      revert c s c' l'
      native_decide)

/-- Whole-domain abstraction of `reparentA`. -/
theorem absDom_reparentA (σ acc : Loom.Hw.St) (oldE newE : Expr 14)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (c : DomainId) :
    Hw.absDom ((Hw.reparentA oldE newE).run σ acc) c =
      (((Hw.abs acc).reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))).doms c) := by
  unfold MachineState.reparent
  dsimp only
  apply domainState_ext
  · funext r
    exact reparentA_frame σ acc oldE newE (Hw.dreg c r) 32
      (fun c' l' => by
      clear * - c r c' l'
      revert c r c' l'
      native_decide)
  · exact reparentA_frame σ acc oldE newE (Hw.dpc c) 12
      (fun c' l' => by
      clear * - c c' l'
      revert c c' l'
      native_decide)
  · funext s
    exact abs_reparentA_caps σ acc oldE newE c s
  · funext s
    exact abs_reparentA_slotGen σ acc oldE newE c s
  · funext l
    exact abs_reparentA_lineage σ acc oldE newE c l (hV c l) (hP c l)
  · funext r
    change (if ((Hw.reparentA oldE newE).run σ acc).regs
        (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (((Hw.reparentA oldE newE).run σ acc).regs
        (Hw.drgn c r) 42)) else none) = _
    rw [reparentA_frame σ acc oldE newE (Hw.drgnV c r) 1
        (fun c' l' => by
      clear * - c r c' l'
      revert c r c' l'
      native_decide),
      reparentA_frame σ acc oldE newE (Hw.drgn c r) 42
        (fun c' l' => by
      clear * - c r c' l'
      revert c r c' l'
      native_decide)]
    rfl
  · change Hw.decRun (((Hw.reparentA oldE newE).run σ acc).regs
      (Hw.drun c) 2) (((Hw.reparentA oldE newE).run σ acc).regs
      (Hw.drunG c) 2) = _
    rw [reparentA_frame σ acc oldE newE (Hw.drun c) 2
        (fun c' l' => by
      clear * - c c' l'
      revert c c' l'
      native_decide),
      reparentA_frame σ acc oldE newE (Hw.drunG c) 2
        (fun c' l' => by
      clear * - c c' l'
      revert c c' l'
      native_decide)]
    rfl
  · change (if ((Hw.reparentA oldE newE).run σ acc).regs
      (Hw.dsrvV c) 1 = 1#1 then
      some (finOfBv (by decide) (((Hw.reparentA oldE newE).run σ acc).regs
        (Hw.dsrv c) 2)) else none) = _
    rw [reparentA_frame σ acc oldE newE (Hw.dsrvV c) 1
        (fun c' l' => by
      clear * - c c' l'
      revert c c' l'
      native_decide),
      reparentA_frame σ acc oldE newE (Hw.dsrv c) 2
        (fun c' l' => by
      clear * - c c' l'
      revert c c' l'
      native_decide)]
    rfl
  · exact reparentA_frame σ acc oldE newE (Hw.dcause c) 32
      (fun c' l' => by
      clear * - c c' l'
      revert c c' l'
      native_decide)
  · change (((Hw.reparentA oldE newE).run σ acc).regs
      (Hw.dbudget c) 32).toNat = _
    rw [reparentA_frame σ acc oldE newE (Hw.dbudget c) 32
      (fun c' l' => by
      clear * - c c' l'
      revert c c' l'
      native_decide)]
    rfl
  · change (((Hw.reparentA oldE newE).run σ acc).regs
      (Hw.dmaxdon c) 32).toNat = _
    rw [reparentA_frame σ acc oldE newE (Hw.dmaxdon c) 32
      (fun c' l' => by
      clear * - c c' l'
      revert c c' l'
      native_decide)]
    rfl

/-- The lineage-valid half of `orphanA` decodes to the spec's removal of
child cells. -/
theorem abs_orphanA_lineage (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (c : DomainId) (l : LineageId)
    (hV : acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14) :
    ((Hw.abs ((Hw.orphanA oldE).run σ acc)).doms c).lineage l =
      (((Hw.abs acc).orphanChildren (Hw.decRef (oldE.eval σ))).doms c).lineage l := by
  rw [orphanChildren_lineage]
  change (if ((Hw.orphanA oldE).run σ acc).regs
      (Hw.dcellV c l) 1 = 1#1 then
      some (⟨Hw.decRef (((Hw.orphanA oldE).run σ acc).regs
        (Hw.dcellPar c l) 14)⟩ : LineageCell) else none) =
    if (match (if acc.regs (Hw.dcellV c l) 1 = 1#1 then
        some (⟨Hw.decRef (acc.regs (Hw.dcellPar c l) 14)⟩ : LineageCell)
          else none) with
      | some cell => decide (cell.parent = Hw.decRef (oldE.eval σ))
      | none => false) then none
    else (if acc.regs (Hw.dcellV c l) 1 = 1#1 then
      some (⟨Hw.decRef (acc.regs (Hw.dcellPar c l) 14)⟩ : LineageCell) else none)
  rw [orphanA_cellV σ acc oldE c l,
    orphanA_frame σ acc oldE (Hw.dcellPar c l) 14
      (fun c' l' => by
        clear * - c l c' l'
        revert c l c' l'
        native_decide)
      (fun c' s' => by
        clear * - c l c' s'
        revert c l c' s'
        native_decide), hP]
  by_cases hv : σ.regs (Hw.dcellV c l) 1 = 1#1
  · have hva : acc.regs (Hw.dcellV c l) 1 = 1#1 := hV.trans hv
    by_cases hp : σ.regs (Hw.dcellPar c l) 14 = oldE.eval σ
    · simp [Expr.eval, hv, hva, hP, hp]
    · have hp' : oldE.eval σ ≠ σ.regs (Hw.dcellPar c l) 14 :=
        fun h => hp h.symm
      have hdec : Hw.decRef (σ.regs (Hw.dcellPar c l) 14) ≠
          Hw.decRef (oldE.eval σ) := by
        intro h
        apply hp
        rw [← encRef_decRef (σ.regs (Hw.dcellPar c l) 14), h,
          encRef_decRef]
      simp [Expr.eval, hv, hva, hP, hp, hp', hdec]
  · have hva : acc.regs (Hw.dcellV c l) 1 ≠ 1#1 := fun h => hv (hV ▸ h)
    have hv0 : σ.regs (Hw.dcellV c l) 1 = 0#1 := bv1_ne_one.mp hv
    by_cases hp : σ.regs (Hw.dcellPar c l) 14 = oldE.eval σ <;>
      simp [Expr.eval, hv0, hva, hp]

/-- Decode the entry-side orphan guard to the selected lineage cell. -/
theorem orphan_cap_guard_iff (σ : Loom.Hw.St) (oldE : Expr 14)
    (c : DomainId) (s : Slot) :
    ((Hw.andAll [.reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
        Hw.muxFin (fun l => .and (.reg 1 (Hw.dcellV c l))
          (.eq (.reg 14 (Hw.dcellPar c l)) oldE))
          (.reg 4 (Hw.dcapLin c s))]).eval σ = 1#1) ↔
      σ.regs (Hw.dcapV c s) 1 = 1#1 ∧
      σ.regs (Hw.dcapLinV c s) 1 = 1#1 ∧
      let l : LineageId := finOfBv
        (by decide : 2 ^ 4 = numLineage) (σ.regs (Hw.dcapLin c s) 4)
      σ.regs (Hw.dcellV c l) 1 = 1#1 ∧
      σ.regs (Hw.dcellPar c l) 14 = oldE.eval σ := by
  rw [andAll_eval]
  simp only [List.forall_mem_cons, List.forall_mem_nil]
  rw [muxFin_eval (n := numLineage) (iw := 4) (w := 1)
    (by decide : 2 ^ 4 = numLineage)]
  simp only [Expr.eval]
  simp only [List.mem_nil_iff, false_implies, forall_const, and_true]
  have hforall : (∀ _ : Expr 1, True) ↔ True :=
    ⟨fun _ => trivial, fun _ _ => trivial⟩
  simp only [hforall, and_true]
  let l : LineageId := finOfBv
    (by decide : 2 ^ 4 = numLineage) (σ.regs (Hw.dcapLin c s) 4)
  change (σ.regs (Hw.dcapV c s) 1 = 1#1 ∧
    σ.regs (Hw.dcapLinV c s) 1 = 1#1 ∧
    (σ.regs (Hw.dcellV c l) 1 &&&
      (if σ.regs (Hw.dcellPar c l) 14 = oldE.eval σ then 1#1 else 0#1) =
        1#1)) ↔ _
  rw [bv1_and_eq_one]
  constructor
  · rintro ⟨hv, hlv, hcv, hp⟩
    refine ⟨hv, hlv, ?_, ?_⟩
    · simpa [l] using hcv
    · simpa [l] using hp
  · rintro ⟨hv, hlv, hcv, hp⟩
    refine ⟨hv, hlv, ?_, ?_⟩
    · simpa [l] using hcv
    · simpa [l] using hp

/-- The capability-lineage half of `orphanA` decodes to the spec's
lineage-link removal. -/
theorem abs_orphanA_caps (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (c : DomainId) (s : Slot)
    (hcapV : acc.regs (Hw.dcapV c s) 1 = σ.regs (Hw.dcapV c s) 1)
    (hlinV : acc.regs (Hw.dcapLinV c s) 1 = σ.regs (Hw.dcapLinV c s) 1)
    (hlin : acc.regs (Hw.dcapLin c s) 4 = σ.regs (Hw.dcapLin c s) 4)
    (hcellV : ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hcellP : ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14) :
    ((Hw.abs ((Hw.orphanA oldE).run σ acc)).doms c).caps s =
      (((Hw.abs acc).orphanChildren (Hw.decRef (oldE.eval σ))).doms c).caps s := by
  rw [orphanChildren_caps]
  let guard := Hw.andAll [.reg 1 (Hw.dcapV c s),
    .reg 1 (Hw.dcapLinV c s),
    Hw.muxFin (fun l => .and (.reg 1 (Hw.dcellV c l))
      (.eq (.reg 14 (Hw.dcellPar c l)) oldE))
      (.reg 4 (Hw.dcapLin c s))]
  have hV := orphanA_frame σ acc oldE (Hw.dcapV c s) 1
    (fun c' l' => by
      clear * - c s c' l'
      revert c s c' l'
      native_decide)
    (fun c' s' => by
      clear * - c s c' s'
      revert c s c' s'
      native_decide)
  have hK := orphanA_frame σ acc oldE (Hw.dcapKind c s) 32
    (fun c' l' => by
      clear * - c s c' l'
      revert c s c' l'
      native_decide)
    (fun c' s' => by
      clear * - c s c' s'
      revert c s c' s'
      native_decide)
  have hL := orphanA_frame σ acc oldE (Hw.dcapLin c s) 4
    (fun c' l' => by
      clear * - c s c' l'
      revert c s c' l'
      native_decide)
    (fun c' s' => by
      clear * - c s c' s'
      revert c s c' s'
      native_decide)
  have hLV := orphanA_capLinV σ acc oldE c s
  change (if ((Hw.orphanA oldE).run σ acc).regs (Hw.dcapV c s) 1 = 1#1
    then some ({
      kind := Hw.decKind (((Hw.orphanA oldE).run σ acc).regs
        (Hw.dcapKind c s) 32)
      lineage := if ((Hw.orphanA oldE).run σ acc).regs
          (Hw.dcapLinV c s) 1 = 1#1 then
        some (finOfBv (by decide) (((Hw.orphanA oldE).run σ acc).regs
          (Hw.dcapLin c s) 4)) else none
    } : CapEntry) else none) = _
  rw [hV, hK, hL]
  rw [show ((Hw.orphanA oldE).run σ acc).regs (Hw.dcapLinV c s) 1 =
      if guard.eval σ = 1#1 then 0#1
      else acc.regs (Hw.dcapLinV c s) 1 from hLV]
  have hbase : ((Hw.abs acc).doms c).caps s =
      if acc.regs (Hw.dcapV c s) 1 = 1#1 then
        some ({
          kind := Hw.decKind (acc.regs (Hw.dcapKind c s) 32)
          lineage := if acc.regs (Hw.dcapLinV c s) 1 = 1#1 then
            some (finOfBv (by decide : 2 ^ 4 = numLineage)
              (acc.regs (Hw.dcapLin c s) 4))
          else none
        } : CapEntry)
      else none := rfl
  rw [hbase]
  by_cases hv : acc.regs (Hw.dcapV c s) 1 = 1#1
  · rw [if_pos hv]
    have hvs : σ.regs (Hw.dcapV c s) 1 = 1#1 := hcapV.symm.trans hv
    by_cases hlv : acc.regs (Hw.dcapLinV c s) 1 = 1#1
    · have hlvs : σ.regs (Hw.dcapLinV c s) 1 = 1#1 := hlinV.symm.trans hlv
      let l : LineageId := finOfBv
        (by decide : 2 ^ 4 = numLineage) (acc.regs (Hw.dcapLin c s) 4)
      have hcell : ((Hw.abs acc).doms c).lineage l =
          if acc.regs (Hw.dcellV c l) 1 = 1#1 then
            some (⟨Hw.decRef (acc.regs (Hw.dcellPar c l) 14)⟩ : LineageCell)
          else none := rfl
      have hls : finOfBv (by decide : 2 ^ 4 = numLineage)
          (σ.regs (Hw.dcapLin c s) 4) = l := by
        rw [← hlin]
      by_cases hcV : acc.regs (Hw.dcellV c l) 1 = 1#1
      · have hcVs : σ.regs (Hw.dcellV c l) 1 = 1#1 :=
          (hcellV l).symm.trans hcV
        by_cases hp : Hw.decRef (acc.regs (Hw.dcellPar c l) 14) =
            Hw.decRef (oldE.eval σ)
        · have hpw : σ.regs (Hw.dcellPar c l) 14 = oldE.eval σ := by
            rw [← hcellP l, ← encRef_decRef
              (acc.regs (Hw.dcellPar c l) 14), hp, encRef_decRef]
          have hg : guard.eval σ = 1#1 :=
            (orphan_cap_guard_iff σ oldE c s).2
              ⟨hvs, hlvs, by simpa [hls] using And.intro hcVs hpw⟩
          simp [guard, hv, hlv, hcV, hp, hg, hcell, l]
        · have hpw : σ.regs (Hw.dcellPar c l) 14 ≠ oldE.eval σ := by
            intro he
            apply hp
            rw [hcellP l, he]
          have hng : guard.eval σ ≠ 1#1 := by
            intro hg
            have := (orphan_cap_guard_iff σ oldE c s).1 hg
            exact hpw (by simpa [hls] using this.2.2.2)
          simp [guard, hv, hlv, hcV, hp, hng, hcell, l]
      · have hcVs : σ.regs (Hw.dcellV c l) 1 ≠ 1#1 := fun h =>
          hcV ((hcellV l).trans h)
        have hng : guard.eval σ ≠ 1#1 := by
          intro hg
          have := (orphan_cap_guard_iff σ oldE c s).1 hg
          exact hcVs (by simpa [hls] using this.2.2.1)
        simp [guard, hv, hlv, hcV, hng, hcell, l]
    · have hlvs : σ.regs (Hw.dcapLinV c s) 1 ≠ 1#1 := fun h =>
        hlv (hlinV.trans h)
      have hng : guard.eval σ ≠ 1#1 := by
        intro hg
        exact hlvs ((orphan_cap_guard_iff σ oldE c s).1 hg).2.1
      simp [guard, hv, hlv, hng]
  · have hvs : σ.regs (Hw.dcapV c s) 1 ≠ 1#1 := fun h =>
      hv (hcapV.trans h)
    have hng : guard.eval σ ≠ 1#1 := by
      intro hg
      exact hvs ((orphan_cap_guard_iff σ oldE c s).1 hg).1
    simp [guard, hv, hng]

/-- Orphaning does not change decoded slot generations. -/
theorem abs_orphanA_slotGen (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (c : DomainId) (s : Slot) :
    ((Hw.abs ((Hw.orphanA oldE).run σ acc)).doms c).slotGen s =
      (((Hw.abs acc).orphanChildren (Hw.decRef (oldE.eval σ))).doms c).slotGen s := by
  rw [orphanChildren_slotGen]
  change ((Hw.orphanA oldE).run σ acc).regs (Hw.dgen c s) 8 = _
  exact orphanA_frame σ acc oldE (Hw.dgen c s) 8
    (fun c' l' => (by native_decide +revert))
    (fun c' s' => (by native_decide +revert))

/-- Whole-domain abstraction of `orphanA`. -/
theorem absDom_orphanA (σ acc : Loom.Hw.St) (oldE : Expr 14)
    (hcapV : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dcapV c s) 1 = σ.regs (Hw.dcapV c s) 1)
    (hlinV : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dcapLinV c s) 1 = σ.regs (Hw.dcapLinV c s) 1)
    (hlin : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dcapLin c s) 4 = σ.regs (Hw.dcapLin c s) 4)
    (hcellV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hcellP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (c : DomainId) :
    Hw.absDom ((Hw.orphanA oldE).run σ acc) c =
      (((Hw.abs acc).orphanChildren (Hw.decRef (oldE.eval σ))).doms c) := by
  unfold MachineState.orphanChildren
  dsimp only
  apply domainState_ext
  · funext r
    exact orphanA_frame σ acc oldE (Hw.dreg c r) 32
      (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert))
  · exact orphanA_frame σ acc oldE (Hw.dpc c) 12
      (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert))
  · funext s
    exact abs_orphanA_caps σ acc oldE c s (hcapV c s) (hlinV c s)
      (hlin c s) (hcellV c) (hcellP c)
  · funext s
    exact abs_orphanA_slotGen σ acc oldE c s
  · funext l
    exact abs_orphanA_lineage σ acc oldE c l (hcellV c l) (hcellP c l)
  · funext r
    change (if ((Hw.orphanA oldE).run σ acc).regs
        (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (((Hw.orphanA oldE).run σ acc).regs
        (Hw.drgn c r) 42)) else none) = _
    rw [orphanA_frame σ acc oldE (Hw.drgnV c r) 1
        (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert)),
      orphanA_frame σ acc oldE (Hw.drgn c r) 42
        (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert))]
    rfl
  · change Hw.decRun (((Hw.orphanA oldE).run σ acc).regs
      (Hw.drun c) 2) (((Hw.orphanA oldE).run σ acc).regs
      (Hw.drunG c) 2) = _
    rw [orphanA_frame σ acc oldE (Hw.drun c) 2
        (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert)),
      orphanA_frame σ acc oldE (Hw.drunG c) 2
        (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert))]
    rfl
  · change (if ((Hw.orphanA oldE).run σ acc).regs
      (Hw.dsrvV c) 1 = 1#1 then
      some (finOfBv (by decide) (((Hw.orphanA oldE).run σ acc).regs
        (Hw.dsrv c) 2)) else none) = _
    rw [orphanA_frame σ acc oldE (Hw.dsrvV c) 1
        (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert)),
      orphanA_frame σ acc oldE (Hw.dsrv c) 2
        (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert))]
    rfl
  · exact orphanA_frame σ acc oldE (Hw.dcause c) 32
      (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert))
  · change (((Hw.orphanA oldE).run σ acc).regs (Hw.dbudget c) 32).toNat = _
    rw [orphanA_frame σ acc oldE (Hw.dbudget c) 32
      (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert))]
    rfl
  · change (((Hw.orphanA oldE).run σ acc).regs (Hw.dmaxdon c) 32).toNat = _
    rw [orphanA_frame σ acc oldE (Hw.dmaxdon c) 32
      (fun c' l' => (by native_decide +revert)) (fun c' s' => (by native_decide +revert))]
    rfl

/-- The capability-table face of `clearSlotA` decodes to spec
`clearSlot`. -/
theorem abs_clearSlotA_caps (σ acc : Loom.Hw.St) (d : DomainId)
    (S : Slot) (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (c : DomainId) (s : Slot) :
    ((Hw.abs ((Hw.clearSlotA d sE linVE linE).run σ acc)).doms c).caps s =
      (((Hw.abs acc).clearSlot d S).doms c).caps s := by
  rw [clearSlot_caps]
  by_cases hc : c = d
  · subst c
    change (if ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
        (Hw.dcapV d s) 1 = 1#1 then
      some ({
        kind := Hw.decKind (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
          (Hw.dcapKind d s) 32)
        lineage := if ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
            (Hw.dcapLinV d s) 1 = 1#1 then
          some (finOfBv (by decide) (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
            (Hw.dcapLin d s) 4)) else none
      } : CapEntry) else none) =
      if d = d ∧ s = S then none else _
    rw [clearSlotA_capV σ acc d S s sE linVE linE hslot,
      clearSlotA_frame σ acc d sE linVE linE (Hw.dcapKind d s) 32
        (fun s' => (by native_decide +revert)) (fun s' => (by native_decide +revert))
        (fun l' => (by native_decide +revert)),
      clearSlotA_frame σ acc d sE linVE linE (Hw.dcapLinV d s) 1
        (fun s' => (by native_decide +revert)) (fun s' => (by native_decide +revert))
        (fun l' => (by native_decide +revert)),
      clearSlotA_frame σ acc d sE linVE linE (Hw.dcapLin d s) 4
        (fun s' => (by native_decide +revert)) (fun s' => (by native_decide +revert))
        (fun l' => (by native_decide +revert))]
    by_cases hs : s = S <;> simp [hs] <;> rfl
  · rw [if_neg (fun h => hc h.1)]
    change (if ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
        (Hw.dcapV c s) 1 = 1#1 then
      some ({
        kind := Hw.decKind (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
          (Hw.dcapKind c s) 32)
        lineage := if ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
            (Hw.dcapLinV c s) 1 = 1#1 then
          some (finOfBv (by decide) (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
            (Hw.dcapLin c s) 4)) else none
      } : CapEntry) else none) = _
    rw [clearSlotA_frame σ acc d sE linVE linE (Hw.dcapV c s) 1
        (fun s' h => hc ((by native_decide +revert : Hw.dcapV c s = Hw.dcapV d s' → c = d) h))
        (fun s' => (by native_decide +revert)) (fun l' => (by native_decide +revert)),
      clearSlotA_frame σ acc d sE linVE linE (Hw.dcapKind c s) 32
        (fun s' => (by native_decide +revert)) (fun s' => (by native_decide +revert))
        (fun l' => (by native_decide +revert)),
      clearSlotA_frame σ acc d sE linVE linE (Hw.dcapLinV c s) 1
        (fun s' => (by native_decide +revert)) (fun s' => (by native_decide +revert))
        (fun l' => (by native_decide +revert)),
      clearSlotA_frame σ acc d sE linVE linE (Hw.dcapLin c s) 4
        (fun s' => (by native_decide +revert)) (fun s' => (by native_decide +revert))
        (fun l' => (by native_decide +revert))]
    rfl

/-- The generation face of `clearSlotA` decodes to spec `clearSlot`. -/
theorem abs_clearSlotA_slotGen (σ acc : Loom.Hw.St) (d : DomainId)
    (S : Slot) (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (hgen : acc.regs (Hw.dgen d S) 8 = σ.regs (Hw.dgen d S) 8)
    (c : DomainId) (s : Slot) :
    ((Hw.abs ((Hw.clearSlotA d sE linVE linE).run σ acc)).doms c).slotGen s =
      (((Hw.abs acc).clearSlot d S).doms c).slotGen s := by
  rw [clearSlot_slotGen]
  change ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.dgen c s) 8 =
    if c = d ∧ s = S then bumpGen (acc.regs (Hw.dgen d S) 8)
    else acc.regs (Hw.dgen c s) 8
  by_cases hc : c = d
  · subst c
    rw [clearSlotA_gen σ acc d S s sE linVE linE hslot]
    by_cases hs : s = S
    · subst s
      simp [hgen]
    · simp [hs]
  · rw [if_neg (fun h => hc h.1)]
    change ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.dgen c s) 8 = acc.regs (Hw.dgen c s) 8
    exact clearSlotA_frame σ acc d sE linVE linE (Hw.dgen c s) 8
      (fun s' => by
        clear * - c s d s'
        native_decide +revert)
      (fun s' h => hc ((by
        clear * - c s d s'
        native_decide +revert : Hw.dgen c s = Hw.dgen d s' → c = d) h))
      (fun l' => by
        clear * - c s d l'
        native_decide +revert)

/-- The lineage-table face of `clearSlotA`, parameterized by the decoded
removed cell carried by its two lineage selector expressions. -/
theorem abs_clearSlotA_lineage (σ acc : Loom.Hw.St) (d : DomainId)
    (S : Slot) (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (hremoved : removedCell (Hw.abs acc) d S =
      if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (linE.eval σ)) else none)
    (c : DomainId) (l : LineageId) :
    ((Hw.abs ((Hw.clearSlotA d sE linVE linE).run σ acc)).doms c).lineage l =
      (((Hw.abs acc).clearSlot d S).doms c).lineage l := by
  rw [clearSlot_lineage]
  change (if ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.dcellV c l) 1 = 1#1 then
      some (⟨Hw.decRef (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
        (Hw.dcellPar c l) 14)⟩ : LineageCell) else none) =
    if c = d ∧ removedCell (Hw.abs acc) d S = some l then none
    else if acc.regs (Hw.dcellV c l) 1 = 1#1 then
      some (⟨Hw.decRef (acc.regs (Hw.dcellPar c l) 14)⟩ : LineageCell)
    else none
  have hpar : ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.dcellPar c l) 14 = acc.regs (Hw.dcellPar c l) 14 :=
    clearSlotA_frame σ acc d sE linVE linE (Hw.dcellPar c l) 14
      (fun s' => by clear * - c l d s'; native_decide +revert)
      (fun s' => by clear * - c l d s'; native_decide +revert)
      (fun l' => by clear * - c l d l'; native_decide +revert)
  rw [hpar]
  by_cases hc : c = d
  · subst c
    by_cases hlv : linVE.eval σ = 1#1
    · let L : LineageId := finOfBv (by decide) (linE.eval σ)
      have hLval : finOfBv (by decide) (linE.eval σ) = L := rfl
      have hlin : linE.eval σ = BitVec.ofNat 4 L.val := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt (linE.eval σ).isLt).symm
      rw [clearSlotA_cellV_some σ acc d S L l sE linVE linE
        hslot hlv hlin, hremoved, if_pos hlv]
      by_cases hL : l = L
      · subst l
        simp [hLval]
      · have hL' : L ≠ l := fun h => hL h.symm
        simp [hLval, hL, hL']
    · have hlv0 : linVE.eval σ = 0#1 := bv1_ne_one.mp hlv
      rw [clearSlotA_cellV_none σ acc d S l sE linVE linE
        hslot hlv0, hremoved, if_neg hlv]
      simp
  · have hcd : ¬(c = d ∧ removedCell (Hw.abs acc) d S = some l) :=
      fun h => hc h.1
    rw [if_neg hcd]
    rw [clearSlotA_frame σ acc d sE linVE linE (Hw.dcellV c l) 1
        (fun s' => by clear * - c l d s'; native_decide +revert)
        (fun s' => by clear * - c l d s'; native_decide +revert)
        (fun l' h => hc ((by
          clear * - c l d l'
          native_decide +revert : Hw.dcellV c l = Hw.dcellV d l' → c = d) h))]

/-- Whole-domain abstraction of `clearSlotA`. -/
@[simp] theorem clearSlot_maxDonation (σ : MachineState) (d : DomainId)
    (s : Slot) (d' : DomainId) :
    ((σ.clearSlot d s).doms d').maxDonation = (σ.doms d').maxDonation := by
  unfold MachineState.clearSlot MachineState.setDom
  by_cases hd : d' = d
  · subst d'; simp [Loom.Fun.update_same]
  · simp [Loom.Fun.update_ne _ _ _ _ hd]

theorem absDom_clearSlotA (σ acc : Loom.Hw.St) (d : DomainId)
    (S : Slot) (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (hgen : acc.regs (Hw.dgen d S) 8 = σ.regs (Hw.dgen d S) 8)
    (hremoved : removedCell (Hw.abs acc) d S =
      if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (linE.eval σ)) else none)
    (c : DomainId) :
    Hw.absDom ((Hw.clearSlotA d sE linVE linE).run σ acc) c =
      (((Hw.abs acc).clearSlot d S).doms c) := by
  apply domainState_ext
  · rw [clearSlot_regs]
    funext r
    exact clearSlotA_frame σ acc d sE linVE linE (Hw.dreg c r) 32
      (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
      (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
  · rw [clearSlot_pc]
    exact clearSlotA_frame σ acc d sE linVE linE (Hw.dpc c) 12
      (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
      (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
  · funext s
    exact abs_clearSlotA_caps σ acc d S sE linVE linE hslot c s
  · funext s
    exact abs_clearSlotA_slotGen σ acc d S sE linVE linE hslot hgen c s
  · funext l
    exact abs_clearSlotA_lineage σ acc d S sE linVE linE hslot hremoved c l
  · rw [clearSlot_regions]
    funext r
    change (if ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
        (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
        (Hw.drgn c r) 42)) else none) = _
    rw [clearSlotA_frame σ acc d sE linVE linE (Hw.drgnV c r) 1
        (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
        (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)),
      clearSlotA_frame σ acc d sE linVE linE (Hw.drgn c r) 42
        (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
        (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))]
    rfl
  · rw [clearSlot_run]
    change Hw.decRun (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.drun c) 2) (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.drunG c) 2) = _
    rw [clearSlotA_frame σ acc d sE linVE linE (Hw.drun c) 2
        (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
        (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)),
      clearSlotA_frame σ acc d sE linVE linE (Hw.drunG c) 2
        (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
        (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))]
    rfl
  · rw [clearSlot_serving]
    change (if ((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.dsrvV c) 1 = 1#1 then
      some (finOfBv (by decide) (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
        (Hw.dsrv c) 2)) else none) = _
    rw [clearSlotA_frame σ acc d sE linVE linE (Hw.dsrvV c) 1
        (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
        (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)),
      clearSlotA_frame σ acc d sE linVE linE (Hw.dsrv c) 2
        (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
        (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))]
    rfl
  · rw [clearSlot_cause]
    exact clearSlotA_frame σ acc d sE linVE linE (Hw.dcause c) 32
      (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
      (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
  · rw [clearSlot_budget]
    change (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.dbudget c) 32).toNat = _
    rw [clearSlotA_frame σ acc d sE linVE linE (Hw.dbudget c) 32
      (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
      (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))]
    rfl
  · change (((Hw.clearSlotA d sE linVE linE).run σ acc).regs
      (Hw.dmaxdon c) 32).toNat = _
    rw [clearSlot_maxDonation]
    rw [clearSlotA_frame σ acc d sE linVE linE (Hw.dmaxdon c) 32
      (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert)) (fun s' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))
      (fun l' => (by clear hslot hgen hremoved σ acc S sE linVE linE; native_decide +revert))]
    rfl

/-- Composition of the derived-entry structural branch: reparent children,
then clear the dropped slot. -/
theorem absDom_reparent_clearSlotA (σ acc : Loom.Hw.St)
    (oldE newE : Expr 14) (d : DomainId) (S : Slot)
    (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (hgen : acc.regs (Hw.dgen d S) 8 = σ.regs (Hw.dgen d S) 8)
    (hremoved : removedCell
      ((Hw.abs acc).reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))) d S =
      if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (linE.eval σ)) else none)
    (c : DomainId) :
    Hw.absDom ((Hw.clearSlotA d sE linVE linE).run σ
      ((Hw.reparentA oldE newE).run σ acc)) c =
      (((Hw.abs acc).reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))).clearSlot d S).doms c := by
  let acc1 := (Hw.reparentA oldE newE).run σ acc
  have hdoms : (Hw.abs acc1).doms =
      ((Hw.abs acc).reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))).doms := by
    funext c'
    exact absDom_reparentA σ acc oldE newE hV hP c'
  have hgen1 : acc1.regs (Hw.dgen d S) 8 = σ.regs (Hw.dgen d S) 8 := by
    rw [reparentA_frame σ acc oldE newE (Hw.dgen d S) 8
      (fun c' l' => by clear * - d S c' l'; native_decide +revert), hgen]
  have hremoved1 : removedCell (Hw.abs acc1) d S =
      if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (linE.eval σ)) else none := by
    unfold removedCell
    rw [congrFun hdoms d]
    exact hremoved
  rw [show (Hw.clearSlotA d sE linVE linE).run σ
      ((Hw.reparentA oldE newE).run σ acc) =
      (Hw.clearSlotA d sE linVE linE).run σ acc1 from rfl]
  rw [absDom_clearSlotA σ acc1 d S sE linVE linE hslot hgen1 hremoved1 c]
  unfold MachineState.clearSlot MachineState.setDom
  rw [hdoms]

/-- Composition of the root-entry structural branch: orphan children,
then clear the dropped slot. -/
theorem absDom_orphan_clearSlotA (σ acc : Loom.Hw.St)
    (oldE : Expr 14) (d : DomainId) (S : Slot)
    (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4)
    (hcapV : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dcapV c s) 1 = σ.regs (Hw.dcapV c s) 1)
    (hlinV : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dcapLinV c s) 1 = σ.regs (Hw.dcapLinV c s) 1)
    (hlin : ∀ c : DomainId, ∀ s : Slot,
      acc.regs (Hw.dcapLin c s) 4 = σ.regs (Hw.dcapLin c s) 4)
    (hcellV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hcellP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hslot : sE.eval σ = BitVec.ofNat 4 S.val)
    (hgen : acc.regs (Hw.dgen d S) 8 = σ.regs (Hw.dgen d S) 8)
    (hremoved : removedCell
      ((Hw.abs acc).orphanChildren (Hw.decRef (oldE.eval σ))) d S =
      if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (linE.eval σ)) else none)
    (c : DomainId) :
    Hw.absDom ((Hw.clearSlotA d sE linVE linE).run σ
      ((Hw.orphanA oldE).run σ acc)) c =
      (((Hw.abs acc).orphanChildren (Hw.decRef (oldE.eval σ))).clearSlot d S).doms c := by
  let acc1 := (Hw.orphanA oldE).run σ acc
  have hdoms : (Hw.abs acc1).doms =
      ((Hw.abs acc).orphanChildren (Hw.decRef (oldE.eval σ))).doms := by
    funext c'
    exact absDom_orphanA σ acc oldE hcapV hlinV hlin hcellV hcellP c'
  have hgen1 : acc1.regs (Hw.dgen d S) 8 = σ.regs (Hw.dgen d S) 8 := by
    rw [orphanA_frame σ acc oldE (Hw.dgen d S) 8
      (fun c' l' => by clear * - d S c' l'; native_decide +revert)
      (fun c' s' => by clear * - d S c' s'; native_decide +revert), hgen]
  have hremoved1 : removedCell (Hw.abs acc1) d S =
      if linVE.eval σ = 1#1 then
        some (finOfBv (by decide) (linE.eval σ)) else none := by
    unfold removedCell
    rw [congrFun hdoms d]
    exact hremoved
  rw [show (Hw.clearSlotA d sE linVE linE).run σ
      ((Hw.orphanA oldE).run σ acc) =
      (Hw.clearSlotA d sE linVE linE).run σ acc1 from rfl]
  rw [absDom_clearSlotA σ acc1 d S sE linVE linE hslot hgen1 hremoved1 c]
  unfold MachineState.clearSlot MachineState.setDom
  rw [hdoms]

/-- Pointwise form of the unique retiring-domain selector. -/
theorem ifDomIs_eval_selected (σ : Loom.Hw.St) (E : DomainId)
    (hsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1) :
    ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1 := by
  intro d
  by_cases h : d = E
  · subst d
    rw [if_pos rfl, hsel]
  · rw [if_neg h, bv1_ne_one.mp (hexcl d h)]

/-- Four-bit slot literals round-trip through the finite decoder. -/
theorem bv4_slot_iff (b : BitVec 4) (s : Slot) :
    (b = BitVec.ofNat 4 s.val) ↔ (finOfBv (by decide) b = s) := by
  constructor
  · intro h
    apply Fin.ext
    show b.toNat = s.val
    rw [h, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := s.isLt; omega)
  · intro h
    apply BitVec.eq_of_toNat_eq
    have hv : b.toNat = s.val := congrArg Fin.val h
    rw [hv, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := s.isLt; omega)).symm

/-! ## `cap_drop` selector and parent-branch bridges -/

/-- Once the selected slot is known, the selector's generation field is
the generation register of that slot. -/
theorem capSel_gen_eval (σ : Loom.Hw.St) (E : DomainId) (hwE : Expr 32)
    (S : Slot)
    (hslot : (Hw.capSel E hwE).slot.eval σ = BitVec.ofNat 4 S.val) :
    (Hw.capSel E hwE).gen.eval σ =
      (hwE.eval σ).extractLsb' 4 8 := by
  rfl

/-- The selected lineage-valid bit comes from the selected capability
slot. -/
theorem capSel_linV_eval (σ : Loom.Hw.St) (E : DomainId) (hwE : Expr 32)
    (S : Slot)
    (hslot : (Hw.capSel E hwE).slot.eval σ = BitVec.ofNat 4 S.val) :
    (Hw.capSel E hwE).linV.eval σ = σ.regs (Hw.dcapLinV E S) 1 := by
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
      ((Hw.capSel E hwE).slot.eval σ) = S :=
    (bv4_slot_iff _ S).mp hslot
  have hfin' : finOfBv (by decide : 2 ^ 4 = numSlots)
      ((Hw.field hwE 0 4).eval σ) = S := by
    simpa [Hw.capSel] using hfin
  show (Hw.muxFin (fun s => .reg 1 (Hw.dcapLinV E s))
    (Hw.field hwE 0 4)).eval σ = _
  rw [muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin']
  rfl

/-- The selected lineage index comes from the selected capability slot. -/
theorem capSel_lin_eval (σ : Loom.Hw.St) (E : DomainId) (hwE : Expr 32)
    (S : Slot)
    (hslot : (Hw.capSel E hwE).slot.eval σ = BitVec.ofNat 4 S.val) :
    (Hw.capSel E hwE).lin.eval σ = σ.regs (Hw.dcapLin E S) 4 := by
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
      ((Hw.capSel E hwE).slot.eval σ) = S :=
    (bv4_slot_iff _ S).mp hslot
  have hfin' : finOfBv (by decide : 2 ^ 4 = numSlots)
      ((Hw.field hwE 0 4).eval σ) = S := by
    simpa [Hw.capSel] using hfin
  show (Hw.muxFin (fun s => .reg 4 (Hw.dcapLin E s))
    (Hw.field hwE 0 4)).eval σ = _
  rw [muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin']
  rfl

/-- Dynamic lineage-cell validity selects the corresponding cell-valid
register. -/
theorem cellVAt_eval (σ : Loom.Hw.St) (E : DomainId) (linE : Expr 4)
    (L : LineageId)
    (hlin : linE.eval σ = BitVec.ofNat 4 L.val) :
    (Hw.cellVAt E linE).eval σ = σ.regs (Hw.dcellV E L) 1 := by
  have hfin : finOfBv (by decide : 2 ^ 4 = numLineage) (linE.eval σ) = L :=
    (bv4_slot_iff _ L).mp hlin
  rw [Hw.cellVAt, muxFin_eval (by decide : 2 ^ 4 = numLineage), hfin]
  rfl

/-- Dynamic lineage-parent selection reads the corresponding packed
parent register. -/
theorem cellParAt_eval (σ : Loom.Hw.St) (E : DomainId) (linE : Expr 4)
    (L : LineageId)
    (hlin : linE.eval σ = BitVec.ofNat 4 L.val) :
    (Hw.cellParAt E linE).eval σ = σ.regs (Hw.dcellPar E L) 14 := by
  have hfin : finOfBv (by decide : 2 ^ 4 = numLineage) (linE.eval σ) = L :=
    (bv4_slot_iff _ L).mp hlin
  rw [Hw.cellParAt, muxFin_eval (by decide : 2 ^ 4 = numLineage), hfin]
  rfl

/-- A selected abstract derived entry forces the selector's lineage-valid
bit and index to encode that entry's lineage cell. -/
theorem capSel_lineage_some_eval (σ : Loom.Hw.St) (E : DomainId)
    (hwE : Expr 32) (S : Slot) (e : CapEntry) (L : LineageId)
    (hslot : (Hw.capSel E hwE).slot.eval σ = BitVec.ofNat 4 S.val)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hlin : e.lineage = some L) :
    (Hw.capSel E hwE).linV.eval σ = 1#1 ∧
      (Hw.capSel E hwE).lin.eval σ = BitVec.ofNat 4 L.val := by
  have hentry :
      (if σ.regs (Hw.dcapLinV E S) 1 = 1#1 then
          some (finOfBv (by decide) (σ.regs (Hw.dcapLin E S) 4))
        else none) = e.lineage := by
    change (if σ.regs (Hw.dcapV E S) 1 = 1#1 then
        some { kind := Hw.decKind (σ.regs (Hw.dcapKind E S) 32)
               lineage := if σ.regs (Hw.dcapLinV E S) 1 = 1#1 then
                 some (finOfBv (by decide) (σ.regs (Hw.dcapLin E S) 4))
               else none }
      else none) = some e at hcap
    by_cases hv : σ.regs (Hw.dcapV E S) 1 = 1#1
    · rw [if_pos hv] at hcap
      exact congrArg CapEntry.lineage (Option.some.inj hcap)
    · rw [if_neg hv] at hcap
      contradiction
  rw [hlin] at hentry
  by_cases hv : σ.regs (Hw.dcapLinV E S) 1 = 1#1
  · rw [if_pos hv] at hentry
    have hL : finOfBv (by decide) (σ.regs (Hw.dcapLin E S) 4) = L :=
      Option.some.inj hentry
    refine ⟨?_, ?_⟩
    · rw [capSel_linV_eval σ E hwE S hslot, hv]
    · rw [capSel_lin_eval σ E hwE S hslot]
      exact (bv4_slot_iff _ L).mpr hL
  · rw [if_neg hv] at hentry
    contradiction

/-- A selected abstract root entry forces the selector's lineage-valid bit
low; consequently the hardware parent-exists guard is low as well. -/
theorem capSel_lineage_none_eval (σ : Loom.Hw.St) (E : DomainId)
    (hwE : Expr 32) (S : Slot) (e : CapEntry)
    (hslot : (Hw.capSel E hwE).slot.eval σ = BitVec.ofNat 4 S.val)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hlin : e.lineage = none) :
    (Hw.capSel E hwE).linV.eval σ = 0#1 := by
  have hentry :
      (if σ.regs (Hw.dcapLinV E S) 1 = 1#1 then
          some (finOfBv (by decide) (σ.regs (Hw.dcapLin E S) 4))
        else none) = e.lineage := by
    change (if σ.regs (Hw.dcapV E S) 1 = 1#1 then
        some { kind := Hw.decKind (σ.regs (Hw.dcapKind E S) 32)
               lineage := if σ.regs (Hw.dcapLinV E S) 1 = 1#1 then
                 some (finOfBv (by decide) (σ.regs (Hw.dcapLin E S) 4))
               else none }
      else none) = some e at hcap
    by_cases hv : σ.regs (Hw.dcapV E S) 1 = 1#1
    · rw [if_pos hv] at hcap
      exact congrArg CapEntry.lineage (Option.some.inj hcap)
    · rw [if_neg hv] at hcap
      contradiction
  rw [hlin] at hentry
  have hv : σ.regs (Hw.dcapLinV E S) 1 ≠ 1#1 := by
    intro hv
    rw [if_pos hv] at hentry
    contradiction
  rw [capSel_linV_eval σ E hwE S hslot, bv1_ne_one.mp hv]

/-- For a well-formed selected derived capability, the hardware drop
parent guard is true and the selected packed parent decodes to the spec
`parentOf` result. -/
theorem drop_parent_guard_some (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (e : CapEntry) (L : LineageId)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hlin : e.lineage = some L) (hwf : Wf (Hw.abs σ)) :
    ∃ cell : LineageCell,
      ((Hw.abs σ).doms E).lineage L = some cell ∧
      (Expr.and (Hw.dropSel E).linV
        (Hw.cellVAt E (Hw.dropSel E).lin)).eval σ = 1#1 ∧
      Hw.decRef ((Hw.cellParAt E (Hw.dropSel E).lin).eval σ) =
        cell.parent ∧
      (Hw.abs σ).parentOf E S = some cell.parent := by
  have hsel := capSel_lineage_some_eval σ E
    (Hw.readReg E Hw.rs1E) S e L hslot hcap hlin
  have hsel' : (Hw.dropSel E).linV.eval σ = 1#1 ∧
      (Hw.dropSel E).lin.eval σ = BitVec.ofNat 4 L.val := by
    simpa [Hw.dropSel] using hsel
  have hused := (hwf.doms E).cell_backed S e L hcap hlin
  cases hc : ((Hw.abs σ).doms E).lineage L with
  | none => simp [hc] at hused
  | some cell =>
      refine ⟨cell, rfl, ?_, ?_, ?_⟩
      · show (Hw.dropSel E).linV.eval σ &&&
          (Hw.cellVAt E (Hw.dropSel E).lin).eval σ = 1#1
        rw [hsel'.1, cellVAt_eval σ E (Hw.dropSel E).lin L hsel'.2]
        change 1#1 &&& σ.regs (Hw.dcellV E L) 1 = 1#1
        change (if σ.regs (Hw.dcellV E L) 1 = 1#1 then
            some ⟨Hw.decRef (σ.regs (Hw.dcellPar E L) 14)⟩
          else none) = some cell at hc
        by_cases hv : σ.regs (Hw.dcellV E L) 1 = 1#1
        · simp [hv]
        · rw [if_neg hv] at hc
          contradiction
      · rw [cellParAt_eval σ E (Hw.dropSel E).lin L hsel'.2]
        change (if σ.regs (Hw.dcellV E L) 1 = 1#1 then
            some ⟨Hw.decRef (σ.regs (Hw.dcellPar E L) 14)⟩
          else none) = some cell at hc
        by_cases hv : σ.regs (Hw.dcellV E L) 1 = 1#1
        · rw [if_pos hv] at hc
          exact congrArg LineageCell.parent (Option.some.inj hc)
        · rw [if_neg hv] at hc
          contradiction
      · simp [MachineState.parentOf, hcap, hlin, hc]

/-- For a selected root capability, the hardware drop parent guard is
false and the spec `parentOf` result is `none`. -/
theorem drop_parent_guard_none (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (e : CapEntry)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hlin : e.lineage = none) :
    (Expr.and (Hw.dropSel E).linV
      (Hw.cellVAt E (Hw.dropSel E).lin)).eval σ = 0#1 ∧
      (Hw.abs σ).parentOf E S = none := by
  have hv := capSel_lineage_none_eval σ E
    (Hw.readReg E Hw.rs1E) S e hslot hcap hlin
  have hv' : (Hw.dropSel E).linV.eval σ = 0#1 := by
    simpa [Hw.dropSel] using hv
  constructor
  · show (Hw.dropSel E).linV.eval σ &&&
      (Hw.cellVAt E (Hw.dropSel E).lin).eval σ = 0#1
    rw [hv']
    simp
  · simp [MachineState.parentOf, hcap, hlin]

/-- On the successful path, the packed `oldE` expression is exactly the
current abstract reference of the selected slot. -/
theorem drop_oldE_decoded (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hlive : (Hw.dropSel E).live.eval σ = 1#1) :
    Hw.decRef ((Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
      (Hw.dropSel E).gen).eval σ) =
      ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩ := by
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4) = S := by
    exact (bv4_slot_iff _ S).mp hslot
  have hS : S.val =
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := by
    exact (congrArg Fin.val hfin).symm
  have hgen :=
    ((capSel_live_eval σ E (Hw.readReg E Hw.rs1E) S hS).mp hlive).2.1
  have henc := encRefE_sel_eval σ E (Hw.readReg E Hw.rs1E)
  have henc' : (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
      (Hw.dropSel E).gen).eval σ =
      Hw.encRef ⟨E,
        finOfBv (by decide) (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4),
        ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 4 8⟩ := by
    simpa [Hw.dropSel] using henc
  rw [henc', decRef_encRef]
  change (⟨E, finOfBv (by decide)
      (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4),
      ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 4 8⟩ : CapRef) =
    (⟨E, S, σ.regs (Hw.dgen E S) 8⟩ : CapRef)
  rw [hfin, hgen]

/-- In the derived branch, reparenting preserves the selected entry, so
`clearSlot` frees precisely its selected lineage cell. -/
theorem removedCell_reparent_drop (σ : MachineState) (E : DomainId)
    (S : Slot) (e : CapEntry) (L : LineageId) (old parent : CapRef)
    (hcap : (σ.doms E).caps S = some e)
    (hlin : e.lineage = some L) :
    removedCell (σ.reparent old parent) E S = some L := by
  simp [removedCell, reparent_caps, hcap, hlin]

/-- In the root branch, orphaning children leaves the selected root entry
rooted, so `clearSlot` has no lineage cell to free. -/
theorem removedCell_orphan_drop (σ : MachineState) (E : DomainId)
    (S : Slot) (e : CapEntry) (old : CapRef)
    (hcap : (σ.doms E).caps S = some e)
    (hlin : e.lineage = none) :
    removedCell (σ.orphanChildren old) E S = none := by
  simp [removedCell, orphanChildren_caps, hcap, hlin]

private def dropStructuralA (E : DomainId) : Act :=
  let cs := Hw.dropSel E
  let oldE := Hw.encRefE (Hw.dLit E) cs.slot cs.gen
  let pEx := Expr.and cs.linV (Hw.cellVAt E cs.lin)
  let pEnc := Hw.cellParAt E cs.lin
  .seq (.ite pEx (Hw.reparentA oldE pEnc) (Hw.orphanA oldE))
    (Hw.clearSlotA E cs.slot cs.linV cs.lin)

private def regPcTailA (E : DomainId) (vE : Expr 32) : Act :=
  .seq (Hw.writeReg E Hw.rdE vE) (Hw.pcAdvA E)

private def dropSuccessA (E : DomainId) : Act :=
  .seq (dropStructuralA E)
    (.seq (Hw.sweepRegionsA (Hw.dropKilled E))
      (regPcTailA E (.lit 0)))

/-- Public arm-level name for the successful drop payload. -/
def dropSuccessArmA (E : DomainId) : Act := dropSuccessA E

/-- Named successful payload is definitionally the five-action list in
`dropCirc`. -/
theorem dropSuccessA_run (σ acc : Loom.Hw.St) (E : DomainId) :
    (dropSuccessA E).run σ acc =
      (Hw.seqAll
        [ .ite
            (Expr.and (Hw.dropSel E).linV
              (Hw.cellVAt E (Hw.dropSel E).lin))
            (Hw.reparentA
              (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
                (Hw.dropSel E).gen)
              (Hw.cellParAt E (Hw.dropSel E).lin))
            (Hw.orphanA
              (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
                (Hw.dropSel E).gen)),
          Hw.clearSlotA E (Hw.dropSel E).slot
            (Hw.dropSel E).linV (Hw.dropSel E).lin,
          Hw.sweepRegionsA (Hw.dropKilled E),
          Hw.writeReg E Hw.rdE (.lit 0),
          Hw.pcAdvA E ]).run σ acc := by
  rfl

/-- The selected `cap_drop` dispatch reduces to its two-check ladder and
the named successful payload. -/
theorem retireFor_drop_ladder (σ : Loom.Hw.St) (E : DomainId)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 17#6) :
    ∀ acc, (Hw.retireFor E).run σ acc =
      if (Expr.not (Hw.dropSel E).live).eval σ = 1#1 then
        (Hw.respA E (.err .staleHandle)).run σ acc
      else if (Expr.not (Hw.dropSel E).clsOk).eval σ = 1#1 then
        (Hw.respA E (.err .badCap)).run σ acc
      else (dropSuccessA E).run σ acc := by
  intro acc
  have hsel := retireFor_sel_of_opc σ E "cap_drop" 17#6 hopc
    (by native_decide +revert) (by native_decide +revert) (Hw.dropCirc E)
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [hsel acc]
  rfl

private theorem regPcTailA_writes (E : DomainId) (vE : Expr 32) :
    (regPcTailA E vE).regWrites =
      [(Hw.dreg E 1, 32), (Hw.dreg E 2, 32), (Hw.dreg E 3, 32),
       (Hw.dreg E 4, 32), (Hw.dreg E 5, 32), (Hw.dreg E 6, 32),
       (Hw.dreg E 7, 32), (Hw.dpc E, 12)] := by
  rfl

private theorem quiet_notin_regPcTailA (c E : DomainId) (vE : Expr 32) :
    ∀ q ∈ domQuietNames c, q ∉ (regPcTailA E vE).regWrites := by
  intro q hq hwrite
  have hfull : ∀ q ∈ domQuietNames c,
      q ∉ ("if_v", 1) ::
        [(Hw.dreg E 1, 32), (Hw.dreg E 2, 32), (Hw.dreg E 3, 32),
         (Hw.dreg E 4, 32), (Hw.dreg E 5, 32), (Hw.dreg E 6, 32),
         (Hw.dreg E 7, 32), (Hw.dpc E, 12)] := by
    fin_cases c <;> fin_cases E <;> decide +kernel
  apply hfull q hq
  rw [regPcTailA_writes] at hwrite
  exact List.mem_cons_of_mem _ hwrite

/-- Generic decoded `writeReg; pcAdv` tail, including hardwired `r0`. -/
theorem absDom_regPcTailA (σ acc : Loom.Hw.St) (E : DomainId)
    (vE : Expr 32) (RD : RegId) (V : BitVec 32)
    (hrd : (Hw.rdE.eval σ).toNat = RD.val)
    (hval : vE.eval σ = V)
    (hpc : acc.regs (Hw.dpc E) 12 = σ.regs (Hw.dpc E) 12)
    (c : DomainId) :
    Hw.absDom ((regPcTailA E vE).run σ acc) c =
      if c = E then
        ({ Hw.absDom acc E with pc := (Hw.absDom acc E).pc + 1 }).setReg RD V
      else Hw.absDom acc c := by
  have hquiet : ∀ q ∈ domQuietNames c,
      ((regPcTailA E vE).run σ acc).regs q.1 q.2 = acc.regs q.1 q.2 := by
    intro q hq
    exact frame (quiet_notin_regPcTailA c E vE q hq) σ acc
  rw [absDom_regpc c hquiet]
  by_cases hc : c = E
  · subst c
    rw [if_pos rfl]
    apply domainState_ext
    · funext r
      change ((regPcTailA E vE).run σ acc).regs (Hw.dreg E r) 32 =
        (({ Hw.absDom acc E with pc := (Hw.absDom acc E).pc + 1 }).setReg
          RD V).regs r
      rw [setReg_regs]
      unfold regPcTailA
      change ((Hw.pcAdvA E).run σ
        ((Hw.writeReg E Hw.rdE vE).run σ acc)).regs (Hw.dreg E r) 32 = _
      rw [frame (show ((Hw.dreg E r : String), (32 : Nat)) ∉
        (Hw.pcAdvA E).regWrites from by
          intro hm
          exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
            (by decide : ¬(32 : Nat) = 12)) σ _]
      by_cases h0 : RD = (0 : RegId)
      · rw [if_pos h0]
        rw [writeReg_run_of_zero σ acc E Hw.rdE vE (by
          rw [hrd, h0]
          rfl)]
        rfl
      · rw [if_neg h0]
        rw [writeReg_run_of_nz σ acc E Hw.rdE vE RD hrd.symm
          (fun h => h0 (Fin.ext h))]
        simp only [Act.run, RegEnv.set]
        by_cases hr : r = RD
        · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial, hval]
        · rw [if_neg (fun h => hr (dreg_inj E r RD h)), if_neg hr]
          rfl
    · rw [setReg_pc]
      change ((regPcTailA E vE).run σ acc).regs (Hw.dpc E) 12 =
        (Hw.absDom acc E).pc + 1
      show (RegEnv.set _ (Hw.dpc E)
        ((Expr.add (Hw.rPc E) (.lit 1)).eval σ)) (Hw.dpc E) 12 = _
      simp only [RegEnv.set]
      rw [if_pos trivial]
      change σ.regs (Hw.dpc E) 12 + 1 = acc.regs (Hw.dpc E) 12 + 1
      rw [hpc]
    · rw [setReg_caps]
    · rw [setReg_slotGen]
    · rw [setReg_lineage]
    · rw [setReg_regions]
    · rw [setReg_run]
    · rw [setReg_serving]
    · rw [setReg_cause]
    · rw [setReg_budget]
    · rw [setReg_maxDonation]
  · rw [if_neg hc]
    apply domainState_ext <;> try rfl
    · funext r
      change ((regPcTailA E vE).run σ acc).regs (Hw.dreg c r) 32 =
        acc.regs (Hw.dreg c r) 32
      have hdis : ∀ (c E : DomainId) (r : RegId), c ≠ E →
          ((Hw.dreg c r, 32) ∉
            [(Hw.dreg E 1, 32), (Hw.dreg E 2, 32), (Hw.dreg E 3, 32),
             (Hw.dreg E 4, 32), (Hw.dreg E 5, 32), (Hw.dreg E 6, 32),
             (Hw.dreg E 7, 32), (Hw.dpc E, 12)]) := by native_decide
      exact frame (by rw [regPcTailA_writes]; exact hdis c E r hc) σ acc
    · change ((regPcTailA E vE).run σ acc).regs (Hw.dpc c) 12 =
        acc.regs (Hw.dpc c) 12
      have hdis : ∀ (c E : DomainId), c ≠ E →
          ((Hw.dpc c, 12) ∉
            [(Hw.dreg E 1, 32), (Hw.dreg E 2, 32), (Hw.dreg E 3, 32),
             (Hw.dreg E 4, 32), (Hw.dreg E 5, 32), (Hw.dreg E 6, 32),
             (Hw.dreg E 7, 32), (Hw.dpc E, 12)]) := by native_decide
      exact frame (by rw [regPcTailA_writes]; exact hdis c E hc) σ acc

/-- The structural prefix frames every register outside the capability and
lineage banks it may edit. -/
theorem dropStructuralA_frame (σ acc : Loom.Hw.St) (E : DomainId)
    (q : String) (qW : Nat)
    (hcapV : ∀ s : Slot, q ≠ Hw.dcapV E s)
    (hgen : ∀ s : Slot, q ≠ Hw.dgen E s)
    (hcellV : ∀ c : DomainId, ∀ l : LineageId, q ≠ Hw.dcellV c l)
    (hcellP : ∀ c : DomainId, ∀ l : LineageId, q ≠ Hw.dcellPar c l)
    (hlinV : ∀ c : DomainId, ∀ s : Slot, q ≠ Hw.dcapLinV c s) :
    ((dropStructuralA E).run σ acc).regs q qW = acc.regs q qW := by
  simp only [dropStructuralA, Act.run]
  rw [clearSlotA_frame σ _ E (Hw.dropSel E).slot
    (Hw.dropSel E).linV (Hw.dropSel E).lin q qW hcapV hgen
    (fun l => hcellV E l)]
  by_cases hp : (Expr.and (Hw.dropSel E).linV
      (Hw.cellVAt E (Hw.dropSel E).lin)).eval σ = 1#1
  · rw [if_pos hp]
    exact reparentA_frame σ acc _ _ q qW hcellP
  · rw [if_neg hp]
    exact orphanA_frame σ acc _ q qW hcellV hlinV

/-- The first two successful `dropCirc` actions (parent splice/orphan, then
slot clear) implement the spec's structural `cap_drop` core on every
abstract domain. -/
theorem absDom_drop_structural (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (e : CapEntry)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hlive : (Hw.dropSel E).live.eval σ = 1#1)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) :
    let cs := Hw.dropSel E
    let oldE := Hw.encRefE (Hw.dLit E) cs.slot cs.gen
    let pEx := Expr.and cs.linV (Hw.cellVAt E cs.lin)
    let pEnc := Hw.cellParAt E cs.lin
    Hw.absDom ((Hw.clearSlotA E cs.slot cs.linV cs.lin).run σ
      ((Act.ite pEx (Hw.reparentA oldE pEnc)
        (Hw.orphanA oldE)).run σ σ)) c =
      ((match (Hw.abs σ).parentOf E S with
        | some p => (Hw.abs σ).reparent
            ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩ p
        | none => (Hw.abs σ).orphanChildren
            ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩).clearSlot E S).doms c := by
  dsimp only
  cases hlin : e.lineage with
  | none =>
      have hg := drop_parent_guard_none σ E S e hslot hcap hlin
      have hold := drop_oldE_decoded σ E S hslot hlive
      rw [show (Act.ite
          (Expr.and (Hw.dropSel E).linV
            (Hw.cellVAt E (Hw.dropSel E).lin))
          (Hw.reparentA
            (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
              (Hw.dropSel E).gen)
            (Hw.cellParAt E (Hw.dropSel E).lin))
          (Hw.orphanA
            (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
              (Hw.dropSel E).gen))).run σ σ =
          (Hw.orphanA
            (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
              (Hw.dropSel E).gen)).run σ σ by
        simp only [Act.run]
        rw [if_neg (by rw [hg.1]; decide)]]
      rw [hg.2]
      rw [← hold]
      apply absDom_orphan_clearSlotA σ σ
      · intro c' s'; rfl
      · intro c' s'; rfl
      · intro c' s'; rfl
      · intro c' l'; rfl
      · intro c' l'; rfl
      · exact hslot
      · rfl
      · have hsel0 : (Hw.dropSel E).linV.eval σ = 0#1 := by
          simpa [Hw.dropSel] using capSel_lineage_none_eval σ E
            (Hw.readReg E Hw.rs1E) S e hslot hcap hlin
        rw [hsel0]
        rw [hold]
        exact removedCell_orphan_drop (Hw.abs σ) E S e
          ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩ hcap hlin
  | some L =>
      obtain ⟨cell, hcell, hguard, hpenc, hparent⟩ :=
        drop_parent_guard_some σ E S e L hslot hcap hlin hwf
      have hold := drop_oldE_decoded σ E S hslot hlive
      have hsel := capSel_lineage_some_eval σ E
        (Hw.readReg E Hw.rs1E) S e L hslot hcap hlin
      rw [show (Act.ite
          (Expr.and (Hw.dropSel E).linV
            (Hw.cellVAt E (Hw.dropSel E).lin))
          (Hw.reparentA
            (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
              (Hw.dropSel E).gen)
            (Hw.cellParAt E (Hw.dropSel E).lin))
          (Hw.orphanA
            (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
              (Hw.dropSel E).gen))).run σ σ =
          (Hw.reparentA
            (Hw.encRefE (Hw.dLit E) (Hw.dropSel E).slot
              (Hw.dropSel E).gen)
            (Hw.cellParAt E (Hw.dropSel E).lin)).run σ σ by
        simp only [Act.run]
        rw [if_pos hguard]]
      rw [hparent]
      rw [← hold, ← hpenc]
      apply absDom_reparent_clearSlotA σ σ
      · intro c' l'; rfl
      · intro c' l'; rfl
      · exact hslot
      · rfl
      · have hsel' : (Hw.dropSel E).linV.eval σ = 1#1 ∧
            (Hw.dropSel E).lin.eval σ = BitVec.ofNat 4 L.val := by
          simpa [Hw.dropSel] using hsel
        rw [hsel'.1, hsel'.2,
          finOfBv_ofNat4 (by decide) L]
        exact removedCell_reparent_drop (Hw.abs σ) E S e L
          ⟨E, S, ((Hw.abs σ).doms E).slotGen S⟩ cell.parent hcap hlin

private def dropRef (σ : MachineState) (E : DomainId) (S : Slot) : CapRef :=
  ⟨E, S, (σ.doms E).slotGen S⟩

private def dropStructSpec (σ : MachineState) (E : DomainId) (S : Slot) :
    MachineState :=
  (match σ.parentOf E S with
   | some p => σ.reparent (dropRef σ E S) p
   | none => σ.orphanChildren (dropRef σ E S)).clearSlot E S

/-- Public arm-level name for the structural drop state. -/
def dropStructSpecArm (σ : MachineState) (E : DomainId) (S : Slot) :
    MachineState :=
  (match σ.parentOf E S with
   | some p => σ.reparent ⟨E, S, (σ.doms E).slotGen S⟩ p
   | none => σ.orphanChildren ⟨E, S, (σ.doms E).slotGen S⟩).clearSlot E S

/-- Convenience form of `absDom_drop_structural` using the named hardware
prefix and spec structural state. -/
theorem absDom_dropStructuralA (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (e : CapEntry)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hlive : (Hw.dropSel E).live.eval σ = 1#1)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hwf : Wf (Hw.abs σ)) (c : DomainId) :
    Hw.absDom ((dropStructuralA E).run σ σ) c =
      (dropStructSpec (Hw.abs σ) E S).doms c := by
  simpa only [dropStructuralA, dropStructSpec, dropRef] using
    absDom_drop_structural σ E S e hslot hlive hcap hwf c

/-- Structural drop edits preserve the entire region table. -/
theorem dropStructSpec_regions (σ : MachineState) (E : DomainId) (S : Slot)
    (c : DomainId) :
    ((dropStructSpec σ E S).doms c).regions = (σ.doms c).regions := by
  unfold dropStructSpec
  split
  · rw [clearSlot_regions]
    rfl
  · rw [clearSlot_regions, orphanChildren_regions]

/-- Structural drop edits remove liveness exactly at the selected slot. -/
theorem dropStructSpec_liveRef (σ : MachineState) (E : DomainId) (S : Slot)
    (r : CapRef) :
    (dropStructSpec σ E S).liveRef r =
      if r.dom = E ∧ r.slot = S then false else σ.liveRef r := by
  unfold dropStructSpec
  split
  · exact reparent_clearSlot_liveRef σ _ _ E S r
  · exact orphan_clearSlot_liveRef σ _ E S r

/-- Structural orphaning may clear lineage metadata, but every surviving
slot still decodes to the same Mover-relevant capability kind. -/
theorem dropStructSpecArm_liveKind (σ : MachineState) (E : DomainId)
    (S : Slot) (d : DomainId) (s : Slot) (g : Gen)
    (hout : ¬(d = E ∧ s = S)) :
    Option.map CapEntry.kind
        (((dropStructSpecArm σ E S).doms d).liveCap s g) =
      Option.map CapEntry.kind ((σ.doms d).liveCap s g) := by
  unfold dropStructSpecArm
  split
  · unfold DomainState.liveCap
    rw [clearSlot_caps, clearSlot_slotGen, if_neg hout]
    simp [hout, MachineState.reparent]
  · unfold DomainState.liveCap
    rw [clearSlot_caps, clearSlot_slotGen, if_neg hout,
      orphanChildren_caps, orphanChildren_slotGen]
    simp only [hout, if_false]
    have hgen :
        (((σ.orphanChildren
          ⟨E, S, (σ.doms E).slotGen S⟩).doms d).slotGen s) =
          (σ.doms d).slotGen s := rfl
    rw [hgen]
    cases hc : (σ.doms d).caps s with
    | none => simp [hc]
    | some e =>
        cases hl : e.lineage with
        | none => simp [hc, hl]
        | some l =>
            cases hcell : (σ.doms d).lineage l with
            | none => simp [hc, hl, hcell]
            | some cell =>
                by_cases hk : cell.parent =
                    ⟨E, S, (σ.doms E).slotGen S⟩ <;>
                  simp [hc, hl, hcell, hk]

/-- Nested packed-field slices compose when the outer slice stays within
the intermediate word. -/
theorem extractLsb'_extractLsb' {n m w : Nat} (b : BitVec n)
    (i j : Nat) (h : j + w ≤ m) :
    (b.extractLsb' i m).extractLsb' j w = b.extractLsb' (i + j) w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb']
  have hjk : j + k < m := by omega
  simp [hjk, Nat.add_assoc]

/-- The selected drop kill predicate is precisely equality with the
issuer domain and the selected slot. -/
theorem dropKilled_eval (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (dm : Expr 2) (sl : Expr 4) :
    ((Hw.dropKilled E dm sl).eval σ = 1#1) ↔
      finOfBv (by decide) (dm.eval σ) = E ∧
      finOfBv (by decide) (sl.eval σ) = S := by
  unfold Hw.dropKilled
  change ((if dm.eval σ = (Hw.dLit E).eval σ then 1#1 else 0#1) &&&
      (if sl.eval σ = (Hw.dropSel E).slot.eval σ then 1#1 else 0#1) = 1#1) ↔ _
  rw [bv1_and_eq_one]
  rw [hslot]
  have ite_one_iff (p : Prop) [Decidable p] :
      ((if p then 1#1 else 0#1) = 1#1) ↔ p := by
    by_cases hp : p <;> simp [hp]
  rw [ite_one_iff, ite_one_iff]
  exact and_congr (bv2_lit_iff _ E) (bv4_slot_iff _ S)

/-- Specialization to the domain/slot fields of a packed capability
reference. -/
theorem dropKilled_ref_eval (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (refE : Expr 14) :
    ((Hw.dropKilled E (Hw.field refE 12 2) (Hw.field refE 8 4)).eval σ =
        1#1) ↔
      (Hw.decRef (refE.eval σ)).dom = E ∧
      (Hw.decRef (refE.eval σ)).slot = S := by
  rw [dropKilled_eval σ E S hslot]
  rfl

/-- A reference outside the dropped slot is silent in the successful
drop's global kill tree.  This is the endpoint-local hypothesis needed by
the active-job Mover bridge. -/
theorem killedByCoreE_drop_ref_zero (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
    (refE : Expr 14)
    (hout : ¬((Hw.decRef (refE.eval σ)).dom = E ∧
      (Hw.decRef (refE.eval σ)).slot = S)) :
    (Hw.killedByCoreE (Hw.field refE 12 2)
      (Hw.field refE 8 4)).eval σ = 0#1 := by
  rw [hkills]
  apply bv1_ne_one.mp
  intro h
  exact hout ((dropKilled_ref_eval σ E S hslot refE).mp h)

/-- The region packing places its backing reference in `[41:28]`, so the
drop predicate on fields `[41:40]`/`[39:36]` is equality with that decoded
backing's domain and slot. -/
theorem dropKilled_region_eval (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (rgE : Expr 42) :
    ((Hw.dropKilled E (Hw.field rgE 40 2) (Hw.field rgE 36 4)).eval σ =
        1#1) ↔
      (Hw.decRegion (rgE.eval σ)).backing.dom = E ∧
      (Hw.decRegion (rgE.eval σ)).backing.slot = S := by
  rw [dropKilled_eval σ E S hslot]
  unfold Hw.decRegion Hw.decRef Hw.field
  rw [extractLsb'_extractLsb' _ 28 12 (by omega),
    extractLsb'_extractLsb' _ 28 8 (by omega)]
  rfl

/-- On a successful retiring `cap_drop`, the global core kill tree selects
exactly that drop's kill predicate. -/
theorem killedByCoreE_drop_eval (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdmn : (Hw.isMn "cap_drop").eval σ = 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1)
    (hok : ∀ d : DomainId, d = E → (Hw.dropOkE d).eval σ = 1#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ := by
  have hrev0 : (Hw.isMn "cap_revoke").eval σ = 0#1 := bv1_ne_one.mp hrev
  have hcall0 : (Hw.isMn "gate_call").eval σ = 0#1 := bv1_ne_one.mp hcall
  have hreturn0 : (Hw.isMn "gate_return").eval σ = 0#1 :=
    bv1_ne_one.mp hreturn
  have honeAnd : ∀ x : BitVec 1, 1#1 &&& x = x := by decide
  have hzeroAnd : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
  have hzeroOr : ∀ x : BitVec 1, 0#1 ||| x = x := by decide
  have horZero : ∀ x : BitVec 1, x ||| 0#1 = x := by decide
  unfold Hw.killedByCoreE
  fin_cases E <;>
    simp [Hw.orAll, List.finRange, Expr.eval, Fin.ext_iff, hret, hif, hdmn,
      hok, hrev0, hcall0, hreturn0, honeAnd, hzeroAnd, hzeroOr, horZero] <;>
    congr 2

/-- A failed `cap_drop` has no kill footprint, even though its mnemonic is
selected: `dropOkE` gates the global kill tree. -/
theorem killedByCoreE_drop_failed (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdmn : (Hw.isMn "cap_drop").eval σ = 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1)
    (hbad : ∀ d : DomainId, d = E → (Hw.dropOkE d).eval σ = 0#1)
    (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = 0#1 := by
  have hrev0 : (Hw.isMn "cap_revoke").eval σ = 0#1 := bv1_ne_one.mp hrev
  have hcall0 : (Hw.isMn "gate_call").eval σ = 0#1 := bv1_ne_one.mp hcall
  have hreturn0 : (Hw.isMn "gate_return").eval σ = 0#1 :=
    bv1_ne_one.mp hreturn
  have honeAnd : ∀ x : BitVec 1, 1#1 &&& x = x := by decide
  have hzeroAnd : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
  have hzeroOr : ∀ x : BitVec 1, 0#1 ||| x = x := by decide
  have horZero : ∀ x : BitVec 1, x ||| 0#1 = x := by decide
  unfold Hw.killedByCoreE
  fin_cases E <;>
    simp [Hw.orAll, List.finRange, Expr.eval, Fin.ext_iff, hret, hif, hdmn,
      hbad, hrev0, hcall0, hreturn0, honeAnd, hzeroAnd, hzeroOr, horZero]

/-- Failed drops are Mover-inert once the unrelated job-install gate is
known off. -/
theorem Inert.of_failed_drop (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hif : ∀ d : DomainId, (Hw.ifDomIs d).eval σ =
      if d = E then 1#1 else 0#1)
    (hdmn : (Hw.isMn "cap_drop").eval σ = 1#1)
    (hrev : (Hw.isMn "cap_revoke").eval σ ≠ 1#1)
    (hcall : (Hw.isMn "gate_call").eval σ ≠ 1#1)
    (hreturn : (Hw.isMn "gate_return").eval σ ≠ 1#1)
    (hbad : ∀ d : DomainId, d = E → (Hw.dropOkE d).eval σ = 0#1)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1) : Inert σ where
  killed := killedByCoreE_drop_failed σ E hret hif hdmn hrev hcall
    hreturn hbad
  newJob := hnew

/-! ## Successful post-core sweep selectors -/

/-- With map/unmap off, post-core region validity is the old valid bit
masked by the selected drop kill predicate. -/
theorem rgnVPostE_drop_eval (σ : Loom.Hw.St) (E : DomainId)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (c : DomainId) (r : RegionId) :
    (Hw.rgnVPostE c r).eval σ =
      σ.regs (Hw.drgnV c r) 1 &&&
        ~~~((Hw.dropKilled E
          (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
          (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval σ) := by
  show (if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _
    else if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _
    else (Expr.and (.reg 1 (Hw.drgnV c r))
      (.not (Hw.killedByCoreE _ _))).eval σ) = _
  rw [hmapz c r, hunmapz c r]
  rw [if_neg (by decide), if_neg (by decide)]
  show σ.regs (Hw.drgnV c r) 1 &&&
      ~~~((Hw.killedByCoreE _ _).eval σ) = _
  rw [hkills]

/-- After the structural prefix, the region-valid sweep produces exactly
the post-core region-valid expression; the structural edits themselves
frame the region bank. -/
theorem drop_structural_sweep_rgnV (σ : Loom.Hw.St) (E : DomainId)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (c : DomainId) (r : RegionId) :
    ((Hw.sweepRegionsA (Hw.dropKilled E)).run σ
      ((dropStructuralA E).run σ σ)).regs (Hw.drgnV c r) 1 =
      (Hw.rgnVPostE c r).eval σ := by
  rw [sweepRegionsA_rgnV, rgnVPostE_drop_eval σ E hkills hmapz hunmapz]
  have hframe : ((dropStructuralA E).run σ σ).regs
      (Hw.drgnV c r) 1 = σ.regs (Hw.drgnV c r) 1 := by
    apply dropStructuralA_frame
    · intro s; clear * - c r E s; native_decide +revert
    · intro s; clear * - c r E s; native_decide +revert
    · intro c' l; clear * - c r c' l; native_decide +revert
    · intro c' l; clear * - c r c' l; native_decide +revert
    · intro c' s; clear * - c r c' s; native_decide +revert
  change (if (σ.regs (Hw.drgnV c r) 1 &&&
      (Hw.dropKilled E (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
        (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval σ) = 1#1
    then 0#1 else ((dropStructuralA E).run σ σ).regs
      (Hw.drgnV c r) 1) = _
  rw [hframe]
  generalize σ.regs (Hw.drgnV c r) 1 = v
  generalize (Hw.dropKilled E
    (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
    (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval σ = k
  revert v k
  decide

/-- The same composite leaves packed region payloads untouched. -/
theorem drop_structural_sweep_rgn (σ : Loom.Hw.St) (E : DomainId)
    (c : DomainId) (r : RegionId) :
    ((Hw.sweepRegionsA (Hw.dropKilled E)).run σ
      ((dropStructuralA E).run σ σ)).regs (Hw.drgn c r) 42 =
      σ.regs (Hw.drgn c r) 42 := by
  rw [sweepRegionsA_rgn]
  apply dropStructuralA_frame
  · intro s; exact (by native_decide +revert)
  · intro s; exact (by native_decide +revert)
  · intro c' l; exact (by native_decide +revert)
  · intro c' l; exact (by native_decide +revert)
  · intro c' s; exact (by native_decide +revert)

/-- The hardware region-valid sweep and the spec `sweepRegions` retain
exactly the same regions after a successful drop. -/
theorem rgnVPostE_drop_sweepRegions (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (τ : MachineState)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
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
    (hwf : Wf (Hw.abs σ)) (c : DomainId) (r : RegionId) :
    (Hw.rgnVPostE c r).eval σ =
      if ((τ.sweepRegions.doms c).regions r).isSome then 1#1 else 0#1 := by
  rw [rgnVPostE_drop_eval σ E hkills hmapz hunmapz]
  rw [sweepRegions_drop_regions (Hw.abs σ) τ E S hregions hlive
    (fun c r rg hr => regionBacking_live hwf hr)]
  rw [abs_regions]
  let rg := Hw.decRegion (σ.regs (Hw.drgn c r) 42)
  let killed := (Hw.dropKilled E
    (Hw.field (.reg 42 (Hw.drgn c r)) 40 2)
    (Hw.field (.reg 42 (Hw.drgn c r)) 36 4)).eval σ
  have hkiff : killed = 1#1 ↔ rg.backing.dom = E ∧ rg.backing.slot = S := by
    exact dropKilled_region_eval σ E S hslot (.reg 42 (Hw.drgn c r))
  by_cases hv : σ.regs (Hw.drgnV c r) 1 = 1#1
  · rw [if_pos hv]
    by_cases hk : rg.backing.dom = E ∧ rg.backing.slot = S
    · have hk1 : killed = 1#1 := hkiff.mpr hk
      simp [hv, hk, hk1, killed, rg]
    · have hk0 : killed = 0#1 := bv1_ne_one.mp (fun h => hk (hkiff.mp h))
      simp [hv, hk, hk0, killed, rg]
  · have hv0 : σ.regs (Hw.drgnV c r) 1 = 0#1 := bv1_ne_one.mp hv
    simp [hv, hv0]

/-- Option-valued strengthening of `rgnVPostE_drop_sweepRegions`: the
swept table is exactly the abstraction encoded by the post-core valid bit
and the unchanged packed region value. -/
theorem sweepRegions_drop_region_eq (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (τ : MachineState)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
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
    (hwf : Wf (Hw.abs σ)) (c : DomainId) (r : RegionId) :
    (τ.sweepRegions.doms c).regions r =
      if (Hw.rgnVPostE c r).eval σ = 1#1 then
        some (Hw.decRegion (σ.regs (Hw.drgn c r) 42)) else none := by
  have hp := rgnVPostE_drop_sweepRegions σ E S τ hslot hkills hmapz
    hunmapz hregions hlive hwf c r
  rw [sweepRegions_drop_regions (Hw.abs σ) τ E S hregions hlive
    (fun c r rg hr => regionBacking_live hwf hr), abs_regions] at hp ⊢
  by_cases hv : σ.regs (Hw.drgnV c r) 1 = 1#1
  · rw [if_pos hv] at hp ⊢
    by_cases hk :
        (Hw.decRegion (σ.regs (Hw.drgn c r) 42)).backing.dom = E ∧
        (Hw.decRegion (σ.regs (Hw.drgn c r) 42)).backing.slot = S
    · simp [hk] at hp ⊢
      rw [hp] <;> decide
    · simp [hk] at hp ⊢
      rw [hp] <;> decide
  · rw [if_neg hv] at hp ⊢
    simp at hp ⊢
    rw [hp] <;> decide

/-- Whole-domain composition of the successful structural prefix and
region sweep. -/
theorem absDom_drop_structural_sweep (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (e : CapEntry)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hlive : (Hw.dropSel E).live.eval σ = 1#1)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hwf : Wf (Hw.abs σ))
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (c : DomainId) :
    Hw.absDom ((Hw.sweepRegionsA (Hw.dropKilled E)).run σ
      ((dropStructuralA E).run σ σ)) c =
      ((dropStructSpec (Hw.abs σ) E S).sweepRegions).doms c := by
  let accS := (dropStructuralA E).run σ σ
  let accR := (Hw.sweepRegionsA (Hw.dropKilled E)).run σ accS
  let τ := dropStructSpec (Hw.abs σ) E S
  have hstruct : Hw.absDom accS c = τ.doms c := by
    exact absDom_dropStructuralA σ E S e hslot hlive hcap hwf c
  have hframe (q : String) (qW : Nat)
      (hne : ∀ c' : DomainId, ∀ r' : RegionId, q ≠ Hw.drgnV c' r') :
      accR.regs q qW = accS.regs q qW := by
    exact sweepRegionsA_frame σ accS (Hw.dropKilled E) q qW hne
  apply domainState_ext
  · rw [sweepRegions_regs]
    funext rr
    change accR.regs (Hw.dreg c rr) 32 = _
    rw [hframe _ _ (fun c' r' => by
      clear * - c rr c' r'; native_decide +revert)]
    exact congrFun (congrArg DomainState.regs hstruct) rr
  · rw [sweepRegions_pc]
    change accR.regs (Hw.dpc c) 12 = _
    rw [hframe _ _ (fun c' r' => by
      clear * - c c' r'; native_decide +revert)]
    exact congrArg DomainState.pc hstruct
  · rw [sweepRegions_caps]
    funext s
    change (if accR.regs (Hw.dcapV c s) 1 = 1#1 then
      some (⟨Hw.decKind (accR.regs (Hw.dcapKind c s) 32),
             if accR.regs (Hw.dcapLinV c s) 1 = 1#1 then
               some (finOfBv (by decide) (accR.regs (Hw.dcapLin c s) 4))
             else none⟩ : CapEntry) else none) = _
    rw [hframe _ _ (fun c' r' => by
          clear * - c s c' r'; native_decide +revert),
      hframe _ _ (fun c' r' => by
          clear * - c s c' r'; native_decide +revert),
      hframe _ _ (fun c' r' => by
          clear * - c s c' r'; native_decide +revert),
      hframe _ _ (fun c' r' => by
          clear * - c s c' r'; native_decide +revert)]
    exact congrFun (congrArg DomainState.caps hstruct) s
  · rw [sweepRegions_slotGen]
    funext s
    change accR.regs (Hw.dgen c s) 8 = _
    rw [hframe _ _ (fun c' r' => by
      clear * - c s c' r'; native_decide +revert)]
    exact congrFun (congrArg DomainState.slotGen hstruct) s
  · rw [sweepRegions_lineage]
    funext l
    change (if accR.regs (Hw.dcellV c l) 1 = 1#1 then
      some ({ parent := Hw.decRef (accR.regs (Hw.dcellPar c l) 14) } :
        LineageCell) else none) = _
    rw [hframe _ _ (fun c' r' => by
          clear * - c l c' r'; native_decide +revert),
      hframe _ _ (fun c' r' => by
          clear * - c l c' r'; native_decide +revert)]
    exact congrFun (congrArg DomainState.lineage hstruct) l
  · funext r
    rw [sweepRegions_drop_region_eq σ E S τ hslot hkills hmapz hunmapz
      (dropStructSpec_regions (Hw.abs σ) E S)
      (dropStructSpec_liveRef (Hw.abs σ) E S) hwf c r]
    change (if accR.regs (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (accR.regs (Hw.drgn c r) 42)) else none) = _
    rw [show accR.regs (Hw.drgnV c r) 1 =
        (Hw.rgnVPostE c r).eval σ from
      drop_structural_sweep_rgnV σ E hkills hmapz hunmapz c r,
      show accR.regs (Hw.drgn c r) 42 = σ.regs (Hw.drgn c r) 42 from
        drop_structural_sweep_rgn σ E c r]
  · rw [sweepRegions_run]
    change Hw.decRun (accR.regs (Hw.drun c) 2)
      (accR.regs (Hw.drunG c) 2) = _
    rw [hframe _ _ (fun c' r' => by
          clear * - c c' r'; native_decide +revert),
      hframe _ _ (fun c' r' => by
          clear * - c c' r'; native_decide +revert)]
    exact congrArg DomainState.run hstruct
  · rw [sweepRegions_serving]
    change (if accR.regs (Hw.dsrvV c) 1 = 1#1 then
      some (finOfBv (by decide) (accR.regs (Hw.dsrv c) 2)) else none) = _
    rw [hframe _ _ (fun c' r' => by
          clear * - c c' r'; native_decide +revert),
      hframe _ _ (fun c' r' => by
          clear * - c c' r'; native_decide +revert)]
    exact congrArg DomainState.serving hstruct
  · rw [sweepRegions_cause]
    change accR.regs (Hw.dcause c) 32 = _
    rw [hframe _ _ (fun c' r' => by
      clear * - c c' r'; native_decide +revert)]
    exact congrArg DomainState.cause hstruct
  · rw [sweepRegions_budget]
    change (accR.regs (Hw.dbudget c) 32).toNat = _
    rw [hframe _ _ (fun c' r' => by
      clear * - c c' r'; native_decide +revert)]
    exact congrArg DomainState.budget hstruct
  · change (accR.regs (Hw.dmaxdon c) 32).toNat = (τ.doms c).maxDonation
    rw [hframe _ _ (fun c' r' => by
      clear * - c c' r'; native_decide +revert)]
    exact congrArg DomainState.maxDonation hstruct

/-- Complete successful payload through `rd := 0` and retirement PC
advance, still before the outer refill/latch and Mover assembly. -/
theorem absDom_dropSuccessA (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (e : CapEntry) (RD : RegId)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hlive : (Hw.dropSel E).live.eval σ = 1#1)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hwf : Wf (Hw.abs σ))
    (hrd : (Hw.rdE.eval σ).toNat = RD.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (c : DomainId) :
    Hw.absDom ((dropSuccessA E).run σ σ) c =
      if c = E then
        ({ ((dropStructSpec (Hw.abs σ) E S).sweepRegions).doms E with
            pc := (((dropStructSpec (Hw.abs σ) E S).sweepRegions).doms E).pc + 1
          }).setReg RD 0
      else ((dropStructSpec (Hw.abs σ) E S).sweepRegions).doms c := by
  let accR := (Hw.sweepRegionsA (Hw.dropKilled E)).run σ
    ((dropStructuralA E).run σ σ)
  have hpc : accR.regs (Hw.dpc E) 12 = σ.regs (Hw.dpc E) 12 := by
    rw [sweepRegionsA_frame σ _ (Hw.dropKilled E) (Hw.dpc E) 12
      (fun c' r' => by
        clear * - E c' r'; native_decide +revert)]
    apply dropStructuralA_frame
    · intro s; clear * - E s; native_decide +revert
    · intro s; clear * - E s; native_decide +revert
    · intro c' l; clear * - E c' l; native_decide +revert
    · intro c' l; clear * - E c' l; native_decide +revert
    · intro c' s; clear * - E c' s; native_decide +revert
  change Hw.absDom ((regPcTailA E (.lit 0)).run σ accR) c = _
  rw [absDom_regPcTailA σ accR E (.lit 0) RD 0 hrd rfl hpc c]
  by_cases hc : c = E
  · subst c
    rw [if_pos rfl, if_pos rfl,
      absDom_drop_structural_sweep σ E S e hslot hlive hcap hwf
        hkills hmapz hunmapz E]
  · rw [if_neg hc, if_neg hc,
      absDom_drop_structural_sweep σ E S e hslot hlive hcap hwf
        hkills hmapz hunmapz c]

/-- Refill commutes with the successful drop payload at the abstraction
boundary.  The payload sees the pre-cycle state `σ`, so changing its
accumulator can only affect registers it frames; among decoded domain
registers refill changes exactly the budget. -/
theorem absDom_dropSuccessA_refill (m : Manifest) (hwfm : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (E : DomainId) (S : Slot) (e : CapEntry) (RD : RegId)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hlive : (Hw.dropSel E).live.eval σ = 1#1)
    (hcap : ((Hw.abs σ).doms E).caps S = some e)
    (hwf : Wf (Hw.abs σ))
    (hrd : (Hw.rdE.eval σ).toNat = RD.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (c : DomainId) :
    let base := if c = E then
        ({ ((dropStructSpecArm (Hw.abs σ) E S).sweepRegions).doms E with
            pc := (((dropStructSpecArm (Hw.abs σ) E S).sweepRegions).doms E).pc + 1
          }).setReg RD 0
      else ((dropStructSpecArm (Hw.abs σ) E S).sweepRegions).doms c
    Hw.absDom
        ((Act.seq (.write 1 "if_v" (.lit 0)) (dropSuccessA E)).run σ
          ((Hw.refillAct m).run σ σ)) c =
      { base with budget := ((refillPhase m (Hw.abs σ)).doms c).budget } := by
  dsimp only
  let acc := (Act.write 1 "if_v" (.lit 0)).run σ
    ((Hw.refillAct m).run σ σ)
  let out := (dropSuccessA E).run σ acc
  let old := (dropSuccessA E).run σ σ
  let base := if c = E then
      ({ ((dropStructSpec (Hw.abs σ) E S).sweepRegions).doms E with
          pc := (((dropStructSpec (Hw.abs σ) E S).sweepRegions).doms E).pc + 1
        }).setReg RD 0
    else ((dropStructSpec (Hw.abs σ) E S).sweepRegions).doms c
  have hold : Hw.absDom old c = base := by
    exact absDom_dropSuccessA σ E S e RD hslot hlive hcap hwf hrd hkills
      hmapz hunmapz c
  have hacc {rn : String} {w : Nat}
      (hif : (rn, w) ≠ ("if_v", 1))
      (hrefill : (rn, w) ∉
        ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
          ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
          ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) :
      acc.regs rn w = σ.regs rn w := by
    rw [show acc.regs rn w =
        ((Hw.refillAct m).run σ σ).regs rn w from
      frame (by simpa [Act.regWrites] using hif) σ
        ((Hw.refillAct m).run σ σ)]
    exact refill_pres m σ hrefill
  have hout {rn : String} {w : Nat}
      (hif : (rn, w) ≠ ("if_v", 1))
      (hrefill : (rn, w) ∉
        ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
          ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
          ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) :
      out.regs rn w = old.regs rn w :=
    Act.run_regs_congr_acc (dropSuccessA E) σ acc σ rn w
      (hacc hif hrefill)
  change Hw.absDom out c = { base with budget := _ }
  apply domainState_ext'
  · funext r
    change out.regs (Hw.dreg c r) 32 = _
    rw [hout (by fin_cases c <;> fin_cases r <;> decide)
      (by fin_cases c <;> fin_cases r <;> decide)]
    exact congrFun (congrArg DomainState.regs hold) r
  · change out.regs (Hw.dpc c) 12 = _
    rw [hout (by fin_cases c <;> decide) (by fin_cases c <;> decide)]
    exact congrArg DomainState.pc hold
  · funext s
    change (if out.regs (Hw.dcapV c s) 1 = 1 then _ else none) = _
    rw [hout (by fin_cases c <;> fin_cases s <;> decide)
      (by fin_cases c <;> fin_cases s <;> decide),
      hout (by fin_cases c <;> fin_cases s <;> decide)
        (by fin_cases c <;> fin_cases s <;> decide),
      hout (by fin_cases c <;> fin_cases s <;> decide)
        (by fin_cases c <;> fin_cases s <;> decide),
      hout (by fin_cases c <;> fin_cases s <;> decide)
        (by fin_cases c <;> fin_cases s <;> decide)]
    exact congrFun (congrArg DomainState.caps hold) s
  · funext s
    change out.regs (Hw.dgen c s) 8 = _
    rw [hout (by fin_cases c <;> fin_cases s <;> decide)
      (by fin_cases c <;> fin_cases s <;> decide)]
    exact congrFun (congrArg DomainState.slotGen hold) s
  · funext l
    change (if out.regs (Hw.dcellV c l) 1 = 1 then _ else none) = _
    rw [hout (by fin_cases c <;> fin_cases l <;> decide)
      (by fin_cases c <;> fin_cases l <;> decide),
      hout (by fin_cases c <;> fin_cases l <;> decide)
        (by fin_cases c <;> fin_cases l <;> decide)]
    exact congrFun (congrArg DomainState.lineage hold) l
  · funext r
    change (if out.regs (Hw.drgnV c r) 1 = 1 then _ else none) = _
    rw [hout (by fin_cases c <;> fin_cases r <;> decide)
      (by fin_cases c <;> fin_cases r <;> decide),
      hout (by fin_cases c <;> fin_cases r <;> decide)
        (by fin_cases c <;> fin_cases r <;> decide)]
    exact congrFun (congrArg DomainState.regions hold) r
  · change decRun (out.regs (Hw.drun c) 2) (out.regs (Hw.drunG c) 2) = _
    rw [hout (by fin_cases c <;> decide) (by fin_cases c <;> decide),
      hout (by fin_cases c <;> decide) (by fin_cases c <;> decide)]
    exact congrArg DomainState.run hold
  · change (if out.regs (Hw.dsrvV c) 1 = 1 then _ else none) = _
    rw [hout (by fin_cases c <;> decide) (by fin_cases c <;> decide),
      hout (by fin_cases c <;> decide) (by fin_cases c <;> decide)]
    exact congrArg DomainState.serving hold
  · change out.regs (Hw.dcause c) 32 = _
    rw [hout (by fin_cases c <;> decide) (by fin_cases c <;> decide)]
    exact congrArg DomainState.cause hold
  · change (out.regs (Hw.dbudget c) 32).toNat = _
    rw [show out.regs (Hw.dbudget c) 32 = acc.regs (Hw.dbudget c) 32 from
      frame (by
        clear * - c E
        native_decide +revert) σ acc]
    rw [show acc.regs (Hw.dbudget c) 32 =
        ((Hw.refillAct m).run σ σ).regs (Hw.dbudget c) 32 from
      frame (by fin_cases c <;> decide) σ ((Hw.refillAct m).run σ σ)]
    exact congrArg (fun τ => (τ.doms c).budget)
      (abs_refill m hwfm hfit σ hsync)
  · change (out.regs (Hw.dmaxdon c) 32).toNat = _
    rw [hout (by fin_cases c <;> decide) (by fin_cases c <;> decide)]
    exact congrArg DomainState.maxDonation hold

/-- The Mover status-authority tree decodes against the post-drop swept
region table. -/
theorem sAuth_drop_eval (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (τ : MachineState)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
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
  rw [orAll_eval]
  rw [show (τ.sweepRegions.domCovers
      (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
      ⟨false, true, false⟩ = true) ↔
      (∃ r : RegionId, ∃ rg,
        (τ.sweepRegions.doms
          (finOfBv (by decide) (ow.eval σ))).regions r = some rg ∧
        rg.covers (sa.eval σ) ⟨false, true, false⟩ = true) from by
    rw [MachineState.domCovers]; simp]
  constructor
  · rintro ⟨e, hmem, heval⟩
    rw [List.mem_flatMap] at hmem
    obtain ⟨c, -, hmem⟩ := hmem
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hmem
    have h3 : ∀ e ∈ [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
        Hw.rgnCoversVal (Hw.rgnValPostE c r) sa ⟨false, true, false⟩],
        e.eval σ = 1#1 := (andAll_eval σ _).mp heval
    have h1 := h3 (Expr.eq ow (Hw.dLit c)) (by simp)
    have h2 := h3 (Hw.rgnVPostE c r) (by simp)
    have hcv := h3 (Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
      ⟨false, true, false⟩) (by simp)
    rw [eqE_eval] at h1
    have hc : finOfBv (by decide) (ow.eval σ) = c :=
      (bv2_lit_iff _ c).mp h1
    rw [rgnCoversVal_eval, rgnValPostE_quiescent σ hmapz] at hcv
    refine ⟨r, Hw.decRegion (σ.regs (Hw.drgn c r) 42), ?_, hcv⟩
    rw [hc, sweepRegions_drop_region_eq σ E S τ hslot hkills hmapz
      hunmapz hregions hlive hwf c r, if_pos h2]
  · rintro ⟨r, rg, hsome, hcov⟩
    set c : DomainId := finOfBv (by decide) (ow.eval σ) with hcdef
    rw [sweepRegions_drop_region_eq σ E S τ hslot hkills hmapz
      hunmapz hregions hlive hwf c r] at hsome
    by_cases hval : (Hw.rgnVPostE c r).eval σ = 1#1
    · rw [if_pos hval] at hsome
      obtain rfl := Option.some.inj hsome
      refine ⟨Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
          Hw.rgnCoversVal (Hw.rgnValPostE c r) sa ⟨false, true, false⟩],
        List.mem_flatMap.mpr ⟨c, List.mem_finRange c,
          List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩⟩, ?_⟩
      rw [andAll_eval]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rw [eqE_eval]
        exact (bv2_lit_iff _ c).mpr rfl
      · exact hval
      · rw [rgnCoversVal_eval, rgnValPostE_quiescent σ hmapz]
        exact hcov
    · rw [if_neg hval] at hsome
      exact absurd hsome (by simp)

/-- The sweeping-op Mover abort guard likewise specializes to the drop
kill predicate on the current source and destination references. -/
theorem movKilledE_drop_eval (σ : Loom.Hw.St) (E : DomainId)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ) :
    (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval σ =
      σ.regs "mov_v" 1 &&&
        ((Hw.dropKilled E Hw.movSrcDom Hw.movSrcSlot).eval σ |||
         (Hw.dropKilled E Hw.movDstDom Hw.movDstSlot).eval σ) := by
  unfold Hw.movKilledE
  change σ.regs "mov_v" 1 &&&
      ((Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot).eval σ |||
       (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot).eval σ) = _
  rw [hkills, hkills]

/-- The hardware Mover abort guard fires exactly when an active decoded
job has an endpoint in the dropped domain/slot. -/
theorem movKilledE_drop_iff (σ : Loom.Hw.St) (E : DomainId) (S : Slot)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ) :
    ((Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval σ = 1#1) ↔
      match Hw.absMover σ with
      | none => False
      | some job =>
          (job.src.dom = E ∧ job.src.slot = S) ∨
          (job.dst.dom = E ∧ job.dst.slot = S) := by
  rw [movKilledE_drop_eval σ E hkills]
  by_cases hv : σ.regs "mov_v" 1 = 1#1
  · rw [absMover_some σ hv, bv1_and_eq_one, bv1_or_eq_one]
    simp only [Hw.movSrcDom, Hw.movSrcSlot, Hw.movDstDom, Hw.movDstSlot]
    rw [
      dropKilled_ref_eval σ E S hslot (.reg 14 "mov_src"),
      dropKilled_ref_eval σ E S hslot (.reg 14 "mov_dst")]
    simp [hv]
    rfl
  · have hv0 : σ.regs "mov_v" 1 = 0#1 := bv1_ne_one.mp hv
    simp [absMover_none σ hv, hv0]

/-- With no same-cycle `move`, every post-job mux falls back to its current
register input. -/
theorem postJ_noNew {w : Nat} (σ : Loom.Hw.St)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (f : DomainId → Expr w) (cur : Expr w) :
    (Hw.postJ f cur).eval σ = cur.eval σ := by
  unfold Hw.postJ
  induction (List.finRange numDomains) with
  | nil => rfl
  | cons d t ih =>
      change (if (Hw.newJobSet d).eval σ = 1#1 then _ else _) = _
      rw [hnew d]
      simpa using ih

private theorem newJobAny_zero (σ : Loom.Hw.St)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1) :
    (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ = 0#1 := by
  apply orAll_zero
  intro e he
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp he
  rw [hnew d]
  decide

/-- With neither an old job nor a newly installed job, `moverAct` remains
empty. -/
theorem absMover_moverAct_nojob (σ acc : Loom.Hw.St)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hv : σ.regs "mov_v" 1 = 0#1) :
    Hw.absMover (Hw.moverAct.run σ acc) = none := by
  have hnewAny := newJobAny_zero σ hnew
  apply absMover_none
  show ¬(Hw.moverAct.run σ acc).regs "mov_v" 1 = 1#1
  simp only [Hw.moverAct, Act.run]
  rw [if_neg (by
    show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ |||
      (σ.regs "mov_v" 1 &&& _) ≠ 1#1
    rw [hnewAny, hv]
    exact (by decide : ∀ b : BitVec 1,
      0#1 ||| (0#1 &&& b) ≠ 1#1) _)]
  simp only [RegEnv.set, if_pos, dif_pos, Expr.eval]
  decide

/-- With neither an old nor new job, `moverAct` performs no memory write. -/
theorem moverAct_mem_nojob (σ acc : Loom.Hw.St)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hv : σ.regs "mov_v" 1 = 0#1) (a : Addr) :
    (Hw.moverAct.run σ acc).mems "mem" a.toNat 32 =
      acc.mems "mem" a.toNat 32 := by
  have hnewAny := newJobAny_zero σ hnew
  show (Act.run σ Hw.moverAct acc).mems "mem" a.toNat 32 = _
  simp only [Hw.moverAct, Act.run]
  rw [if_neg (by
    show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ |||
      (σ.regs "mov_v" 1 &&& _) ≠ 1#1
    rw [hnewAny, hv]
    exact (by decide : ∀ b : BitVec 1,
      0#1 ||| (0#1 &&& b) ≠ 1#1) _)]

/-- With no same-cycle `move` installation, a fired endpoint kill makes
the Mover rule take its empty-job branch. -/
theorem absMover_moverAct_killed (σ acc : Loom.Hw.St)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hkilled :
      (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval σ = 1#1) :
    Hw.absMover (Hw.moverAct.run σ acc) = none := by
  have hnewAny :
      (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ = 0#1 := by
    apply orAll_zero
    intro e he
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp he
    rw [hnew d]
    decide
  have hjob0 :
      ((Expr.or (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet))
        (.and (.reg 1 "mov_v")
          (.not (.and (.reg 1 "mov_v")
            (.or (Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot)
                 (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot)))))).eval σ =
        0#1) := by
    show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ |||
      (σ.regs "mov_v" 1 &&&
        ~~~((Hw.movKilledE
          (fun dm sl => Hw.killedByCoreE dm sl)).eval σ)) = 0#1
    rw [hnewAny, hkilled]
    generalize σ.regs "mov_v" 1 = b
    revert b
    decide
  apply absMover_none
  show ¬(Hw.moverAct.run σ acc).regs "mov_v" 1 = 1#1
  simp only [Hw.moverAct, Act.run]
  rw [if_neg (by rw [hjob0]; decide)]
  simp [RegEnv.set, Expr.eval]

/-- The empty-job branch taken after an endpoint kill performs no Mover
memory write; the stale-status write belongs to the sweeping core op. -/
theorem moverAct_mem_killed (σ acc : Loom.Hw.St)
    (hnew : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1)
    (hkilled :
      (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval σ = 1#1)
    (a : Addr) :
    (Hw.moverAct.run σ acc).mems "mem" a.toNat 32 =
      acc.mems "mem" a.toNat 32 := by
  have hnewAny :
      (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ = 0#1 := by
    apply orAll_zero
    intro e he
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp he
    rw [hnew d]
    decide
  have hjob0 :
      ((Expr.or (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet))
        (.and (.reg 1 "mov_v")
          (.not (.and (.reg 1 "mov_v")
            (.or (Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot)
                 (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot)))))).eval σ =
        0#1) := by
    show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ |||
      (σ.regs "mov_v" 1 &&&
        ~~~((Hw.movKilledE
          (fun dm sl => Hw.killedByCoreE dm sl)).eval σ)) = 0#1
    rw [hnewAny, hkilled]
    generalize σ.regs "mov_v" 1 = b
    revert b
    decide
  show (Act.run σ Hw.moverAct acc).mems "mem" a.toNat 32 = _
  simp only [Hw.moverAct, Act.run]
  rw [if_neg (by rw [hjob0]; decide)]

/-- Kill-aware Mover-field bridge for a successful drop. A pre-existing job
is either absent, killed at one endpoint, or survives with both endpoints
outside the dropped slot. -/
theorem absMover_moverAct_drop (σ acc : Loom.Hw.St) (τ : MachineState)
    (E : DomainId) (S : Slot)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
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
  by_cases hv : σ.regs "mov_v" 1 = 1#1
  · let job : MoverJob :=
      { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
        src := Hw.decRef (σ.regs "mov_src" 14)
        dst := Hw.decRef (σ.regs "mov_dst" 14)
        srcCur := σ.regs "mov_srccur" 12
        dstCur := σ.regs "mov_dstcur" 12
        remaining := (σ.regs "mov_rem" 13).toNat
        statusAddr := σ.regs "mov_status" 12 }
    have habs : Hw.absMover σ = some job := absMover_some σ hv
    by_cases hk : (job.src.dom = E ∧ job.src.slot = S) ∨
        (job.dst.dom = E ∧ job.dst.slot = S)
    · have hguard :
          (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval σ =
            1#1 := (movKilledE_drop_iff σ E S hslot hkills).mpr (by
          rw [habs]
          exact hk)
      have hτ : τ.mover = none := by
        rw [hjob, habs]
        simp [hk]
      rw [absMover_moverAct_killed σ acc hnew hguard]
      simp [Machines.Lnp64u.moverPhase, hτ]
    · have hguard :
          (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval σ =
            0#1 := bv1_ne_one.mp (by
          intro h
          apply hk
          have hh := (movKilledE_drop_iff σ E S hslot hkills).mp h
          simpa [habs] using hh)
      have hnewAny := newJobAny_zero σ hnew
      have hjobV : (Expr.or
          (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet))
          (.and (.reg 1 "mov_v")
            (.not (.and (.reg 1 "mov_v")
              (.or (Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot)
                   (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot)))))).eval σ =
          1#1 := by
        show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ |||
          (σ.regs "mov_v" 1 &&& ~~~((Hw.movKilledE
            (fun dm sl => Hw.killedByCoreE dm sl)).eval σ)) = 1#1
        rw [hnewAny, hv, hguard]
        decide
      have hkillS : ∀ e : Expr 14, e.eval σ = σ.regs "mov_src" 14 →
          (Hw.killedByCoreE (Hw.field e 12 2)
            (Hw.field e 8 4)).eval σ = 0#1 := by
        intro refE href
        apply killedByCoreE_drop_ref_zero σ E S hslot hkills refE
        intro hout
        apply hk
        left
        simpa [job, href] using hout
      have hkillD : ∀ e : Expr 14, e.eval σ = σ.regs "mov_dst" 14 →
          (Hw.killedByCoreE (Hw.field e 12 2)
            (Hw.field e 8 4)).eval σ = 0#1 := by
        intro refE href
        apply killedByCoreE_drop_ref_zero σ E S hslot hkills refE
        intro hout
        apply hk
        right
        simpa [job, href] using hout
      have houtS : ¬(job.src.dom = E ∧ job.src.slot = S) :=
        fun h => hk (Or.inl h)
      have houtD : ¬(job.dst.dom = E ∧ job.dst.slot = S) :=
        fun h => hk (Or.inr h)
      have hτ : τ.mover = some job := by
        rw [hjob, habs]
        simp [hk]
      exact absMover_moverAct_run σ acc τ
        (σ.regs "mov_src" 14) (σ.regs "mov_dst" 14)
        (σ.regs "mov_owner" 2) (σ.regs "mov_srccur" 12)
        (σ.regs "mov_dstcur" 12) (σ.regs "mov_status" 12)
        (σ.regs "mov_rem" 13)
        hkillS hkillD
        (by simpa [job] using
          hkind job.src.dom job.src.slot job.src.gen houtS)
        (by simpa [job] using
          hkind job.dst.dom job.dst.slot job.dst.gen houtD)
        hjobV
        (postJ_noNew σ hnew _ _) (postJ_noNew σ hnew _ _)
        (postJ_noNew σ hnew _ _) (postJ_noNew σ hnew _ _)
        (postJ_noNew σ hnew _ _) (postJ_noNew σ hnew _ _)
        (postJ_noNew σ hnew _ _)
        (by simpa [job] using hτ)
  · have hv0 : σ.regs "mov_v" 1 = 0#1 := bv1_ne_one.mp hv
    have habs : Hw.absMover σ = none := absMover_none σ hv
    have hτ : τ.mover = none := by rw [hjob, habs]
    rw [absMover_moverAct_nojob σ acc hnew hv0]
    simp [Machines.Lnp64u.moverPhase, hτ]

/-- Memory-face sibling of `absMover_moverAct_drop`. The killed case's
stale-status write is already present in `τ.mem`; `moverAct` itself is quiet
there, while a surviving job takes the ordinary active-job bridge. -/
theorem moverAct_mem_drop (σ acc : Loom.Hw.St) (τ : MachineState)
    (E : DomainId) (S : Slot)
    (hslot : (Hw.dropSel E).slot.eval σ = BitVec.ofNat 4 S.val)
    (hkills : ∀ (dm : Expr 2) (sl : Expr 4),
      (Hw.killedByCoreE dm sl).eval σ = (Hw.dropKilled E dm sl).eval σ)
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
  by_cases hv : σ.regs "mov_v" 1 = 1#1
  · let job : MoverJob :=
      { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
        src := Hw.decRef (σ.regs "mov_src" 14)
        dst := Hw.decRef (σ.regs "mov_dst" 14)
        srcCur := σ.regs "mov_srccur" 12
        dstCur := σ.regs "mov_dstcur" 12
        remaining := (σ.regs "mov_rem" 13).toNat
        statusAddr := σ.regs "mov_status" 12 }
    have habs : Hw.absMover σ = some job := absMover_some σ hv
    by_cases hk : (job.src.dom = E ∧ job.src.slot = S) ∨
        (job.dst.dom = E ∧ job.dst.slot = S)
    · have hguard :
          (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval σ =
            1#1 := (movKilledE_drop_iff σ E S hslot hkills).mpr (by
          rw [habs]
          exact hk)
      have hτ : τ.mover = none := by
        rw [hjob, habs]
        simp [hk]
      rw [moverAct_mem_killed σ acc hnew hguard a, hmemτ a]
      simp [Machines.Lnp64u.moverPhase, hτ]
    · have hguard :
          (Hw.movKilledE (fun dm sl => Hw.killedByCoreE dm sl)).eval σ =
            0#1 := bv1_ne_one.mp (by
          intro h
          apply hk
          have hh := (movKilledE_drop_iff σ E S hslot hkills).mp h
          simpa [habs] using hh)
      have hnewAny := newJobAny_zero σ hnew
      have hjobV : (Expr.or
          (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet))
          (.and (.reg 1 "mov_v")
            (.not (.and (.reg 1 "mov_v")
              (.or (Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot)
                   (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot)))))).eval σ =
          1#1 := by
        show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ |||
          (σ.regs "mov_v" 1 &&& ~~~((Hw.movKilledE
            (fun dm sl => Hw.killedByCoreE dm sl)).eval σ)) = 1#1
        rw [hnewAny, hv, hguard]
        decide
      have hkillS : ∀ e : Expr 14, e.eval σ = σ.regs "mov_src" 14 →
          (Hw.killedByCoreE (Hw.field e 12 2)
            (Hw.field e 8 4)).eval σ = 0#1 := by
        intro refE href
        apply killedByCoreE_drop_ref_zero σ E S hslot hkills refE
        intro hout
        apply hk
        left
        simpa [job, href] using hout
      have hkillD : ∀ e : Expr 14, e.eval σ = σ.regs "mov_dst" 14 →
          (Hw.killedByCoreE (Hw.field e 12 2)
            (Hw.field e 8 4)).eval σ = 0#1 := by
        intro refE href
        apply killedByCoreE_drop_ref_zero σ E S hslot hkills refE
        intro hout
        apply hk
        right
        simpa [job, href] using hout
      have houtS : ¬(job.src.dom = E ∧ job.src.slot = S) :=
        fun h => hk (Or.inl h)
      have houtD : ¬(job.dst.dom = E ∧ job.dst.slot = S) :=
        fun h => hk (Or.inr h)
      have hτ : τ.mover = some job := by
        rw [hjob, habs]
        simp [hk]
      exact moverAct_mem_run σ acc τ
        (σ.regs "mov_src" 14) (σ.regs "mov_dst" 14)
        (σ.regs "mov_owner" 2) (σ.regs "mov_srccur" 12)
        (σ.regs "mov_dstcur" 12) (σ.regs "mov_status" 12)
        (σ.regs "mov_rem" 13)
        hkillS hkillD
        (by simpa [job] using
          hkind job.src.dom job.src.slot job.src.gen houtS)
        (by simpa [job] using
          hkind job.dst.dom job.dst.slot job.dst.gen houtD)
        hjobV
        (postJ_noNew σ hnew _ _) (postJ_noNew σ hnew _ _)
        (postJ_noNew σ hnew _ _) (postJ_noNew σ hnew _ _)
        (postJ_noNew σ hnew _ _) (postJ_noNew σ hnew _ _)
        (postJ_noNew σ hnew _ _)
        (by simpa [job] using hτ) hauthτ hmemτ (hswτ job habs hk) a
  · have hv0 : σ.regs "mov_v" 1 = 0#1 := bv1_ne_one.mp hv
    have habs : Hw.absMover σ = none := absMover_none σ hv
    have hτ : τ.mover = none := by rw [hjob, habs]
    rw [moverAct_mem_nojob σ acc hnew hv0 a, hmemτ a]
    simp [Machines.Lnp64u.moverPhase, hτ]

/-! ## Kill-aware retirement assembly -/

/-- Retirement-square assembler for a core action whose Mover behavior is
not inert. The caller supplies the two exact post-core Mover faces; all other
state components use the same framing argument as `square_retire_store`. -/
theorem square_retire_kill (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (X : Act) (τ2 : MachineState)
    (hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w =
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs rn w)
    (hXifv : ("if_v", 1) ∉ X.regWrites)
    (hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2)
    (habsD : ∀ x, Hw.absDom
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) x = τ2.doms x)
    (habsG : ∀ g, Hw.absGate
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
        ((Hw.refillAct m).run σ σ)) g = τ2.gates g)
    (hmover : Hw.absMover (Hw.moverAct.run σ
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))) =
        (moverPhase τ2).mover)
    (hmem : ∀ a : Addr,
      (Hw.moverAct.run σ
        ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))).mems
          "mem" a.toNat 32 = (moverPhase τ2).mem a)
    (hcyc : τ2.cycle = σ.regs "cycle" 32)
    (hτ2if : τ2.inflight = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set σ1 := (Hw.refillAct m).run σ σ
  set τ1 := refillPhase m (Hw.abs σ)
  have hp : ∀ (rn : String) (w : Nat),
      rn.startsWith "mov_" = false → ¬(rn = "cycle" ∧ w = 32) →
      ((Hw.core m).cycle σ).regs rn w =
        ((Hw.coreAct m).run σ σ1).regs rn w := by
    intro rn w h2 h4
    rw [core_cycle_unfold]
    rw [frame (show (rn, w) ∉ Hw.tickAct.regWrites from by
      intro hmem'
      simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
        Prod.mk.injEq] at hmem'
      exact h4 hmem')]
    rw [run_WritesPrefixed h2 w _ mover_prefixed]
  have hstep : step m (Hw.abs σ) =
      { moverPhase (corePhase m τ1) with
        cycle := (moverPhase (corePhase m τ1)).cycle + 1 } := rfl
  rw [hstep]
  apply machineState_ext'
  · show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hspec, hcyc]
  · funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    rw [show (moverPhase (corePhase m τ1)).mem = (moverPhase τ2).mem from by
      rw [hspec]]
    exact hmem a
  · funext x
    have hRHS : (moverPhase (corePhase m τ1)).doms x = τ2.doms x := by
      rw [moverPhase_doms, hspec]
    show Hw.absDom ((Hw.core m).cycle σ) x = _
    rw [hRHS, ← habsD x]
    have hmovfree : ∀ q ∈ domReadNames x,
        q.1.startsWith "mov_" = false := by
      fin_cases x <;> decide +kernel
    have hcycfree : ∀ q ∈ domReadNames x,
        ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases x <;> exact of_decide_eq_true rfl
    apply absDom_congr
    intro p hp'
    rw [← hcoreR p.1 p.2]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g = τ2.gates g := by
      rw [moverPhase_gates, hspec]
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS, ← habsG g]
    have hmovfree : ∀ q ∈ gateReadNames g,
        q.1.startsWith "mov_" = false := by
      fin_cases g <;> decide +kernel
    have hcycfree : ∀ q ∈ gateReadNames g,
        ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases g <;> exact of_decide_eq_true rfl
    apply absGate_congr
    intro p hp'
    rw [← hcoreR p.1 p.2]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · show Hw.absMover ((Hw.core m).cycle σ) =
      (moverPhase (corePhase m τ1)).mover
    rw [core_cycle_unfold]
    have htick : ∀ (rn : String) (w : Nat), ¬(rn = "cycle" ∧ w = 32) →
        (Hw.tickAct.run σ
          (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))).regs rn w =
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)).regs rn w := by
      intro rn w h4
      exact frame (by
        intro hmem'
        simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
          Prod.mk.injEq] at hmem'
        exact h4 hmem') σ _
    rw [show Hw.absMover (Hw.tickAct.run σ
        (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1))) =
        Hw.absMover (Hw.moverAct.run σ ((Hw.coreAct m).run σ σ1)) from by
      unfold Hw.absMover
      rw [htick "mov_v" 1 (by decide), htick "mov_owner" 2 (by decide),
        htick "mov_src" 14 (by decide), htick "mov_dst" 14 (by decide),
        htick "mov_srccur" 12 (by decide), htick "mov_dstcur" 12 (by decide),
        htick "mov_rem" 13 (by decide), htick "mov_status" 12 (by decide)]]
    rw [show (moverPhase (corePhase m τ1)).mover = (moverPhase τ2).mover
      from by rw [hspec]]
    exact hmover
  · have hRHS : (moverPhase (corePhase m τ1)).inflight = none := by
      rw [moverPhase_inflight, hspec, hτ2if]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    rw [hp "if_v" 1 (by native_decide +revert) (by decide), hcoreR "if_v" 1]
    rw [show ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ σ1).regs
        "if_v" 1 = ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs
          "if_v" 1 from frame hXifv σ _]
    rw [show ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs
        "if_v" 1 = 0#1 from by simp [Act.run, RegEnv.set, Expr.eval]]
    rw [if_neg (by decide)]

end Machines.Lnp64u.Theorems.RMC
