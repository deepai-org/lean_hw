-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireMove

/-!
# R-MC retirement: `cap_dup` support (NEXTSTEPS tier 2, stage D1)

Free-slot/free-cell priority-encoder bridges: the circuits' foldr-mux
trees against the spec's lowest-index `find?`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## Generic foldr-mux vs `find?` -/

private theorem fold_mux_of_find_some {n w : Nat} (σ : Loom.Hw.St)
    (okE : Fin n → Expr 1) (valE : Fin n → Expr w) (dflt : Expr w)
    (p : Fin n → Bool)
    (hok : ∀ t, ((okE t).eval σ = 1#1) ↔ p t = true) :
    ∀ (L : List (Fin n)) (s : Fin n), L.find? p = some s →
      ((L.foldr (fun t acc => Expr.mux (okE t) (valE t) acc) dflt).eval σ
        = (valE s).eval σ) := by
  intro L
  induction L with
  | nil => intro s hf; exact absurd hf (by simp)
  | cons t L ih =>
      intro s hf
      by_cases hp : p t = true
      · rw [List.find?_cons_of_pos hp] at hf
        injection hf with hf
        subst hf
        show (if (okE t).eval σ = 1#1 then (valE t).eval σ else _) = _
        rw [if_pos (hok t |>.mpr hp)]
      · rw [List.find?_cons_of_neg (by simpa using hp)] at hf
        show (if (okE t).eval σ = 1#1 then (valE t).eval σ else _) = _
        rw [if_neg (fun hc => hp ((hok t).mp hc))]
        exact ih s hf

private theorem fold_mux_of_find_none {n w : Nat} (σ : Loom.Hw.St)
    (okE : Fin n → Expr 1) (valE : Fin n → Expr w) (dflt : Expr w)
    (p : Fin n → Bool)
    (hok : ∀ t, ((okE t).eval σ = 1#1) ↔ p t = true) :
    ∀ L : List (Fin n), L.find? p = none →
      ((L.foldr (fun t acc => Expr.mux (okE t) (valE t) acc) dflt).eval σ
        = dflt.eval σ) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons t L ih =>
      intro hf
      have hnp : ¬ p t = true := by
        have := List.find?_eq_none.mp hf t (List.mem_cons_self ..)
        simpa using this
      have hf' : L.find? p = none := by
        rw [List.find?_cons_of_neg (by simpa using hnp)] at hf
        exact hf
      show (if (okE t).eval σ = 1#1 then (valE t).eval σ else _) = _
      rw [if_neg (fun hc => hnp ((hok t).mp hc))]
      exact ih hf'

/-! ## The free-slot encoder -/

/-- Per-slot freeness test against the abstraction. -/
theorem freeSlotOk_eval (σ : Loom.Hw.St) (E : DomainId) (s : Slot) :
    ((Hw.freeSlotOk E s).eval σ = 1#1)
      ↔ (((((Hw.abs σ).doms E).caps s).isNone
          && (((Hw.abs σ).doms E).slotGen s != genRetired)) = true) := by
  show ((~~~(σ.regs (Hw.dcapV E s) 1) &&&
    ~~~(if σ.regs (Hw.dgen E s) 8 = (255 : BitVec 8)
      then (1#1 : BitVec 1) else 0#1)) = 1#1) ↔ _
  rw [show (((Hw.abs σ).doms E).caps s).isNone
      = !(decide (σ.regs (Hw.dcapV E s) 1 = 1)) from by
    show (if σ.regs (Hw.dcapV E s) 1 = 1 then some _ else none).isNone = _
    by_cases hv : σ.regs (Hw.dcapV E s) 1 = 1
    · rw [if_pos hv, decide_eq_true hv]; rfl
    · rw [if_neg hv, decide_eq_false hv]; rfl]
  rw [show (((Hw.abs σ).doms E).slotGen s != genRetired)
      = !(decide (σ.regs (Hw.dgen E s) 8 = (255 : BitVec 8))) from by
    show (σ.regs (Hw.dgen E s) 8 != (255 : BitVec 8)) = _
    rfl]
  by_cases hv : σ.regs (Hw.dcapV E s) 1 = 1#1
  · by_cases hg : σ.regs (Hw.dgen E s) 8 = (255 : BitVec 8)
    · rw [decide_eq_true (show (σ.regs (Hw.dcapV E s) 1 = 1) from hv),
        decide_eq_true hg, if_pos hg, hv]
      decide
    · rw [decide_eq_true (show (σ.regs (Hw.dcapV E s) 1 = 1) from hv),
        decide_eq_false hg, if_neg hg, hv]
      decide
  · by_cases hg : σ.regs (Hw.dgen E s) 8 = (255 : BitVec 8)
    · rw [decide_eq_false (show ¬(σ.regs (Hw.dcapV E s) 1 = 1) from hv),
        decide_eq_true hg, if_pos hg, bv1_ne_one.mp hv]
      decide
    · rw [decide_eq_false (show ¬(σ.regs (Hw.dcapV E s) 1 = 1) from hv),
        decide_eq_false hg, if_neg hg, bv1_ne_one.mp hv]
      decide


/-- The free-slot index mux selects the spec's lowest free slot. -/
theorem freeSlotIdx_eval (σ : Loom.Hw.St) (E : DomainId) (s : Slot)
    (hf : (Hw.abs σ).freeSlot E = some s) :
    (Hw.freeSlotIdx E).eval σ = BitVec.ofNat 4 s.val :=
  fold_mux_of_find_some σ (Hw.freeSlotOk E) (fun t => Hw.sLit t) (.lit 0)
    _ (freeSlotOk_eval σ E) _ s hf

/-! ## The free-cell encoder -/

/-- Per-cell freeness test against the abstraction. -/
theorem freeCellOk_eval (σ : Loom.Hw.St) (E : DomainId) (l : LineageId) :
    ((Hw.freeCellOk E l).eval σ = 1#1)
      ↔ ((((Hw.abs σ).doms E).lineage l).isNone = true) := by
  show ((~~~(σ.regs (Hw.dcellV E l) 1)) = 1#1) ↔ _
  rw [show (((Hw.abs σ).doms E).lineage l).isNone
      = !(decide (σ.regs (Hw.dcellV E l) 1 = 1)) from by
    show (if σ.regs (Hw.dcellV E l) 1 = 1 then some _ else none).isNone = _
    by_cases hv : σ.regs (Hw.dcellV E l) 1 = 1
    · rw [if_pos hv, decide_eq_true hv]; rfl
    · rw [if_neg hv, decide_eq_false hv]; rfl]
  by_cases hv : σ.regs (Hw.dcellV E l) 1 = 1#1
  · rw [decide_eq_true (show (σ.regs (Hw.dcellV E l) 1 = 1) from hv), hv]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
  · rw [decide_eq_false (show ¬(σ.regs (Hw.dcellV E l) 1 = 1) from hv),
      bv1_ne_one.mp hv]
    constructor
    · intro _; rfl
    · intro _; decide

/-- The free-cell valid bit tracks the spec's `freeCell`. -/
theorem freeCellV_eval (σ : Loom.Hw.St) (E : DomainId) :
    ((Hw.freeCellV E).eval σ = 1#1)
      ↔ ((Hw.abs σ).freeCell E).isSome = true := by
  rw [show (Hw.abs σ).freeCell E
      = (List.finRange numLineage).find? (fun l =>
          ((((Hw.abs σ).doms E).lineage l).isNone)) from rfl]
  rw [List.find?_isSome]
  constructor
  · intro h
    obtain ⟨e, hmem, he⟩ := (orAll_eval σ _).mp h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
    exact ⟨l, hl, (freeCellOk_eval σ E l).mp he⟩
  · rintro ⟨l, hl, hp⟩
    exact (orAll_eval σ _).mpr ⟨Hw.freeCellOk E l,
      List.mem_map.mpr ⟨l, hl, rfl⟩, (freeCellOk_eval σ E l).mpr hp⟩

/-- The free-cell index mux selects the spec's lowest free cell. -/
theorem freeCellIdx_eval (σ : Loom.Hw.St) (E : DomainId) (l : LineageId)
    (hf : (Hw.abs σ).freeCell E = some l) :
    (Hw.freeCellIdx E).eval σ = BitVec.ofNat 4 l.val :=
  fold_mux_of_find_some σ (Hw.freeCellOk E) (fun t => Hw.lLit t) (.lit 0)
    _ (freeCellOk_eval σ E) _ l hf

/-- `freeSlot` only reads caps and slot generations. -/
theorem freeSlot_congr (τ τ' : MachineState) (E : DomainId)
    (hc : ∀ s, (τ'.doms E).caps s = (τ.doms E).caps s)
    (hg : ∀ s, (τ'.doms E).slotGen s = (τ.doms E).slotGen s) :
    τ'.freeSlot E = τ.freeSlot E := by
  show (List.finRange numSlots).find? _ = (List.finRange numSlots).find? _
  congr 1
  funext s
  rw [hc s, hg s]

/-- `freeCell` only reads the lineage cells. -/
theorem freeCell_congr (τ τ' : MachineState) (E : DomainId)
    (hl : ∀ l, (τ'.doms E).lineage l = (τ.doms E).lineage l) :
    τ'.freeCell E = τ.freeCell E := by
  show (List.finRange numLineage).find? _ = (List.finRange numLineage).find? _
  congr 1
  funext l
  rw [hl l]


/-! ## Watched-ref Mover wrappers (tier-2 installs)

An installing op is core-inert for the kill/newJob trees, but its `τ2`
tables differ from the abstraction at the freshly-installed slot. The
re-check only probes the running job's refs, so agreement there (from
`MoverLiveSrc`/`MoverLiveMem` through `hsr`) suffices. -/

theorem absMover_moverAct_watched (σ acc : Loom.Hw.St) (τ : MachineState)
    (hnr : Inert σ)
    (hjob : τ.mover = Hw.absMover σ)
    (hcapsS : σ.regs "mov_v" 1 = 1#1 →
      (τ.doms (Hw.decRef (σ.regs "mov_src" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_src" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_src" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_src" 14)).slot)
    (hgenS : σ.regs "mov_v" 1 = 1#1 →
      (τ.doms (Hw.decRef (σ.regs "mov_src" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_src" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_src" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_src" 14)).slot)
    (hcapsD : σ.regs "mov_v" 1 = 1#1 →
      (τ.doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_dst" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_dst" 14)).slot)
    (hgenD : σ.regs "mov_v" 1 = 1#1 →
      (τ.doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_dst" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_dst" 14)).slot) :
    Hw.absMover (Hw.moverAct.run σ acc) = (moverPhase τ).mover := by
  by_cases hv : σ.regs "mov_v" 1 = 1#1
  case neg =>
    have hnone : Hw.absMover (Hw.moverAct.run σ acc) = none := by
      apply absMover_none
      show ¬ (Act.run σ Hw.moverAct acc).regs "mov_v" 1 = 1#1
      simp only [Hw.moverAct]
      simp only [Act.run]
      rw [jobV_quiescent σ hnr, if_neg hv]
      simp [RegEnv.set, Expr.eval]
    have hτ : τ.mover = none := by rw [hjob]; exact absMover_none σ hv
    rw [hnone]
    simp [Machines.Lnp64u.moverPhase, hτ]
  case pos =>
    exact absMover_moverAct_run σ acc τ hnr.killed
      (σ.regs "mov_src" 14) (σ.regs "mov_dst" 14)
      (σ.regs "mov_owner" 2) (σ.regs "mov_srccur" 12)
      (σ.regs "mov_dstcur" 12) (σ.regs "mov_status" 12)
      (σ.regs "mov_rem" 13)
      (hcapsS hv) (hgenS hv) (hcapsD hv) (hgenD hv)
      ((jobV_quiescent σ hnr).trans hv)
      (postJ_quiescent σ hnr _ _) (postJ_quiescent σ hnr _ _)
      (postJ_quiescent σ hnr _ _) (postJ_quiescent σ hnr _ _)
      (postJ_quiescent σ hnr _ _) (postJ_quiescent σ hnr _ _)
      (postJ_quiescent σ hnr _ _)
      (by rw [hjob]; exact absMover_some σ hv)

theorem moverAct_mem_watched (σ acc : Loom.Hw.St) (τ : MachineState)
    (hnr : Inert σ)
    (hjob : τ.mover = Hw.absMover σ)
    (hcapsS : σ.regs "mov_v" 1 = 1#1 →
      (τ.doms (Hw.decRef (σ.regs "mov_src" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_src" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_src" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_src" 14)).slot)
    (hgenS : σ.regs "mov_v" 1 = 1#1 →
      (τ.doms (Hw.decRef (σ.regs "mov_src" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_src" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_src" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_src" 14)).slot)
    (hcapsD : σ.regs "mov_v" 1 = 1#1 →
      (τ.doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_dst" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_dst" 14)).slot)
    (hgenD : σ.regs "mov_v" 1 = 1#1 →
      (τ.doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_dst" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_dst" 14)).slot)
    (hauthτ : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
              Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true)
    (hmemτ : ∀ b : Addr, acc.mems "mem" b.toNat 32 = τ.mem b)
    (hswτ : ∀ sc : Expr 12, Expr.eval σ
      (((List.finRange numDomains).foldr
        (fun d acc' =>
          Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
              Hw.domCoversE d
                (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                ⟨false, true, false⟩,
              .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
            (Hw.readReg d Hw.rs2E) acc')
        (.memRead 32 "mem" sc)))
      = τ.mem (sc.eval σ))
    (a : Addr) :
    (Hw.moverAct.run σ acc).mems "mem" a.toNat 32 = (moverPhase τ).mem a := by
  by_cases hv : σ.regs "mov_v" 1 = 1#1
  case neg =>
    have hτn : τ.mover = none := by rw [hjob]; exact absMover_none σ hv
    have hlhs : (Hw.moverAct.run σ acc).mems "mem" a.toNat 32
        = acc.mems "mem" a.toNat 32 := by
      show (Act.run σ Hw.moverAct acc).mems "mem" a.toNat 32 = _
      simp only [Hw.moverAct]
      simp only [Act.run]
      rw [jobV_quiescent σ hnr, if_neg hv]
    rw [hlhs, hmemτ a]
    simp [Machines.Lnp64u.moverPhase, hτn]
  case pos =>
    exact moverAct_mem_run σ acc τ hnr.killed
      (σ.regs "mov_src" 14) (σ.regs "mov_dst" 14)
      (σ.regs "mov_owner" 2) (σ.regs "mov_srccur" 12)
      (σ.regs "mov_dstcur" 12) (σ.regs "mov_status" 12)
      (σ.regs "mov_rem" 13)
      (hcapsS hv) (hgenS hv) (hcapsD hv) (hgenD hv)
      ((jobV_quiescent σ hnr).trans hv)
      (postJ_quiescent σ hnr _ _) (postJ_quiescent σ hnr _ _)
      (postJ_quiescent σ hnr _ _) (postJ_quiescent σ hnr _ _)
      (postJ_quiescent σ hnr _ _) (postJ_quiescent σ hnr _ _)
      (postJ_quiescent σ hnr _ _)
      (by rw [hjob]; exact absMover_some σ hv)
      hauthτ hmemτ hswτ a

end Machines.Lnp64u.Theorems.RMC
