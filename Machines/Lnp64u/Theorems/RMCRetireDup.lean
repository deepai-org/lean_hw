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

set_option maxHeartbeats 25600000 in
/-- The installing-op square glue: `square_retire_rgnop` with the Mover
faces routed through the watched-ref wrappers (tables may differ from
the abstraction at the freshly-installed slot only). -/
theorem square_retire_install (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hin : Inert σ)
    (X : Act) (τ2 : MachineState)
    (hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).regs rn w
        = ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
            ((Hw.refillAct m).run σ σ)).regs rn w)
    (hXifv : ("if_v", 1) ∉ X.regWrites)
    (hspec : corePhase m (refillPhase m (Hw.abs σ)) = τ2)
    (habsD : ∀ x, Hw.absDom ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
      ((Hw.refillAct m).run σ σ)) x = τ2.doms x)
    (habsG : ∀ g, Hw.absGate ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
      ((Hw.refillAct m).run σ σ)) g = τ2.gates g)
    (hjob : τ2.mover = Hw.absMover σ)
    (hwcapsS : σ.regs "mov_v" 1 = 1#1 →
      (τ2.doms (Hw.decRef (σ.regs "mov_src" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_src" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_src" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_src" 14)).slot)
    (hwgenS : σ.regs "mov_v" 1 = 1#1 →
      (τ2.doms (Hw.decRef (σ.regs "mov_src" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_src" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_src" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_src" 14)).slot)
    (hwcapsD : σ.regs "mov_v" 1 = 1#1 →
      (τ2.doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_dst" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).caps
        (Hw.decRef (σ.regs "mov_dst" 14)).slot)
    (hwgenD : σ.regs "mov_v" 1 = 1#1 →
      (τ2.doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_dst" 14)).slot
      = ((Hw.abs σ).doms (Hw.decRef (σ.regs "mov_dst" 14)).dom).slotGen
        (Hw.decRef (σ.regs "mov_dst" 14)).slot)
    (hauthτ2 : ∀ (ow : Expr 2) (sa : Expr 12),
      ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
          (List.finRange numRegions).map fun r =>
            Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
              Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
                ⟨false, true, false⟩])).eval σ = 1#1) ↔
        τ2.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
          ⟨false, true, false⟩ = true)
    (hmemτ2 : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = τ2.mem b)
    (hswτ2 : ∀ sc : Expr 12, Expr.eval σ
      (((List.finRange numDomains).foldr
        (fun d acc' =>
          Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
              Hw.domCoversE d
                (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                ⟨false, true, false⟩,
              .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
            (Hw.readReg d Hw.rs2E) acc')
        (.memRead 32 "mem" sc)))
      = τ2.mem (sc.eval σ))
    (hcyc : τ2.cycle = σ.regs "cycle" 32)
    (hτ2if : τ2.inflight = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
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
  · -- cycle
    show ((Hw.core m).cycle σ).regs "cycle" 32 = _
    rw [cycle_regs_cycle]
    show _ = (moverPhase (corePhase m τ1)).cycle + 1
    rw [moverPhase_cycle, hspec, hcyc]
  · -- mem
    funext a
    show ((Hw.core m).cycle σ).mems "mem" a.toNat 32 = _
    rw [core_cycle_unfold]
    rw [Loom.Hw.Compile.run_mems_notin "mem" Hw.tickAct
      (by simp [Hw.tickAct, Act.memWrites]) σ _ a.toNat 32]
    rw [show (moverPhase (corePhase m τ1)).mem = (moverPhase τ2).mem from by
      rw [hspec]]
    exact moverAct_mem_watched σ _ τ2 hin hjob
      hwcapsS hwgenS hwcapsD hwgenD
      (fun ow sa => hspec ▸ hauthτ2 ow sa)
      hmemτ2 hswτ2 a
  · -- doms
    funext x
    have hRHS : (moverPhase (corePhase m τ1)).doms x = τ2.doms x := by
      rw [moverPhase_doms, hspec]
    show Hw.absDom ((Hw.core m).cycle σ) x = _
    rw [hRHS, ← habsD x]
    have hmovfree : ∀ q ∈ domReadNames x, q.1.startsWith "mov_" = false := by
      fin_cases x <;> decide +kernel
    have hcycfree : ∀ q ∈ domReadNames x, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases x <;> exact of_decide_eq_true rfl
    apply absDom_congr
    intro p hp'
    rw [← hcoreR p.1 p.2]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · -- gates
    funext g
    have hRHS : (moverPhase (corePhase m τ1)).gates g = τ2.gates g := by
      rw [moverPhase_gates, hspec]
    show Hw.absGate ((Hw.core m).cycle σ) g = _
    rw [hRHS, ← habsG g]
    have hmovfree : ∀ q ∈ gateReadNames g, q.1.startsWith "mov_" = false := by
      fin_cases g <;> decide +kernel
    have hcycfree : ∀ q ∈ gateReadNames g, ¬(q.1 = "cycle" ∧ q.2 = 32) := by
      fin_cases g <;> exact of_decide_eq_true rfl
    apply absGate_congr
    intro p hp'
    rw [← hcoreR p.1 p.2]
    exact hp p.1 p.2 (hmovfree p hp') (hcycfree p hp')
  · -- mover
    show Hw.absMover ((Hw.core m).cycle σ)
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
    rw [show (moverPhase (corePhase m τ1)).mover = (moverPhase τ2).mover
      from by rw [hspec]]
    exact absMover_moverAct_watched σ _ τ2 hin hjob
      hwcapsS hwgenS hwcapsD hwgenD
  · -- inflight
    have hRHS : (moverPhase (corePhase m τ1)).inflight = none := by
      rw [moverPhase_inflight, hspec, hτ2if]
    show Hw.absInflight ((Hw.core m).cycle σ) = _
    rw [hRHS]
    unfold Hw.absInflight
    rw [hp "if_v" 1 (by decide +kernel) (by decide), hcoreR "if_v" 1]
    rw [show ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ σ1).regs "if_v" 1
        = ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs "if_v" 1 from
      frame hXifv σ _]
    rw [show ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs "if_v" 1 = 0#1
      from by simp [Act.run, RegEnv.set, Expr.eval]]
    rw [if_neg (by decide)]



/-! ## Install-face infrastructure -/

/-- The full `cap_dup` core act (dispatch `if_v` clear + the ok action). -/
def dupFull (e : DomainId) : Act :=
  .seq (.write 1 "if_v" (.lit 0))
    (Hw.seqAll
      [ Hw.installA e (Hw.freeSlotIdx e)
          (.mux (Hw.kIsMem (Hw.dupSel e).kindW)
            (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
            (Hw.dupSel e).kindW)
          (.lit 1) (Hw.freeCellIdx e)
          (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen),
        Hw.writeReg e Hw.rdE (Hw.handleE (Hw.freeSlotIdx e)
          (Hw.genOfE e (Hw.freeSlotIdx e))
          (Hw.field (Hw.dupSel e).kindW 0 1)),
        Hw.pcAdvA e ])

/-- The non-`regs`/`pc`/`caps`/`lineage` names `absDom · x` reads. -/
def domQuietNamesCap (x : DomainId) : List (String × Nat) :=
  ((List.finRange numSlots).map fun s => ((Hw.dgen x s : String), (8 : Nat)))
  ++ ((List.finRange numRegions).flatMap fun r =>
      [(Hw.drgnV x r, 1), (Hw.drgn x r, 42)])
  ++ [(Hw.drun x, 2), (Hw.drunG x, 2), (Hw.dsrvV x, 1), (Hw.dsrv x, 2),
      (Hw.dcause x, 32), (Hw.dbudget x, 32), (Hw.dmaxdon x, 32)]

/-- The regs/pc/caps/lineage face of `absDom` (quiet elsewhere). -/
theorem absDom_regpccap {S1 S2 : Loom.Hw.St} (e : DomainId)
    (hq : ∀ q ∈ domQuietNamesCap e, S2.regs q.1 q.2 = S1.regs q.1 q.2) :
    Hw.absDom S2 e =
      { Hw.absDom S1 e with
        regs := fun r => S2.regs (Hw.dreg e r) 32
        pc := S2.regs (Hw.dpc e) 12
        caps := fun s =>
          if S2.regs (Hw.dcapV e s) 1 = 1 then
            some { kind := Hw.decKind (S2.regs (Hw.dcapKind e s) 32)
                   lineage :=
                     if S2.regs (Hw.dcapLinV e s) 1 = 1 then
                       some (finOfBv (by decide)
                         (S2.regs (Hw.dcapLin e s) 4))
                     else none }
          else none
        lineage := fun l =>
          if S2.regs (Hw.dcellV e l) 1 = 1 then
            some ⟨Hw.decRef (S2.regs (Hw.dcellPar e l) 14)⟩
          else none } := by
  have hg : ∀ (s : Slot),
      S2.regs (Hw.dgen e s) 8 = S1.regs (Hw.dgen e s) 8 := fun s =>
    hq (Hw.dgen e s, 8) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩)))
  have hr : ∀ (r : RegionId) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.drgnV e r, 1), (Hw.drgn e r, 42)] →
      S2.regs rn w = S1.regs rn w := fun r rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨r, List.mem_finRange r, hp⟩)))
  have ht : ∀ (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.drun e, 2), (Hw.drunG e, 2), (Hw.dsrvV e, 1),
        (Hw.dsrv e, 2), (Hw.dcause e, 32), (Hw.dbudget e, 32),
        (Hw.dmaxdon e, 32)] →
      S2.regs rn w = S1.regs rn w := fun rn w hp =>
    hq (rn, w) (List.mem_append_right _ hp)
  apply domainState_ext'
  · rfl
  · rfl
  · rfl
  · show (Hw.absDom S2 e).slotGen = (Hw.absDom S1 e).slotGen
    funext s
    show S2.regs (Hw.dgen e s) 8 = S1.regs (Hw.dgen e s) 8
    rw [hg s]
  · rfl
  · show (Hw.absDom S2 e).regions = (Hw.absDom S1 e).regions
    funext r
    show (if S2.regs (Hw.drgnV e r) 1 = 1 then _ else none)
      = (if S1.regs (Hw.drgnV e r) 1 = 1 then _ else none)
    rw [hr r (Hw.drgnV e r) 1 (by simp), hr r (Hw.drgn e r) 42 (by simp)]
  · show decRun (S2.regs (Hw.drun e) 2) (S2.regs (Hw.drunG e) 2)
      = decRun (S1.regs (Hw.drun e) 2) (S1.regs (Hw.drunG e) 2)
    rw [ht (Hw.drun e) 2 (by simp), ht (Hw.drunG e) 2 (by simp)]
  · show (if S2.regs (Hw.dsrvV e) 1 = 1 then _ else none)
      = (if S1.regs (Hw.dsrvV e) 1 = 1 then _ else none)
    rw [ht (Hw.dsrvV e) 1 (by simp), ht (Hw.dsrv e) 2 (by simp)]
  · show S2.regs (Hw.dcause e) 32 = S1.regs (Hw.dcause e) 32
    rw [ht (Hw.dcause e) 32 (by simp)]
  · show (S2.regs (Hw.dbudget e) 32).toNat = (S1.regs (Hw.dbudget e) 32).toNat
    rw [ht (Hw.dbudget e) 32 (by simp)]
  · show (S2.regs (Hw.dmaxdon e) 32).toNat
      = (S1.regs (Hw.dmaxdon e) 32).toNat
    rw [ht (Hw.dmaxdon e) 32 (by simp)]

private theorem quietCap_notin_dup (x e : DomainId) :
    ∀ q ∈ domQuietNamesCap x, q ∉ (dupFull e).regWrites := by
  fin_cases x <;> fin_cases e <;> decide +kernel

private theorem read_notin_dup_ne (x e : DomainId) (hne : x ≠ e) :
    ∀ q ∈ domReadNames x, q ∉ (dupFull e).regWrites := by
  fin_cases x <;> fin_cases e <;>
    first
      | exact absurd rfl hne
      | decide +kernel

private theorem gate_notin_dup (g : GateId) (e : DomainId) :
    ∀ q ∈ gateReadNames g, q ∉ (dupFull e).regWrites := by
  fin_cases g <;> fin_cases e <;> decide +kernel

private theorem ifv_notin_dupX (e : DomainId) :
    (("if_v" : String), (1 : Nat)) ∉
      (Hw.seqAll
        [ Hw.installA e (Hw.freeSlotIdx e)
            (.mux (Hw.kIsMem (Hw.dupSel e).kindW)
              (Hw.narrowKindE (Hw.dupSel e).kindW (Hw.readReg e Hw.rs2E))
              (Hw.dupSel e).kindW)
            (.lit 1) (Hw.freeCellIdx e)
            (Hw.encRefE (Hw.dLit e) (Hw.dupSel e).slot (Hw.dupSel e).gen),
          Hw.writeReg e Hw.rdE (Hw.handleE (Hw.freeSlotIdx e)
            (Hw.genOfE e (Hw.freeSlotIdx e))
            (Hw.field (Hw.dupSel e).kindW 0 1)),
          Hw.pcAdvA e ]).regWrites := by
  fin_cases e <;> decide +kernel

/-- 4-bit `finOfBv`/`ofNat` round-trip (slot and cell indices). -/
theorem finOfBv_ofNat4 {k : Nat} (h : (2:Nat) ^ 4 = k) (t : Fin k) :
    finOfBv h (BitVec.ofNat 4 t.val) = t := by
  apply Fin.ext
  show (BitVec.ofNat 4 t.val).toNat = t.val
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := t.isLt; omega)

/-! ## The `cap_dup` arm: head + spec do-term -/

set_option maxHeartbeats 51200000 in
/-- The `cap_dup` retirement arm (opcode 16). -/
theorem square_retire_dup (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 16#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (16#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (16#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hdupmn : (Hw.isMn "cap_dup").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "cap_dup" = 16#6).symm
  have hret := retiringE_one σ hifv hcl
  have hin : Inert σ := Inert.of_benign7 σ (fun mn' hmn' =>
    isMn_ne_of_opc σ mn' 16#6 hopc
      ((by decide +kernel : ∀ mn' ∈ ["cap_drop", "cap_revoke", "gate_call",
        "gate_return", "move"], (16#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn'))
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 16#6 hopc (by decide +kernel))
  have hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "unmap" 16#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 16#6 hopc (by decide +kernel))
  have hben5 : ∀ mn ∈ memMns, (Hw.isMn mn).eval σ ≠ 1#1 := fun mn hmn =>
    isMn_ne_of_opc σ mn 16#6 hopc
      ((by decide +kernel : ∀ mn ∈ memMns, (16#6 : BitVec 6)
        ≠ Hw.opcodeOf mn) mn hmn)
  have hselC := retireFor_sel_of_opc σ E "cap_dup" 16#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨Hw.ladder E (Hw.dupChecks E) (Hw.seqAll
      [ Hw.installA E (Hw.freeSlotIdx E)
          (.mux (Hw.kIsMem (Hw.dupSel E).kindW)
            (Hw.narrowKindE (Hw.dupSel E).kindW (Hw.readReg E Hw.rs2E))
            (Hw.dupSel E).kindW)
          (.lit 1) (Hw.freeCellIdx E)
          (Hw.encRefE (Hw.dLit E) (Hw.dupSel E).slot (Hw.dupSel E).gen),
        Hw.writeReg E Hw.rdE (Hw.handleE (Hw.freeSlotIdx E)
          (Hw.genOfE E (Hw.freeSlotIdx E))
          (Hw.field (Hw.dupSel E).kindW 0 1)),
        Hw.pcAdvA E ]),
      .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_right _ (List.mem_cons_self ..))
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ)
      = refillPhase m (Hw.abs σ) := abs_refill m hwf hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y
    rw [← habs1]
    rfl
  have hR1 : (Hw.readReg E Hw.rs1E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs1 :=
    readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl
  have hR2 : (Hw.readReg E Hw.rs2E).eval σ
      = ((Hw.abs σ).doms E).reg (operandsOf W).rs2 :=
    readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl
  set HWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs1 with hHWv
  set DWv := ((Hw.abs σ).doms E).reg (operandsOf W).rs2 with hDWv
  have hSPr : ∀ rs : RegId,
      ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg rs
        = ((Hw.abs σ).doms E).reg rs := fun rs => specReg_bridge m σ E rs
  have hSval : (finOfBv (by decide : 2 ^ 4 = numSlots)
      (HWv.extractLsb' 0 4)).val
      = (((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 0 4).toNat := by
    rw [hR1]
    rfl
  have hlivE := capSel_live_eval σ E (Hw.readReg E Hw.rs1E) _ hSval
  rw [hR1] at hlivE
  have hkwE : (Hw.dupSel E).kindW.eval σ
      = σ.regs (Hw.dcapKind E (finOfBv (by decide)
          (HWv.extractLsb' 0 4))) 32 :=
    capSel_kindW_eval σ E (Hw.readReg E Hw.rs1E) _ hSval
  have hcore0 : corePhase m (refillPhase m (Hw.abs σ))
      = retire { refillPhase m (Hw.abs σ) with inflight := none } E W := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
  have hDO : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
      = (match ((SpecM.reg E (operandsOf W).rs1 >>= fun hw =>
          SpecM.reg E (operandsOf W).rs2 >>= fun dw =>
          Machines.Lnp64u.Isa.capLive E hw >>= fun x =>
          match x with
          | (s, g, e) =>
            match e.kind with
            | .mem base len perms =>
                Machines.Lnp64u.Isa.narrow base len perms dw >>= fun kind =>
                Machines.Lnp64u.Isa.allocDerived E kind ⟨E, s, g⟩ >>=
                  fun h => SpecM.setReg E (operandsOf W).rd h
            | .gate gid =>
                (pure (CapKind.gate gid) : SpecM CapKind) >>= fun kind =>
                Machines.Lnp64u.Isa.allocDerived E kind ⟨E, s, g⟩ >>=
                  fun h => SpecM.setReg E (operandsOf W).rd h)
          (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))) with
        | .ok _ σ' => σ'
        | .err e σ' =>
            σ'.setDom E fun ds => ds.setReg (operandsOf W).rd e.toWord
        | .fault fl => haltWith { refillPhase m (Hw.abs σ) with inflight := none } E fl) := by
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl
  have hladder : ∀ acc : Loom.Hw.St, (Hw.retireFor E).run σ acc
      = (
          if (Expr.not (Hw.dupSel E).live).eval σ = 1#1
          then (Hw.respA E (.err .staleHandle)).run σ acc
          else if (Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1
          then (Hw.respA E (.err .badCap)).run σ acc
          else if (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14) (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14) (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1
          then (Hw.respA E (.err .outOfRange)).run σ acc
          else if (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.not (Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)))).eval σ = 1#1
          then (Hw.respA E (.err .outOfRange)).run σ acc
          else if (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))])).eval σ = 1#1
          then (Hw.respA E (.err .permDenied)).run σ acc
          else if (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ = 1#1
          then (Hw.respA E (.err .permDenied)).run σ acc
          else if (Expr.not (Hw.freeSlotV E)).eval σ = 1#1
          then (Hw.respA E (.err .slotOccupied)).run σ acc
          else if (Expr.not (Hw.freeCellV E)).eval σ = 1#1
          then (Hw.respA E (.err .noLineage)).run σ acc
          else (Hw.seqAll
            [ Hw.installA E (Hw.freeSlotIdx E)
                (.mux (Hw.kIsMem (Hw.dupSel E).kindW)
                  (Hw.narrowKindE (Hw.dupSel E).kindW (Hw.readReg E Hw.rs2E))
                  (Hw.dupSel E).kindW)
                (.lit 1) (Hw.freeCellIdx E)
                (Hw.encRefE (Hw.dLit E) (Hw.dupSel E).slot (Hw.dupSel E).gen),
              Hw.writeReg E Hw.rdE (Hw.handleE (Hw.freeSlotIdx E)
                (Hw.genOfE E (Hw.freeSlotIdx E))
                (Hw.field (Hw.dupSel E).kindW 0 1)),
              Hw.pcAdvA E ]).run σ acc) := by
    intro acc
    rw [hselC acc]
    rfl
  have hRD : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs1 = HWv :=
    hSPr (operandsOf W).rs1
  have hRD2 : (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).reg (operandsOf W).rs2 = DWv :=
    hSPr (operandsOf W).rs2
  by_cases hlv : σ.regs (Hw.dcapV E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1
      ∧ σ.regs (Hw.dgen E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 8 = HWv.extractLsb' 4 8
      ∧ HWv.extractLsb' 4 8 ≠ 0
  case neg =>
    -- stale handle
    have hlive0 : ¬((Hw.dupSel E).live.eval σ = 1#1) :=
      fun hc => hlv (hlivE.mp hc)
    have hlcN : ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = none := by
      rw [specLiveCap_bridge, abs_liveCap]
      exact if_neg hlv
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.staleHandle.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_pos (show (Expr.not (Hw.dupSel E).live).eval σ = 1#1 from by
          show ~~~((Hw.dupSel E).live.eval σ) = 1#1
          rw [bv1_ne_one.mp hlive0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcN]
      rfl
  case pos =>
  have hliv1 : (Hw.dupSel E).live.eval σ = 1#1 := hlivE.mpr hlv
  have hlcS : ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
      (Handle.decode HWv).slot (Handle.decode HWv).gen
      = some { kind := Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)
               lineage := if σ.regs (Hw.dcapLinV E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 1 = 1#1
                 then some (finOfBv (by decide)
                   (σ.regs (Hw.dcapLin E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 4))
                 else none } := by
    rw [specLiveCap_bridge, abs_liveCap]
    exact if_pos hlv
  obtain ⟨ce, hlcS', hcek⟩ :
      ∃ c0 : CapEntry, ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E)).liveCap
        (Handle.decode HWv).slot (Handle.decode HWv).gen = some c0
      ∧ c0.kind = Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) := ⟨_, hlcS, rfl⟩
  have hclsE2 : (Hw.dupSel E).clsOk.eval σ
      = (if (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 0 1 = HWv.extractLsb' 12 1
        then (1#1 : BitVec 1) else 0#1) := by
    show (if ((Hw.dupSel E).kindW.eval σ).extractLsb' 0 1
        = ((Hw.readReg E Hw.rs1E).eval σ).extractLsb' 12 1
      then (1#1 : BitVec 1) else 0#1) = _
    simp only [hkwE, hR1]
  by_cases hbit : HWv.getLsbD 12 = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 0
  case neg =>
    -- class mismatch
    have hcls0 : ¬((Hw.dupSel E).clsOk.eval σ = 1#1) := by
      rw [hclsE2]
      intro h
      by_cases hcx : (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 0 1 = HWv.extractLsb' 12 1
      · exact hbit ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) HWv 0 12).mp hcx).symm
      · rw [if_neg hcx] at h
        exact absurd h (by decide)
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.badCap.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_pos (show (Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1 from by
          show ~~~((Hw.dupSel E).clsOk.eval σ) = 1#1
          rw [bv1_ne_one.mp hcls0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [show (decide ((Handle.decode HWv).cls
          = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).cls)) = false from decide_eq_false
        (fun hA => hbit ((cls_eq_iff_bits HWv (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mp hA))]
      rfl
  case pos =>
  have hcls1 : (Hw.dupSel E).clsOk.eval σ = 1#1 := by
    rw [hclsE2]
    rw [if_pos ((extract1_eq_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) HWv 0 12).mpr hbit.symm)]
  have hdecT : (decide ((Handle.decode HWv).cls
      = (Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).cls)) = true :=
    decide_eq_true ((cls_eq_iff_bits HWv (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mpr hbit)
  by_cases hmem : (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 0 = false
  case neg =>
    -- gate kind: narrowing skipped
    sorry
  case pos =>
  -- memory kind: narrowing applies
  have hmk : Hw.decKind (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) = .mem ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12)
      ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13) (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) :=
    (decKind_mem_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32)).mp hmem
  have hkm1 : (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = 1#1 := by
    show (if ((Hw.dupSel E).kindW.eval σ).extractLsb' 0 1
        = (Expr.lit 0).eval σ then (1#1 : BitVec 1) else 0#1) = 1#1
    rw [show ((Expr.lit 0 : Expr 1)).eval σ = 0#1 from rfl]
    simp only [hkwE]
    rw [if_pos ((extract1_eq_zero_iff (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 0).mpr hmem)]
  have hklenE : (Hw.kLen (Hw.dupSel E).kindW).eval σ
      = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13 := by
    show ((Hw.dupSel E).kindW.eval σ).extractLsb' 13 13 = _
    rw [hkwE]
  have hkbaseE : (Hw.kBase (Hw.dupSel E).kindW).eval σ
      = (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12 := by
    show ((Hw.dupSel E).kindW.eval σ).extractLsb' 1 12 = _
    rw [hkwE]
  have hoffE : (Hw.descOffE (Hw.readReg E Hw.rs2E)).eval σ = DWv.extractLsb' 5 12 := by
    show ((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12 = _
    rw [hR2]
  have hlenE : (Hw.descLenE (Hw.readReg E Hw.rs2E)).eval σ = DWv.extractLsb' 17 13 := by
    show ((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 17 13 = _
    rw [hR2]
  -- range check
  by_cases hr1 : ((DWv.extractLsb' 5 12).toNat
      + (DWv.extractLsb' 17 13).toNat ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)
  case neg =>
    -- narrow out of range
    have hc3 : (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14) (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14) (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1 := by
      show ((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
        (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14)
          (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
            (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ) = 1#1
      rw [hkm1]
      rw [(ultE_eval _ _ σ).mpr (by
        show (((Hw.kLen (Hw.dupSel E).kindW).eval σ).setWidth 14).toNat
          < ((((Hw.descOffE (Hw.readReg E Hw.rs2E)).eval σ).setWidth 14)
            + (((Hw.descLenE (Hw.readReg E Hw.rs2E)).eval σ).setWidth 14)).toNat
        rw [hklenE, hoffE, hlenE, toNat_setWidth_le (by omega)]
        rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
          toNat_setWidth_le (by omega)]
        have b1 := (DWv.extractLsb' 5 12).isLt
        have b2 := (DWv.extractLsb' 17 13).isLt
        rw [Nat.mod_eq_of_lt (by omega)]
        omega)]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.outOfRange.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_pos hc3]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = false from
        decide_eq_false hr1]
      rfl
  case pos =>
  have hc3z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14) (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14) (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
      (Expr.ult (.zext (Hw.kLen (Hw.dupSel E).kindW) 14)
        (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
          (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ = 1#1)
    rw [bv1_ne_one.mp (show ¬((Expr.ult
        (.zext (Hw.kLen (Hw.dupSel E).kindW) 14)
        (.add (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 14)
          (.zext (Hw.descLenE (Hw.readReg E Hw.rs2E)) 14))).eval σ = 1#1) from by
      intro hc
      have h2 : ((((Hw.dupSel E).kindW.eval σ).extractLsb' 13 13
          ).setWidth 14).toNat
          < (((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
            ).setWidth 14)
            + ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 17 13
              ).setWidth 14)).toNat :=
        (ultE_eval _ _ σ).mp hc
      rw [hkwE, hR2] at h2
      rw [toNat_setWidth_le (by omega), BitVec.toNat_add,
        toNat_setWidth_le (by omega), toNat_setWidth_le (by omega)] at h2
      have b1 := (DWv.extractLsb' 5 12).isLt
      have b2 := (DWv.extractLsb' 17 13).isLt
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      omega)]
    generalize (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = b
    revert b
    decide
  -- one-bit extract as ofBool (for the perm-bit walks)
  have hEx1 : ∀ {n : Nat} (x : BitVec n) (i : Nat),
      x.extractLsb' i 1 = BitVec.ofBool (x.getLsbD i) := by
    intro n x i
    cases h : x.getLsbD i
    · rw [(extract1_eq_zero_iff x i).mpr h]; rfl
    · rw [(extract1_eq_one_iff x i).mpr h]; rfl
  -- no-wrap check
  by_cases hr2 : (((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
      + (DWv.extractLsb' 5 12).toNat < 4096)
  case neg =>
    -- narrowed base out of physical memory
    have hult0 : ¬((Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ = 1#1) := by
      intro hc
      have h2 : ((((Hw.dupSel E).kindW.eval σ).extractLsb' 1 12
          ).setWidth 13
          + (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
            ).setWidth 13).toNat
          < ((4096 : BitVec 13)).toNat :=
        (ultE_eval _ _ σ).mp hc
      rw [hkwE, hR2] at h2
      rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
        toNat_setWidth_le (by omega)] at h2
      have b1 := ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).isLt
      have b2 := (DWv.extractLsb' 5 12).isLt
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      exact hr2 (by
        have h3 : ((4096 : BitVec 13)).toNat = 4096 := rfl
        omega)
    have hc4 : (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
        (Expr.not (Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)))).eval σ = 1#1 := by
      show ((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
        ~~~((Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ)) = 1#1
      rw [hkm1, bv1_ne_one.mp hult0]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.outOfRange.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_neg hc3z,
        if_pos hc4]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = false from decide_eq_false hr2]
      rfl
  case pos =>
  have hult1 : (Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ = 1#1 := by
    rw [ultE_eval]
    show ((((Hw.dupSel E).kindW.eval σ).extractLsb' 1 12).setWidth 13
      + (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 5 12
        ).setWidth 13).toNat < ((4096 : BitVec 13)).toNat
    rw [hkwE, hR2]
    rw [BitVec.toNat_add, toNat_setWidth_le (by omega),
      toNat_setWidth_le (by omega)]
    have b1 := ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).isLt
    have b2 := (DWv.extractLsb' 5 12).isLt
    rw [Nat.mod_eq_of_lt (by omega)]
    show _ < (4096 : BitVec 13).toNat
    have h3 : ((4096 : BitVec 13)).toNat = 4096 := rfl
    omega
  have hc4z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
      (Expr.not (Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
      ~~~((Expr.ult (.add (.zext (Hw.kBase (Hw.dupSel E).kindW) 13) (.zext (Hw.descOffE (Hw.readReg E Hw.rs2E)) 13)) (.lit 4096)).eval σ) = 1#1)
    rw [hult1]
    generalize (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = b
    revert b
    decide
  -- permission checks
  have hpermsOr : ((Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))]).eval σ = 1#1)
      ↔ ¬((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) = true) := by
    show ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 2 1 &&&
        ~~~(((Hw.dupSel E).kindW.eval σ).extractLsb' 26 1)) |||
      ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 3 1 &&&
        ~~~(((Hw.dupSel E).kindW.eval σ).extractLsb' 27 1)) |||
       (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 4 1 &&&
        ~~~(((Hw.dupSel E).kindW.eval σ).extractLsb' 28 1)))) = 1#1 ↔ _
    rw [hkwE, hR2]
    rw [show (Machines.Lnp64u.Isa.descPerms DWv)
        = ⟨DWv.getLsbD 2, DWv.getLsbD 3, DWv.getLsbD 4⟩ from rfl]
    rw [show (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))
        = ⟨(σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 26, (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 27, (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 28⟩ from by
      show (⟨((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 0,
        ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 1,
        ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3).getLsbD 2⟩ : Perms) = _
      simp [BitVec.getLsbD_extractLsb']]
    rw [hEx1 DWv 2, hEx1 DWv 3, hEx1 DWv 4,
      hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 26, hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 27, hEx1 (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32) 28]
    cases DWv.getLsbD 2 <;> cases DWv.getLsbD 3 <;> cases DWv.getLsbD 4 <;>
      cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 26 <;> cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 27 <;>
      cases (σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).getLsbD 28 <;> simp [Perms.le]
  by_cases hr3 : ((Machines.Lnp64u.Isa.descPerms DWv).le
      (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)) = true)
  case neg =>
    -- permission escalation
    have hc5 : (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))])).eval σ
        = 1#1 := by
      show ((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
        (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))]).eval σ) = 1#1
      rw [hkm1, hpermsOr.mpr hr3]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.permDenied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_neg hc3z,
        if_neg hc4z,
        if_pos hc5]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = false from by
        cases h : ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3)))
        · rfl
        · exact absurd h hr3]
      rfl
  case pos =>
  have hc5z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
      (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))])).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
      (Hw.orAll [.and (Hw.descR (Hw.readReg E Hw.rs2E)) (.not (Hw.kR (Hw.dupSel E).kindW)), .and (Hw.descW (Hw.readReg E Hw.rs2E)) (.not (Hw.kW (Hw.dupSel E).kindW)), .and (Hw.descX (Hw.readReg E Hw.rs2E)) (.not (Hw.kX (Hw.dupSel E).kindW))]).eval σ = 1#1)
    rw [bv1_ne_one.mp (fun hc => (hpermsOr.mp hc) hr3)]
    generalize (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = b
    revert b
    decide
  -- W^X check
  have hwxOr : ((Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ = 1#1)
      ↔ ¬((Machines.Lnp64u.Isa.descPerms DWv).wx = true) := by
    show ((((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 3 1) &&&
      (((Hw.readReg E Hw.rs2E).eval σ).extractLsb' 4 1)) = 1#1 ↔ _
    rw [hR2]
    rw [show (Machines.Lnp64u.Isa.descPerms DWv)
        = ⟨DWv.getLsbD 2, DWv.getLsbD 3, DWv.getLsbD 4⟩ from rfl]
    rw [hEx1 DWv 3, hEx1 DWv 4]
    cases DWv.getLsbD 3 <;> cases DWv.getLsbD 4 <;> simp [Perms.wx]
  by_cases hr4 : ((Machines.Lnp64u.Isa.descPerms DWv).wx = true)
  case neg =>
    -- W^X violation
    have hc6 : (Expr.and (Hw.kIsMem (Hw.dupSel E).kindW) (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ
        = 1#1 := by
      show ((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
        (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ) = 1#1
      rw [hkm1, hwxOr.mpr hr4]
      decide
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.permDenied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_neg hc3z,
        if_neg hc4z,
        if_neg hc5z,
        if_pos hc6]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = false from by
        cases h : ((Machines.Lnp64u.Isa.descPerms DWv).wx)
        · rfl
        · exact absurd h hr4]
      rfl
  case pos =>
  have hc6z : ¬((Expr.and (Hw.kIsMem (Hw.dupSel E).kindW)
      (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E)))).eval σ = 1#1) := by
    show ¬((Hw.kIsMem (Hw.dupSel E).kindW).eval σ &&&
      (Expr.and (Hw.descW (Hw.readReg E Hw.rs2E)) (Hw.descX (Hw.readReg E Hw.rs2E))).eval σ = 1#1)
    rw [bv1_ne_one.mp (fun hc => absurd hr4 (fun h4 =>
      (hwxOr.mp hc) h4))]
    generalize (Hw.kIsMem (Hw.dupSel E).kindW).eval σ = b
    revert b
    decide
  -- free-slot / free-cell bridges (the pc bump touches neither table)
  have hcapsB : ∀ s : Slot, (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).caps s
      = ((Hw.abs σ).doms E).caps s := fun s => by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
      ({ (refillPhase m (Hw.abs σ)).doms E with
        pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).caps s = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).caps s = _
    rw [refillPhase_caps]
  have hgenB : ∀ s : Slot, (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).slotGen s
      = ((Hw.abs σ).doms E).slotGen s := fun s => by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
      ({ (refillPhase m (Hw.abs σ)).doms E with
        pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).slotGen s
      = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).slotGen s = _
    rw [refillPhase_slotGen]
  have hlinB : ∀ l : LineageId, (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).doms E).lineage l
      = ((Hw.abs σ).doms E).lineage l := fun l => by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E
      ({ (refillPhase m (Hw.abs σ)).doms E with
        pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 })) E).lineage l
      = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).lineage l = _
    rw [refillPhase_lineage]
  have hfsB : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).freeSlot E = (Hw.abs σ).freeSlot E :=
    freeSlot_congr _ _ E hcapsB hgenB
  have hfcB : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E (fun ds => { ds with pc := ds.pc + 1 }))).freeCell E = (Hw.abs σ).freeCell E :=
    freeCell_congr _ _ E hlinB
  cases hfs : (Hw.abs σ).freeSlot E with
  | none =>
    -- no free slot
    have hfsv0 : ¬((Hw.freeSlotV E).eval σ = 1#1) := fun hc => by
      have h2 := (freeSlotV_eval σ E).mp hc
      rw [hfs] at h2
      exact absurd h2 (by decide)
    refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
      hswz hben5 E rfl Errno.slotOccupied.toWord ?_ ?_
    · intro acc
      rw [hladder acc,
        if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
          rw [hliv1]
          decide),
        if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
          show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
          rw [hcls1]
          decide),
        if_neg hc3z,
        if_neg hc4z,
        if_neg hc5z,
        if_neg hc6z,
        if_pos (show (Expr.not (Hw.freeSlotV E)).eval σ = 1#1 from by
          show ~~~((Hw.freeSlotV E).eval σ) = 1#1
          rw [bv1_ne_one.mp hfsv0]
          decide)]
      rfl
    · rw [hcore0, hDO]
      simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
        SpecM.reg, SpecM.load, SpecM.demand,
        Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
        SpecM.modify, specM_pure]
      simp only [hRD, hRD2]
      simp only [hlcS', hcek]
      rw [hdecT]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [hcek]
      simp only [hmk]
      simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
        SpecM.raise, specM_pure]
      rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
          + (Machines.Lnp64u.Isa.descLen DWv).toNat
          ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
        decide_eq_true hr1]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
          + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
          = true from decide_eq_true hr2]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
          (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
      simp only [reduceIte, specM_bind, specM_pure]
      rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = true from hr4]
      simp only [reduceIte, specM_bind, specM_pure]
      simp only [Machines.Lnp64u.Isa.allocDerived, SpecM.get, specM_bind,
        SpecM.raise, specM_pure]
      rw [hfsB.trans hfs]
      rfl
  | some NS =>
    have hfsv1 : (Hw.freeSlotV E).eval σ = 1#1 :=
      (freeSlotV_eval σ E).mpr (by rw [hfs]; rfl)
    cases hfc : (Hw.abs σ).freeCell E with
    | none =>
      -- no free lineage cell
      have hfcv0 : ¬((Hw.freeCellV E).eval σ = 1#1) := fun hc => by
        have h2 := (freeCellV_eval σ E).mp hc
        rw [hfc] at h2
        exact absurd h2 (by decide)
      refine map_err_common m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
        hswz hben5 E rfl Errno.noLineage.toWord ?_ ?_
      · intro acc
        rw [hladder acc,
          if_neg (show ¬((Expr.not (Hw.dupSel E).live).eval σ = 1#1) from by
            show ¬(~~~((Hw.dupSel E).live.eval σ) = 1#1)
            rw [hliv1]
            decide),
          if_neg (show ¬((Expr.not (Hw.dupSel E).clsOk).eval σ = 1#1) from by
            show ¬(~~~((Hw.dupSel E).clsOk.eval σ) = 1#1)
            rw [hcls1]
            decide),
          if_neg hc3z,
          if_neg hc4z,
          if_neg hc5z,
          if_neg hc6z,
          if_neg (show ¬((Expr.not (Hw.freeSlotV E)).eval σ = 1#1) from by
            show ¬(~~~((Hw.freeSlotV E).eval σ) = 1#1)
            rw [hfsv1]
            decide),
          if_pos (show (Expr.not (Hw.freeCellV E)).eval σ = 1#1 from by
            show ~~~((Hw.freeCellV E).eval σ) = 1#1
            rw [bv1_ne_one.mp hfcv0]
            decide)]
        rfl
      · rw [hcore0, hDO]
        simp only [specM_bind, SpecM.get, SpecM.require, SpecM.raise,
          SpecM.reg, SpecM.load, SpecM.demand,
          Machines.Lnp64u.Isa.capLive, SpecM.set, SpecM.setReg,
          SpecM.modify, specM_pure]
        simp only [hRD, hRD2]
        simp only [hlcS', hcek]
        rw [hdecT]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [hcek]
        simp only [hmk]
        simp only [Machines.Lnp64u.Isa.narrow, specM_bind, SpecM.require,
          SpecM.raise, specM_pure]
        rw [show (decide ((Machines.Lnp64u.Isa.descOff DWv).toNat
            + (Machines.Lnp64u.Isa.descLen DWv).toNat
            ≤ ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 13 13).toNat)) = true from
          decide_eq_true hr1]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show (decide ((((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 1 12).toNat
            + (Machines.Lnp64u.Isa.descOff DWv).toNat < memWords)))
            = true from decide_eq_true hr2]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show ((Machines.Lnp64u.Isa.descPerms DWv).le
            (Hw.decPerms ((σ.regs (Hw.dcapKind E (finOfBv (by decide) (HWv.extractLsb' 0 4))) 32).extractLsb' 26 3))) = true from hr3]
        simp only [reduceIte, specM_bind, specM_pure]
        rw [show ((Machines.Lnp64u.Isa.descPerms DWv).wx) = true from hr4]
        simp only [reduceIte, specM_bind, specM_pure]
        simp only [Machines.Lnp64u.Isa.allocDerived, SpecM.get, specM_bind,
          SpecM.raise, specM_pure]
        rw [hfsB.trans hfs]
        simp only [specM_bind, specM_pure]
        rw [hfcB.trans hfc]
        rfl
    | some NL =>
      -- install (mem kind)
      sorry

end Machines.Lnp64u.Theorems.RMC
