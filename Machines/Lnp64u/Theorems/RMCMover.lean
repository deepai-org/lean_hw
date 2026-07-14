-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCBridge
import Machines.Lnp64u.Logic.PhaseLemmas

/-!
# R-MC support: the Mover bridge (quiescent-core case)

`moverAct` re-derives the *post-core* state from pre-cycle registers
(D9): the kill sweeps, the retiring `move`'s job install, and same-cycle
store forwarding are all mux trees gated on `retiringE`. On a cycle where
no instruction retires (`retiringE = 0` — the countdown and idle arms of
the square), every one of those gates is off and the rule collapses to
`Step.moverPhase` over the plain registers.

This file proves that collapse:

* quiescence lemmas — each derived signal falls back to its register;
* `absMover_moverAct_quiescent` / `moverAct_mem_quiescent` — the two
  faces of the bridge, stated against any spec state `τ` that agrees with
  the abstraction on the Mover's read set (job, cap tables, regions,
  memory), which is how the square's arms instantiate it after the
  refill/core phases.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-! ## Quiescence: every retire-gated signal falls back to its register -/

private theorem bv1_zero_and (x : BitVec 1) : 0#1 &&& x = 0#1 := by
  revert x; decide

private theorem bv1_and_zero (x : BitVec 1) : x &&& 0#1 = 0#1 := by
  revert x; decide

/-- An `andAll` chain is off when any link is. -/
theorem andAll_zero_of_mem (σ : Loom.Hw.St) {L : List (Expr 1)} {e : Expr 1}
    (he : e ∈ L) (h0 : e.eval σ ≠ 1#1) : (Hw.andAll L).eval σ = 0#1 :=
  bv1_ne_one.mp fun h => h0 ((andAll_eval σ L).mp h e he)

/-- An `orAll` tree is off when every leaf is. -/
theorem orAll_zero (σ : Loom.Hw.St) {L : List (Expr 1)}
    (h : ∀ e ∈ L, e.eval σ ≠ 1#1) : (Hw.orAll L).eval σ = 0#1 :=
  bv1_ne_one.mp fun hc =>
    let ⟨e, hm, he⟩ := (orAll_eval σ L).mp hc
    h e hm he

/-- **Core inertness for the Mover rule.** The four gate families through
which a retiring instruction can reach the Mover's re-derivation trees are
all off. Holds on non-retiring cycles (countdown/idle/issue arms) and on
cycles retiring an op that neither kills references, installs a job,
edits regions, nor stores (the benign retirement arms). -/
structure Inert (σ : Loom.Hw.St) : Prop where
  killed : ∀ (dm : Expr 2) (sl : Expr 4),
    (Hw.killedByCoreE dm sl).eval σ = 0#1
  newJob : ∀ d : DomainId, (Hw.newJobSet d).eval σ = 0#1
  mapSet : ∀ (c : DomainId) (r : RegionId),
    (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
      .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1
  unmapSet : ∀ (c : DomainId) (r : RegionId),
    (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
      .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1
  swHit : ∀ (d : DomainId) (srcCur : Expr 12),
    (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
      Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
        ⟨false, true, false⟩,
      .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
        srcCur]).eval σ = 0#1

/-- `killedByCoreE` is off on an inert cycle. -/
theorem killedByCoreE_quiescent (σ : Loom.Hw.St)
    (hnr : Inert σ) (dm : Expr 2) (sl : Expr 4) :
    (Hw.killedByCoreE dm sl).eval σ = 0#1 :=
  hnr.killed dm sl

/-- `newJobSet` is off on an inert cycle. -/
theorem newJobSet_quiescent (σ : Loom.Hw.St)
    (hnr : Inert σ) (d : DomainId) :
    (Hw.newJobSet d).eval σ = 0#1 :=
  hnr.newJob d

/-- `postJ` falls back to the current register on an inert cycle. -/
theorem postJ_quiescent {w : Nat} (σ : Loom.Hw.St)
    (hnr : Inert σ) (f : DomainId → Expr w)
    (cur : Expr w) :
    (Hw.postJ f cur).eval σ = cur.eval σ := by
  show ((List.finRange numDomains).foldr
    (fun d acc => Expr.mux (Hw.newJobSet d) (f d) acc) cur).eval σ = _
  induction (List.finRange numDomains) with
  | nil => rfl
  | cons d t ih =>
      show (if (Hw.newJobSet d).eval σ = 1#1 then _ else _) = _
      rw [newJobSet_quiescent σ hnr d]
      simpa using ih


private theorem bv1_and_one (x : BitVec 1) : x &&& 1#1 = x := by
  revert x; decide

private theorem bv1_or_zero (x : BitVec 1) : 0#1 ||| x = x := by
  revert x; decide

private theorem bv1_not_zero : ~~~(0#1) = 1#1 := by decide

/-- The head-`retiringE` `andAll` chains are off on a non-retiring cycle. -/
private theorem andAll_retiring_quiescent (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) (rest : List (Expr 1)) :
    (Hw.andAll (Hw.retiringE :: rest)).eval σ = 0#1 := by
  cases rest with
  | nil => exact hnr
  | cons e t =>
      show Hw.retiringE.eval σ &&& _ = 0#1
      rw [hnr]
      exact bv1_zero_and _

/-- Every gate family is off on a non-retiring cycle. -/
theorem Inert.of_nonretiring (σ : Loom.Hw.St)
    (hnr : Hw.retiringE.eval σ = 0#1) : Inert σ where
  killed dm sl := by
    show Hw.retiringE.eval σ &&& _ = 0#1
    rw [hnr]
    exact bv1_zero_and _
  newJob d := andAll_retiring_quiescent σ hnr _
  mapSet c r := andAll_retiring_quiescent σ hnr _
  unmapSet c r := andAll_retiring_quiescent σ hnr _
  swHit d srcCur := andAll_retiring_quiescent σ hnr _

/-- Every gate family is off when the latched mnemonic is none of the
Mover-relevant ops (kill ops, `move`, `map`/`unmap`, `sw`) — the benign
retirement arms. -/
theorem Inert.of_benign (σ : Loom.Hw.St)
    (hben : ∀ mn ∈ ["cap_drop", "cap_revoke", "gate_call", "gate_return",
      "move", "map", "unmap", "sw"], (Hw.isMn mn).eval σ ≠ 1#1) :
    Inert σ where
  killed dm sl := by
    have hz : ∀ (mn : String) (Y : Expr 1),
        mn ∈ ["cap_drop", "cap_revoke", "gate_call", "gate_return", "move",
          "map", "unmap", "sw"] →
        ¬(Expr.and (Hw.isMn mn) Y).eval σ = 1#1 := by
      intro mn Y hmn hc
      have hc' : (Hw.isMn mn).eval σ &&& Y.eval σ = 1#1 := hc
      rw [bv1_ne_one.mp (hben mn hmn), bv1_zero_and] at hc'
      exact absurd hc' (by decide)
    show Hw.retiringE.eval σ &&&
      (Hw.orAll ((List.finRange numDomains).map fun d =>
        Expr.and (Hw.ifDomIs d) (Hw.orAll
          [ .and (Hw.isMn "cap_drop")
              (.and (Hw.dropOkE d) (Hw.dropKilled d dm sl)),
            .and (Hw.isMn "cap_revoke")
              (.and (Hw.revOkE d) (Hw.revKilled dm sl)),
            .and (Hw.isMn "gate_call")
              (.and (Hw.callOkE d) (Hw.callKilled d dm sl)),
            .and (Hw.isMn "gate_return")
              (.and (Hw.retOkE d) (Hw.retKilled d dm sl)) ]))).eval σ = 0#1
    rw [orAll_zero σ (by
      intro e he
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp he
      intro hc
      have hc' : (Hw.ifDomIs d).eval σ &&&
          (Hw.orAll
            [ .and (Hw.isMn "cap_drop")
                (.and (Hw.dropOkE d) (Hw.dropKilled d dm sl)),
              .and (Hw.isMn "cap_revoke")
                (.and (Hw.revOkE d) (Hw.revKilled dm sl)),
              .and (Hw.isMn "gate_call")
                (.and (Hw.callOkE d) (Hw.callKilled d dm sl)),
              .and (Hw.isMn "gate_return")
                (.and (Hw.retOkE d) (Hw.retKilled d dm sl)) ]).eval σ = 1#1 :=
        hc
      rw [orAll_zero σ (by
        intro e' he'
        rcases he' with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, h⟩⟩⟩⟩
        · exact hz "cap_drop" _ (List.mem_cons_self ..)
        · exact hz "cap_revoke" _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        · exact hz "gate_call" _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        · exact hz "gate_return" _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
        · exact absurd h (List.not_mem_nil)), bv1_and_zero] at hc'
      exact absurd hc' (by decide))]
    exact bv1_and_zero _
  newJob d := andAll_zero_of_mem σ
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (hben "move" (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))))
  mapSet c r := andAll_zero_of_mem σ
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (hben "map" (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
  unmapSet c r := andAll_zero_of_mem σ
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (hben "unmap" (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..))))))))
  swHit d srcCur := andAll_zero_of_mem σ
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (hben "sw" (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))

/-- `rgnVPostE` falls back to the validity register. -/
theorem rgnVPostE_quiescent (σ : Loom.Hw.St)
    (hnr : Inert σ) (c : DomainId) (r : RegionId) :
    (Hw.rgnVPostE c r).eval σ = σ.regs (Hw.drgnV c r) 1 := by
  show (if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _
    else if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _
    else (Expr.and (.reg 1 (Hw.drgnV c r))
      (.not (Hw.killedByCoreE _ _))).eval σ) = _
  rw [hnr.mapSet c r, hnr.unmapSet c r]
  show (if (0#1 : BitVec 1) = 1#1 then _
    else if (0#1 : BitVec 1) = 1#1 then _ else _) = _
  rw [if_neg (by decide), if_neg (by decide)]
  show σ.regs (Hw.drgnV c r) 1 &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
  rw [killedByCoreE_quiescent σ hnr, bv1_not_zero, bv1_and_one]

/-- `rgnValPostE` falls back to the region register. -/
theorem rgnValPostE_quiescent (σ : Loom.Hw.St)
    (hnr : Inert σ) (c : DomainId) (r : RegionId) :
    (Hw.rgnValPostE c r).eval σ = σ.regs (Hw.drgn c r) 42 := by
  show (if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _
    else (Expr.reg 42 (Hw.drgn c r)).eval σ) = _
  rw [hnr.mapSet c r]
  rw [if_neg (by decide)]
  rfl


/-- The forwarding mux falls back to the memory read. -/
theorem srcWord_quiescent (σ : Loom.Hw.St)
    (hnr : Inert σ) (srcCur : Expr 12) :
    (((List.finRange numDomains).foldr
      (fun d acc =>
        let eaddr : Expr 12 := Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12
        Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
            Hw.domCoversE d eaddr ⟨false, true, false⟩,
            .eq eaddr srcCur])
          (Hw.readReg d Hw.rs2E) acc)
      (.memRead 32 "mem" srcCur)) : Expr 32).eval σ
      = σ.mems "mem" ((srcCur.eval σ)).toNat 32 := by
  induction (List.finRange numDomains) with
  | nil => rfl
  | cons d t ih =>
      show (if (Hw.andAll (Hw.retiringE :: _)).eval σ = 1#1 then _ else _) = _
      rw [hnr.swHit d srcCur, if_neg (by decide)]
      exact ih

/-- `rgnCoversVal` decodes to `Region.covers` of the decoded value. -/
theorem rgnCoversVal_eval (rv : Expr 42) (a : Expr 12) (need : Perms)
    (σ : Loom.Hw.St) :
    ((Hw.rgnCoversVal rv a need).eval σ = 1#1) ↔
      (Hw.decRegion (rv.eval σ)).covers (a.eval σ) need = true := by
  obtain ⟨hr, hw, hx⟩ := decRegion_perm_bits (rv.eval σ)
  have hfb : (Hw.field rv 16 12).eval σ = (rv.eval σ).extractLsb' 16 12 := rfl
  have hbase : ((Expr.not (.ult a (Hw.field rv 16 12))).eval σ = 1#1) ↔
      ((rv.eval σ).extractLsb' 16 12).toNat ≤ (a.eval σ).toNat := by
    rw [notE_eval]
    constructor
    · intro h
      have hn : ¬((Expr.ult a (Hw.field rv 16 12)).eval σ = 1#1) := by
        rw [h]; decide
      rw [ultE_eval, hfb] at hn
      omega
    · intro h
      apply bv1_ne_one.mp
      intro hlt
      rw [ultE_eval, hfb] at hlt
      omega
  have hlen : ((Expr.ult (.zext a 14)
      (.add (.zext (Hw.field rv 16 12) 14)
            (.zext (Hw.field rv 3 13) 14))).eval σ = 1#1) ↔
      (a.eval σ).toNat <
        ((rv.eval σ).extractLsb' 16 12).toNat
          + ((rv.eval σ).extractLsb' 3 13).toNat := by
    rw [ultE_eval]
    show ((a.eval σ).setWidth 14).toNat <
        ((((rv.eval σ).extractLsb' 16 12).setWidth 14) +
         (((rv.eval σ).extractLsb' 3 13).setWidth 14)).toNat ↔ _
    rw [toNat_setWidth_le (by omega), BitVec.toNat_add,
      toNat_setWidth_le (by omega), toNat_setWidth_le (by omega)]
    have hb := ((rv.eval σ).extractLsb' 16 12).isLt
    have hl := ((rv.eval σ).extractLsb' 3 13).isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  have hPR : ((Hw.field rv 0 1).eval σ = 1#1) ↔
      (rv.eval σ).getLsbD 0 = true := extract1_eq_one (rv.eval σ) 0
  have hPW : ((Hw.field rv 1 1).eval σ = 1#1) ↔
      (rv.eval σ).getLsbD 1 = true := extract1_eq_one (rv.eval σ) 1
  have hPX : ((Hw.field rv 2 1).eval σ = 1#1) ↔
      (rv.eval σ).getLsbD 2 = true := extract1_eq_one (rv.eval σ) 2
  rw [Hw.rgnCoversVal, andAll_eval]
  rcases need with ⟨nr, nw, nx⟩
  cases nr <;> cases nw <;> cases nx <;>
  · simp only [reduceIte, List.cons_append, List.nil_append,
      List.forall_mem_cons]
    rw [hbase, hlen]
    simp only [Region.covers, Perms.le, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or,
      Bool.true_and, Bool.and_true, hr, hw, hx, hPR, hPW, hPX,
      Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
      List.cons_append, List.forall_mem_cons, and_assoc]
    try simp [Hw.decRegion]


/-! ## The per-word re-check -/

private theorem extract14_idx (v : BitVec 14) :
    (v.extractLsb' 8 6).toNat
      = (v.extractLsb' 12 2).toNat * 16 + (v.extractLsb' 8 4).toNat := by
  revert v; decide

/-- `kindWAt` at a packed reference's node bits reads the referenced kind
register. -/
theorem kindWAt_ref_eval (σ : Loom.Hw.St) (e : Expr 14) :
    (Hw.kindWAt (Hw.field e 8 6)).eval σ =
      σ.regs (Hw.dcapKind (Hw.decRef (e.eval σ)).dom
        (Hw.decRef (e.eval σ)).slot) 32 := by
  rw [Hw.kindWAt, muxFin_eval (by decide : 2 ^ 6 = numDomains * numSlots)]
  have hnode := nDom_pack (Hw.decRef (e.eval σ)).dom.val
    (Hw.decRef (e.eval σ)).slot.val (Fin.isLt _) (Fin.isLt _)
  have hidx : (finOfBv (by decide : 2 ^ 6 = numDomains * numSlots)
      ((Hw.field e 8 6).eval σ)) =
      (⟨(Hw.decRef (e.eval σ)).dom.val * 16 + (Hw.decRef (e.eval σ)).slot.val,
        by
          have h2 := (Hw.decRef (e.eval σ)).dom.isLt
          have h4 := (Hw.decRef (e.eval σ)).slot.isLt
          show _ < numDomains * numSlots
          simp only [numDomains, numSlots] at *
          omega⟩ : Hw.NodeId) := by
    apply Fin.ext
    show ((e.eval σ).extractLsb' 8 6).toNat = _
    rw [extract14_idx]
    rfl
  rw [hidx, hnode.1, hnode.2]
  rfl

/-- The decoded cap-table entry behind `liveCap`, through the abstraction. -/
theorem abs_liveCap (σ : Loom.Hw.St) (c : DomainId) (s : Slot) (g : Gen) :
    ((Hw.abs σ).doms c).liveCap s g =
      (if σ.regs (Hw.dcapV c s) 1 = 1#1 ∧ σ.regs (Hw.dgen c s) 8 = g ∧ g ≠ 0
       then some
        { kind := Hw.decKind (σ.regs (Hw.dcapKind c s) 32)
          lineage :=
            if σ.regs (Hw.dcapLinV c s) 1 = 1#1 then
              some (finOfBv (by decide) (σ.regs (Hw.dcapLin c s) 4))
            else none }
       else none) := by
  rw [DomainState.liveCap]
  show (match (if σ.regs (Hw.dcapV c s) 1 = 1#1 then _ else none :
      Option CapEntry) with
    | some e => if σ.regs (Hw.dgen c s) 8 = g && g != 0 then some e else none
    | none => none) = _
  by_cases hv : σ.regs (Hw.dcapV c s) 1 = 1#1
  · rw [if_pos hv]
    by_cases hg : σ.regs (Hw.dgen c s) 8 = g
    · by_cases hz : g = 0
      · simp [hg, hz]
      · simp [hg, hv, show ¬g = 0#8 from hz]
    · simp [hg]
  · rw [if_neg hv]
    simp [hv]

/-- The spec's per-word Mover check against any state agreeing with the
abstraction on the cap tables. -/
theorem moverCheck_abs (σ : Loom.Hw.St) (τ : MachineState)
    (hcaps : ∀ d, (τ.doms d).caps = ((Hw.abs σ).doms d).caps)
    (hgen : ∀ d, (τ.doms d).slotGen = ((Hw.abs σ).doms d).slotGen)
    (r : CapRef) (a : Addr) (need : Perms) :
    (Machines.Lnp64u.moverCheck τ r a need = true) ↔
      ((Hw.abs σ).liveRef r = true ∧
       (Hw.decKind (σ.regs (Hw.dcapKind r.dom r.slot) 32)).covers a need
         = true) := by
  rw [Machines.Lnp64u.moverCheck]
  have hlc : (τ.doms r.dom).liveCap r.slot r.gen
      = ((Hw.abs σ).doms r.dom).liveCap r.slot r.gen := by
    rw [DomainState.liveCap, DomainState.liveCap, hcaps, hgen]
  rw [hlc, abs_liveCap]
  have hRl : ((Hw.abs σ).liveRef r = true) ↔
      (σ.regs (Hw.dcapV r.dom r.slot) 1 = 1#1 ∧
       σ.regs (Hw.dgen r.dom r.slot) 8 = r.gen ∧ r.gen ≠ 0) :=
    abs_liveRef σ r.dom r.slot r.gen
  rw [hRl]
  by_cases hcond : σ.regs (Hw.dcapV r.dom r.slot) 1 = 1#1 ∧
      σ.regs (Hw.dgen r.dom r.slot) 8 = r.gen ∧ r.gen ≠ 0
  · rw [if_pos hcond]
    simp only [hcond.1, hcond.2.1]
    simp only [true_and]
    constructor
    · intro h
      exact ⟨hcond.2.2, h⟩
    · rintro ⟨-, h⟩
      exact h
  · rw [if_neg hcond]
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨hl, -⟩
      exact absurd hl hcond


/-! ## Job-valid collapse -/

/-- No retiring `move` can program a new job on a non-retiring cycle. -/
theorem newAny_quiescent (σ : Loom.Hw.St)
    (hnr : Inert σ) :
    (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ = 0#1 := by
  apply bv1_ne_one.mp
  intro h
  obtain ⟨e, hmem, he⟩ := (orAll_eval σ _).mp h
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hmem
  rw [newJobSet_quiescent σ hnr d] at he
  exact absurd he (by decide)

/-- `jobV` collapses to the job-valid register on a non-retiring cycle. -/
theorem jobV_quiescent (σ : Loom.Hw.St)
    (hnr : Inert σ) :
    ((Expr.or (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet))
      (.and (.reg 1 "mov_v")
        (.not (.and (.reg 1 "mov_v")
          (.or (Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot)
               (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot)))))).eval σ)
      = σ.regs "mov_v" 1 := by
  show (Hw.orAll ((List.finRange numDomains).map Hw.newJobSet)).eval σ |||
      (σ.regs "mov_v" 1 &&&
        ~~~(σ.regs "mov_v" 1 &&&
          ((Hw.killedByCoreE Hw.movSrcDom Hw.movSrcSlot).eval σ |||
           (Hw.killedByCoreE Hw.movDstDom Hw.movDstSlot).eval σ))) = _
  rw [newAny_quiescent σ hnr, killedByCoreE_quiescent σ hnr _ _,
    killedByCoreE_quiescent σ hnr _ _]
  generalize σ.regs "mov_v" 1 = b
  revert b; decide


/-! ## The mover-field face of the quiescent bridge -/

/-- Decoding of a live Mover job (job-valid register set). -/
theorem absMover_some (σ : Loom.Hw.St) (hv : σ.regs "mov_v" 1 = 1#1) :
    Hw.absMover σ = some
      { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
        src := Hw.decRef (σ.regs "mov_src" 14)
        dst := Hw.decRef (σ.regs "mov_dst" 14)
        srcCur := σ.regs "mov_srccur" 12
        dstCur := σ.regs "mov_dstcur" 12
        remaining := (σ.regs "mov_rem" 13).toNat
        statusAddr := σ.regs "mov_status" 12 } := by
  rw [Hw.absMover]
  rw [if_pos (show σ.regs "mov_v" 1 = 1 from hv)]

theorem absMover_none (σ : Loom.Hw.St) (hv : ¬ σ.regs "mov_v" 1 = 1#1) :
    Hw.absMover σ = none := by
  rw [Hw.absMover]
  rw [if_neg (show ¬σ.regs "mov_v" 1 = 1 from hv)]

/-- **The quiescent Mover bridge, mover-field face.** -/
theorem absMover_moverAct_quiescent (σ acc : Loom.Hw.St) (τ : MachineState)
    (hnr : Inert σ)
    (hcaps : ∀ d, (τ.doms d).caps = ((Hw.abs σ).doms d).caps)
    (hgen : ∀ d, (τ.doms d).slotGen = ((Hw.abs σ).doms d).slotGen)
    (hjob : τ.mover = Hw.absMover σ) :
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
    have hjs : τ.mover = some
        { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
          src := Hw.decRef (σ.regs "mov_src" 14)
          dst := Hw.decRef (σ.regs "mov_dst" 14)
          srcCur := σ.regs "mov_srccur" 12
          dstCur := σ.regs "mov_dstcur" 12
          remaining := (σ.regs "mov_rem" 13).toNat
          statusAddr := σ.regs "mov_status" 12 } := by
      rw [hjob]; exact absMover_some σ hv
    -- reduce the circuit side to the written registers
    show Hw.absMover (Act.run σ Hw.moverAct acc) = _
    simp only [Hw.moverAct]
    simp only [Act.run]
    rw [jobV_quiescent σ hnr, if_pos hv]
    simp only [Hw.seqAll, List.foldr, Act.run]
    rw [Hw.absMover]
    simp only [RegEnv.set, regs_ite, ite_self, String.reduceEq, reduceIte,
      dite_true]
    -- name the derived-signal trees and collapse them to registers
    set R := Hw.postJ (fun d => (Hw.moveJob d).rem) (Expr.reg 13 "mov_rem")
      with hRdef
    set SRC := Hw.postJ (fun d => (Hw.moveJob d).srcEnc)
      (Expr.reg 14 "mov_src") with hSRCdef
    set DST := Hw.postJ (fun d => (Hw.moveJob d).dstEnc)
      (Expr.reg 14 "mov_dst") with hDSTdef
    set SC := Hw.postJ (fun d => (Hw.moveJob d).srcCur)
      (Expr.reg 12 "mov_srccur") with hSCdef
    set DC := Hw.postJ (fun d => (Hw.moveJob d).dstCur)
      (Expr.reg 12 "mov_dstcur") with hDCdef
    set OW := Hw.postJ (fun d => Hw.dLit d) (Expr.reg 2 "mov_owner")
      with hOWdef
    set SA := Hw.postJ (fun d => (Hw.moveJob d).sa) (Expr.reg 12 "mov_status")
      with hSAdef
    have hR : R.eval σ = σ.regs "mov_rem" 13 := postJ_quiescent σ hnr _ _
    have hSRC : SRC.eval σ = σ.regs "mov_src" 14 := postJ_quiescent σ hnr _ _
    have hDST : DST.eval σ = σ.regs "mov_dst" 14 := postJ_quiescent σ hnr _ _
    have hSC : SC.eval σ = σ.regs "mov_srccur" 12 := postJ_quiescent σ hnr _ _
    have hDC : DC.eval σ = σ.regs "mov_dstcur" 12 := postJ_quiescent σ hnr _ _
    have hOW : OW.eval σ = σ.regs "mov_owner" 2 := postJ_quiescent σ hnr _ _
    have hSA : SA.eval σ = σ.regs "mov_status" 12 := postJ_quiescent σ hnr _ _
    -- the check tree
    set CHK := Hw.andAll
      [(Hw.liveRefE (Hw.field SRC 12 2) (Hw.field SRC 8 4)
          (Hw.field SRC 0 8)).and
        (Expr.not (Hw.killedByCoreE (Hw.field SRC 12 2) (Hw.field SRC 8 4))),
       Hw.kCovers (Hw.kindWAt (Hw.field SRC 8 6)) SC
         { r := true, w := false, x := false },
       (Hw.liveRefE (Hw.field DST 12 2) (Hw.field DST 8 4)
          (Hw.field DST 0 8)).and
        (Expr.not (Hw.killedByCoreE (Hw.field DST 12 2) (Hw.field DST 8 4))),
       Hw.kCovers (Hw.kindWAt (Hw.field DST 8 6)) DC
         { r := false, w := true, x := false }] with hCHKdef
    -- the spec-side check, bridged
    have hlivS : ((Hw.liveRefE (Hw.field SRC 12 2) (Hw.field SRC 8 4)
          (Hw.field SRC 0 8)).and
        (Expr.not (Hw.killedByCoreE (Hw.field SRC 12 2)
          (Hw.field SRC 8 4)))).eval σ =
        (Hw.liveRefE (Hw.field SRC 12 2) (Hw.field SRC 8 4)
          (Hw.field SRC 0 8)).eval σ := by
      show _ &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
      rw [killedByCoreE_quiescent σ hnr]
      generalize (Hw.liveRefE _ _ _).eval σ = b
      revert b; decide
    have hlivD : ((Hw.liveRefE (Hw.field DST 12 2) (Hw.field DST 8 4)
          (Hw.field DST 0 8)).and
        (Expr.not (Hw.killedByCoreE (Hw.field DST 12 2)
          (Hw.field DST 8 4)))).eval σ =
        (Hw.liveRefE (Hw.field DST 12 2) (Hw.field DST 8 4)
          (Hw.field DST 0 8)).eval σ := by
      show _ &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
      rw [killedByCoreE_quiescent σ hnr]
      generalize (Hw.liveRefE _ _ _).eval σ = b
      revert b; decide
    -- the re-check tree decodes to the spec's two per-word checks
    have hsrcJ : SRC.eval σ = σ.regs "mov_src" 14 := hSRC
    have hchkiff : (CHK.eval σ = 1#1) ↔
        ((Machines.Lnp64u.moverCheck τ (Hw.decRef (σ.regs "mov_src" 14))
            (σ.regs "mov_srccur" 12) ⟨true, false, false⟩ &&
          Machines.Lnp64u.moverCheck τ (Hw.decRef (σ.regs "mov_dst" 14))
            (σ.regs "mov_dstcur" 12) ⟨false, true, false⟩) = true) := by
      rw [hCHKdef, andAll_eval, Bool.and_eq_true]
      simp only [List.forall_mem_cons]
      rw [hlivS, hlivD]
      have hsrcLive : ((Hw.liveRefE (Hw.field SRC 12 2) (Hw.field SRC 8 4)
            (Hw.field SRC 0 8)).eval σ = 1#1) ↔
          ((Hw.abs σ).liveRef (Hw.decRef (σ.regs "mov_src" 14)) = true) := by
        have := liveRefE_eval σ (Hw.field SRC 12 2) (Hw.field SRC 8 4)
          (Hw.field SRC 0 8)
          (Hw.decRef (σ.regs "mov_src" 14)).dom
          (Hw.decRef (σ.regs "mov_src" 14)).slot
          (by show _ = ((SRC.eval σ).extractLsb' 12 2).toNat; rw [hSRC]; rfl)
          (by show _ = ((SRC.eval σ).extractLsb' 8 4).toNat; rw [hSRC]; rfl)
        rw [this]
        rw [show (Hw.field SRC 0 8).eval σ = (SRC.eval σ).extractLsb' 0 8
          from rfl, hSRC]
        rfl
      have hdstLive : ((Hw.liveRefE (Hw.field DST 12 2) (Hw.field DST 8 4)
            (Hw.field DST 0 8)).eval σ = 1#1) ↔
          ((Hw.abs σ).liveRef (Hw.decRef (σ.regs "mov_dst" 14)) = true) := by
        have := liveRefE_eval σ (Hw.field DST 12 2) (Hw.field DST 8 4)
          (Hw.field DST 0 8)
          (Hw.decRef (σ.regs "mov_dst" 14)).dom
          (Hw.decRef (σ.regs "mov_dst" 14)).slot
          (by show _ = ((DST.eval σ).extractLsb' 12 2).toNat; rw [hDST]; rfl)
          (by show _ = ((DST.eval σ).extractLsb' 8 4).toNat; rw [hDST]; rfl)
        rw [this]
        rw [show (Hw.field DST 0 8).eval σ = (DST.eval σ).extractLsb' 0 8
          from rfl, hDST]
        rfl
      have hsrcCov : ((Hw.kCovers (Hw.kindWAt (Hw.field SRC 8 6)) SC
            { r := true, w := false, x := false }).eval σ = 1#1) ↔
          ((Hw.decKind (σ.regs
              (Hw.dcapKind (Hw.decRef (σ.regs "mov_src" 14)).dom
                (Hw.decRef (σ.regs "mov_src" 14)).slot) 32)).covers
            (σ.regs "mov_srccur" 12) ⟨true, false, false⟩ = true) := by
        rw [kCovers_eval, kindWAt_ref_eval, hSRC, hSC]
      have hdstCov : ((Hw.kCovers (Hw.kindWAt (Hw.field DST 8 6)) DC
            { r := false, w := true, x := false }).eval σ = 1#1) ↔
          ((Hw.decKind (σ.regs
              (Hw.dcapKind (Hw.decRef (σ.regs "mov_dst" 14)).dom
                (Hw.decRef (σ.regs "mov_dst" 14)).slot) 32)).covers
            (σ.regs "mov_dstcur" 12) ⟨false, true, false⟩ = true) := by
        rw [kCovers_eval, kindWAt_ref_eval, hDST, hDC]
      rw [hsrcLive, hdstLive, hsrcCov, hdstCov,
        moverCheck_abs σ τ hcaps hgen, moverCheck_abs σ τ hcaps hgen]
      simp [and_assoc]
    -- spec side: expose the phase's if-chain on the decoded job
    simp only [Machines.Lnp64u.moverPhase, hjs]
    -- rem/check facts
    have hzero_and : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
    have hand_zero : ∀ x : BitVec 1, x &&& 0#1 = 0#1 := by decide
    have hcondsplit : Expr.eval σ
        (((Hw.neqE R (.lit 0)).and CHK).and (Hw.neqE R (.lit 1)))
        = ((Hw.neqE R (.lit 0)).eval σ &&& CHK.eval σ) &&&
          (Hw.neqE R (.lit 1)).eval σ := rfl
    by_cases hrem0 : σ.regs "mov_rem" 13 = 0#13
    · -- completed job: status write only, job cleared
      have hn0 : (Hw.neqE R (.lit 0)).eval σ = 0#1 := by
        apply bv1_ne_one.mp
        intro hcon
        rw [neqE_eval] at hcon
        exact hcon (by rw [hR, hrem0]; rfl)
      rw [if_neg (show ¬(Expr.eval σ
          (((Hw.neqE R (.lit 0)).and CHK).and (Hw.neqE R (.lit 1))) = 1) from by
        rw [hcondsplit, hn0, hzero_and, hzero_and]; decide)]
      rw [if_pos (show ((σ.regs "mov_rem" 13).toNat = 0) from by
        rw [hrem0]; rfl)]
      rw [moverStatus_mover]
    · by_cases hchk : CHK.eval σ = 1#1
      · by_cases hrem1 : σ.regs "mov_rem" 13 = 1#13
        · -- last word this cycle: transfer + status, job cleared
          have hn1 : (Hw.neqE R (.lit 1)).eval σ = 0#1 := by
            apply bv1_ne_one.mp
            intro hcon
            rw [neqE_eval] at hcon
            exact hcon (by rw [hR, hrem1]; rfl)
          rw [if_neg (show ¬(Expr.eval σ
              (((Hw.neqE R (.lit 0)).and CHK).and (Hw.neqE R (.lit 1))) = 1)
              from by
            rw [hcondsplit, hn1, hand_zero]; decide)]
          rw [if_neg (show ¬((σ.regs "mov_rem" 13).toNat = 0) from fun h =>
            hrem0 (by apply BitVec.eq_of_toNat_eq; simpa using h))]
          rw [if_pos (hchkiff.mp hchk)]
          rw [if_pos (show (σ.regs "mov_rem" 13).toNat - 1 = 0 from by
            rw [hrem1]; rfl)]
          rw [moverStatus_mover]
        · -- mid-transfer: move one word, job continues
          have hn0 : (Hw.neqE R (.lit 0)).eval σ = 1#1 := by
            rw [neqE_eval, hR]
            intro hcon
            exact hrem0 (by rw [hcon]; rfl)
          have hn1 : (Hw.neqE R (.lit 1)).eval σ = 1#1 := by
            rw [neqE_eval, hR]
            intro hcon
            exact hrem1 (by rw [hcon]; rfl)
          rw [if_pos (show (Expr.eval σ
              (((Hw.neqE R (.lit 0)).and CHK).and (Hw.neqE R (.lit 1))) = 1)
              from by
            rw [hcondsplit, hn0, hchk, hn1]; decide)]
          rw [if_neg (show ¬((σ.regs "mov_rem" 13).toNat = 0) from fun h =>
            hrem0 (by apply BitVec.eq_of_toNat_eq; simpa using h))]
          rw [if_pos (hchkiff.mp hchk)]
          have htoN1 : ¬((σ.regs "mov_rem" 13).toNat = 1) := fun h =>
            hrem1 (by apply BitVec.eq_of_toNat_eq; simpa using h)
          rw [if_neg (show ¬((σ.regs "mov_rem" 13).toNat - 1 = 0) from by
            have h0 : (σ.regs "mov_rem" 13).toNat ≠ 0 := fun h =>
              hrem0 (by apply BitVec.eq_of_toNat_eq; simpa using h)
            omega)]
          have hsub1 : (Expr.eval σ (R.sub (.lit 1))).toNat
              = (σ.regs "mov_rem" 13).toNat - 1 := by
            show (R.eval σ - (1:BitVec 13)).toNat = _
            rw [hR, BitVec.toNat_sub]
            have h0 : (σ.regs "mov_rem" 13).toNat ≠ 0 := fun h =>
              hrem0 (by apply BitVec.eq_of_toNat_eq; simpa using h)
            have hlt := (σ.regs "mov_rem" 13).isLt
            show (2 ^ 13 - (1#13).toNat + (σ.regs "mov_rem" 13).toNat) % 2 ^ 13 = _
            rw [show (1#13).toNat = 1 from rfl]
            omega
          rw [show Expr.eval σ (SC.add (.lit 1)) = SC.eval σ + 1 from rfl,
            show Expr.eval σ (DC.add (.lit 1)) = DC.eval σ + 1 from rfl,
            hsub1, hOW, hSRC, hDST, hSC, hDC, hSA]
      · -- re-check failed: abort with -ESTALE, job cleared
        have hchk0 : CHK.eval σ = 0#1 := bv1_ne_one.mp hchk
        rw [if_neg (show ¬(Expr.eval σ
            (((Hw.neqE R (.lit 0)).and CHK).and (Hw.neqE R (.lit 1))) = 1)
            from by
          rw [hcondsplit, hchk0, hand_zero, hzero_and]; decide)]
        rw [if_neg (show ¬((σ.regs "mov_rem" 13).toNat = 0) from fun h =>
          hrem0 (by apply BitVec.eq_of_toNat_eq; simpa using h))]
        rw [if_neg (show ¬((Machines.Lnp64u.moverCheck τ
            (Hw.decRef (σ.regs "mov_src" 14)) (σ.regs "mov_srccur" 12)
            ⟨true, false, false⟩ &&
          Machines.Lnp64u.moverCheck τ (Hw.decRef (σ.regs "mov_dst" 14))
            (σ.regs "mov_dstcur" 12) ⟨false, true, false⟩) = true) from
          fun h => hchk (hchkiff.mpr h))]
        rw [moverStatus_mover]



/-! ## The memory face of the quiescent bridge -/

/-- Distribute a memory read over a branch in the accumulated state. -/
@[simp] theorem mems_ite (c : Prop) [Decidable c] (a b : Loom.Hw.St)
    (mn : String) (ad w : Nat) :
    (if c then a else b).mems mn ad w
      = if c then a.mems mn ad w else b.mems mn ad w := by
  split <;> rfl

theorem bv2_lit_iff (b : BitVec 2) (c : DomainId) :
    (b = BitVec.ofNat 2 c.val) ↔ (finOfBv (by decide) b = c) := by
  constructor
  · intro h
    apply Fin.ext
    show b.toNat = c.val
    rw [h, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := c.isLt; omega)
  · intro h
    apply BitVec.eq_of_toNat_eq
    have : b.toNat = c.val := congrArg Fin.val h
    rw [this, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := c.isLt; omega)).symm

/-- The status-write authority OR-tree decodes to `domCovers` of the
owner on the abstraction (quiescent core). -/
theorem sAuth_quiescent_eval (σ : Loom.Hw.St)
    (hnr : Inert σ) (ow : Expr 2) (sa : Expr 12) :
    ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
      (Hw.abs σ).domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
        ⟨false, true, false⟩ = true := by
  rw [orAll_eval]
  rw [show ((Hw.abs σ).domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
      ⟨false, true, false⟩ = true) ↔
      (∃ r : RegionId, ∃ rg,
        ((Hw.abs σ).doms (finOfBv (by decide) (ow.eval σ))).regions r = some rg
          ∧ rg.covers (sa.eval σ) ⟨false, true, false⟩ = true) from by
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
    have hc : finOfBv (by decide) (ow.eval σ) = c := (bv2_lit_iff _ c).mp h1
    rw [rgnVPostE_quiescent σ hnr] at h2
    rw [rgnCoversVal_eval, rgnValPostE_quiescent σ hnr] at hcv
    refine ⟨r, Hw.decRegion (σ.regs (Hw.drgn c r) 42), ?_, hcv⟩
    rw [hc, abs_regions, if_pos h2]
  · rintro ⟨r, rg, hsome, hcov⟩
    set c : DomainId := finOfBv (by decide) (ow.eval σ) with hcdef
    refine ⟨Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
        Hw.rgnCoversVal (Hw.rgnValPostE c r) sa ⟨false, true, false⟩],
      List.mem_flatMap.mpr ⟨c, List.mem_finRange c,
        List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩⟩, ?_⟩
    rw [abs_regions] at hsome
    by_cases hval : σ.regs (Hw.drgnV c r) 1 = 1#1
    · rw [if_pos hval] at hsome
      obtain rfl := Option.some.inj hsome
      rw [andAll_eval]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rw [eqE_eval]
        exact (bv2_lit_iff _ c).mpr rfl
      · rw [rgnVPostE_quiescent σ hnr]
        exact hval
      · rw [rgnCoversVal_eval, rgnValPostE_quiescent σ hnr]
        exact hcov
    · rw [if_neg hval] at hsome
      exact absurd hsome (by simp)


/-- **The quiescent Mover bridge, memory face.** -/
theorem moverAct_mem_quiescent (σ acc : Loom.Hw.St) (τ : MachineState)
    (hnr : Inert σ)
    (hcaps : ∀ d, (τ.doms d).caps = ((Hw.abs σ).doms d).caps)
    (hgen : ∀ d, (τ.doms d).slotGen = ((Hw.abs σ).doms d).slotGen)
    (hrgn : ∀ d, (τ.doms d).regions = ((Hw.abs σ).doms d).regions)
    (hjob : τ.mover = Hw.absMover σ)
    (hmem : ∀ ad, acc.mems "mem" ad 32 = σ.mems "mem" ad 32)
    (hτm : ∀ b : Addr, τ.mem b = σ.mems "mem" b.toNat 32)
    (a : Addr) :
    (Hw.moverAct.run σ acc).mems "mem" a.toNat 32 = (moverPhase τ).mem a := by
  have hdc : ∀ (c : DomainId) (b : Addr) (need : Perms),
      τ.domCovers c b need = (Hw.abs σ).domCovers c b need := by
    intro c b need
    rw [MachineState.domCovers, MachineState.domCovers]
    simp only [hrgn]
  by_cases hv : σ.regs "mov_v" 1 = 1#1
  case neg =>
    have hτn : τ.mover = none := by rw [hjob]; exact absMover_none σ hv
    have hlhs : (Hw.moverAct.run σ acc).mems "mem" a.toNat 32
        = acc.mems "mem" a.toNat 32 := by
      show (Act.run σ Hw.moverAct acc).mems "mem" a.toNat 32 = _
      simp only [Hw.moverAct]
      simp only [Act.run]
      rw [jobV_quiescent σ hnr, if_neg hv]
    rw [hlhs, hmem, ← hτm]
    simp [Machines.Lnp64u.moverPhase, hτn]
  case pos =>
    have hjs : τ.mover = some
        { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
          src := Hw.decRef (σ.regs "mov_src" 14)
          dst := Hw.decRef (σ.regs "mov_dst" 14)
          srcCur := σ.regs "mov_srccur" 12
          dstCur := σ.regs "mov_dstcur" 12
          remaining := (σ.regs "mov_rem" 13).toNat
          statusAddr := σ.regs "mov_status" 12 } := by
      rw [hjob]; exact absMover_some σ hv
    show (Act.run σ Hw.moverAct acc).mems "mem" a.toNat 32 = _
    simp only [Hw.moverAct]
    simp only [Act.run]
    rw [jobV_quiescent σ hnr, if_pos hv]
    simp only [Hw.seqAll, List.foldr, Act.run]
    simp only [mems_ite, MemEnv.set, dite_true, true_and]
    -- name the derived-signal trees
    set R := Hw.postJ (fun d => (Hw.moveJob d).rem) (Expr.reg 13 "mov_rem")
      with hRdef
    set SRC := Hw.postJ (fun d => (Hw.moveJob d).srcEnc)
      (Expr.reg 14 "mov_src") with hSRCdef
    set DST := Hw.postJ (fun d => (Hw.moveJob d).dstEnc)
      (Expr.reg 14 "mov_dst") with hDSTdef
    set SC := Hw.postJ (fun d => (Hw.moveJob d).srcCur)
      (Expr.reg 12 "mov_srccur") with hSCdef
    set DC := Hw.postJ (fun d => (Hw.moveJob d).dstCur)
      (Expr.reg 12 "mov_dstcur") with hDCdef
    set OW := Hw.postJ (fun d => Hw.dLit d) (Expr.reg 2 "mov_owner")
      with hOWdef
    set SA := Hw.postJ (fun d => (Hw.moveJob d).sa) (Expr.reg 12 "mov_status")
      with hSAdef
    have hR : R.eval σ = σ.regs "mov_rem" 13 := postJ_quiescent σ hnr _ _
    have hSC : SC.eval σ = σ.regs "mov_srccur" 12 := postJ_quiescent σ hnr _ _
    have hDC : DC.eval σ = σ.regs "mov_dstcur" 12 := postJ_quiescent σ hnr _ _
    have hOW : OW.eval σ = σ.regs "mov_owner" 2 := postJ_quiescent σ hnr _ _
    have hSA : SA.eval σ = σ.regs "mov_status" 12 := postJ_quiescent σ hnr _ _
    set CHK := Hw.andAll
      [(Hw.liveRefE (Hw.field SRC 12 2) (Hw.field SRC 8 4)
          (Hw.field SRC 0 8)).and
        (Expr.not (Hw.killedByCoreE (Hw.field SRC 12 2) (Hw.field SRC 8 4))),
       Hw.kCovers (Hw.kindWAt (Hw.field SRC 8 6)) SC
         { r := true, w := false, x := false },
       (Hw.liveRefE (Hw.field DST 12 2) (Hw.field DST 8 4)
          (Hw.field DST 0 8)).and
        (Expr.not (Hw.killedByCoreE (Hw.field DST 12 2) (Hw.field DST 8 4))),
       Hw.kCovers (Hw.kindWAt (Hw.field DST 8 6)) DC
         { r := false, w := true, x := false }] with hCHKdef
    set AUTH := Hw.orAll ((List.finRange numDomains).flatMap fun c =>
      (List.finRange numRegions).map fun r =>
        Hw.andAll [Expr.eq OW (Hw.dLit c), Hw.rgnVPostE c r,
          Hw.rgnCoversVal (Hw.rgnValPostE c r) SA
            { r := false, w := true, x := false }]) with hAUTHdef
    -- the authority bridge
    have hauthiff : (AUTH.eval σ = 1#1) ↔
        (Hw.abs σ).domCovers (finOfBv (by decide) (σ.regs "mov_owner" 2))
          (σ.regs "mov_status" 12) ⟨false, true, false⟩ = true := by
      rw [hAUTHdef]
      have := sAuth_quiescent_eval σ hnr OW SA
      rw [this, hOW, hSA]
    -- spec side
    simp only [Machines.Lnp64u.moverPhase, hjs]
    -- expression decompositions
    have hzero_and : ∀ x : BitVec 1, 0#1 &&& x = 0#1 := by decide
    have hand_zero : ∀ x : BitVec 1, x &&& 0#1 = 0#1 := by decide
    have hone_or : ∀ x : BitVec 1, 1#1 ||| x = 1#1 := by decide
    have hzero_or : ∀ x : BitVec 1, 0#1 ||| x = x := by decide
    have hand_one : ∀ x : BitVec 1, x &&& 1#1 = x := by decide
    have hmwsplit : Expr.eval σ ((Hw.neqE R (.lit 0)).and CHK)
        = (Hw.neqE R (.lit 0)).eval σ &&& CHK.eval σ := rfl
    have hsesplit : Expr.eval σ (AUTH.and ((Expr.eq R (.lit 0)).or
        ((Expr.not CHK).or (Expr.eq R (.lit 1)))))
        = AUTH.eval σ &&& ((Expr.eq R (.lit 0)).eval σ |||
          ((Expr.not CHK).eval σ ||| (Expr.eq R (.lit 1)).eval σ)) := rfl
    have haddr : ∀ x y : BitVec 12, (x.toNat = y.toNat) ↔ x = y :=
      fun x y => ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]⟩
    have hsw : ∀ (sc : Expr 12), Expr.eval σ
        (((List.finRange numDomains).foldr
          (fun d acc =>
            Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
                Hw.domCoversE d
                  (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                  ⟨false, true, false⟩,
                .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12) sc])
              (Hw.readReg d Hw.rs2E) acc)
          (.memRead 32 "mem" sc)))
        = σ.mems "mem" ((sc.eval σ)).toNat 32 := fun sc =>
      srcWord_quiescent σ hnr sc
    -- the re-check bridge (same as the mover-field face)
    have hlivS : ((Hw.liveRefE (Hw.field SRC 12 2) (Hw.field SRC 8 4)
          (Hw.field SRC 0 8)).and
        (Expr.not (Hw.killedByCoreE (Hw.field SRC 12 2)
          (Hw.field SRC 8 4)))).eval σ =
        (Hw.liveRefE (Hw.field SRC 12 2) (Hw.field SRC 8 4)
          (Hw.field SRC 0 8)).eval σ := by
      show _ &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
      rw [killedByCoreE_quiescent σ hnr]
      generalize (Hw.liveRefE _ _ _).eval σ = b
      revert b; decide
    have hlivD : ((Hw.liveRefE (Hw.field DST 12 2) (Hw.field DST 8 4)
          (Hw.field DST 0 8)).and
        (Expr.not (Hw.killedByCoreE (Hw.field DST 12 2)
          (Hw.field DST 8 4)))).eval σ =
        (Hw.liveRefE (Hw.field DST 12 2) (Hw.field DST 8 4)
          (Hw.field DST 0 8)).eval σ := by
      show _ &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
      rw [killedByCoreE_quiescent σ hnr]
      generalize (Hw.liveRefE _ _ _).eval σ = b
      revert b; decide
    have hSRC : SRC.eval σ = σ.regs "mov_src" 14 := postJ_quiescent σ hnr _ _
    have hDST : DST.eval σ = σ.regs "mov_dst" 14 := postJ_quiescent σ hnr _ _
    have hchkiff : (CHK.eval σ = 1#1) ↔
        ((Machines.Lnp64u.moverCheck τ (Hw.decRef (σ.regs "mov_src" 14))
            (σ.regs "mov_srccur" 12) ⟨true, false, false⟩ &&
          Machines.Lnp64u.moverCheck τ (Hw.decRef (σ.regs "mov_dst" 14))
            (σ.regs "mov_dstcur" 12) ⟨false, true, false⟩) = true) := by
      rw [hCHKdef, andAll_eval, Bool.and_eq_true]
      simp only [List.forall_mem_cons]
      rw [hlivS, hlivD]
      have hsrcLive : ((Hw.liveRefE (Hw.field SRC 12 2) (Hw.field SRC 8 4)
            (Hw.field SRC 0 8)).eval σ = 1#1) ↔
          ((Hw.abs σ).liveRef (Hw.decRef (σ.regs "mov_src" 14)) = true) := by
        have := liveRefE_eval σ (Hw.field SRC 12 2) (Hw.field SRC 8 4)
          (Hw.field SRC 0 8)
          (Hw.decRef (σ.regs "mov_src" 14)).dom
          (Hw.decRef (σ.regs "mov_src" 14)).slot
          (by show _ = ((SRC.eval σ).extractLsb' 12 2).toNat; rw [hSRC]; rfl)
          (by show _ = ((SRC.eval σ).extractLsb' 8 4).toNat; rw [hSRC]; rfl)
        rw [this]
        rw [show (Hw.field SRC 0 8).eval σ = (SRC.eval σ).extractLsb' 0 8
          from rfl, hSRC]
        rfl
      have hdstLive : ((Hw.liveRefE (Hw.field DST 12 2) (Hw.field DST 8 4)
            (Hw.field DST 0 8)).eval σ = 1#1) ↔
          ((Hw.abs σ).liveRef (Hw.decRef (σ.regs "mov_dst" 14)) = true) := by
        have := liveRefE_eval σ (Hw.field DST 12 2) (Hw.field DST 8 4)
          (Hw.field DST 0 8)
          (Hw.decRef (σ.regs "mov_dst" 14)).dom
          (Hw.decRef (σ.regs "mov_dst" 14)).slot
          (by show _ = ((DST.eval σ).extractLsb' 12 2).toNat; rw [hDST]; rfl)
          (by show _ = ((DST.eval σ).extractLsb' 8 4).toNat; rw [hDST]; rfl)
        rw [this]
        rw [show (Hw.field DST 0 8).eval σ = (DST.eval σ).extractLsb' 0 8
          from rfl, hDST]
        rfl
      have hsrcCov : ((Hw.kCovers (Hw.kindWAt (Hw.field SRC 8 6)) SC
            { r := true, w := false, x := false }).eval σ = 1#1) ↔
          ((Hw.decKind (σ.regs
              (Hw.dcapKind (Hw.decRef (σ.regs "mov_src" 14)).dom
                (Hw.decRef (σ.regs "mov_src" 14)).slot) 32)).covers
            (σ.regs "mov_srccur" 12) ⟨true, false, false⟩ = true) := by
        rw [kCovers_eval, kindWAt_ref_eval, hSRC, hSC]
      have hdstCov : ((Hw.kCovers (Hw.kindWAt (Hw.field DST 8 6)) DC
            { r := false, w := true, x := false }).eval σ = 1#1) ↔
          ((Hw.decKind (σ.regs
              (Hw.dcapKind (Hw.decRef (σ.regs "mov_dst" 14)).dom
                (Hw.decRef (σ.regs "mov_dst" 14)).slot) 32)).covers
            (σ.regs "mov_dstcur" 12) ⟨false, true, false⟩ = true) := by
        rw [kCovers_eval, kindWAt_ref_eval, hDST, hDC]
      rw [hsrcLive, hdstLive, hsrcCov, hdstCov,
        moverCheck_abs σ τ hcaps hgen, moverCheck_abs σ τ hcaps hgen]
      simp [and_assoc]
    -- shared spec-address facts
    have hup : ∀ (f : Addr → Loom.Word32) (x : Addr) (v : Loom.Word32),
        Loom.Fun.update f x v a = if a = x then v else f a := by
      intro f x v
      by_cases hax : a = x
      · rw [hax]; simp [Loom.Fun.update]
      · simp [Loom.Fun.update, hax]
    -- the four arms
    by_cases hrem0 : σ.regs "mov_rem" 13 = 0#13
    · -- completed: status write only
      have hmw : Expr.eval σ ((Hw.neqE R (.lit 0)).and CHK) = 0#1 := by
        rw [hmwsplit]
        have : (Hw.neqE R (.lit 0)).eval σ = 0#1 := by
          apply bv1_ne_one.mp
          intro hcon
          rw [neqE_eval] at hcon
          exact hcon (by rw [hR, hrem0]; rfl)
        rw [this, hzero_and]
      have heq0 : (Expr.eq R (.lit 0)).eval σ = 1#1 := by
        rw [eqE_eval, hR, hrem0]; rfl
      have hse : Expr.eval σ (AUTH.and ((Expr.eq R (.lit 0)).or
          ((Expr.not CHK).or (Expr.eq R (.lit 1))))) = AUTH.eval σ := by
        rw [hsesplit, heq0, hone_or, hand_one]
      rw [if_pos (show ((σ.regs "mov_rem" 13).toNat = 0) from by
        rw [hrem0]; rfl)]
      simp only [Machines.Lnp64u.moverStatus]
      by_cases hauth : (Hw.abs σ).domCovers
          (finOfBv (by decide) (σ.regs "mov_owner" 2))
          (σ.regs "mov_status" 12) ⟨false, true, false⟩ = true
      · rw [if_pos (show Expr.eval σ (AUTH.and _) = 1#1 from by
          rw [hse]; exact hauthiff.mpr hauth)]
        rw [if_pos (show (({ τ with mover := none } :
            MachineState)).domCovers _ _ _ = true from
          (show τ.domCovers _ _ _ = true from by rw [hdc]; exact hauth))]
        rw [show ((({ τ with mover := none } : MachineState)).write
            (σ.regs "mov_status" 12) 1).mem a =
          Loom.Fun.update τ.mem (σ.regs "mov_status" 12) 1 a from rfl, hup]
        by_cases haa : a.toNat = (SA.eval σ).toNat
        · rw [if_pos haa]
          rw [if_pos (show a = σ.regs "mov_status" 12 from by
            rw [← hSA]; exact (haddr _ _).mp haa)]
          show Expr.eval σ (Expr.mux ((Hw.neqE R (.lit 0)).and (.not CHK))
            (.lit Errno.staleHandle.toWord) (.lit 1)) = 1
          show (if Expr.eval σ ((Hw.neqE R (.lit 0)).and (.not CHK)) = 1#1
            then Errno.staleHandle.toWord else 1) = 1
          rw [if_neg (show ¬(Expr.eval σ ((Hw.neqE R (.lit 0)).and
              (.not CHK)) = 1#1) from by
            show ¬((Hw.neqE R (.lit 0)).eval σ &&&
              (Expr.not CHK).eval σ = 1#1)
            rw [show (Hw.neqE R (.lit 0)).eval σ = 0#1 from by
              apply bv1_ne_one.mp
              intro hcon
              rw [neqE_eval] at hcon
              exact hcon (by rw [hR, hrem0]; rfl), hzero_and]
            decide)]
        · rw [if_neg haa, if_neg (show ¬(a = σ.regs "mov_status" 12) from by
            rw [← hSA]; exact fun h => haa ((haddr _ _).mpr h)), hmw]
          rw [if_neg (by decide : ¬((0#1:BitVec 1) = 1#1))]
          rw [hmem, ← hτm]
      · rw [if_neg (show ¬(Expr.eval σ (AUTH.and _) = 1#1) from by
          rw [hse]; exact fun h => hauth (hauthiff.mp h))]
        rw [if_neg (show ¬((({ τ with mover := none } :
            MachineState)).domCovers _ _ _ = true) from
          (show ¬(τ.domCovers _ _ _ = true) from by
            rw [hdc]; exact hauth))]
        rw [hmw, if_neg (by decide : ¬((0#1:BitVec 1) = 1#1))]
        show acc.mems "mem" a.toNat 32 = τ.mem a
        rw [hmem, ← hτm]
    · -- an active word this cycle
      have htoN0 : ¬((σ.regs "mov_rem" 13).toNat = 0) := fun h =>
        hrem0 (by apply BitVec.eq_of_toNat_eq; simpa using h)
      have hne0 : (Hw.neqE R (.lit 0)).eval σ = 1#1 := by
        rw [neqE_eval, hR]
        intro hcon
        exact hrem0 (by rw [hcon]; rfl)
      have heq0 : (Expr.eq R (.lit 0)).eval σ = 0#1 := by
        apply bv1_ne_one.mp
        intro hcon
        rw [eqE_eval, hR] at hcon
        exact hrem0 (by rw [hcon]; rfl)
      rw [if_neg htoN0]
      by_cases hchk : CHK.eval σ = 1#1
      · rw [if_pos (hchkiff.mp hchk)]
        have hmw1 : Expr.eval σ ((Hw.neqE R (.lit 0)).and CHK) = 1#1 := by
          rw [hmwsplit, hne0, hchk]; decide
        have hnotchk : (Expr.not CHK).eval σ = 0#1 := by
          show ~~~(CHK.eval σ) = 0#1
          rw [hchk]; decide
        have hdata1 : Expr.eval σ (Expr.mux ((Hw.neqE R (.lit 0)).and
            (.not CHK)) (.lit Errno.staleHandle.toWord) (.lit 1)) = 1 := by
          show (if Expr.eval σ ((Hw.neqE R (.lit 0)).and (.not CHK)) = 1#1
            then Errno.staleHandle.toWord else 1) = 1
          rw [if_neg (show ¬(Expr.eval σ ((Hw.neqE R (.lit 0)).and
              (.not CHK)) = 1#1) from by
            show ¬((Hw.neqE R (.lit 0)).eval σ &&&
              (Expr.not CHK).eval σ = 1#1)
            rw [hnotchk, hand_zero]
            decide)]
        have hwrval : ∀ hab : a.toNat = (DC.eval σ).toNat,
            Expr.eval σ (((List.finRange numDomains).foldr
              (fun d acc =>
                Expr.mux (Hw.andAll [Hw.retiringE, Hw.ifDomIs d,
                    Hw.isMn "sw",
                    Hw.domCoversE d
                      (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                      ⟨false, true, false⟩,
                    .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
                      SC])
                  (Hw.readReg d Hw.rs2E) acc)
              (.memRead 32 "mem" SC)))
            = τ.mem (σ.regs "mov_srccur" 12) := by
          intro _
          rw [hsw SC, hSC, ← hτm]
        by_cases hrem1 : σ.regs "mov_rem" 13 = 1#13
        · -- last word: data + status
          have heq1 : (Expr.eq R (.lit 1)).eval σ = 1#1 := by
            rw [eqE_eval, hR, hrem1]; rfl
          have hse : Expr.eval σ (AUTH.and ((Expr.eq R (.lit 0)).or
              ((Expr.not CHK).or (Expr.eq R (.lit 1))))) = AUTH.eval σ := by
            rw [hsesplit, heq0, hzero_or, hnotchk, hzero_or, heq1, hand_one]
          rw [if_pos (show (σ.regs "mov_rem" 13).toNat - 1 = 0 from by
            rw [hrem1]; rfl)]
          simp only [Machines.Lnp64u.moverStatus]
          by_cases hauth : (Hw.abs σ).domCovers
              (finOfBv (by decide) (σ.regs "mov_owner" 2))
              (σ.regs "mov_status" 12) ⟨false, true, false⟩ = true
          · rw [if_pos (show Expr.eval σ (AUTH.and _) = 1#1 from by
              rw [hse]; exact hauthiff.mpr hauth)]
            rw [if_pos (show (({ (τ.write (σ.regs "mov_dstcur" 12)
                (τ.read (σ.regs "mov_srccur" 12))) with mover := none } :
                MachineState)).domCovers _ _ _ = true from
              (show τ.domCovers _ _ _ = true from by
                rw [hdc]; exact hauth))]
            rw [show ((({ (τ.write (σ.regs "mov_dstcur" 12)
                (τ.read (σ.regs "mov_srccur" 12))) with mover := none } :
                MachineState)).write (σ.regs "mov_status" 12) 1).mem a =
              Loom.Fun.update
                (Loom.Fun.update τ.mem (σ.regs "mov_dstcur" 12)
                  (τ.mem (σ.regs "mov_srccur" 12)))
                (σ.regs "mov_status" 12) 1 a from rfl, hup]
            by_cases haa : a.toNat = (SA.eval σ).toNat
            · rw [if_pos haa,
                if_pos (show a = σ.regs "mov_status" 12 from by
                  rw [← hSA]; exact (haddr _ _).mp haa)]
              exact hdata1
            · rw [if_neg haa,
                if_neg (show ¬(a = σ.regs "mov_status" 12) from by
                  rw [← hSA]; exact fun h => haa ((haddr _ _).mpr h)),
                if_pos hmw1, hup]
              by_cases hab : a.toNat = (DC.eval σ).toNat
              · rw [if_pos hab,
                  if_pos (show a = σ.regs "mov_dstcur" 12 from by
                    rw [← hDC]; exact (haddr _ _).mp hab)]
                exact hwrval hab
              · rw [if_neg hab,
                  if_neg (show ¬(a = σ.regs "mov_dstcur" 12) from by
                    rw [← hDC]; exact fun h => hab ((haddr _ _).mpr h)),
                  hmem, ← hτm]
          · rw [if_neg (show ¬(Expr.eval σ (AUTH.and _) = 1#1) from by
              rw [hse]; exact fun h => hauth (hauthiff.mp h))]
            rw [if_neg (show ¬((({ (τ.write (σ.regs "mov_dstcur" 12)
                (τ.read (σ.regs "mov_srccur" 12))) with mover := none } :
                MachineState)).domCovers _ _ _ = true) from
              (show ¬(τ.domCovers _ _ _ = true) from by
                rw [hdc]; exact hauth))]
            rw [if_pos hmw1,
              show (({ (τ.write (σ.regs "mov_dstcur" 12)
                (τ.read (σ.regs "mov_srccur" 12))) with mover := none } :
                MachineState)).mem a =
              Loom.Fun.update τ.mem (σ.regs "mov_dstcur" 12)
                (τ.mem (σ.regs "mov_srccur" 12)) a from rfl, hup]
            by_cases hab : a.toNat = (DC.eval σ).toNat
            · rw [if_pos hab,
                if_pos (show a = σ.regs "mov_dstcur" 12 from by
                  rw [← hDC]; exact (haddr _ _).mp hab)]
              exact hwrval hab
            · rw [if_neg hab,
                if_neg (show ¬(a = σ.regs "mov_dstcur" 12) from by
                  rw [← hDC]; exact fun h => hab ((haddr _ _).mpr h)),
                hmem, ← hτm]
        · -- mid-transfer: data write only
          have heq1 : (Expr.eq R (.lit 1)).eval σ = 0#1 := by
            apply bv1_ne_one.mp
            intro hcon
            rw [eqE_eval, hR] at hcon
            exact hrem1 (by rw [hcon]; rfl)
          have hse : Expr.eval σ (AUTH.and ((Expr.eq R (.lit 0)).or
              ((Expr.not CHK).or (Expr.eq R (.lit 1))))) = 0#1 := by
            rw [hsesplit, heq0, hzero_or, hnotchk, hzero_or, heq1, hand_zero]
          rw [if_neg (show ¬((σ.regs "mov_rem" 13).toNat - 1 = 0) from by
            have h1 : ¬((σ.regs "mov_rem" 13).toNat = 1) := fun h =>
              hrem1 (by apply BitVec.eq_of_toNat_eq; simpa using h)
            omega)]
          rw [if_neg (show ¬(Expr.eval σ (AUTH.and _) = 1#1) from by
            rw [hse]; decide)]
          rw [if_pos hmw1,
            show ({ (τ.write (σ.regs "mov_dstcur" 12)
              (τ.read (σ.regs "mov_srccur" 12))) with
              mover := some _ } : MachineState).mem a =
            Loom.Fun.update τ.mem (σ.regs "mov_dstcur" 12)
              (τ.mem (σ.regs "mov_srccur" 12)) a from rfl, hup]
          by_cases hab : a.toNat = (DC.eval σ).toNat
          · rw [if_pos hab,
              if_pos (show a = σ.regs "mov_dstcur" 12 from by
                rw [← hDC]; exact (haddr _ _).mp hab)]
            exact hwrval hab
          · rw [if_neg hab,
              if_neg (show ¬(a = σ.regs "mov_dstcur" 12) from by
                rw [← hDC]; exact fun h => hab ((haddr _ _).mpr h)),
              hmem, ← hτm]
      · -- re-check failed: stale status write only
        rw [if_neg (show ¬((Machines.Lnp64u.moverCheck τ
            (Hw.decRef (σ.regs "mov_src" 14)) (σ.regs "mov_srccur" 12)
            ⟨true, false, false⟩ &&
          Machines.Lnp64u.moverCheck τ (Hw.decRef (σ.regs "mov_dst" 14))
            (σ.regs "mov_dstcur" 12) ⟨false, true, false⟩) = true) from
          fun h => hchk (hchkiff.mpr h))]
        have hchk0 : CHK.eval σ = 0#1 := bv1_ne_one.mp hchk
        have hnotchk : (Expr.not CHK).eval σ = 1#1 := by
          show ~~~(CHK.eval σ) = 1#1
          rw [hchk0]; decide
        have hmw : Expr.eval σ ((Hw.neqE R (.lit 0)).and CHK) = 0#1 := by
          rw [hmwsplit, hchk0, hand_zero]
        have hse : Expr.eval σ (AUTH.and ((Expr.eq R (.lit 0)).or
            ((Expr.not CHK).or (Expr.eq R (.lit 1))))) = AUTH.eval σ := by
          rw [hsesplit, heq0, hzero_or, hnotchk, hone_or, hand_one]
        have hdataS : Expr.eval σ (Expr.mux ((Hw.neqE R (.lit 0)).and
            (.not CHK)) (.lit Errno.staleHandle.toWord) (.lit 1))
            = Errno.staleHandle.toWord := by
          show (if Expr.eval σ ((Hw.neqE R (.lit 0)).and (.not CHK)) = 1#1
            then Errno.staleHandle.toWord else 1) = _
          rw [if_pos (show Expr.eval σ ((Hw.neqE R (.lit 0)).and
              (.not CHK)) = 1#1 from by
            show (Hw.neqE R (.lit 0)).eval σ &&&
              (Expr.not CHK).eval σ = 1#1
            rw [hne0, hnotchk]; decide)]
        simp only [Machines.Lnp64u.moverStatus]
        by_cases hauth : (Hw.abs σ).domCovers
            (finOfBv (by decide) (σ.regs "mov_owner" 2))
            (σ.regs "mov_status" 12) ⟨false, true, false⟩ = true
        · rw [if_pos (show Expr.eval σ (AUTH.and _) = 1#1 from by
            rw [hse]; exact hauthiff.mpr hauth)]
          rw [if_pos (show (({ τ with mover := none } :
              MachineState)).domCovers _ _ _ = true from
            (show τ.domCovers _ _ _ = true from by
              rw [hdc]; exact hauth))]
          rw [show ((({ τ with mover := none } : MachineState)).write
              (σ.regs "mov_status" 12) Errno.staleHandle.toWord).mem a =
            Loom.Fun.update τ.mem (σ.regs "mov_status" 12)
              Errno.staleHandle.toWord a from rfl, hup]
          by_cases haa : a.toNat = (SA.eval σ).toNat
          · rw [if_pos haa,
              if_pos (show a = σ.regs "mov_status" 12 from by
                rw [← hSA]; exact (haddr _ _).mp haa)]
            exact hdataS
          · rw [if_neg haa,
              if_neg (show ¬(a = σ.regs "mov_status" 12) from by
                rw [← hSA]; exact fun h => haa ((haddr _ _).mpr h)),
              hmw, if_neg (by decide : ¬((0#1:BitVec 1) = 1#1)),
              hmem, ← hτm]
        · rw [if_neg (show ¬(Expr.eval σ (AUTH.and _) = 1#1) from by
            rw [hse]; exact fun h => hauth (hauthiff.mp h))]
          rw [if_neg (show ¬((({ τ with mover := none } :
              MachineState)).domCovers _ _ _ = true) from
            (show ¬(τ.domCovers _ _ _ = true) from by
              rw [hdc]; exact hauth))]
          rw [hmw, if_neg (by decide : ¬((0#1:BitVec 1) = 1#1))]
          show acc.mems "mem" a.toNat 32 = τ.mem a
          rw [hmem, ← hτm]


end Machines.Lnp64u.Theorems.RMC
