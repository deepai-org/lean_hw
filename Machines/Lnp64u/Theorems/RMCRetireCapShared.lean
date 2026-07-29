-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRgn
import Machines.Lnp64u.Logic.Tombstone

/-!
# R-MC retirement: shared capability-datapath lemmas

Hoisted off the arm-chain spine (from `RMCRetireDup`/`RMCRetireMove`):
free-slot/free-cell priority-encoder bridges, the watched-ref Mover
wrappers and the installing-op square glue, the `absDom` regs/pc/caps/
lineage face, and the small `finOfBv` round-trips. Consumed by the
install arms (`cap_dup`, `mem_grant`) and the gate chain.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 400000

/-! ## Bit-level class/kind bridges (hoisted from `RMCRetireMap`) -/

theorem extract1_eq_iff {n m : Nat} (a : BitVec n) (b : BitVec m)
    (i j : Nat) :
    (a.extractLsb' i 1 = b.extractLsb' j 1) ↔ (a.getLsbD i = b.getLsbD j) := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec 1 => v.getLsbD 0) h
    simpa [BitVec.getLsbD_extractLsb'] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k
    simpa [BitVec.getLsbD_extractLsb'] using h

theorem extract1_eq_zero_iff {n : Nat} (a : BitVec n) (i : Nat) :
    (a.extractLsb' i 1 = 0#1) ↔ (a.getLsbD i = false) := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec 1 => v.getLsbD 0) h
    simpa [BitVec.getLsbD_extractLsb'] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k
    simpa [BitVec.getLsbD_extractLsb'] using h

/-- Class agreement between a handle word and a kind word is the
tag-bit test. -/
theorem cls_eq_iff_bits (hw kw : BitVec 32) :
    ((Handle.decode hw).cls = (Hw.decKind kw).cls)
      ↔ (hw.getLsbD 12 = kw.getLsbD 0) := by
  rw [show (Handle.decode hw).cls
    = (if hw.getLsbD 12 then CapClass.gate else CapClass.mem) from rfl]
  rw [Hw.decKind]
  cases h1 : hw.getLsbD 12 <;> cases h2 : kw.getLsbD 0 <;>
    simp [CapKind.cls]


/-! ## The shared errno-outcome assembly for `map` -/

set_option maxHeartbeats 25600000 in
/-- Both `map` errno outcomes retire as `pc += 1; rd := errno` with the
Mover fully quiescent (`mapOkE` is off, so even the fired-`map`
composites collapse). -/
theorem retire_err_common_mem (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hin : Inert σ)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1)
    (hcoremem : ∀ b : Addr,
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ)).mems "mem"
        b.toNat 32 = σ.mems "mem" b.toNat 32)
    (E : DomainId) (hE : E.val = (σ.regs "if_dom" 2).toNat)
    (errw : Loom.Word32)
    (hcoreX : ∀ acc, (Hw.retireFor E).run σ acc
      = (Act.seq (Hw.pcAdvA E) (Hw.writeReg E Hw.rdE (.lit errw))).run σ acc)
    (hspecE : corePhase m (refillPhase m (Hw.abs σ))
      = (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).setDom E
          (fun ds => ds.setReg (operandsOf (σ.regs "if_word" 32)).rd errw)) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y
    rw [← habs1]
    rfl
  set W := σ.regs "if_word" 32 with hW
  have hτ2E : ((({ refillPhase m (Hw.abs σ) with inflight := none
      }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).setDom E
      (fun ds => ds.setReg (operandsOf W).rd errw)).doms E
      = ({ (refillPhase m (Hw.abs σ)).doms E with
          pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 }).setReg
          (operandsOf W).rd errw := by
    rw [setDom_setDom]
    show (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E = _
    rw [Loom.Fun.update_same]
  have hτ2x : ∀ x, x ≠ E → ((({ refillPhase m (Hw.abs σ) with inflight :=
      none }).setDom E (fun ds => { ds with pc := ds.pc + 1 })).setDom E
      (fun ds => ds.setReg (operandsOf W).rd errw)).doms x
      = (refillPhase m (Hw.abs σ)).doms x := by
    intro x hx
    rw [setDom_setDom]
    show (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x = _
    rw [Loom.Fun.update_ne _ _ _ _ hx]
  refine square_retire_store m hwf hfit σ hsync hifv hcl hin hmapz hunmapz
    (Act.seq (Hw.pcAdvA E) (Hw.writeReg E Hw.rdE (.lit errw))) _
    (fun rn w => by
      rw [coreAct_run_retire_eq m σ _ hifv hcl,
        retireAct_run_regs σ _ E hE rn w, hcoreX]
      rfl)
    (by
      intro hm
      rcases List.mem_cons.mp (show (("if_v" : String), (1 : Nat)) ∈
          (Hw.dpc E, (12 : Nat)) :: (Hw.writeReg E Hw.rdE
            (Expr.lit errw)).regWrites from hm) with h | h
      · exact absurd (congrArg Prod.snd h) (show ¬((1 : Nat) = 12) by decide)
      · exact absurd h ((by decide +kernel : ∀ e : DomainId,
          (("if_v" : String), (1 : Nat))
            ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) E)
    )
    hspecE
    (fun x => by
      by_cases hx : x = E
      · subst hx
        rw [hτ2E]
        have hq : ∀ q ∈ domQuietNames x,
            ((Act.seq (.write 1 "if_v" (.lit 0))
              (Act.seq (Hw.pcAdvA x) (Hw.writeReg x Hw.rdE
                (.lit errw)))).run σ ((Hw.refillAct m).run σ σ)).regs
              q.1 q.2 = ((Hw.refillAct m).run σ σ).regs q.1 q.2 := by
          intro q hq'
          refine frame ?_ σ _
          intro hm
          rcases List.mem_cons.mp (show q ∈ ("if_v", (1 : Nat)) ::
              ((Hw.dpc x, (12 : Nat)) :: (Hw.writeReg x Hw.rdE
                (Expr.lit errw)).regWrites) from hm) with h | h
          · exact absurd (h ▸ hq' : _)
              (fun hmem => (quiet_notin_dom x x q hq')
                (h ▸ List.mem_cons_self ..))
          · rcases List.mem_cons.mp h with h' | h'
            · exact (quiet_notin_dom x x q hq')
                (h' ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (List.mem_cons_self ..)))))))))
            · exact (quiet_notin_dom x x q hq')
                ((by decide +kernel : ∀ (e : DomainId)
                    (q' : String × Nat),
                    q' ∈ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites →
                    q' ∈ ("if_v", 1) :: domWrites e) x q h')
        rw [absDom_regpc x hq, hL1 x]
        apply domainState_ext'
        · funext r
          show ((Hw.writeReg x Hw.rdE (.lit errw)).run σ
            ((Hw.pcAdvA x).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ)))).regs (Hw.dreg x r) 32 = _
          rw [setReg_regs]
          have hbase : ∀ (rr : RegId),
              ((Hw.pcAdvA x).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ))).regs (Hw.dreg x rr) 32
              = ((Hw.refillAct m).run σ σ).regs (Hw.dreg x rr) 32 := by
            intro rr
            rw [frame (fun hm => absurd
              (congrArg Prod.snd (List.mem_singleton.mp hm))
              (show ¬((32 : Nat) = 12) by decide)) σ _]
            exact frame (fun hm => absurd
              (congrArg Prod.snd (List.mem_singleton.mp hm))
              (show ¬((32 : Nat) = 1) by decide)) σ _
          by_cases h0 : (operandsOf W).rd = (0 : Fin numRegs)
          · rw [if_pos h0]
            rw [writeReg_run_of_zero σ _ x Hw.rdE _ (by
              rw [show ((Hw.rdE.eval σ)).toNat
                = ((operandsOf W).rd : Fin numRegs).val from rfl, h0]
              rfl)]
            rw [hbase r]
            rfl
          · rw [if_neg h0]
            rw [writeReg_run_of_nz σ _ x Hw.rdE _ (operandsOf W).rd rfl
              (fun hc => h0 (Fin.ext hc))]
            show (RegEnv.set _ (Hw.dreg x (operandsOf W).rd) _)
              (Hw.dreg x r) 32 = _
            simp only [RegEnv.set]
            by_cases hr : r = (operandsOf W).rd
            · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial]
              rfl
            · rw [if_neg (fun hc => hr (dreg_inj x r (operandsOf W).rd hc)),
                if_neg hr]
              rw [hbase r]
              rfl
        · show ((Hw.writeReg x Hw.rdE (.lit errw)).run σ
            ((Hw.pcAdvA x).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ)))).regs (Hw.dpc x) 12 = _
          rw [setReg_pc]
          rw [frame (show ((Hw.dpc x : String), (12 : Nat))
              ∉ (Hw.writeReg x Hw.rdE (Expr.lit errw)).regWrites from
            (by decide +kernel : ∀ e : DomainId,
              ((Hw.dpc e : String), (12 : Nat))
                ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) x) σ _]
          rw [show ((Hw.pcAdvA x).run σ ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ))).regs (Hw.dpc x) 12
            = σ.regs (Hw.dpc x) 12 + 1 from by
            show (RegEnv.set _ (Hw.dpc x)
              ((Expr.add (Hw.rPc x) (.lit 1)).eval σ)) (Hw.dpc x) 12 = _
            simp [RegEnv.set, Expr.eval, Hw.rPc]]
          show σ.regs (Hw.dpc x) 12 + 1
            = ((Hw.refillAct m).run σ σ).regs (Hw.dpc x) 12 + 1
          rw [refill_pres m σ ((by decide +kernel : ∀ e : DomainId,
            ((Hw.dpc e : String), (12 : Nat)) ∉
            ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
              ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
              ("d3_budget", 32), ("d3_rctr", 32)] :
              List (String × Nat))) x)]
        · rw [setReg_caps]
        · rw [setReg_slotGen]
        · rw [setReg_lineage]
        · rw [setReg_regions]
        · rw [setReg_run]
        · rw [setReg_serving]
        · rw [setReg_cause]
        · rw [setReg_budget]
        · rw [setReg_maxDonation]
      · rw [hτ2x x hx, hL1 x]
        refine absDom_congr x (fun p hp => frame ?_ σ _)
        intro hm
        rcases List.mem_cons.mp (show p ∈ ("if_v", (1 : Nat)) ::
            ((Hw.dpc E, (12 : Nat)) :: (Hw.writeReg E Hw.rdE
              (Expr.lit errw)).regWrites) from hm) with h | h
        · exact (read_notin_dom_ne x E hx p hp)
            (h ▸ List.mem_cons_self ..)
        · rcases List.mem_cons.mp h with h' | h'
          · exact (read_notin_dom_ne x E hx p hp)
              (h' ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_self ..)))))))))
          · exact (read_notin_dom_ne x E hx p hp)
              ((by decide +kernel : ∀ (e : DomainId) (q' : String × Nat),
                q' ∈ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites →
                q' ∈ ("if_v", 1) :: domWrites e) E p h')
    )
    (fun g => by
      refine (absGate_congr g (fun p hp => frame ?_ σ _)).trans ?_
      · intro hm
        rcases List.mem_cons.mp (show p ∈ ("if_v", (1 : Nat)) ::
            ((Hw.dpc E, (12 : Nat)) :: (Hw.writeReg E Hw.rdE
              (Expr.lit errw)).regWrites) from hm) with h | h
        · exact (gate_notin_dom g E p hp) (h ▸ List.mem_cons_self ..)
        · rcases List.mem_cons.mp h with h' | h'
          · exact (gate_notin_dom g E p hp)
              (h' ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_self ..)))))))))
          · exact (gate_notin_dom g E p hp)
              ((by decide +kernel : ∀ (e : DomainId) (q' : String × Nat),
                q' ∈ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites →
                q' ∈ ("if_v", 1) :: domWrites e) E p h')
      · rw [← habs1]
        rfl)
    (fun x => by
      by_cases hx : x = E
      · subst hx
        rw [hτ2E, setReg_caps]
        show ((refillPhase m (Hw.abs σ)).doms x).caps = _
        rw [refillPhase_caps]
      · rw [hτ2x x hx, refillPhase_caps])
    (fun x => by
      by_cases hx : x = E
      · subst hx
        rw [hτ2E, setReg_slotGen]
        show ((refillPhase m (Hw.abs σ)).doms x).slotGen = _
        rw [refillPhase_slotGen]
      · rw [hτ2x x hx, refillPhase_slotGen])
    (fun x => by
      by_cases hx : x = E
      · subst hx
        rw [hτ2E, setReg_regions]
        show ((refillPhase m (Hw.abs σ)).doms x).regions = _
        rw [refillPhase_regions]
      · rw [hτ2x x hx, refillPhase_regions])
    (by
      show (refillPhase m (Hw.abs σ)).mover = _
      rw [refillPhase_mover]
      rfl)
    hcoremem
    (fun sc => by
      rw [srcWord_quiescent σ hswz sc]
      rfl)
    (by
      show (refillPhase m (Hw.abs σ)).cycle = _
      rfl)
    rfl



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

/-- The gate-kind case complementary to `decKind_mem_iff`. -/
theorem decKind_gate_iff (kw : BitVec 32) :
    (kw.getLsbD 0 = true) ↔
      Hw.decKind kw = .gate (finOfBv (by decide) (kw.extractLsb' 1 2)) := by
  rw [Hw.decKind]
  cases h : kw.getLsbD 0 <;> simp

/-- Installing into a free slot cannot change the capability-table entry at
an already-live reference. This is the watched-reference fact needed by both
`cap_dup` and `mem_grant`. -/
theorem installDerived_caps_at_live (τ : MachineState) (d : DomainId)
    (s : Slot) (l : LineageId) (kind : CapKind) (parent r : CapRef)
    (hfree : (τ.doms d).caps s = none)
    (hlive : ∃ ce, (τ.doms r.dom).liveCap r.slot r.gen = some ce) :
    (((τ.installDerived d s l kind parent).1).doms r.dom).caps r.slot =
      (τ.doms r.dom).caps r.slot := by
  obtain ⟨ce, hlive⟩ := hlive
  have hcap : ∃ ce, (τ.doms r.dom).caps r.slot = some ce := by
    cases hc : (τ.doms r.dom).caps r.slot with
    | none => simp [DomainState.liveCap, hc] at hlive
    | some ce0 => exact ⟨ce0, rfl⟩
  have hne : ¬(r.dom = d ∧ r.slot = s) := by
    rintro ⟨hd, hs⟩
    obtain ⟨ce, hcap⟩ := hcap
    rw [hd, hs, hfree] at hcap
    cases hcap
  change ((τ.setDom d (fun ds => { ds with
    caps := Loom.Fun.update ds.caps s
      (some { kind := kind, lineage := some l })
    lineage := Loom.Fun.update ds.lineage l (some { parent := parent }) })).doms
      r.dom).caps r.slot = (τ.doms r.dom).caps r.slot
  unfold MachineState.setDom
  dsimp only
  by_cases hd : r.dom = d
  · subst hd
    rw [Loom.Fun.update_same]
    simp only
    rw [Loom.Fun.update_ne _ _ _ _ (fun hs => hne ⟨rfl, hs⟩)]
  · rw [Loom.Fun.update_ne _ _ _ _ hd]

/-- Reachability supplies liveness of both hardware-decoded watched refs
whenever the Mover-valid bit is set. -/
theorem watched_live_of_reachable (m : Manifest) (σ : Loom.Hw.St)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hv : σ.regs "mov_v" 1 = 1#1) :
    (∃ ce, ((Hw.abs σ).doms
      (Hw.decRef (σ.regs "mov_src" 14)).dom).liveCap
        (Hw.decRef (σ.regs "mov_src" 14)).slot
        (Hw.decRef (σ.regs "mov_src" 14)).gen = some ce) ∧
    (∃ ce, ((Hw.abs σ).doms
      (Hw.decRef (σ.regs "mov_dst" 14)).dom).liveCap
        (Hw.decRef (σ.regs "mov_dst" 14)).slot
        (Hw.decRef (σ.regs "mov_dst" 14)).gen = some ce) := by
  let job : MoverJob :=
    { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
      src := Hw.decRef (σ.regs "mov_src" 14)
      dst := Hw.decRef (σ.regs "mov_dst" 14)
      srcCur := σ.regs "mov_srccur" 12
      dstCur := σ.regs "mov_dstcur" 12
      remaining := (σ.regs "mov_rem" 13).toNat
      statusAddr := σ.regs "mov_status" 12 }
  have hj : Hw.absMover σ = some job := absMover_some σ hv
  have hs := moverLiveSrc_invariant m (Hw.abs σ) hsr job hj
  have hd := moverLiveMem_invariant m (Hw.abs σ) hsr job hj
  obtain ⟨ce, hlive, _⟩ := hd
  exact ⟨hs, ⟨ce, hlive⟩⟩

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
    exact absMover_moverAct_run σ acc τ
      (σ.regs "mov_src" 14) (σ.regs "mov_dst" 14)
      (σ.regs "mov_owner" 2) (σ.regs "mov_srccur" 12)
      (σ.regs "mov_dstcur" 12) (σ.regs "mov_status" 12)
      (σ.regs "mov_rem" 13)
      (fun _ _ => hnr.killed _ _) (fun _ _ => hnr.killed _ _)
      (by unfold DomainState.liveCap; rw [hcapsS hv, hgenS hv])
      (by unfold DomainState.liveCap; rw [hcapsD hv, hgenD hv])
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
    exact moverAct_mem_run σ acc τ
      (σ.regs "mov_src" 14) (σ.regs "mov_dst" 14)
      (σ.regs "mov_owner" 2) (σ.regs "mov_srccur" 12)
      (σ.regs "mov_dstcur" 12) (σ.regs "mov_status" 12)
      (σ.regs "mov_rem" 13)
      (fun _ _ => hnr.killed _ _) (fun _ _ => hnr.killed _ _)
      (by unfold DomainState.liveCap; rw [hcapsS hv, hgenS hv])
      (by unfold DomainState.liveCap; rw [hcapsD hv, hgenD hv])
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
    rw [Loom.Hw.Act.run_mems_notin "mem" Hw.tickAct
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

/-- The selector's packed backing ref is `encRef` of the handle fields. -/
theorem encRefE_sel_eval (σ : Loom.Hw.St) (E : DomainId) (hwE : Expr 32) :
    (Hw.encRefE (Hw.dLit E) (Hw.capSel E hwE).slot
      (Hw.capSel E hwE).gen).eval σ
    = Hw.encRef ⟨E, finOfBv (by decide) ((hwE.eval σ).extractLsb' 0 4),
        (hwE.eval σ).extractLsb' 4 8⟩ := by
  show (((hwE.eval σ).extractLsb' 4 8).setWidth 14 |||
    ((((hwE.eval σ).extractLsb' 0 4).setWidth 14 <<< (8#14).toNat) |||
      (((BitVec.ofNat 2 E.val).setWidth 14) <<< (12#14).toNat))) = _
  have hSv : BitVec.ofNat 14 (finOfBv (by decide : 2 ^ 4 = numSlots)
      ((hwE.eval σ).extractLsb' 0 4)).val
      = ((hwE.eval σ).extractLsb' 0 4).setWidth 14 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    rfl
  have hEv : BitVec.ofNat 14 E.val
      = (BitVec.ofNat 2 E.val).setWidth 14 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := E.isLt
    rw [Nat.mod_eq_of_lt (by omega : E.val < 2 ^ 2)]
  show _ = ((hwE.eval σ).extractLsb' 4 8).setWidth 14 |||
    (BitVec.ofNat 14 (finOfBv (by decide : 2 ^ 4 = numSlots)
      ((hwE.eval σ).extractLsb' 0 4)).val <<< 8) |||
    (BitVec.ofNat 14 E.val <<< 12)
  rw [hSv, hEv, BitVec.or_assoc]
  rfl

/-- `dLit` round-trips through `finOfBv`. -/
theorem finOfBv_dLit (E : DomainId) :
    finOfBv (by decide : 2 ^ 2 = numDomains) (BitVec.ofNat 2 E.val)
      = E := by
  apply Fin.ext
  show (BitVec.ofNat 2 E.val).toNat = E.val
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := E.isLt; omega)

/-- 4-bit `finOfBv`/`ofNat` round-trip (slot and cell indices). -/
theorem finOfBv_ofNat4 {k : Nat} (h : (2:Nat) ^ 4 = k) (t : Fin k) :
    finOfBv h (BitVec.ofNat 4 t.val) = t := by
  apply Fin.ext
  show (BitVec.ofNat 4 t.val).toNat = t.val
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := t.isLt; omega)

end Machines.Lnp64u.Theorems.RMC


