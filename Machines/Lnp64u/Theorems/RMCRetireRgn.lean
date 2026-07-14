-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireSw

/-!
# R-MC support: the region-op retirement arms (`map`/`unmap`)

Region edits are the second Mover interaction: the status-write
authority (`sAuth`) re-derives the *post-core* region file through the
`mapSet`/`unmapSet` composites. This file proves the fired forms of
those composites, the region-face `absDom` decomposition, and the
`unmap` arm; `map` follows with its check ladder.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 12800000
set_option maxRecDepth 400000

private theorem bv1_one_and3 (x : BitVec 1) : 1#1 &&& x = x := by
  revert x; decide

private theorem bv1_mid_zero (x y : BitVec 1) : x &&& (0#1 &&& y) = 0#1 := by
  revert x y; decide

/-- The fired `unmap` chain: on the owner at the selected region it is
the region-index test; elsewhere it is off. -/
private theorem unmapChain_eval (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hunm : (Hw.isMn "unmap").eval σ = 1#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val) :
    ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ
      = if c = E ∧ r = RI then 1#1 else 0#1 := by
  intro c r
  by_cases hc : c = E
  · subst hc
    show Hw.retiringE.eval σ &&& ((Hw.ifDomIs c).eval σ &&&
      ((Hw.isMn "unmap").eval σ &&&
        (Expr.eq Hw.riE (Hw.rLit r)).eval σ)) = _
    rw [hret, hifsel, hunm, bv1_one_and3, bv1_one_and3, bv1_one_and3]
    by_cases hr : r = RI
    · subst hr
      rw [if_pos ⟨rfl, rfl⟩]
      show (if Hw.riE.eval σ = (Hw.rLit r).eval σ then (1#1 : BitVec 1)
        else 0#1) = 1#1
      rw [if_pos (by rw [hri]; rfl)]
    · rw [if_neg (fun hc' => hr hc'.2)]
      show (if Hw.riE.eval σ = (Hw.rLit r).eval σ then (1#1 : BitVec 1)
        else 0#1) = 0#1
      rw [if_neg (by
        rw [hri]
        intro hc'
        apply hr
        apply Fin.ext
        have : (BitVec.ofNat 2 RI.val).toNat = (BitVec.ofNat 2 r.val).toNat :=
          by rw [hc']; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (show r.val < 2 ^ 2 from r.isLt),
          Nat.mod_eq_of_lt (show RI.val < 2 ^ 2 from RI.isLt)] at this
        omega)]
  · rw [if_neg (fun hc' => hc hc'.1)]
    show Hw.retiringE.eval σ &&& ((Hw.ifDomIs c).eval σ &&&
      ((Hw.isMn "unmap").eval σ &&&
        (Expr.eq Hw.riE (Hw.rLit r)).eval σ)) = 0#1
    rw [bv1_ne_one.mp (hifexcl c hc)]
    exact bv1_mid_zero _ _

/-- `rgnVPostE` under a fired `unmap`: dead at the selected region,
the validity register elsewhere. -/
private theorem rgnVPostE_unmap (σ : Loom.Hw.St) (E : DomainId)
    (hnr : Inert σ)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hunm : (Hw.isMn "unmap").eval σ = 1#1)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val)
    (c : DomainId) (r : RegionId) :
    (Hw.rgnVPostE c r).eval σ
      = if c = E ∧ r = RI then 0#1 else σ.regs (Hw.drgnV c r) 1 := by
  show (if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map",
      Hw.mapOkE c, .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1
    then (Expr.lit 1).eval σ
    else if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1
      then (Expr.lit 0).eval σ
      else (Expr.and (.reg 1 (Hw.drgnV c r))
        (.not (Hw.killedByCoreE _ _))).eval σ) = _
  rw [if_neg (by rw [hmapz c r]; decide)]
  rw [unmapChain_eval σ E hret hifsel hifexcl hunm RI hri c r]
  by_cases hcr : c = E ∧ r = RI
  · rw [if_pos hcr, if_pos rfl, if_pos hcr]
    rfl
  · rw [if_neg hcr, if_neg (by decide : ¬((0#1 : BitVec 1) = 1#1)),
      if_neg hcr]
    show σ.regs (Hw.drgnV c r) 1 &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
    rw [hnr.killed]
    generalize σ.regs (Hw.drgnV c r) 1 = b
    revert b
    decide

/-- The status-authority tree under a fired `unmap`, against any spec
state whose regions are the abstraction's with the selected one dead. -/
theorem sAuth_unmap_eval (σ : Loom.Hw.St) (E : DomainId)
    (hnr : Inert σ)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hunm : (Hw.isMn "unmap").eval σ = 1#1)
    (hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val)
    (τ : MachineState)
    (hrgnτ : ∀ (c : DomainId) (r : RegionId), ((τ.doms c)).regions r
      = if c = E ∧ r = RI then none else ((Hw.abs σ).doms c).regions r)
    (ow : Expr 2) (sa : Expr 12) :
    ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
      τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
        ⟨false, true, false⟩ = true := by
  rw [orAll_eval]
  rw [show (τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
      ⟨false, true, false⟩ = true) ↔
      (∃ r : RegionId, ∃ rg,
        (τ.doms (finOfBv (by decide) (ow.eval σ))).regions r = some rg
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
    rw [rgnVPostE_unmap σ E hnr hret hifsel hifexcl hunm hmapz RI hri c r]
      at h2
    by_cases hcr : c = E ∧ r = RI
    · rw [if_pos hcr] at h2
      exact absurd h2 (by decide)
    · rw [if_neg hcr] at h2
      rw [rgnCoversVal_eval, rgnValPostE_quiescent σ hmapz] at hcv
      refine ⟨r, Hw.decRegion (σ.regs (Hw.drgn c r) 42), ?_, hcv⟩
      rw [hc, hrgnτ c r, if_neg hcr, abs_regions, if_pos h2]
  · rintro ⟨r, rg, hsome, hcov⟩
    set c : DomainId := finOfBv (by decide) (ow.eval σ) with hcdef
    rw [hrgnτ c r] at hsome
    by_cases hcr : c = E ∧ r = RI
    · rw [if_pos hcr] at hsome
      exact absurd hsome (by simp)
    · rw [if_neg hcr] at hsome
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
        · rw [rgnVPostE_unmap σ E hnr hret hifsel hifexcl hunm hmapz RI hri
            c r, if_neg hcr]
          exact hval
        · rw [rgnCoversVal_eval, rgnValPostE_quiescent σ hmapz]
          exact hcov
      · rw [if_neg hval] at hsome
        exact absurd hsome (by simp)

/-! ## The region-op glue and the `unmap` write-set faces -/

/-- The `unmap` payload with the latch clear in front. -/
def unmapFull (e : DomainId) : Act :=
  .seq (.write 1 "if_v" (.lit 0))
    (Hw.seqAll <|
      ((List.finRange numRegions).map fun r =>
        .ite (.eq Hw.riE (Hw.rLit r)) (.write 1 (Hw.drgnV e r) (.lit 0))
          .skip)
      ++ [Hw.writeReg e Hw.rdE (.lit 0), Hw.pcAdvA e])

private theorem unmapFull_writes (e : DomainId) :
    (unmapFull e).regWrites
      = [("if_v", 1), (Hw.drgnV e 0, 1), (Hw.drgnV e 1, 1),
         (Hw.drgnV e 2, 1), (Hw.drgnV e 3, 1), (Hw.dreg e 1, 32),
         (Hw.dreg e 2, 32), (Hw.dreg e 3, 32), (Hw.dreg e 4, 32),
         (Hw.dreg e 5, 32), (Hw.dreg e 6, 32), (Hw.dreg e 7, 32),
         (Hw.dpc e, 12)] := rfl

/-- The non-`regs`/`pc`/`regions` register names `absDom · x` reads. -/
def domQuietNamesRg (x : DomainId) : List (String × Nat) :=
  ((List.finRange numSlots).flatMap fun s =>
      [(Hw.dcapV x s, 1), (Hw.dcapKind x s, 32), (Hw.dcapLinV x s, 1),
       (Hw.dcapLin x s, 4), (Hw.dgen x s, 8)])
  ++ ((List.finRange numLineage).flatMap fun l =>
      [(Hw.dcellV x l, 1), (Hw.dcellPar x l, 14)])
  ++ [(Hw.drun x, 2), (Hw.drunG x, 2), (Hw.dsrvV x, 1), (Hw.dsrv x, 2),
      (Hw.dcause x, 32), (Hw.dbudget x, 32), (Hw.dmaxdon x, 32)]

private theorem quietRg_notin_unmap (x e : DomainId) :
    ∀ q ∈ domQuietNamesRg x, q ∉ (unmapFull e).regWrites := by
  rw [unmapFull_writes]
  fin_cases x <;> fin_cases e <;> decide +kernel

private theorem read_notin_unmap_ne (x e : DomainId) (hne : x ≠ e) :
    ∀ q ∈ domReadNames x, q ∉ (unmapFull e).regWrites := by
  rw [unmapFull_writes]
  fin_cases x <;> fin_cases e <;>
    first
      | exact absurd rfl hne
      | decide +kernel

private theorem gate_notin_unmap (g : GateId) (e : DomainId) :
    ∀ q ∈ gateReadNames g, q ∉ (unmapFull e).regWrites := by
  rw [unmapFull_writes]
  fin_cases g <;> fin_cases e <;> decide +kernel

/-- `drgn` (the 42-bit value registers) are never written by `unmap`. -/
private theorem drgn_notin_unmap : ∀ (x e : DomainId) (r : RegionId),
    ((Hw.drgn x r : String), (42 : Nat)) ∉ (unmapFull e).regWrites := by
  intro x e r
  rw [unmapFull_writes]
  revert r
  fin_cases x <;> fin_cases e <;> decide +kernel

/-- The regs/pc/regions face of `absDom` (quiet elsewhere). -/
theorem absDom_regpcrgn {S1 S2 : Loom.Hw.St} (e : DomainId)
    (hq : ∀ q ∈ domQuietNamesRg e, S2.regs q.1 q.2 = S1.regs q.1 q.2) :
    Hw.absDom S2 e =
      { Hw.absDom S1 e with
        regs := fun r => S2.regs (Hw.dreg e r) 32
        pc := S2.regs (Hw.dpc e) 12
        regions := fun r =>
          if S2.regs (Hw.drgnV e r) 1 = 1
          then some (Hw.decRegion (S2.regs (Hw.drgn e r) 42))
          else none } := by
  have hs : ∀ (s : Slot) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.dcapV e s, 1), (Hw.dcapKind e s, 32),
        (Hw.dcapLinV e s, 1), (Hw.dcapLin e s, 4), (Hw.dgen e s, 8)] →
      S2.regs rn w = S1.regs rn w := fun s rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨s, List.mem_finRange s, hp⟩)))
  have hl : ∀ (l : Fin numLineage) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.dcellV e l, 1), (Hw.dcellPar e l, 14)] →
      S2.regs rn w = S1.regs rn w := fun l rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨l, List.mem_finRange l, hp⟩)))
  have ht : ∀ (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.drun e, 2), (Hw.drunG e, 2), (Hw.dsrvV e, 1),
        (Hw.dsrv e, 2), (Hw.dcause e, 32), (Hw.dbudget e, 32),
        (Hw.dmaxdon e, 32)] →
      S2.regs rn w = S1.regs rn w := fun rn w hp =>
    hq (rn, w) (List.mem_append_right _ hp)
  apply domainState_ext'
  · rfl
  · rfl
  · show (Hw.absDom S2 e).caps = (Hw.absDom S1 e).caps
    funext s
    show (if S2.regs (Hw.dcapV e s) 1 = 1 then _ else none)
      = (if S1.regs (Hw.dcapV e s) 1 = 1 then _ else none)
    rw [hs s (Hw.dcapV e s) 1 (by simp), hs s (Hw.dcapKind e s) 32 (by simp),
      hs s (Hw.dcapLinV e s) 1 (by simp), hs s (Hw.dcapLin e s) 4 (by simp)]
  · show (Hw.absDom S2 e).slotGen = (Hw.absDom S1 e).slotGen
    funext s
    show S2.regs (Hw.dgen e s) 8 = S1.regs (Hw.dgen e s) 8
    rw [hs s (Hw.dgen e s) 8 (by simp)]
  · show (Hw.absDom S2 e).lineage = (Hw.absDom S1 e).lineage
    funext l
    show (if S2.regs (Hw.dcellV e l) 1 = 1 then _ else none)
      = (if S1.regs (Hw.dcellV e l) 1 = 1 then _ else none)
    rw [hl l (Hw.dcellV e l) 1 (by simp), hl l (Hw.dcellPar e l) 14 (by simp)]
  · rfl
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
  · show (S2.regs (Hw.dmaxdon e) 32).toNat = (S1.regs (Hw.dmaxdon e) 32).toNat
    rw [ht (Hw.dmaxdon e) 32 (by simp)]

/-! ## The `unmap` arm -/

private theorem seqAll_append_run (σ : Loom.Hw.St) :
    ∀ (l1 l2 : List Act) (acc : Loom.Hw.St),
      (Hw.seqAll (l1 ++ l2)).run σ acc
        = (Hw.seqAll l2).run σ ((Hw.seqAll l1).run σ acc)
  | [], _, _ => rfl
  | a :: t, l2, acc => by
      show (Hw.seqAll (t ++ l2)).run σ (a.run σ acc) = _
      rw [seqAll_append_run σ t l2 (a.run σ acc)]
      rfl

private theorem drgnV_inj : ∀ (e : DomainId) (r r' : RegionId),
    Hw.drgnV e r = Hw.drgnV e r' → r = r' := by decide +kernel

private theorem drgnV_notin_refill : ∀ (e : DomainId) (r : RegionId),
    ((Hw.drgnV e r : String), (1 : Nat)) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat)) := by
  decide +kernel

private theorem drgn_notin_refill' : ∀ (e : DomainId) (r : RegionId),
    ((Hw.drgn e r : String), (42 : Nat)) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat)) := by
  decide +kernel

set_option maxHeartbeats 25600000 in
/-- The `unmap` arm: opcode 21 — clear a region register. -/
theorem square_retire_unmap (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 21#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  set RIfin : RegionId := finOfBv (by decide)
    (((operandsOf W).imm).extractLsb' 0 2) with hRIdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (21#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (21#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  obtain ⟨hifsel, hifexcl⟩ := ifDomIs_sel σ E rfl
  have hunm : (Hw.isMn "unmap").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "unmap" = 21#6).symm
  have hret := retiringE_one σ hifv hcl
  have hin : Inert σ := Inert.of_benign7 σ (fun mn' hmn' =>
    isMn_ne_of_opc σ mn' 21#6 hopc
      ((by decide +kernel : ∀ mn' ∈ ["cap_drop", "cap_revoke", "gate_call",
        "gate_return", "move"], (21#6 : BitVec 6)
        ≠ Hw.opcodeOf mn') mn' hmn'))
  have hmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1 := fun c r =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "map" 21#6 hopc (by decide +kernel))
  have hswz : ∀ (d : DomainId) (sc : Expr 12),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs d, Hw.isMn "sw",
        Hw.domCoversE d (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          ⟨false, true, false⟩,
        .eq (Hw.field (.add (Hw.readReg d Hw.rs1E) Hw.immX) 0 12)
          sc]).eval σ = 0#1 := fun d sc =>
    andAll_zero_of_mem σ
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      (isMn_ne_of_opc σ "sw" 21#6 hopc (by decide +kernel))
  have hben5 : ∀ mn ∈ memMns, (Hw.isMn mn).eval σ ≠ 1#1 := fun mn hmn =>
    isMn_ne_of_opc σ mn 21#6 hopc
      ((by decide +kernel : ∀ mn ∈ memMns, (21#6 : BitVec 6)
        ≠ Hw.opcodeOf mn) mn hmn)
  have hri : Hw.riE.eval σ = BitVec.ofNat 2 RIfin.val := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (show RIfin.val < 2 ^ 2 from RIfin.isLt)).symm
  have hselC := retireFor_sel_of_opc σ E "unmap" 21#6 hopc
    (by decide +kernel) (by decide +kernel)
    ⟨Hw.seqAll (((List.finRange numRegions).map fun r =>
        .ite (.eq Hw.riE (Hw.rLit r)) (.write 1 (Hw.drgnV E r) (.lit 0))
          .skip)
      ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E]),
      .lit 0, .lit 0, .lit 0⟩
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))))))
  have hfl : (refillPhase m (Hw.abs σ)).inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have habs1 : Hw.abs ((Hw.refillAct m).run σ σ) = refillPhase m (Hw.abs σ) :=
    abs_refill m hwf hfit σ hsync
  have hL1 : ∀ y, (refillPhase m (Hw.abs σ)).doms y
      = Hw.absDom ((Hw.refillAct m).run σ σ) y := by
    intro y
    rw [← habs1]
    rfl
  have hspec : corePhase m (refillPhase m (Hw.abs σ))
      = ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
          (fun ds => ({ { ds with pc := ds.pc + 1 } with
            regions := Loom.Fun.update ({ ds with pc := ds.pc + 1 }).regions
              RIfin none }).setReg (operandsOf W).rd 0) := by
    rw [corePhase_retire m _ _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
    show retire { refillPhase m (Hw.abs σ) with inflight := none }
      (finOfBv (by decide) (σ.regs "if_dom" 2)) W = _
    rw [← hEdef]
    have h1 : retire { refillPhase m (Hw.abs σ) with inflight := none } E W
        = (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
            (fun ds => { ds with pc := ds.pc + 1 })).setDom E
            (fun ds => { ds with
              regions := Loom.Fun.update ds.regions RIfin none })).setDom E
            (fun ds => ds.setReg (operandsOf W).rd 0)) := by
      rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
      rfl
    rw [h1, setDom_setDom, setDom_setDom]
  have hτ2doms : ∀ x, (({ refillPhase m (Hw.abs σ) with inflight := none
      }).setDom E (fun ds => ({ { ds with pc := ds.pc + 1 } with
        regions := Loom.Fun.update ({ ds with pc := ds.pc + 1 }).regions
          RIfin none }).setReg (operandsOf W).rd 0)).doms x
      = if x = E
        then ({ { (refillPhase m (Hw.abs σ)).doms E with
            pc := ((refillPhase m (Hw.abs σ)).doms E).pc + 1 } with
            regions := Loom.Fun.update
              ((refillPhase m (Hw.abs σ)).doms E).regions RIfin
              none }).setReg (operandsOf W).rd 0
        else (refillPhase m (Hw.abs σ)).doms x := by
    intro x
    show (Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) x = _
    by_cases hx : x = E
    · subst hx
      rw [Loom.Fun.update_same, if_pos rfl]
    · rw [Loom.Fun.update_ne _ _ _ _ hx, if_neg hx]
  -- HW faces of the drgnV file
  have hrgnV : ∀ r : RegionId,
      ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.drgnV E r) 1
      = if r = RIfin then 0#1 else σ.regs (Hw.drgnV E r) 1 := by
    intro r
    show ((Hw.seqAll (((List.finRange numRegions).map fun r' =>
        Act.ite (.eq Hw.riE (Hw.rLit r')) (.write 1 (Hw.drgnV E r') (.lit 0))
          .skip)
      ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E])).run σ
        ((Act.write 1 "if_v" (.lit 0)).run σ
          ((Hw.refillAct m).run σ σ))).regs (Hw.drgnV E r) 1 = _
    rw [seqAll_append_run]
    rw [show ((Hw.seqAll [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E]).run σ
        ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
          Act.ite (.eq Hw.riE (Hw.rLit r'))
            (.write 1 (Hw.drgnV E r') (.lit 0)) .skip)).run σ
          ((Act.write 1 "if_v" (.lit 0)).run σ
            ((Hw.refillAct m).run σ σ)))).regs (Hw.drgnV E r) 1
      = ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
          Act.ite (.eq Hw.riE (Hw.rLit r'))
            (.write 1 (Hw.drgnV E r') (.lit 0)) .skip)).run σ
          ((Act.write 1 "if_v" (.lit 0)).run σ
            ((Hw.refillAct m).run σ σ))).regs (Hw.drgnV E r) 1 from by
      show ((Hw.pcAdvA E).run σ ((Hw.writeReg E Hw.rdE (Expr.lit 0)).run σ
        _)).regs (Hw.drgnV E r) 1 = _
      rw [frame (show (Hw.drgnV E r, 1) ∉ (Hw.pcAdvA E).regWrites from by
        intro hm
        exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
          (show ¬((1 : Nat) = 12) by decide)) σ _]
      rw [frame ((by decide +kernel : ∀ (e : DomainId) (r' : RegionId),
        ((Hw.drgnV e r' : String), (1 : Nat))
          ∉ (Hw.writeReg e Hw.rdE (Expr.lit 0)).regWrites) E r) σ _]]
    rw [seqAll_ite_run_unique σ _
      (fun r' : RegionId => Expr.eq Hw.riE (Hw.rLit r'))
      (fun r' : RegionId => Act.write 1 (Hw.drgnV E r') (.lit 0)) RIfin
      (by
        show (Expr.eq Hw.riE (Hw.rLit RIfin)).eval σ = 1#1
        rw [eqE_eval, hri]
        rfl)
      (fun j hj => by
        intro hc0
        have hc : (Expr.eq Hw.riE (Hw.rLit j)).eval σ = 1#1 := hc0
        rw [eqE_eval, hri] at hc
        apply hj
        apply Fin.ext
        have : (BitVec.ofNat 2 RIfin.val).toNat
            = (BitVec.ofNat 2 j.val).toNat := by rw [hc]; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show j.val < 2 ^ 2 from j.isLt),
          Nat.mod_eq_of_lt (show RIfin.val < 2 ^ 2 from RIfin.isLt)] at this
        omega)
      _ (List.mem_finRange RIfin) (List.nodup_finRange _)]
    show (RegEnv.set _ (Hw.drgnV E RIfin) ((Expr.lit 0).eval σ))
      (Hw.drgnV E r) 1 = _
    simp only [RegEnv.set]
    by_cases hr : r = RIfin
    · rw [if_pos (by rw [hr]), if_pos hr]
      rfl
    · rw [if_neg (fun hc => hr (drgnV_inj E r RIfin hc)), if_neg hr]
      rw [frame (fun hm => absurd
        (congrArg Prod.fst (List.mem_singleton.mp hm))
        ((by decide +kernel : ∀ (e : DomainId) (r' : RegionId),
          ¬(Hw.drgnV e r' = "if_v")) E r)) σ _]
      exact refill_pres m σ (drgnV_notin_refill E r)
  have hrgn42 : ∀ r : RegionId,
      ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
        (Hw.drgn E r) 42 = σ.regs (Hw.drgn E r) 42 := by
    intro r
    rw [frame (drgn_notin_unmap E E r) σ _]
    exact refill_pres m σ (drgn_notin_refill' E r)
  refine square_retire_rgnop m hwf hfit σ hsync hifv hcl hin
    (Hw.seqAll (((List.finRange numRegions).map fun r =>
        .ite (.eq Hw.riE (Hw.rLit r)) (.write 1 (Hw.drgnV E r) (.lit 0))
          .skip)
      ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E])) _
    (fun rn w => by
      rw [coreAct_run_retire_eq m σ _ hifv hcl,
        retireAct_run_regs σ _ E rfl rn w, hselC]
      rfl)
    ((by decide +kernel : ∀ e : DomainId, (("if_v" : String), (1 : Nat))
      ∉ (Hw.seqAll (((List.finRange numRegions).map fun r =>
        Act.ite (.eq Hw.riE (Hw.rLit r)) (.write 1 (Hw.drgnV e r) (.lit 0))
          .skip)
      ++ [Hw.writeReg e Hw.rdE (Expr.lit 0), Hw.pcAdvA e])).regWrites) E)
    hspec ?_ ?_ ?_ ?_ ?_ (fun ow sa => ?_) ?_ ?_ ?_ ?_
  · -- absDom faces
    intro x
    rw [hτ2doms x]
    by_cases hx : x = E
    · rw [if_pos hx]
      subst hx
      show Hw.absDom ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)) E = _
      have hq : ∀ q ∈ domQuietNamesRg E,
          ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs q.1 q.2
            = ((Hw.refillAct m).run σ σ).regs q.1 q.2 :=
        fun q hq' => frame (quietRg_notin_unmap E E q hq') σ _
      rw [absDom_regpcrgn E hq]
      rw [show (refillPhase m (Hw.abs σ)).doms E
        = Hw.absDom ((Hw.refillAct m).run σ σ) E from hL1 E]
      apply domainState_ext'
      · funext r
        show ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
          (Hw.dreg E r) 32 = _
        rw [show ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.dreg E r) 32
            = ((Hw.writeReg E Hw.rdE (.lit 0)).run σ
                ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
                  Act.ite (.eq Hw.riE (Hw.rLit r'))
                    (.write 1 (Hw.drgnV E r') (.lit 0)) .skip)).run σ
                  ((Act.write 1 "if_v" (.lit 0)).run σ
                    ((Hw.refillAct m).run σ σ)))).regs (Hw.dreg E r) 32 from by
          show ((Hw.seqAll (((List.finRange numRegions).map fun r' =>
              Act.ite (.eq Hw.riE (Hw.rLit r'))
                (.write 1 (Hw.drgnV E r') (.lit 0)) .skip)
            ++ [Hw.writeReg E Hw.rdE (.lit 0), Hw.pcAdvA E])).run σ
              ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ))).regs (Hw.dreg E r) 32 = _
          rw [seqAll_append_run]
          show ((Hw.pcAdvA E).run σ
            ((Hw.writeReg E Hw.rdE (Expr.lit 0)).run σ _)).regs
            (Hw.dreg E r) 32 = _
          rw [frame (show (Hw.dreg E r, 32) ∉ (Hw.pcAdvA E).regWrites from by
            intro hm
            exact absurd (congrArg Prod.snd (List.mem_singleton.mp hm))
              (show ¬((32 : Nat) = 12) by decide)) σ _]]
        show _ = (({ { Hw.absDom ((Hw.refillAct m).run σ σ) E with
            pc := (Hw.absDom ((Hw.refillAct m).run σ σ) E).pc + 1 } with
            regions := Loom.Fun.update
              ({ Hw.absDom ((Hw.refillAct m).run σ σ) E with
                pc := (Hw.absDom ((Hw.refillAct m).run σ σ) E).pc + 1
                }).regions RIfin none }).setReg (operandsOf W).rd 0).regs r
        rw [setReg_regs]
        have hitefr :
            ((Hw.seqAll ((List.finRange numRegions).map fun r' =>
              Act.ite (.eq Hw.riE (Hw.rLit r'))
                (.write 1 (Hw.drgnV E r') (.lit 0)) .skip)).run σ
              ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ))).regs (Hw.dreg E r) 32
            = ((Act.write 1 "if_v" (.lit 0)).run σ
                ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32 := by
          rw [seqAll_ite_run_unique σ _
            (fun r' : RegionId => Expr.eq Hw.riE (Hw.rLit r'))
            (fun r' : RegionId => Act.write 1 (Hw.drgnV E r') (.lit 0)) RIfin
            (by
              show (Expr.eq Hw.riE (Hw.rLit RIfin)).eval σ = 1#1
              rw [eqE_eval, hri]
              rfl)
            (fun j hj => by
              intro hc0
              have hc : (Expr.eq Hw.riE (Hw.rLit j)).eval σ = 1#1 := hc0
              rw [eqE_eval, hri] at hc
              apply hj
              apply Fin.ext
              have : (BitVec.ofNat 2 RIfin.val).toNat
                  = (BitVec.ofNat 2 j.val).toNat := by rw [hc]; rfl
              rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (show j.val < 2 ^ 2 from j.isLt),
                Nat.mod_eq_of_lt
                  (show RIfin.val < 2 ^ 2 from RIfin.isLt)] at this
              omega)
            _ (List.mem_finRange RIfin) (List.nodup_finRange _)]
          exact frame (fun hm => absurd
            (congrArg Prod.snd (List.mem_singleton.mp hm))
            (show ¬((32 : Nat) = 1) by decide)) σ _
        have hifvframe :
            ((Act.write 1 "if_v" (.lit 0)).run σ
              ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32
            = ((Hw.refillAct m).run σ σ).regs (Hw.dreg E r) 32 :=
          frame (fun hm => absurd
            (congrArg Prod.snd (List.mem_singleton.mp hm))
            (show ¬((32 : Nat) = 1) by decide)) σ _
        by_cases h0 : (operandsOf W).rd = (0 : Fin numRegs)
        · rw [if_pos h0]
          rw [writeReg_run_of_zero σ _ E Hw.rdE _ (by
            rw [show ((Hw.rdE.eval σ)).toNat
              = ((operandsOf W).rd : Fin numRegs).val from rfl, h0]
            rfl)]
          rw [hitefr, hifvframe]
          rfl
        · rw [if_neg h0]
          rw [writeReg_run_of_nz σ _ E Hw.rdE _ (operandsOf W).rd rfl
            (fun hc => h0 (Fin.ext hc))]
          show (RegEnv.set _ (Hw.dreg E (operandsOf W).rd) _)
            (Hw.dreg E r) 32 = _
          simp only [RegEnv.set]
          by_cases hr : r = (operandsOf W).rd
          · rw [if_pos (by rw [hr]), if_pos hr, dif_pos trivial]
            rfl
          · rw [if_neg (fun hc => hr (dreg_inj E r (operandsOf W).rd hc)),
              if_neg hr]
            rw [hitefr, hifvframe]
            rfl
      · show ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
          (Hw.dpc E) 12 = _
        rw [show ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.dpc E) 12 = σ.regs (Hw.dpc E) 12 + 1 from by
          show (RegEnv.set _ (Hw.dpc E)
            ((Expr.add (Hw.rPc E) (.lit 1)).eval σ)) (Hw.dpc E) 12 = _
          simp [RegEnv.set, Expr.eval, Hw.rPc]]
        rw [setReg_pc]
        show σ.regs (Hw.dpc E) 12 + 1
          = ((Hw.refillAct m).run σ σ).regs (Hw.dpc E) 12 + 1
        rw [refill_pres m σ ((by decide +kernel : ∀ e : DomainId,
          ((Hw.dpc e : String), (12 : Nat)) ∉
          ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
            ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
            ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat))) E)]
      · rw [setReg_caps]
      · rw [setReg_slotGen]
      · rw [setReg_lineage]
      · -- the region file
        funext r
        rw [setReg_regions]
        show (if ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
            (Hw.drgnV E r) 1 = 1
          then some (Hw.decRegion
            (((unmapFull E).run σ ((Hw.refillAct m).run σ σ)).regs
              (Hw.drgn E r) 42))
          else none)
          = Loom.Fun.update
              (Hw.absDom ((Hw.refillAct m).run σ σ) E).regions RIfin none r
        rw [hrgnV r, hrgn42 r]
        unfold Loom.Fun.update
        by_cases hr : r = RIfin
        · rw [if_pos hr, if_pos hr, if_neg (by decide : ¬((0#1 : BitVec 1)
            = 1))]
        · rw [if_neg hr, if_neg hr]
          show (if σ.regs (Hw.drgnV E r) 1 = 1 then _ else none) = _
          rw [show (Hw.absDom ((Hw.refillAct m).run σ σ) E).regions r
            = (if ((Hw.refillAct m).run σ σ).regs (Hw.drgnV E r) 1 = 1
              then some (Hw.decRegion
                (((Hw.refillAct m).run σ σ).regs (Hw.drgn E r) 42))
              else none) from rfl]
          rw [refill_pres m σ (drgnV_notin_refill E r),
            refill_pres m σ (drgn_notin_refill' E r)]
      · rw [setReg_run]
      · rw [setReg_serving]
      · rw [setReg_cause]
      · rw [setReg_budget]
      · rw [setReg_maxDonation]
    · rw [if_neg hx]
      show Hw.absDom ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)) x = _
      rw [hL1 x]
      exact absDom_congr x (fun p hp =>
        frame (read_notin_unmap_ne x E hx p hp) σ _)
  · -- gates
    intro g
    show Hw.absGate ((unmapFull E).run σ ((Hw.refillAct m).run σ σ)) g = _
    rw [absGate_congr g (fun p hp =>
      frame (gate_notin_unmap g E p hp) σ _)]
    rw [← habs1]
    rfl
  · intro x
    rw [hτ2doms x]
    by_cases hx : x = E
    · rw [if_pos hx, setReg_caps]
      show ((refillPhase m (Hw.abs σ)).doms E).caps = _
      rw [refillPhase_caps, hx]
    · rw [if_neg hx, refillPhase_caps]
  · intro x
    rw [hτ2doms x]
    by_cases hx : x = E
    · rw [if_pos hx, setReg_slotGen]
      show ((refillPhase m (Hw.abs σ)).doms E).slotGen = _
      rw [refillPhase_slotGen, hx]
    · rw [if_neg hx, refillPhase_slotGen]
  · show (refillPhase m (Hw.abs σ)).mover = _
    rw [refillPhase_mover]
    rfl
  · -- the fired-unmap status authority
    refine sAuth_unmap_eval σ E hin hret hifsel hifexcl hunm hmapz RIfin hri
      _ ?_ ow sa
    intro c r
    rw [hτ2doms c]
    by_cases hc : c = E
    · subst hc
      rw [if_pos rfl, setReg_regions]
      show Loom.Fun.update ((refillPhase m (Hw.abs σ)).doms E).regions RIfin
        none r = _
      unfold Loom.Fun.update
      by_cases hr : r = RIfin
      · rw [if_pos hr, if_pos ⟨rfl, hr⟩]
      · rw [if_neg hr, if_neg (fun hcr => hr hcr.2)]
        rw [refillPhase_regions]
    · rw [if_neg hc, if_neg (fun hcr => hc hcr.1), refillPhase_regions]
  · -- memory: no store
    intro b
    rw [coreAct_mems_quiet m σ _ hifv hcl hben5]
    rw [refill_pres_mem m σ "mem" b.toNat 32]
    rfl
  · -- forwarding quiescent
    intro sc
    rw [srcWord_quiescent σ hswz sc]
    rfl
  · show (refillPhase m (Hw.abs σ)).cycle = _
    rfl
  · rfl

/-! ## Capability-selector bridges (shared by the system-op arms) -/

/-- The selector's slot/gen expressions read the handle word's fields. -/
theorem capSel_live_eval (σ : Loom.Hw.St) (E : DomainId) (hwE : Expr 32)
    (S : Slot) (hS : S.val = ((hwE.eval σ).extractLsb' 0 4).toNat) :
    ((Hw.capSel E hwE).live.eval σ = 1#1) ↔
      (σ.regs (Hw.dcapV E S) 1 = 1#1
        ∧ σ.regs (Hw.dgen E S) 8 = (hwE.eval σ).extractLsb' 4 8
        ∧ (hwE.eval σ).extractLsb' 4 8 ≠ 0) := by
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
      ((Hw.field hwE 0 4).eval σ) = S :=
    Fin.ext (by rw [hS]; rfl)
  rw [show (Hw.capSel E hwE).live = Hw.andAll
    [Hw.muxFin (fun s => .reg 1 (Hw.dcapV E s)) (Hw.field hwE 0 4),
     .eq (Hw.muxFin (fun s => .reg 8 (Hw.dgen E s)) (Hw.field hwE 0 4))
       (Hw.field hwE 4 8),
     Hw.neqE (Hw.field hwE 4 8) (.lit 0)] from rfl]
  constructor
  · intro h
    have h3 := (andAll_eval σ _).mp h
    have h1 := h3 _ (List.mem_cons_self ..)
    have h2 := h3 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h4 := h3 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))
    rw [muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin] at h1
    rw [eqE_eval, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin] at h2
    rw [neqE_eval] at h4
    exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h3⟩
    rw [andAll_eval]
    intro e he
    rcases he with _ | ⟨_, _ | ⟨_, _ | ⟨_, h⟩⟩⟩
    · rw [muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
      exact h1
    · rw [eqE_eval, muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
      exact h2
    · rw [neqE_eval]
      exact h3
    · exact absurd h (List.not_mem_nil)

/-- The selector's kind word reads the slot's kind register. -/
theorem capSel_kindW_eval (σ : Loom.Hw.St) (E : DomainId) (hwE : Expr 32)
    (S : Slot) (hS : S.val = ((hwE.eval σ).extractLsb' 0 4).toNat) :
    (Hw.capSel E hwE).kindW.eval σ = σ.regs (Hw.dcapKind E S) 32 := by
  have hfin : finOfBv (by decide : 2 ^ 4 = numSlots)
      ((Hw.field hwE 0 4).eval σ) = S :=
    Fin.ext (by rw [hS]; rfl)
  show (Hw.muxFin (fun s => Expr.reg 32 (Hw.dcapKind E s))
    (Hw.field hwE 0 4)).eval σ = _
  rw [muxFin_eval (by decide : 2 ^ 4 = numSlots), hfin]
  rfl

/-- `liveCap` of the advanced spec state against the selector's test. -/
theorem specLiveCap_bridge (m : Manifest) (σ : Loom.Hw.St) (E : DomainId)
    (S : Slot) (g : Gen) :
    ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })).doms E)).liveCap S g)
      = (((Hw.abs σ).doms E).liveCap S g) := by
  have hcp : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })).doms E).caps
      = ((Hw.abs σ).doms E).caps := by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E).caps = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).caps = _
    rw [refillPhase_caps]
  have hgn : ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })).doms E).slotGen
      = ((Hw.abs σ).doms E).slotGen := by
    show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E).slotGen = _
    rw [Loom.Fun.update_same]
    show ((refillPhase m (Hw.abs σ)).doms E).slotGen = _
    rw [refillPhase_slotGen]
  show DomainState.liveCap _ S g = DomainState.liveCap _ S g
  unfold DomainState.liveCap
  rw [hcp, hgn]

/-! ## The `map` value bridge -/

private theorem encKindMem_base (B : BitVec 12) (L : BitVec 13) (P : Perms) :
    (Hw.encKind (.mem B L P)).extractLsb' 1 12 = B := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Hw.encKind, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [Hw.encPerms]

private theorem encKindMem_len (B : BitVec 12) (L : BitVec 13) (P : Perms) :
    (Hw.encKind (.mem B L P)).extractLsb' 13 13 = L := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Hw.encKind, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [Hw.encPerms]

private theorem encKindMem_perms (B : BitVec 12) (L : BitVec 13) (P : Perms) :
    (Hw.encKind (.mem B L P)).extractLsb' 26 3 = Hw.encPerms P := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Hw.encKind, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [Hw.encPerms]

/-- The packed region value the `map` circuit writes, for a canonical
memory kind word: exactly `encRegion`. -/
private theorem mapVal_pack (B : BitVec 12) (L : BitVec 13) (P : Perms)
    (rf : BitVec 14) :
    (((Hw.encKind (.mem B L P)).extractLsb' 26 3).setWidth 42
      ||| ((((Hw.encKind (.mem B L P)).extractLsb' 13 13).setWidth 42 <<< 3)
      ||| ((((Hw.encKind (.mem B L P)).extractLsb' 1 12).setWidth 42 <<< 16)
      ||| (rf.setWidth 42 <<< 28))))
    = Hw.encRegion { base := B, len := L, perms := P,
                     backing := Hw.decRef rf } := by
  rw [encKindMem_base, encKindMem_len, encKindMem_perms]
  have hER : Hw.encRegion { base := B, len := L, perms := P, backing := Hw.decRef rf }
      = ((Hw.encPerms P).setWidth 42 ||| (L.setWidth 42 <<< 3) |||
        (B.setWidth 42 <<< 16) |||
        ((Hw.encRef (Hw.decRef rf)).setWidth 42 <<< 28)) := rfl
  rw [hER, encRef_decRef]
  simp [BitVec.or_assoc]

/-! ## The fired-`map` status authority -/

/-- The fired `map` chain (checks passing): the region-index test on the
owner, off elsewhere. -/
private theorem mapChain_eval (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hmap : (Hw.isMn "map").eval σ = 1#1)
    (hok : (Hw.mapOkE E).eval σ = 1#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val) :
    ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map", Hw.mapOkE c,
        .eq Hw.riE (Hw.rLit r)]).eval σ
      = if c = E ∧ r = RI then 1#1 else 0#1 := by
  intro c r
  by_cases hc : c = E
  · subst hc
    show Hw.retiringE.eval σ &&& ((Hw.ifDomIs c).eval σ &&&
      ((Hw.isMn "map").eval σ &&& ((Hw.mapOkE c).eval σ &&&
        (Expr.eq Hw.riE (Hw.rLit r)).eval σ))) = _
    rw [hret, hifsel, hmap, hok, bv1_one_and3, bv1_one_and3, bv1_one_and3,
      bv1_one_and3]
    by_cases hr : r = RI
    · subst hr
      rw [if_pos ⟨rfl, rfl⟩]
      show (if Hw.riE.eval σ = (Hw.rLit r).eval σ then (1#1 : BitVec 1)
        else 0#1) = 1#1
      rw [if_pos (by rw [hri]; rfl)]
    · rw [if_neg (fun hc' => hr hc'.2)]
      show (if Hw.riE.eval σ = (Hw.rLit r).eval σ then (1#1 : BitVec 1)
        else 0#1) = 0#1
      rw [if_neg (by
        rw [hri]
        intro hc'
        apply hr
        apply Fin.ext
        have : (BitVec.ofNat 2 RI.val).toNat = (BitVec.ofNat 2 r.val).toNat :=
          by rw [hc']; rfl
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show r.val < 2 ^ 2 from r.isLt),
          Nat.mod_eq_of_lt (show RI.val < 2 ^ 2 from RI.isLt)] at this
        omega)]
  · rw [if_neg (fun hc' => hc hc'.1)]
    show Hw.retiringE.eval σ &&& ((Hw.ifDomIs c).eval σ &&&
      ((Hw.isMn "map").eval σ &&& ((Hw.mapOkE c).eval σ &&&
        (Expr.eq Hw.riE (Hw.rLit r)).eval σ))) = 0#1
    rw [bv1_ne_one.mp (hifexcl c hc)]
    exact bv1_mid_zero _ _

/-- `rgnVPostE` under a fired `map`: live at the selected register, the
validity register elsewhere. -/
private theorem rgnVPostE_map (σ : Loom.Hw.St) (E : DomainId)
    (hnr : Inert σ)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hmap : (Hw.isMn "map").eval σ = 1#1)
    (hok : (Hw.mapOkE E).eval σ = 1#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val)
    (c : DomainId) (r : RegionId) :
    (Hw.rgnVPostE c r).eval σ
      = if c = E ∧ r = RI then 1#1 else σ.regs (Hw.drgnV c r) 1 := by
  show (if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map",
      Hw.mapOkE c, .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1
    then (Expr.lit 1).eval σ
    else if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1
      then (Expr.lit 0).eval σ
      else (Expr.and (.reg 1 (Hw.drgnV c r))
        (.not (Hw.killedByCoreE _ _))).eval σ) = _
  rw [mapChain_eval σ E hret hifsel hifexcl hmap hok RI hri c r]
  by_cases hcr : c = E ∧ r = RI
  · rw [if_pos hcr, if_pos rfl, if_pos hcr]
    rfl
  · rw [if_neg hcr, if_neg (by decide : ¬((0#1 : BitVec 1) = 1#1)),
      if_neg hcr, hunmapz c r,
      if_neg (by decide : ¬((0#1 : BitVec 1) = 1#1))]
    show σ.regs (Hw.drgnV c r) 1 &&& ~~~((Hw.killedByCoreE _ _).eval σ) = _
    rw [hnr.killed]
    generalize σ.regs (Hw.drgnV c r) 1 = b
    revert b
    decide

/-- `rgnValPostE` under a fired `map`: the packed map value at the
selected register, the value register elsewhere. -/
private theorem rgnValPostE_map (σ : Loom.Hw.St) (E : DomainId)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hmap : (Hw.isMn "map").eval σ = 1#1)
    (hok : (Hw.mapOkE E).eval σ = 1#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val)
    (c : DomainId) (r : RegionId) :
    (Hw.rgnValPostE c r).eval σ
      = if c = E ∧ r = RI then (Hw.mapValE E).eval σ
        else σ.regs (Hw.drgn c r) 42 := by
  show (if (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "map",
      Hw.mapOkE c, .eq Hw.riE (Hw.rLit r)]).eval σ = 1#1
    then (Hw.mapValE c).eval σ
    else (Expr.reg 42 (Hw.drgn c r)).eval σ) = _
  rw [mapChain_eval σ E hret hifsel hifexcl hmap hok RI hri c r]
  by_cases hcr : c = E ∧ r = RI
  · rw [if_pos hcr, if_pos rfl, if_pos hcr, hcr.1]
  · rw [if_neg hcr, if_neg (by decide : ¬((0#1 : BitVec 1) = 1#1)),
      if_neg hcr]
    rfl

/-- The status-authority tree under a fired `map`, against any spec
state whose regions are the abstraction's with the selected one caching
the decoded map value. -/
theorem sAuth_map_eval (σ : Loom.Hw.St) (E : DomainId)
    (hnr : Inert σ)
    (hret : Hw.retiringE.eval σ = 1#1)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hmap : (Hw.isMn "map").eval σ = 1#1)
    (hok : (Hw.mapOkE E).eval σ = 1#1)
    (hunmapz : ∀ (c : DomainId) (r : RegionId),
      (Hw.andAll [Hw.retiringE, Hw.ifDomIs c, Hw.isMn "unmap",
        .eq Hw.riE (Hw.rLit r)]).eval σ = 0#1)
    (RI : RegionId) (hri : Hw.riE.eval σ = BitVec.ofNat 2 RI.val)
    (τ : MachineState)
    (hrgnτ : ∀ (c : DomainId) (r : RegionId), ((τ.doms c)).regions r
      = if c = E ∧ r = RI
        then some (Hw.decRegion ((Hw.mapValE E).eval σ))
        else ((Hw.abs σ).doms c).regions r)
    (ow : Expr 2) (sa : Expr 12) :
    ((Hw.orAll ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numRegions).map fun r =>
          Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
            Hw.rgnCoversVal (Hw.rgnValPostE c r) sa
              ⟨false, true, false⟩])).eval σ = 1#1) ↔
      τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
        ⟨false, true, false⟩ = true := by
  rw [orAll_eval]
  rw [show (τ.domCovers (finOfBv (by decide) (ow.eval σ)) (sa.eval σ)
      ⟨false, true, false⟩ = true) ↔
      (∃ r : RegionId, ∃ rg,
        (τ.doms (finOfBv (by decide) (ow.eval σ))).regions r = some rg
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
    rw [rgnCoversVal_eval,
      rgnValPostE_map σ E hret hifsel hifexcl hmap hok RI hri c r] at hcv
    by_cases hcr : c = E ∧ r = RI
    · rw [if_pos hcr] at hcv
      refine ⟨r, Hw.decRegion ((Hw.mapValE E).eval σ), ?_, hcv⟩
      rw [hc, hrgnτ c r, if_pos hcr]
    · rw [rgnVPostE_map σ E hnr hret hifsel hifexcl hmap hok hunmapz RI hri
        c r, if_neg hcr] at h2
      rw [if_neg hcr] at hcv
      refine ⟨r, Hw.decRegion (σ.regs (Hw.drgn c r) 42), ?_, hcv⟩
      rw [hc, hrgnτ c r, if_neg hcr, abs_regions, if_pos h2]
  · rintro ⟨r, rg, hsome, hcov⟩
    set c : DomainId := finOfBv (by decide) (ow.eval σ) with hcdef
    rw [hrgnτ c r] at hsome
    refine ⟨Hw.andAll [Expr.eq ow (Hw.dLit c), Hw.rgnVPostE c r,
        Hw.rgnCoversVal (Hw.rgnValPostE c r) sa ⟨false, true, false⟩],
      List.mem_flatMap.mpr ⟨c, List.mem_finRange c,
        List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩⟩, ?_⟩
    by_cases hcr : c = E ∧ r = RI
    · rw [if_pos hcr] at hsome
      obtain rfl := Option.some.inj hsome
      rw [andAll_eval]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rw [eqE_eval]
        exact (bv2_lit_iff _ c).mpr rfl
      · rw [rgnVPostE_map σ E hnr hret hifsel hifexcl hmap hok hunmapz RI
          hri c r, if_pos hcr]
      · rw [rgnCoversVal_eval,
          rgnValPostE_map σ E hret hifsel hifexcl hmap hok RI hri c r,
          if_pos hcr]
        exact hcov
    · rw [if_neg hcr] at hsome
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
        · rw [rgnVPostE_map σ E hnr hret hifsel hifexcl hmap hok hunmapz RI
            hri c r, if_neg hcr]
          exact hval
        · rw [rgnCoversVal_eval,
            rgnValPostE_map σ E hret hifsel hifexcl hmap hok RI hri c r,
            if_neg hcr]
          exact hcov
      · rw [if_neg hval] at hsome
        exact absurd hsome (by simp)

end Machines.Lnp64u.Theorems.RMC





