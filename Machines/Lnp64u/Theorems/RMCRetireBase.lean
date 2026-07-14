-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetire
import Machines.Lnp64u.Theorems.RMCZero

/-!
# R-MC support: the benign-retirement glue

A *benign* retiring op (ALU/branch/jump/load class) neither kills
references, installs a Mover job, edits regions, nor stores — so the
Mover rule stays quiescent (`Inert.of_benign`) and the retirement's only
footprint is the owner's registers plus the cleared latch.
`square_retire_benign` packages the whole refill/Mover/tick assembly
once; a per-op arm supplies only

* the selected circuit and its register effect (`hcoreR`, from the
  dispatch skeleton),
* the spec's post-core state and the `absDom`/`absGate` correspondence
  on it (the op's actual datapath content).
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-! ## Opcode-driven benignness -/

/-- A mnemonic whose opcode differs from the latched one is off. -/
theorem isMn_ne_of_opc (σ : Loom.Hw.St) (mn : String) (k : BitVec 6)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = k)
    (hne : k ≠ Hw.opcodeOf mn) : (Hw.isMn mn).eval σ ≠ 1#1 := by
  intro h
  rw [isMn_eval, hopc] at h
  exact hne h

/-- The eight Mover-relevant mnemonics (`Inert.of_benign`'s list). -/
def moverMns : List String :=
  ["cap_drop", "cap_revoke", "gate_call", "gate_return", "move", "map",
   "unmap", "sw"]

/-- Benignness from the latched opcode: distinct from all eight
Mover-relevant opcodes. -/
theorem inert_of_opc (σ : Loom.Hw.St) (k : BitVec 6)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = k)
    (hne : ∀ mn ∈ moverMns, k ≠ Hw.opcodeOf mn) : Inert σ :=
  Inert.of_benign σ (fun mn hmn => isMn_ne_of_opc σ mn k hopc (hne mn hmn))

/-! ## The retirement memory port is idle for benign ops -/

/-- Syntactic literal-zero test for enable expressions. -/
private def isLit0 (e : Expr 1) : Bool :=
  match e with
  | .lit v => v == 0#1
  | _ => false

/-- Every op circuit's memory enable is either literally off or gated by
a Mover-relevant mnemonic. -/
private def memInert (l : List (String × Hw.OpCirc)) : Bool :=
  l.all fun p => decide (p.1 ∈ moverMns) || isLit0 p.2.memEn

private theorem memInert_opCircs : ∀ d : DomainId,
    memInert (Hw.opCircs d) = true := by
  intro d
  fin_cases d <;> decide +kernel

private theorem bv1_and_zero' (x : BitVec 1) : x &&& 0#1 = 0#1 := by
  revert x; decide

private theorem isLit0_eval (σ : Loom.Hw.St) (e : Expr 1)
    (h : isLit0 e = true) : e.eval σ = 0#1 := by
  cases e <;> simp_all [isLit0, Expr.eval]

private theorem bv1_zero_and' (x : BitVec 1) : 0#1 &&& x = 0#1 := by
  revert x; decide

private theorem bv1_zero_or (x : BitVec 1) : 0#1 ||| x = x := by
  revert x; decide

/-- The op-level enable/address/data fold (the body of
`Hw.retireMemFor`). -/
private def enFold (l : List (String × Hw.OpCirc)) :
    Expr 1 × Expr 12 × Expr 32 :=
  l.foldr
    (fun (p : String × Hw.OpCirc) (acc : Expr 1 × Expr 12 × Expr 32) =>
      let g := Expr.and (Hw.isMn p.1) p.2.memEn
      (.or g acc.1, .mux g p.2.memAddr acc.2.1, .mux g p.2.memData acc.2.2))
    (.lit 0, .lit 0, .lit 0)

/-- The per-domain enable fold is off under benignness. -/
private theorem memFold_en_zero (σ : Loom.Hw.St)
    (hben : ∀ mn ∈ moverMns, (Hw.isMn mn).eval σ ≠ 1#1) :
    ∀ (l : List (String × Hw.OpCirc)), memInert l = true →
      ((enFold l).1).eval σ = 0#1
  | [], _ => rfl
  | p :: t, h => by
      simp only [memInert, List.all_cons, Bool.and_eq_true,
        Bool.or_eq_true] at h
      show ((Hw.isMn p.1).eval σ &&& p.2.memEn.eval σ) |||
        ((enFold t).1).eval σ = 0#1
      have hg : (Hw.isMn p.1).eval σ &&& p.2.memEn.eval σ = 0#1 := by
        rcases h.1 with hmn | hlit
        · rw [bv1_ne_one.mp (hben p.1 (of_decide_eq_true hmn))]
          exact bv1_zero_and' _
        · rw [isLit0_eval σ _ hlit]
          exact bv1_and_zero' _
      rw [hg, bv1_zero_or]
      exact memFold_en_zero σ hben t
        (by simp only [memInert]; exact h.2)

/-- The cross-domain mux fold (the body of `retireAct`'s commit). -/
private def domFold (l : List DomainId) : Expr 1 × Expr 12 × Expr 32 :=
  l.foldr
    (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
      let (en_d, ad_d, da_d) := Hw.retireMemFor d
      let g := Expr.and (Hw.ifDomIs d) en_d
      (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
    ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))

private theorem domFold_en_zero (σ : Loom.Hw.St)
    (hben : ∀ mn ∈ moverMns, (Hw.isMn mn).eval σ ≠ 1#1) :
    ∀ (l : List DomainId), ((domFold l).1).eval σ = 0#1
  | [] => rfl
  | d :: t => by
      show ((Hw.ifDomIs d).eval σ &&& ((Hw.retireMemFor d).1).eval σ) |||
        ((domFold t).1).eval σ = 0#1
      rw [show Hw.retireMemFor d = enFold (Hw.opCircs d) from rfl]
      rw [memFold_en_zero σ hben (Hw.opCircs d) (memInert_opCircs d),
        bv1_and_zero', bv1_zero_or]
      exact domFold_en_zero σ hben t

/-- The muxed port-0 commit is disabled on a benign retiring cycle. -/
theorem retireMem_en_zero (σ : Loom.Hw.St)
    (hben : ∀ mn ∈ moverMns, (Hw.isMn mn).eval σ ≠ 1#1) :
    (((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))).1).eval σ
      = 0#1 :=
  domFold_en_zero σ hben (List.finRange numDomains)

/-- On a benign retiring cycle the core writes no memory. -/
theorem coreAct_mems_benign (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hben : ∀ mn ∈ moverMns, (Hw.isMn mn).eval σ ≠ 1#1)
    (ad w : Nat) :
    ((Hw.coreAct m).run σ acc).mems "mem" ad w = acc.mems "mem" ad w := by
  rw [coreAct_run_retire_eq m σ acc hifv hcl,
    retireAct_run_mems σ acc ad w]
  have hen := retireMem_en_zero σ hben
  show (if _ = 1#1 then _ else acc).mems "mem" ad w = _
  rw [if_neg (by rw [hen]; decide)]

/-! ## The shared square assembly -/

/-- **The benign-retirement square glue.** Instantiated per op with the
selected circuit (`hcoreR` via the dispatch skeleton) and the spec's
post-core state `τ2` (via `corePhase_retire`/`retire_of_decode_some` and
the op's exec unfolding). -/
theorem square_retire_benign (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hben : ∀ mn ∈ moverMns, (Hw.isMn mn).eval σ ≠ 1#1)
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
    (hcaps : ∀ x, (τ2.doms x).caps = ((Hw.abs σ).doms x).caps)
    (hgen : ∀ x, (τ2.doms x).slotGen = ((Hw.abs σ).doms x).slotGen)
    (hrgn : ∀ x, (τ2.doms x).regions = ((Hw.abs σ).doms x).regions)
    (hjob : τ2.mover = Hw.absMover σ)
    (hτm : ∀ b : Addr, τ2.mem b = σ.mems "mem" b.toNat 32)
    (hcyc : τ2.cycle = σ.regs "cycle" 32)
    (hτ2if : τ2.inflight = none) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hin : Inert σ := Inert.of_benign σ hben
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  -- memory: the core is silent on the port
  have hmem2 : ∀ ad, ((Hw.coreAct m).run σ σ1).mems "mem" ad 32
      = σ.mems "mem" ad 32 := by
    intro ad
    rw [coreAct_mems_benign m σ σ1 hifv hcl hben, hσ1]
    exact Loom.Hw.Compile.run_mems_notin "mem" _
      (by rw [refillAct_memWrites]; simp) σ σ ad 32
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
    exact moverAct_mem_quiescent σ _ τ2 hin
      (fun x => (hspec ▸ hcaps x : _)) (fun x => hspec ▸ hgen x)
      (fun x => hspec ▸ hrgn x) (hspec ▸ hjob)
      (by
        intro d sc
        exact andAll_zero_of_mem σ
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_self ..)))
          (hben "sw" (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))
      hmem2 hτm a
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
    exact absMover_moverAct_quiescent σ _ τ2 hin hcaps hgen hjob
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

/-! ## Port-0 commit selection for a retiring `sw` -/

private theorem bv1_one_and (x : BitVec 1) : 1#1 &&& x = x := by
  revert x; decide

/-- The op-level fold with an open accumulator. -/
private def enFoldR (l : List (String × Hw.OpCirc))
    (rest : Expr 1 × Expr 12 × Expr 32) : Expr 1 × Expr 12 × Expr 32 :=
  l.foldr
    (fun (p : String × Hw.OpCirc) (acc : Expr 1 × Expr 12 × Expr 32) =>
      let g := Expr.and (Hw.isMn p.1) p.2.memEn
      (.or g acc.1, .mux g p.2.memAddr acc.2.1, .mux g p.2.memData acc.2.2))
    rest

private theorem enFoldR_eq (l : List (String × Hw.OpCirc)) :
    enFold l = enFoldR l (.lit 0, .lit 0, .lit 0) := rfl

/-- The cross-domain fold with an open accumulator. -/
private def domFoldR (l : List DomainId)
    (rest : Expr 1 × Expr 12 × Expr 32) : Expr 1 × Expr 12 × Expr 32 :=
  l.foldr
    (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
      let (en_d, ad_d, da_d) := Hw.retireMemFor d
      let g := Expr.and (Hw.ifDomIs d) en_d
      (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
    rest

/-- The op-level fold skips a run of quiet entries. -/
private theorem enFoldR_skip (σ : Loom.Hw.St) :
    ∀ (l : List (String × Hw.OpCirc)) (rest : Expr 1 × Expr 12 × Expr 32),
      (∀ p ∈ l, (Hw.isMn p.1).eval σ = 0#1 ∨ isLit0 p.2.memEn = true) →
      (((enFoldR l rest).1).eval σ = (rest.1).eval σ)
      ∧ (((enFoldR l rest).2.1).eval σ = (rest.2.1).eval σ)
      ∧ (((enFoldR l rest).2.2).eval σ = (rest.2.2).eval σ)
  | [], _, _ => ⟨rfl, rfl, rfl⟩
  | p :: t, rest, hq => by
      have hg : (Expr.and (Hw.isMn p.1) p.2.memEn).eval σ = 0#1 := by
        rcases hq p (List.mem_cons_self ..) with h | h
        · show (Hw.isMn p.1).eval σ &&& p.2.memEn.eval σ = 0#1
          rw [h]
          exact bv1_zero_and' _
        · show (Hw.isMn p.1).eval σ &&& p.2.memEn.eval σ = 0#1
          rw [isLit0_eval σ _ h]
          exact bv1_and_zero' _
      obtain ⟨ih1, ih2, ih3⟩ := enFoldR_skip σ t rest
        (fun q hq' => hq q (List.mem_cons_of_mem _ hq'))
      refine ⟨?_, ?_, ?_⟩
      · show (Expr.and (Hw.isMn p.1) p.2.memEn).eval σ
          ||| ((enFoldR t rest).1).eval σ = _
        rw [hg, bv1_zero_or, ih1]
      · show (if (Expr.and (Hw.isMn p.1) p.2.memEn).eval σ = 1#1
          then p.2.memAddr.eval σ else ((enFoldR t rest).2.1).eval σ) = _
        rw [if_neg (by rw [hg]; decide), ih2]
      · show (if (Expr.and (Hw.isMn p.1) p.2.memEn).eval σ = 1#1
          then p.2.memData.eval σ else ((enFoldR t rest).2.2).eval σ) = _
        rw [if_neg (by rw [hg]; decide), ih3]

/-- The op-level fold selects the (unique) `sw` circuit. -/
private theorem enFoldR_sw (σ : Loom.Hw.St) (c : Hw.OpCirc)
    (hsel1 : (Hw.isMn "sw").eval σ = 1#1) :
    ∀ (l : List (String × Hw.OpCirc)) (rest : Expr 1 × Expr 12 × Expr 32),
      ("sw", c) ∈ l →
      ((l.map Prod.fst).Nodup) →
      (∀ p ∈ l, p.1 ≠ "sw" →
        (Hw.isMn p.1).eval σ = 0#1 ∨ isLit0 p.2.memEn = true) →
      ((rest.1).eval σ = 0#1) →
      (((enFoldR l rest).1).eval σ = (c.memEn).eval σ)
      ∧ ((c.memEn).eval σ = 1#1 →
          ((enFoldR l rest).2.1).eval σ = (c.memAddr).eval σ
          ∧ ((enFoldR l rest).2.2).eval σ = (c.memData).eval σ)
  | [], _, hmem, _, _, _ => absurd hmem (List.not_mem_nil)
  | (mn', c') :: t, rest, hmem, hnd, hq, hr0 => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hsw : mn' = "sw"
      · subst hsw
        have hc' : c' = c := by
          rcases List.mem_cons.mp hmem with heq | hmt
          · cases heq
            rfl
          · exact absurd (List.mem_map_of_mem hmt : ("sw" : String) ∈ _)
              hnd.1
        subst hc'
        have htq : ∀ p ∈ t, (Hw.isMn p.1).eval σ = 0#1
            ∨ isLit0 p.2.memEn = true := by
          intro p hp
          by_cases hps : p.1 = "sw"
          · exact absurd (hps ▸ (List.mem_map_of_mem hp : p.1 ∈ _)) hnd.1
          · exact hq p (List.mem_cons_of_mem _ hp) hps
        obtain ⟨ht1, ht2, ht3⟩ := enFoldR_skip σ t rest htq
        have hg : (Expr.and (Hw.isMn "sw") c'.memEn).eval σ
            = c'.memEn.eval σ := by
          show (Hw.isMn "sw").eval σ &&& c'.memEn.eval σ = _
          rw [hsel1]
          exact bv1_one_and _
        refine ⟨?_, fun hen => ⟨?_, ?_⟩⟩
        · show (Expr.and (Hw.isMn "sw") c'.memEn).eval σ
            ||| ((enFoldR t rest).1).eval σ = _
          rw [hg, ht1, hr0]
          generalize c'.memEn.eval σ = b
          revert b; decide
        · show (if (Expr.and (Hw.isMn "sw") c'.memEn).eval σ = 1#1
            then c'.memAddr.eval σ else ((enFoldR t rest).2.1).eval σ) = _
          rw [if_pos (by rw [hg]; exact hen)]
        · show (if (Expr.and (Hw.isMn "sw") c'.memEn).eval σ = 1#1
            then c'.memData.eval σ else ((enFoldR t rest).2.2).eval σ) = _
          rw [if_pos (by rw [hg]; exact hen)]
      · have hg : (Expr.and (Hw.isMn mn') c'.memEn).eval σ = 0#1 := by
          rcases hq (mn', c') (List.mem_cons_self ..) hsw with h | h
          · show (Hw.isMn mn').eval σ &&& c'.memEn.eval σ = 0#1
            rw [h]
            exact bv1_zero_and' _
          · show (Hw.isMn mn').eval σ &&& c'.memEn.eval σ = 0#1
            rw [isLit0_eval σ _ h]
            exact bv1_and_zero' _
        have hmem' : ("sw", c) ∈ t := by
          rcases List.mem_cons.mp hmem with heq | h
          · exact absurd (congrArg Prod.fst heq).symm hsw
          · exact h
        obtain ⟨ih1, ih2⟩ := enFoldR_sw σ c hsel1 t rest hmem' hnd.2
          (fun p hp => hq p (List.mem_cons_of_mem _ hp)) hr0
        refine ⟨?_, fun hen => ⟨?_, ?_⟩⟩
        · show (Expr.and (Hw.isMn mn') c'.memEn).eval σ
            ||| ((enFoldR t rest).1).eval σ = _
          rw [hg, bv1_zero_or, ih1]
        · show (if (Expr.and (Hw.isMn mn') c'.memEn).eval σ = 1#1
            then c'.memAddr.eval σ else ((enFoldR t rest).2.1).eval σ) = _
          rw [if_neg (by rw [hg]; decide)]
          exact (ih2 hen).1
        · show (if (Expr.and (Hw.isMn mn') c'.memEn).eval σ = 1#1
            then c'.memData.eval σ else ((enFoldR t rest).2.2).eval σ) = _
          rw [if_neg (by rw [hg]; decide)]
          exact (ih2 hen).2

/-- The cross-domain fold skips non-owning domains. -/
private theorem domFoldR_skip (σ : Loom.Hw.St) (E : DomainId)
    (hexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1) :
    ∀ (l : List DomainId) (rest : Expr 1 × Expr 12 × Expr 32),
      (∀ d ∈ l, d ≠ E) →
      (((domFoldR l rest).1).eval σ = (rest.1).eval σ)
      ∧ (((domFoldR l rest).2.1).eval σ = (rest.2.1).eval σ)
      ∧ (((domFoldR l rest).2.2).eval σ = (rest.2.2).eval σ)
  | [], _, _ => ⟨rfl, rfl, rfl⟩
  | d :: t, rest, hne => by
      have hg : (Expr.and (Hw.ifDomIs d) (Hw.retireMemFor d).1).eval σ
          = 0#1 := by
        show (Hw.ifDomIs d).eval σ &&& _ = 0#1
        rw [bv1_ne_one.mp (hexcl d (hne d (List.mem_cons_self ..)))]
        exact bv1_zero_and' _
      obtain ⟨ih1, ih2, ih3⟩ := domFoldR_skip σ E hexcl t rest
        (fun d' hd' => hne d' (List.mem_cons_of_mem _ hd'))
      refine ⟨?_, ?_, ?_⟩
      · show (Expr.and (Hw.ifDomIs d) (Hw.retireMemFor d).1).eval σ
          ||| ((domFoldR t rest).1).eval σ = _
        rw [hg, bv1_zero_or, ih1]
      · show (if (Expr.and (Hw.ifDomIs d) (Hw.retireMemFor d).1).eval σ = 1#1
          then ((Hw.retireMemFor d).2.1).eval σ
          else ((domFoldR t rest).2.1).eval σ) = _
        rw [if_neg (by rw [hg]; decide), ih2]
      · show (if (Expr.and (Hw.ifDomIs d) (Hw.retireMemFor d).1).eval σ = 1#1
          then ((Hw.retireMemFor d).2.2).eval σ
          else ((domFoldR t rest).2.2).eval σ) = _
        rw [if_neg (by rw [hg]; decide), ih3]

/-- The cross-domain fold selects the owner. -/
private theorem domFoldR_sw (σ : Loom.Hw.St) (E : DomainId)
    (hsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1) :
    ∀ (l : List DomainId) (rest : Expr 1 × Expr 12 × Expr 32),
      E ∈ l → l.Nodup → ((rest.1).eval σ = 0#1) →
      (((domFoldR l rest).1).eval σ = ((Hw.retireMemFor E).1).eval σ)
      ∧ (((Hw.retireMemFor E).1).eval σ = 1#1 →
          ((domFoldR l rest).2.1).eval σ = ((Hw.retireMemFor E).2.1).eval σ
          ∧ ((domFoldR l rest).2.2).eval σ
            = ((Hw.retireMemFor E).2.2).eval σ)
  | [], _, hmem, _, _ => absurd hmem (List.not_mem_nil)
  | d :: t, rest, hmem, hnd, hr0 => by
      rw [List.nodup_cons] at hnd
      by_cases hd : d = E
      · subst hd
        have htne : ∀ d' ∈ t, d' ≠ d := fun d' hd' hc => hnd.1 (hc ▸ hd')
        obtain ⟨ht1, ht2, ht3⟩ := domFoldR_skip σ d hexcl t rest htne
        have hg : (Expr.and (Hw.ifDomIs d) (Hw.retireMemFor d).1).eval σ
            = ((Hw.retireMemFor d).1).eval σ := by
          show (Hw.ifDomIs d).eval σ &&& _ = _
          rw [hsel]
          exact bv1_one_and _
        refine ⟨?_, fun hen => ⟨?_, ?_⟩⟩
        · show (Expr.and (Hw.ifDomIs d) (Hw.retireMemFor d).1).eval σ
            ||| ((domFoldR t rest).1).eval σ = _
          rw [hg, ht1, hr0]
          generalize ((Hw.retireMemFor d).1).eval σ = b
          revert b; decide
        · show (if (Expr.and (Hw.ifDomIs d)
            (Hw.retireMemFor d).1).eval σ = 1#1
            then ((Hw.retireMemFor d).2.1).eval σ
            else ((domFoldR t rest).2.1).eval σ) = _
          rw [if_pos (by rw [hg]; exact hen)]
        · show (if (Expr.and (Hw.ifDomIs d)
            (Hw.retireMemFor d).1).eval σ = 1#1
            then ((Hw.retireMemFor d).2.2).eval σ
            else ((domFoldR t rest).2.2).eval σ) = _
          rw [if_pos (by rw [hg]; exact hen)]
      · have hg : (Expr.and (Hw.ifDomIs d) (Hw.retireMemFor d).1).eval σ
            = 0#1 := by
          show (Hw.ifDomIs d).eval σ &&& _ = 0#1
          rw [bv1_ne_one.mp (hexcl d hd)]
          exact bv1_zero_and' _
        have hmem' : E ∈ t := by
          rcases List.mem_cons.mp hmem with heq | h
          · exact absurd heq.symm hd
          · exact h
        obtain ⟨ih1, ih2⟩ := domFoldR_sw σ E hsel hexcl t rest hmem' hnd.2 hr0
        refine ⟨?_, fun hen => ⟨?_, ?_⟩⟩
        · show (Expr.and (Hw.ifDomIs d) (Hw.retireMemFor d).1).eval σ
            ||| ((domFoldR t rest).1).eval σ = _
          rw [hg, bv1_zero_or, ih1]
        · show (if (Expr.and (Hw.ifDomIs d)
            (Hw.retireMemFor d).1).eval σ = 1#1
            then ((Hw.retireMemFor d).2.1).eval σ
            else ((domFoldR t rest).2.1).eval σ) = _
          rw [if_neg (by rw [hg]; decide)]
          exact (ih2 hen).1
        · show (if (Expr.and (Hw.ifDomIs d)
            (Hw.retireMemFor d).1).eval σ = 1#1
            then ((Hw.retireMemFor d).2.2).eval σ
            else ((domFoldR t rest).2.2).eval σ) = _
          rw [if_neg (by rw [hg]; decide)]
          exact (ih2 hen).2

/-- **The retiring-`sw` commit**: the muxed port-0 triple evaluates to the
`sw` circuit's enable/address/data. Stated against `retireAct`'s literal
fold (the shape `retireAct_run_mems` exposes). -/
theorem retireMem_sw_sel (σ : Loom.Hw.St) (E : DomainId) (c : Hw.OpCirc)
    (hifsel : (Hw.ifDomIs E).eval σ = 1#1)
    (hifexcl : ∀ d : DomainId, d ≠ E → (Hw.ifDomIs d).eval σ ≠ 1#1)
    (hsel1 : (Hw.isMn "sw").eval σ = 1#1)
    (hmem : ("sw", c) ∈ Hw.opCircs E)
    (hnd : ((Hw.opCircs E).map Prod.fst).Nodup)
    (hq : ∀ p ∈ Hw.opCircs E, p.1 ≠ "sw" →
      (Hw.isMn p.1).eval σ = 0#1 ∨ isLit0 p.2.memEn = true) :
    ((((List.finRange numDomains).foldr
      (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
        let (en_d, ad_d, da_d) := Hw.retireMemFor d
        let g := Expr.and (Hw.ifDomIs d) en_d
        (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
      ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))).1).eval σ
      = (c.memEn).eval σ)
    ∧ ((c.memEn).eval σ = 1#1 →
        ((((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
            (.lit 0 : Expr 32))).2.1).eval σ = (c.memAddr).eval σ)
        ∧ ((((List.finRange numDomains).foldr
          (fun d (acc' : Expr 1 × Expr 12 × Expr 32) =>
            let (en_d, ad_d, da_d) := Hw.retireMemFor d
            let g := Expr.and (Hw.ifDomIs d) en_d
            (.or g acc'.1, .mux g ad_d acc'.2.1, .mux g da_d acc'.2.2))
          ((.lit 0 : Expr 1), (.lit 0 : Expr 12),
            (.lit 0 : Expr 32))).2.2).eval σ = (c.memData).eval σ)) := by
  obtain ⟨he1, he2⟩ := enFoldR_sw σ c hsel1 (Hw.opCircs E)
    (.lit 0, .lit 0, .lit 0) hmem hnd hq rfl
  obtain ⟨hd1, hd2⟩ := domFoldR_sw σ E hifsel hifexcl
    (List.finRange numDomains) (.lit 0, .lit 0, .lit 0)
    (List.mem_finRange E) (List.nodup_finRange _) rfl
  have hEn1 : ((Hw.retireMemFor E).1).eval σ = (c.memEn).eval σ := he1
  refine ⟨?_, fun hen => ⟨?_, ?_⟩⟩
  · show ((domFoldR (List.finRange numDomains)
      (.lit 0, .lit 0, .lit 0)).1).eval σ = _
    rw [hd1, hEn1]
  · show ((domFoldR (List.finRange numDomains)
      (.lit 0, .lit 0, .lit 0)).2.1).eval σ = _
    rw [(hd2 (by rw [hEn1]; exact hen)).1]
    exact (he2 hen).1
  · show ((domFoldR (List.finRange numDomains)
      (.lit 0, .lit 0, .lit 0)).2.2).eval σ = _
    rw [(hd2 (by rw [hEn1]; exact hen)).2]
    exact (he2 hen).2

end Machines.Lnp64u.Theorems.RMC

