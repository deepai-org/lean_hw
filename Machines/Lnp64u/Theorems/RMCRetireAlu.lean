-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireBase

/-!
# R-MC support: the `setReg`-shaped retirement arms

Nine of the base ops (`add sub and or xor shl shr addi lui`) retire as
`writeReg rd v; pc += 1` against a spec `exec` of `setReg rd V` — the
only per-op content is the datapath value equivalence `v.eval σ = V`
(the Stage-1 finding). `square_retire_setReg` proves the square once for
that shape; each op instantiates it with its value expression, spec
value, and three kernel-checked opcode facts.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 3200000
set_option maxRecDepth 200000

/-! ## The dispatch table's mnemonic spine -/

/-- All 25 mnemonics, in `opCircs` order. -/
def allMns : List String :=
  ["add", "sub", "and", "or", "xor", "shl", "shr", "addi", "lui", "lw",
   "sw", "beq", "blt", "jalr", "cap_dup", "cap_drop", "cap_revoke",
   "mem_grant", "map", "unmap", "gate_call", "gate_return", "move",
   "yield", "halt"]

theorem opCircs_fst_all : ∀ e : DomainId,
    (Hw.opCircs e).map Prod.fst = allMns := by
  intro e
  fin_cases e <;> rfl

theorem allMns_nodup : allMns.Nodup := by decide

/-- First-match uniqueness from a duplicate-free mnemonic spine. -/
theorem huniq_of_nodup {l : List (String × Hw.OpCirc)} {mn : String}
    {c : Hw.OpCirc} (hnd : (l.map Prod.fst).Nodup) (hmem : (mn, c) ∈ l) :
    ∀ p ∈ l, p.1 = mn → p.2 = c := by
  induction l with
  | nil => exact fun p hp => absurd hp (List.not_mem_nil)
  | cons q t ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      intro p hp hpe
      rcases List.mem_cons.mp hp with rfl | hpt
      · rcases List.mem_cons.mp hmem with heq | hmt
        · cases heq
          rfl
        · exact absurd (hpe ▸ (List.mem_map_of_mem hmt : mn ∈ _)) hnd.1
      · rcases List.mem_cons.mp hmem with heq | hmt
        · cases heq
          exact absurd (hpe ▸ (List.mem_map_of_mem hpt : p.1 ∈ _)) hnd.1
        · exact ih hnd.2 hmt p hpt hpe

/-! ## Write-set disjointness (kernel walks; the value exprs stay opaque) -/

/-- The non-`regs`/`pc` register names `absDom · x` reads. -/
def domQuietNames (x : DomainId) : List (String × Nat) :=
  ((List.finRange numSlots).flatMap fun s =>
      [(Hw.dcapV x s, 1), (Hw.dcapKind x s, 32), (Hw.dcapLinV x s, 1),
       (Hw.dcapLin x s, 4), (Hw.dgen x s, 8)])
  ++ ((List.finRange numLineage).flatMap fun l =>
      [(Hw.dcellV x l, 1), (Hw.dcellPar x l, 14)])
  ++ ((List.finRange numRegions).flatMap fun r =>
      [(Hw.drgnV x r, 1), (Hw.drgn x r, 42)])
  ++ [(Hw.drun x, 2), (Hw.drunG x, 2), (Hw.dsrvV x, 1), (Hw.dsrv x, 2),
      (Hw.dcause x, 32), (Hw.dbudget x, 32), (Hw.dmaxdon x, 32)]

/-- The `setReg`-shaped payload with the cleared latch in front. -/
def aluFull (e : DomainId) (v : Expr 32) : Act :=
  .seq (.write 1 "if_v" (.lit 0))
    (.seq (Hw.writeReg e Hw.rdE v) (Hw.pcAdvA e))

/-- The write set of the payload, value-free (the shape the kernel can
walk with the value expression opaque). -/
private theorem aluX_writes (e : DomainId) (v : Expr 32) :
    (Act.seq (Hw.writeReg e Hw.rdE v) (Hw.pcAdvA e)).regWrites
      = [(Hw.dreg e 1, 32), (Hw.dreg e 2, 32), (Hw.dreg e 3, 32),
         (Hw.dreg e 4, 32), (Hw.dreg e 5, 32), (Hw.dreg e 6, 32),
         (Hw.dreg e 7, 32), (Hw.dpc e, 12)] := rfl

private theorem aluFull_writes (e : DomainId) (v : Expr 32) :
    (aluFull e v).regWrites
      = [("if_v", 1), (Hw.dreg e 1, 32), (Hw.dreg e 2, 32),
         (Hw.dreg e 3, 32), (Hw.dreg e 4, 32), (Hw.dreg e 5, 32),
         (Hw.dreg e 6, 32), (Hw.dreg e 7, 32), (Hw.dpc e, 12)] := rfl

private theorem quiet_notin_alu (x e : DomainId) (v : Expr 32) :
    ∀ q ∈ domQuietNames x, q ∉ (aluFull e v).regWrites := by
  rw [aluFull_writes]
  fin_cases x <;> fin_cases e <;> decide +kernel

private theorem read_notin_alu_ne (x e : DomainId) (hne : x ≠ e)
    (v : Expr 32) :
    ∀ q ∈ domReadNames x, q ∉ (aluFull e v).regWrites := by
  rw [aluFull_writes]
  fin_cases x <;> fin_cases e <;>
    first
      | exact absurd rfl hne
      | decide +kernel

private theorem gate_notin_alu (g : GateId) (e : DomainId) (v : Expr 32) :
    ∀ q ∈ gateReadNames g, q ∉ (aluFull e v).regWrites := by
  rw [aluFull_writes]
  fin_cases g <;> fin_cases e <;> decide +kernel

private theorem ifv_notin_aluX (e : DomainId) (v : Expr 32) :
    ("if_v", 1) ∉ (Act.seq (Hw.writeReg e Hw.rdE v) (Hw.pcAdvA e)).regWrites
    := by
  rw [aluX_writes]
  fin_cases e <;> decide +kernel

/-- `dreg` names are injective in the register index. -/
theorem dreg_inj : ∀ (e : DomainId) (r r' : RegId),
    Hw.dreg e r = Hw.dreg e r' → r = r' := by decide +kernel

/-- The refill rule never writes the architectural file or `pc`. -/
private theorem dreg_notin_refill : ∀ (e : DomainId) (r : RegId),
    ((Hw.dreg e r : String), (32 : Nat)) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat)) := by
  decide +kernel

/-! ## Spec-side field helpers -/

theorem setReg_caps (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).caps = ds.caps := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_slotGen (ds : DomainState) (r : RegId)
    (v : Loom.Word32) : (ds.setReg r v).slotGen = ds.slotGen := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_lineage (ds : DomainState) (r : RegId)
    (v : Loom.Word32) : (ds.setReg r v).lineage = ds.lineage := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_regions (ds : DomainState) (r : RegId)
    (v : Loom.Word32) : (ds.setReg r v).regions = ds.regions := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_run (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).run = ds.run := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_serving (ds : DomainState) (r : RegId)
    (v : Loom.Word32) : (ds.setReg r v).serving = ds.serving := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_cause (ds : DomainState) (r : RegId)
    (v : Loom.Word32) : (ds.setReg r v).cause = ds.cause := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_budget (ds : DomainState) (r : RegId)
    (v : Loom.Word32) : (ds.setReg r v).budget = ds.budget := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_maxDonation (ds : DomainState) (r : RegId)
    (v : Loom.Word32) : (ds.setReg r v).maxDonation = ds.maxDonation := by
  unfold DomainState.setReg; split <;> rfl

theorem setReg_pc (ds : DomainState) (r : RegId) (v : Loom.Word32) :
    (ds.setReg r v).pc = ds.pc := by
  unfold DomainState.setReg; split <;> rfl

/-- The updated register file of `setReg` (architectural: `r0` discards). -/
theorem setReg_regs (ds : DomainState) (r : RegId) (v : Loom.Word32)
    (r' : RegId) :
    (ds.setReg r v).regs r'
      = if r = (0 : Fin numRegs) then ds.regs r'
        else if r' = r then v else ds.regs r' := by
  unfold DomainState.setReg
  split
  · rfl
  · show (Loom.Fun.update ds.regs r v) r' = _
    unfold Loom.Fun.update
    split <;> rfl

/-- The quiet-field face of `absDom`: if only the file/`pc` registers of
`e` (and unrelated names) changed, `absDom` is the old record with the
new file and `pc`. -/
theorem absDom_regpc {S1 S2 : Loom.Hw.St} (e : DomainId)
    (hq : ∀ q ∈ domQuietNames e, S2.regs q.1 q.2 = S1.regs q.1 q.2) :
    Hw.absDom S2 e =
      { Hw.absDom S1 e with
        regs := fun r => S2.regs (Hw.dreg e r) 32
        pc := S2.regs (Hw.dpc e) 12 } := by
  have hs : ∀ (s : Slot) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.dcapV e s, 1), (Hw.dcapKind e s, 32),
        (Hw.dcapLinV e s, 1), (Hw.dcapLin e s, 4), (Hw.dgen e s, 8)] →
      S2.regs rn w = S1.regs rn w := fun s rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨s, List.mem_finRange s, hp⟩))))
  have hl : ∀ (l : Fin numLineage) (rn : String) (w : Nat),
      (rn, w) ∈ [(Hw.dcellV e l, 1), (Hw.dcellPar e l, 14)] →
      S2.regs rn w = S1.regs rn w := fun l rn w hp =>
    hq (rn, w) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨l, List.mem_finRange l, hp⟩))))
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
  · show (S2.regs (Hw.dmaxdon e) 32).toNat = (S1.regs (Hw.dmaxdon e) 32).toNat
    rw [ht (Hw.dmaxdon e) 32 (by simp)]

/-- The refill rule never writes any domain's `pc`. -/
private theorem dpc_notin_refill : ∀ (e : DomainId),
    ((Hw.dpc e : String), (12 : Nat)) ∉
      ([("d0_budget", 32), ("d0_rctr", 32), ("d1_budget", 32),
        ("d1_rctr", 32), ("d2_budget", 32), ("d2_rctr", 32),
        ("d3_budget", 32), ("d3_rctr", 32)] : List (String × Nat)) := by
  decide +kernel

set_option maxHeartbeats 6400000 in
/-- **The `setReg`-shaped retirement square.** One hardware cycle retiring
a benign `writeReg rd v; pc += 1` op is exactly one spec step retiring
`setReg rd V` — given the datapath value equivalence `v.eval σ = V` and
the op's kernel-checked opcode facts. -/
theorem square_retire_setReg (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (mn : String) (k : BitVec 6)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = k)
    (hkmn : Hw.opcodeOf mn = k)
    (hbenk : ∀ mn' ∈ moverMns, k ≠ Hw.opcodeOf mn')
    (hexk : ∀ mn' ∈ allMns, mn' ≠ mn → k ≠ Hw.opcodeOf mn')
    (E : DomainId) (hE : E.val = (σ.regs "if_dom" 2).toNat)
    (vE : Expr 32) (V : Loom.Word32)
    (hmem : (mn, (⟨Act.seq (Hw.writeReg E Hw.rdE vE) (Hw.pcAdvA E),
      .lit 0, .lit 0, .lit 0⟩ : Hw.OpCirc)) ∈ Hw.opCircs E)
    (hv : vE.eval σ = V)
    (hretire :
      retire { refillPhase m (Hw.abs σ) with inflight := none } E
          (σ.regs "if_word" 32)
        = (({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
            (fun ds => { ds with pc := ds.pc + 1 })).setDom E
            (fun ds =>
              ds.setReg (operandsOf (σ.regs "if_word" 32)).rd V)) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hben : ∀ mn' ∈ moverMns, (Hw.isMn mn').eval σ ≠ 1#1 :=
    fun mn' hmn' => isMn_ne_of_opc σ mn' k hopc (hbenk mn' hmn')
  set W := σ.regs "if_word" 32 with hWdef
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  set rd := (operandsOf W).rd with hrddef
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  have habs1 : Hw.abs σ1 = τ1 := abs_refill m hwf hfit σ hsync
  -- dispatch selection
  have hsel : (Hw.isMn mn).eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact hkmn.symm
  have hexcl : ∀ p ∈ Hw.opCircs E, p.1 ≠ mn →
      (Hw.isMn p.1).eval σ ≠ 1#1 := by
    intro p hp hne
    have hmns : p.1 ∈ allMns := by
      rw [← opCircs_fst_all E]
      exact List.mem_map_of_mem hp
    exact isMn_ne_of_opc σ p.1 k hopc (hexk p.1 hmns hne)
  have hnd : ((Hw.opCircs E).map Prod.fst).Nodup := by
    rw [opCircs_fst_all E]
    exact allMns_nodup
  have huniq := huniq_of_nodup hnd hmem
  have hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ σ1).regs rn w
        = ((aluFull E vE).run σ σ1).regs rn w := by
    intro rn w
    rw [coreAct_run_retire_eq m σ σ1 hifv hcl,
        retireAct_run_regs σ σ1 E hE rn w,
        retireFor_run_sel σ _ E mn _ hmem hsel hexcl huniq]
    rfl
  -- the spec retirement
  have hfl : τ1.inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have hdomE : (finOfBv (by decide : 2 ^ 2 = numDomains)
      (σ.regs "if_dom" 2)) = E :=
    Fin.ext hE.symm
  have hspec : corePhase m τ1
      = (({ τ1 with inflight := none }).setDom E
          (fun ds => { ds with pc := ds.pc + 1 })).setDom E
          (fun ds => ds.setReg rd V) := by
    rw [corePhase_retire m τ1 _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
    show retire { τ1 with inflight := none }
      (finOfBv (by decide) (σ.regs "if_dom" 2)) W = _
    rw [hdomE]
    exact hretire
  set DS1 : DomainState :=
    { τ1.doms E with pc := (τ1.doms E).pc + 1 } with hDS1
  have hτ2E : ((({ τ1 with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })).setDom E
      (fun ds => ds.setReg rd V)).doms E = DS1.setReg rd V := by
    show (Loom.Fun.update (Loom.Fun.update τ1.doms E DS1) E
      (DomainState.setReg ((Loom.Fun.update τ1.doms E DS1) E) rd V)) E
      = DS1.setReg rd V
    rw [Loom.Fun.update_same, Loom.Fun.update_same]
  have hτ2x : ∀ x, x ≠ E → ((({ τ1 with inflight := none }).setDom E
      (fun ds => { ds with pc := ds.pc + 1 })).setDom E
      (fun ds => ds.setReg rd V)).doms x = τ1.doms x := by
    intro x hx
    show (Loom.Fun.update (Loom.Fun.update τ1.doms E DS1) E
      (DomainState.setReg ((Loom.Fun.update τ1.doms E DS1) E) rd V)) x
      = τ1.doms x
    rw [Loom.Fun.update_ne _ _ _ _ hx, Loom.Fun.update_ne _ _ _ _ hx]
  have hL1 : ∀ x, τ1.doms x = Hw.absDom σ1 x := by
    intro x
    rw [← habs1]
    rfl
  -- the operand index reads the latched word's field
  have hrdval : rd.val = (Hw.rdE.eval σ).toNat := rfl
  -- assemble through the shared glue
  refine square_retire_benign m hwf hfit σ hsync hifv hcl hben
    (Act.seq (Hw.writeReg E Hw.rdE vE) (Hw.pcAdvA E)) _
    hcoreR (ifv_notin_aluX E vE) hspec ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- absDom faces
    intro x
    by_cases hx : x = E
    · subst hx
      rw [hτ2E]
      have hq : ∀ q ∈ domQuietNames x,
          ((aluFull x vE).run σ σ1).regs q.1 q.2 = σ1.regs q.1 q.2 :=
        fun q hq' => frame (quiet_notin_alu x x vE q hq') σ σ1
      rw [show ((Act.seq (.write 1 "if_v" (.lit 0))
          (Act.seq (Hw.writeReg x Hw.rdE vE) (Hw.pcAdvA x))).run σ σ1)
        = (aluFull x vE).run σ σ1 from rfl]
      rw [absDom_regpc x hq]
      have hifvframe : ∀ (rn : String) (w : Nat), w ≠ 1 →
          ((Act.write 1 "if_v" (.lit 0)).run σ σ1).regs rn w
            = σ1.regs rn w := by
        intro rn w hw
        exact frame (by
          intro hm
          simp only [Act.regWrites, List.mem_singleton, Prod.mk.injEq] at hm
          exact hw hm.2) σ σ1
      apply domainState_ext'
      · -- the register file
        funext r
        show ((aluFull x vE).run σ σ1).regs (Hw.dreg x r) 32
          = (DS1.setReg rd V).regs r
        rw [setReg_regs]
        have hpcframe :
            ((aluFull x vE).run σ σ1).regs (Hw.dreg x r) 32
              = ((Hw.writeReg x Hw.rdE vE).run σ
                  ((Act.write 1 "if_v" (.lit 0)).run σ σ1)).regs
                  (Hw.dreg x r) 32 :=
          frame (show (Hw.dreg x r, 32) ∉ (Hw.pcAdvA x).regWrites from by
            intro hm
            simp only [Hw.pcAdvA, Act.regWrites, List.mem_singleton,
              Prod.mk.injEq] at hm
            exact absurd hm.2 (by decide)) σ _
        rw [hpcframe]
        by_cases h0 : rd = (0 : Fin numRegs)
        · rw [if_pos h0]
          rw [writeReg_run_of_zero σ _ x Hw.rdE vE
            (by rw [← hrdval, h0]; rfl)]
          rw [hifvframe _ 32 (by decide)]
          show σ1.regs (Hw.dreg x r) 32 = (τ1.doms x).regs r
          rw [hL1 x]
          rfl
        · rw [if_neg h0]
          rw [writeReg_run_of_nz σ _ x Hw.rdE vE rd hrdval
            (fun hc => h0 (Fin.ext hc))]
          show (RegEnv.set _ (Hw.dreg x rd) (vE.eval σ)) (Hw.dreg x r) 32
            = _
          simp only [RegEnv.set]
          by_cases hr : r = rd
          · rw [if_pos (by rw [hr]), if_pos hr]
            rw [dif_pos trivial]
            exact hv
          · rw [if_neg (fun hc => hr (dreg_inj x r rd hc)), if_neg hr]
            rw [hifvframe _ 32 (by decide)]
            show σ1.regs (Hw.dreg x r) 32 = (τ1.doms x).regs r
            rw [hL1 x]
            rfl
      · -- pc
        show ((aluFull x vE).run σ σ1).regs (Hw.dpc x) 12
          = (DS1.setReg rd V).pc
        rw [setReg_pc]
        rw [show ((aluFull x vE).run σ σ1).regs (Hw.dpc x) 12
            = σ.regs (Hw.dpc x) 12 + 1 from by
          show (RegEnv.set _ (Hw.dpc x)
            ((Expr.add (Hw.rPc x) (.lit 1)).eval σ)) (Hw.dpc x) 12 = _
          simp [RegEnv.set, Expr.eval, Hw.rPc]]
        show σ.regs (Hw.dpc x) 12 + 1 = (τ1.doms x).pc + 1
        rw [hL1 x]
        show σ.regs (Hw.dpc x) 12 + 1 = σ1.regs (Hw.dpc x) 12 + 1
        rw [hσ1, refill_pres m σ (dpc_notin_refill x)]
      · show (Hw.absDom σ1 x).caps = (DS1.setReg rd V).caps
        rw [setReg_caps]
        show (Hw.absDom σ1 x).caps = (τ1.doms x).caps
        rw [hL1 x]
      · show (Hw.absDom σ1 x).slotGen = (DS1.setReg rd V).slotGen
        rw [setReg_slotGen]
        show (Hw.absDom σ1 x).slotGen = (τ1.doms x).slotGen
        rw [hL1 x]
      · show (Hw.absDom σ1 x).lineage = (DS1.setReg rd V).lineage
        rw [setReg_lineage]
        show (Hw.absDom σ1 x).lineage = (τ1.doms x).lineage
        rw [hL1 x]
      · show (Hw.absDom σ1 x).regions = (DS1.setReg rd V).regions
        rw [setReg_regions]
        show (Hw.absDom σ1 x).regions = (τ1.doms x).regions
        rw [hL1 x]
      · show (Hw.absDom σ1 x).run = (DS1.setReg rd V).run
        rw [setReg_run]
        show (Hw.absDom σ1 x).run = (τ1.doms x).run
        rw [hL1 x]
      · show (Hw.absDom σ1 x).serving = (DS1.setReg rd V).serving
        rw [setReg_serving]
        show (Hw.absDom σ1 x).serving = (τ1.doms x).serving
        rw [hL1 x]
      · show (Hw.absDom σ1 x).cause = (DS1.setReg rd V).cause
        rw [setReg_cause]
        show (Hw.absDom σ1 x).cause = (τ1.doms x).cause
        rw [hL1 x]
      · show (Hw.absDom σ1 x).budget = (DS1.setReg rd V).budget
        rw [setReg_budget]
        show (Hw.absDom σ1 x).budget = (τ1.doms x).budget
        rw [hL1 x]
      · show (Hw.absDom σ1 x).maxDonation = (DS1.setReg rd V).maxDonation
        rw [setReg_maxDonation]
        show (Hw.absDom σ1 x).maxDonation = (τ1.doms x).maxDonation
        rw [hL1 x]
    · rw [hτ2x x hx, hL1 x]
      exact absDom_congr x (fun p hp =>
        frame (read_notin_alu_ne x E hx vE p hp) σ σ1)
  · -- absGate faces
    intro g
    have hg : Hw.absGate ((aluFull E vE).run σ σ1) g = Hw.absGate σ1 g :=
      absGate_congr g (fun p hp => frame (gate_notin_alu g E vE p hp) σ σ1)
    rw [show ((Act.seq (.write 1 "if_v" (.lit 0))
        (Act.seq (Hw.writeReg E Hw.rdE vE) (Hw.pcAdvA E))).run σ σ1)
      = (aluFull E vE).run σ σ1 from rfl]
    rw [hg]
    show Hw.absGate σ1 g = τ1.gates g
    rw [← habs1]
    rfl
  · -- caps preserved
    intro x
    by_cases hx : x = E
    · subst hx
      rw [hτ2E, setReg_caps]
      show (τ1.doms x).caps = _
      rw [hτ1, refillPhase_caps]
    · rw [hτ2x x hx, hτ1, refillPhase_caps]
  · -- slotGen preserved
    intro x
    by_cases hx : x = E
    · subst hx
      rw [hτ2E, setReg_slotGen]
      show (τ1.doms x).slotGen = _
      rw [hτ1, refillPhase_slotGen]
    · rw [hτ2x x hx, hτ1, refillPhase_slotGen]
  · -- regions preserved
    intro x
    by_cases hx : x = E
    · subst hx
      rw [hτ2E, setReg_regions]
      show (τ1.doms x).regions = _
      rw [hτ1, refillPhase_regions]
    · rw [hτ2x x hx, hτ1, refillPhase_regions]
  · -- mover job preserved
    show τ1.mover = _
    rw [hτ1, refillPhase_mover]
    rfl
  · -- memory preserved
    intro b
    show τ1.mem b = _
    rw [hτ1]
    rfl
  · -- cycle preserved
    show τ1.cycle = _
    rw [hτ1]
    rfl
  · -- latch cleared
    rfl

/-! ## Per-op instantiation support -/

/-- The post-refill, post-`pc`-advance architectural read is the
pre-cycle abstraction's (refill and the `pc` bump touch neither the
file nor `r0`). -/
theorem specReg_bridge (m : Manifest) (σ : Loom.Hw.St) (E : DomainId)
    (rs : RegId) :
    ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg rs
      = ((Hw.abs σ).doms E).reg rs := by
  show ((Loom.Fun.update (refillPhase m (Hw.abs σ)).doms E _) E).reg rs = _
  rw [Loom.Fun.update_same]
  unfold DomainState.reg
  by_cases h : rs = (0 : Fin numRegs)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact congrFun (refillPhase_dregs m (Hw.abs σ) E) rs

/-- The `add` arm: opcode 0 retires `rd := rs1 + rs2`. -/
theorem square_retire_add (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 0#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (0#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (0#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "add" 0#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.add (Hw.readReg E Hw.rs1E) (Hw.readReg E Hw.rs2E))
    (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs1
      + ((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs2)
    (List.mem_append_left _ (List.mem_cons_self ..))
    ?_ ?_
  · -- datapath value equivalence
    show (Hw.readReg E Hw.rs1E).eval σ + (Hw.readReg E Hw.rs2E).eval σ = _
    rw [readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl,
        readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl,
        specReg_bridge, specReg_bridge]
  · -- spec exec reduction
    rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl


/-- The `sub` arm: opcode 1. -/
theorem square_retire_sub (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 1#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (1#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (1#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "sub" 1#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.sub (Hw.readReg E Hw.rs1E) (Hw.readReg E Hw.rs2E))
    ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs1)
      - (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs2))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    ?_ ?_
  · show (Hw.readReg E Hw.rs1E).eval σ - (Hw.readReg E Hw.rs2E).eval σ = _
    rw [readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl,
        readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl,
        specReg_bridge, specReg_bridge]
  · rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl

/-- The `and` arm: opcode 2. -/
theorem square_retire_and (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 2#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (2#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (2#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "and" 2#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.and (Hw.readReg E Hw.rs1E) (Hw.readReg E Hw.rs2E))
    ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs1)
      &&& (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs2))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    ?_ ?_
  · show (Hw.readReg E Hw.rs1E).eval σ &&& (Hw.readReg E Hw.rs2E).eval σ = _
    rw [readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl,
        readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl,
        specReg_bridge, specReg_bridge]
  · rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl

/-- The `or` arm: opcode 3. -/
theorem square_retire_or (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 3#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (3#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (3#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "or" 3#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.or (Hw.readReg E Hw.rs1E) (Hw.readReg E Hw.rs2E))
    ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs1)
      ||| (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs2))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    ?_ ?_
  · show (Hw.readReg E Hw.rs1E).eval σ ||| (Hw.readReg E Hw.rs2E).eval σ = _
    rw [readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl,
        readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl,
        specReg_bridge, specReg_bridge]
  · rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl

/-- The `xor` arm: opcode 4. -/
theorem square_retire_xor (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 4#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (4#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (4#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "xor" 4#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.xor (Hw.readReg E Hw.rs1E) (Hw.readReg E Hw.rs2E))
    ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs1)
      ^^^ (((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs2))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
    ?_ ?_
  · show (Hw.readReg E Hw.rs1E).eval σ ^^^ (Hw.readReg E Hw.rs2E).eval σ = _
    rw [readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl,
        readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl,
        specReg_bridge, specReg_bridge]
  · rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl

/-- The `shl` arm: opcode 5. -/
theorem square_retire_shl (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 5#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (5#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (5#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "shl" 5#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.shl (Hw.readReg E Hw.rs1E) (.and (Hw.readReg E Hw.rs2E) (.lit 31)))
    ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs1)
      <<< ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs2) &&& (31 : Loom.Word32)))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
    ?_ ?_
  · show (Hw.readReg E Hw.rs1E).eval σ <<<
      ((Hw.readReg E Hw.rs2E).eval σ &&& (31#32 : BitVec 32)) = _
    rw [readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl,
        readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl,
        specReg_bridge, specReg_bridge]
    rfl
  · rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl

/-- The `shr` arm: opcode 6. -/
theorem square_retire_shr (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 6#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (6#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (6#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "shr" 6#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.shr (Hw.readReg E Hw.rs1E) (.and (Hw.readReg E Hw.rs2E) (.lit 31)))
    ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs1)
      >>> ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs2) &&& (31 : Loom.Word32)))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
    ?_ ?_
  · show (Hw.readReg E Hw.rs1E).eval σ >>>
      ((Hw.readReg E Hw.rs2E).eval σ &&& (31#32 : BitVec 32)) = _
    rw [readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl,
        readReg_eval σ hz E Hw.rs2E (operandsOf W).rs2 rfl,
        specReg_bridge, specReg_bridge]
    rfl
  · rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl

/-- The `addi` arm: opcode 7. -/
theorem square_retire_addi (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 7#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (7#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (7#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "addi" 7#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.add (Hw.readReg E Hw.rs1E) Hw.immX)
    ((((({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
        (fun ds => { ds with pc := ds.pc + 1 })).doms E).reg
          (operandsOf W).rs1)
      + immExt (operandsOf W).imm)
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))
    ?_ ?_
  · show (Hw.readReg E Hw.rs1E).eval σ + Hw.immX.eval σ = _
    rw [readReg_eval σ hz E Hw.rs1E (operandsOf W).rs1 rfl, specReg_bridge]
    rfl
  · rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl

/-- The `lui` arm: opcode 8. -/
theorem square_retire_lui (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 8#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  set W := σ.regs "if_word" 32 with hW
  set E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2) with hEdef
  have hop : Machines.Lnp64u.sig.opcodeOf W = (8#6 : BitVec 6) := hopc
  have hdec : Loom.Isa.decode isa W
      = isa.find? (fun d => d.opcode == (8#6 : BitVec 6)) := by
    rw [decode_eq_find, hop]
  refine square_retire_setReg m hwf hfit σ hsync hifv hcl "lui" 8#6 hopc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    E rfl
    (.shl (.zext Hw.immE 32) (.lit 15))
    (((operandsOf W).imm.setWidth 32) <<< (15 : Nat))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))
    ?_ ?_
  · rfl
  · rw [retire_of_decode_some _ E W _ (hdec.trans rfl)]
    rfl

/-! ## The general domain-footprint shape

`square_retire_domShape` generalizes the `setReg` shape: the payload `X`
may write any subset of the owner's file/`pc` registers, and the spec's
per-domain effect is an arbitrary transform `DSF` that fixes the nine
quiet fields. Branches (`pc` only), `jalr` (link + jump), and `lw`'s
authorized branch all instantiate it. -/

/-- The owner-file/`pc` write footprint. -/
def domWrites (e : DomainId) : List (String × Nat) :=
  [(Hw.dreg e 1, 32), (Hw.dreg e 2, 32), (Hw.dreg e 3, 32),
   (Hw.dreg e 4, 32), (Hw.dreg e 5, 32), (Hw.dreg e 6, 32),
   (Hw.dreg e 7, 32), (Hw.dpc e, 12)]

theorem quiet_notin_dom (x e : DomainId) :
    ∀ q ∈ domQuietNames x, q ∉ ("if_v", 1) :: domWrites e := by
  fin_cases x <;> fin_cases e <;> decide +kernel

theorem read_notin_dom_ne (x e : DomainId) (hne : x ≠ e) :
    ∀ q ∈ domReadNames x, q ∉ ("if_v", 1) :: domWrites e := by
  fin_cases x <;> fin_cases e <;>
    first
      | exact absurd rfl hne
      | decide +kernel

theorem gate_notin_dom (g : GateId) (e : DomainId) :
    ∀ q ∈ gateReadNames g, q ∉ ("if_v", 1) :: domWrites e := by
  fin_cases g <;> fin_cases e <;> decide +kernel

theorem ifv_notin_dom (e : DomainId) :
    ("if_v", 1) ∉ domWrites e := by
  fin_cases e <;> decide +kernel

set_option maxHeartbeats 6400000 in
/-- **The general benign retirement square.** -/
theorem square_retire_domShape (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (k : BitVec 6)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = k)
    (hbenk : ∀ mn' ∈ moverMns, k ≠ Hw.opcodeOf mn')
    (E : DomainId) (hE : E.val = (σ.regs "if_dom" 2).toNat)
    (X : Act)
    (hXsub : ∀ q ∈ X.regWrites, q ∈ domWrites E)
    (hcoreX : ∀ acc, (Hw.retireFor E).run σ acc = X.run σ acc)
    (DSF : DomainState → DomainState)
    (hcapsF : ∀ ds, (DSF ds).caps = ds.caps)
    (hgenF : ∀ ds, (DSF ds).slotGen = ds.slotGen)
    (hlinF : ∀ ds, (DSF ds).lineage = ds.lineage)
    (hrgnF : ∀ ds, (DSF ds).regions = ds.regions)
    (hrunF : ∀ ds, (DSF ds).run = ds.run)
    (hsrvF : ∀ ds, (DSF ds).serving = ds.serving)
    (hcauF : ∀ ds, (DSF ds).cause = ds.cause)
    (hbudF : ∀ ds, (DSF ds).budget = ds.budget)
    (hmaxF : ∀ ds, (DSF ds).maxDonation = ds.maxDonation)
    (hregs : ∀ r : RegId,
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs (Hw.dreg E r) 32
        = (DSF (Hw.absDom ((Hw.refillAct m).run σ σ) E)).regs r)
    (hpc :
      ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ
          ((Hw.refillAct m).run σ σ)).regs (Hw.dpc E) 12
        = (DSF (Hw.absDom ((Hw.refillAct m).run σ σ) E)).pc)
    (hretire :
      retire { refillPhase m (Hw.abs σ) with inflight := none } E
          (σ.regs "if_word" 32)
        = ({ refillPhase m (Hw.abs σ) with inflight := none }).setDom E
            DSF) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hben : ∀ mn' ∈ moverMns, (Hw.isMn mn').eval σ ≠ 1#1 :=
    fun mn' hmn' => isMn_ne_of_opc σ mn' k hopc (hbenk mn' hmn')
  set W := σ.regs "if_word" 32 with hWdef
  set τ1 := refillPhase m (Hw.abs σ) with hτ1
  set σ1 := (Hw.refillAct m).run σ σ with hσ1
  have habs1 : Hw.abs σ1 = τ1 := abs_refill m hwf hfit σ hsync
  have hfullsub : ∀ q ∈ (Act.seq (.write 1 "if_v" (.lit 0)) X).regWrites,
      q ∈ ("if_v", 1) :: domWrites E := by
    intro q hq
    rcases List.mem_cons.mp
      (show q ∈ ("if_v", (1 : Nat)) :: X.regWrites from hq) with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hXsub q h)
  have hXifv : ("if_v", 1) ∉ X.regWrites :=
    fun hm => absurd (hXsub _ hm) (ifv_notin_dom E)
  have hcoreR : ∀ (rn : String) (w : Nat),
      ((Hw.coreAct m).run σ σ1).regs rn w
        = ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ σ1).regs rn w := by
    intro rn w
    rw [coreAct_run_retire_eq m σ σ1 hifv hcl,
        retireAct_run_regs σ σ1 E hE rn w, hcoreX]
    rfl
  have hfl : τ1.inflight = some
      { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
        word := W
        cyclesLeft := (σ.regs "if_cl" 8).toNat } := by
    show Hw.absInflight σ = _
    exact absInflight_some σ hifv
  have hdomE : (finOfBv (by decide : 2 ^ 2 = numDomains)
      (σ.regs "if_dom" 2)) = E :=
    Fin.ext hE.symm
  have hspec : corePhase m τ1
      = ({ τ1 with inflight := none }).setDom E DSF := by
    rw [corePhase_retire m τ1 _ hfl (by omega : (σ.regs "if_cl" 8).toNat ≤ 1)]
    show retire { τ1 with inflight := none }
      (finOfBv (by decide) (σ.regs "if_dom" 2)) W = _
    rw [hdomE]
    exact hretire
  have hτ2E : (({ τ1 with inflight := none }).setDom E DSF).doms E
      = DSF (τ1.doms E) := by
    show (Loom.Fun.update τ1.doms E (DSF (τ1.doms E))) E = _
    rw [Loom.Fun.update_same]
  have hτ2x : ∀ x, x ≠ E →
      (({ τ1 with inflight := none }).setDom E DSF).doms x = τ1.doms x := by
    intro x hx
    show (Loom.Fun.update τ1.doms E (DSF (τ1.doms E))) x = _
    rw [Loom.Fun.update_ne _ _ _ _ hx]
  have hL1 : ∀ x, τ1.doms x = Hw.absDom σ1 x := by
    intro x
    rw [← habs1]
    rfl
  refine square_retire_benign m hwf hfit σ hsync hifv hcl hben
    X _ hcoreR hXifv hspec ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- absDom faces
    intro x
    by_cases hx : x = E
    · subst hx
      rw [hτ2E, hL1 x]
      have hq : ∀ q ∈ domQuietNames x,
          ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ σ1).regs q.1 q.2
            = σ1.regs q.1 q.2 :=
        fun q hq' => frame (fun hm =>
          absurd (hfullsub q hm) (quiet_notin_dom x x q hq')) σ σ1
      rw [absDom_regpc x hq]
      apply domainState_ext'
      · funext r
        exact hregs r
      · exact hpc
      · show (Hw.absDom σ1 x).caps = (DSF (Hw.absDom σ1 x)).caps
        exact (hcapsF _).symm
      · show (Hw.absDom σ1 x).slotGen = (DSF (Hw.absDom σ1 x)).slotGen
        exact (hgenF _).symm
      · show (Hw.absDom σ1 x).lineage = (DSF (Hw.absDom σ1 x)).lineage
        exact (hlinF _).symm
      · show (Hw.absDom σ1 x).regions = (DSF (Hw.absDom σ1 x)).regions
        exact (hrgnF _).symm
      · show (Hw.absDom σ1 x).run = (DSF (Hw.absDom σ1 x)).run
        exact (hrunF _).symm
      · show (Hw.absDom σ1 x).serving = (DSF (Hw.absDom σ1 x)).serving
        exact (hsrvF _).symm
      · show (Hw.absDom σ1 x).cause = (DSF (Hw.absDom σ1 x)).cause
        exact (hcauF _).symm
      · show (Hw.absDom σ1 x).budget = (DSF (Hw.absDom σ1 x)).budget
        exact (hbudF _).symm
      · show (Hw.absDom σ1 x).maxDonation
          = (DSF (Hw.absDom σ1 x)).maxDonation
        exact (hmaxF _).symm
    · rw [hτ2x x hx, hL1 x]
      exact absDom_congr x (fun p hp => frame (fun hm =>
        absurd (hfullsub p hm) (read_notin_dom_ne x E hx p hp)) σ σ1)
  · -- absGate faces
    intro g
    have hg : Hw.absGate
        ((Act.seq (.write 1 "if_v" (.lit 0)) X).run σ σ1) g
        = Hw.absGate σ1 g :=
      absGate_congr g (fun p hp => frame (fun hm =>
        absurd (hfullsub p hm) (gate_notin_dom g E p hp)) σ σ1)
    rw [hg]
    show Hw.absGate σ1 g = τ1.gates g
    rw [← habs1]
    rfl
  · intro x
    by_cases hx : x = E
    · subst hx
      rw [hτ2E, hcapsF]
      show (τ1.doms x).caps = _
      rw [hτ1, refillPhase_caps]
    · rw [hτ2x x hx, hτ1, refillPhase_caps]
  · intro x
    by_cases hx : x = E
    · subst hx
      rw [hτ2E, hgenF]
      show (τ1.doms x).slotGen = _
      rw [hτ1, refillPhase_slotGen]
    · rw [hτ2x x hx, hτ1, refillPhase_slotGen]
  · intro x
    by_cases hx : x = E
    · subst hx
      rw [hτ2E, hrgnF]
      show (τ1.doms x).regions = _
      rw [hτ1, refillPhase_regions]
    · rw [hτ2x x hx, hτ1, refillPhase_regions]
  · show τ1.mover = _
    rw [hτ1, refillPhase_mover]
    rfl
  · intro b
    show τ1.mem b = _
    rw [hτ1]
    rfl
  · show τ1.cycle = _
    rw [hτ1]
    rfl
  · rfl

end Machines.Lnp64u.Theorems.RMC
