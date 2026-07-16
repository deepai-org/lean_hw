-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireDrop

/-!
# R-MC support: the `cap_revoke` mark-engine coupling (design spike)

The rv-coupling invariant relates
the hidden pointer-doubling registers (`rv_j`/`rv_v`/`rv_r`,
`SysOps.rvInit`/`rvStep`) to descendant marking on the abstraction. The
sequential-marking equivalence and finite saturation bridge are proved here;
the circuit initialization/doubling preservation remains the convergence
obligation.

## The engine, semantically

`rvInit` runs on the first countdown cycle of an in-flight `cap_revoke`
(pre-cycle `if_cl = revokeCost`); each further countdown cycle
(pre-cycle `2 ≤ if_cl < revokeCost`) runs one `rvStep` doubling round.
The tables the engine reads (caps, cells, generations, the issuing
domain's `rs1`) are stable while the instruction is in flight, so the
invariant is stated against the *current* abstraction. With
`k = revokeCost - 1 - if_cl` rounds done:

* `rv_r i = 1` iff a live parent chain of length `< 2^k` from node `i`
  ends in an edge pointing at the revoked root (`reachRootN (2^k)`);
* `rv_v i = 1` iff the `2^k`-step parent chain from `i` exists with
  every edge generation-live (`liveChainN (2^k)`);
* where that chain exists, `rv_j i` indexes its endpoint (`chainEndN`).

At retirement (pre-cycle `if_cl ≤ 1`) `k = revokeCost - 2 = 22` rounds
are done, and `2^22 > numDomains * numSlots`, so `rv_r` has reached the
`Kernel.marks` fixpoint (`marks_eq_reachRootN` and
`reachRootN_eq_marks_of_nodeCount_le` below). This uses the already-proved
finite marking fixpoint and needs no extra acyclicity assumption.

## Plumbing notes (for the eventual `Coupled` clause)

* Vacuity everywhere else: the guard requires an in-flight `cap_revoke`
  *past its first countdown*. Issue latches `if_cl = revokeCost` (guard
  false), retirement clears `if_v`, non-revoke words fail the opcode
  guard — so only the countdown rule carries proof obligations
  (`rvInit` at `if_cl = revokeCost` establishes `k = 0`; `rvStep`
  advances `k`), and refill/mover/tick preserve it by frames (they
  write neither `rv_*` nor the guard registers nor cap tables).
* The proven `square_countdown` arm needs no change: `abs` ignores
  `rv_*`, and the clause is carried by `coupled_step`, not the square.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

private def rvNameBlock (i : Hw.NodeId) : List String :=
  [Hw.rvJ i, Hw.rvV i, Hw.rvR i]

/-- The reset manifest's global name proof specializes to the hidden revoke
register suffix. This gives structural disjointness without reducing all
64-by-64 string pairs. -/
private theorem rvNameBlocks_nodup (m : Manifest) :
    ((List.finRange (numDomains * numSlots)).flatMap rvNameBlock).Nodup := by
  have h := names_nodup m
  unfold Hw.regDecls at h
  simp only [List.map_append, List.map_flatMap] at h
  exact (by simpa [rvNameBlock] using h.of_append_right)

private theorem rvNameBlock_nodup (m : Manifest) (i : Hw.NodeId) :
    (rvNameBlock i).Nodup := by
  exact (List.nodup_flatMap.mp (rvNameBlocks_nodup m)).1 i
    (List.mem_finRange i)

private theorem rvNameBlock_disjoint (m : Manifest) (i j : Hw.NodeId)
    (hne : i ≠ j) : List.Disjoint (rvNameBlock i) (rvNameBlock j) := by
  have hp := (List.nodup_flatMap.mp (rvNameBlocks_nodup m)).2
  by_cases hij : i.val < j.val
  · have hd := hp.rel_get_of_lt
        (a := ⟨i.val, by simpa using i.isLt⟩)
        (b := ⟨j.val, by simpa using j.isLt⟩) hij
    simpa using hd
  · have hji : j.val < i.val := by
      have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
      omega
    have hd := hp.rel_get_of_lt
        (a := ⟨j.val, by simpa using j.isLt⟩)
        (b := ⟨i.val, by simpa using i.isLt⟩) hji
    simpa using hd.symm

theorem seqAll_actions_frame {I : Type} {w : Nat}
    (σ acc : Loom.Hw.St) (a : I → Act) (l : List I)
    (rn : String)
    (hframe : ∀ i ∈ l, ∀ acc', ((a i).run σ acc').regs rn w =
      acc'.regs rn w) :
    ((Hw.seqAll (l.map a)).run σ acc).regs rn w = acc.regs rn w := by
  induction l generalizing acc with
  | nil => rfl
  | cons i t ih =>
      change ((Hw.seqAll (t.map a)).run σ ((a i).run σ acc)).regs rn w = _
      rw [ih _ (fun j hj => hframe j (List.mem_cons_of_mem i hj))]
      exact hframe i (List.mem_cons_self ..) acc

theorem seqAll_actions_at {I : Type} {w : Nat}
    (σ acc : Loom.Hw.St) (a : I → Act) (l : List I) (i : I)
    (hi : i ∈ l) (hnd : l.Nodup) (rn : String) (v : BitVec w)
    (hat : ∀ acc', ((a i).run σ acc').regs rn w = v)
    (hframe : ∀ j ∈ l, j ≠ i → ∀ acc',
      ((a j).run σ acc').regs rn w = acc'.regs rn w) :
    ((Hw.seqAll (l.map a)).run σ acc).regs rn w = v := by
  induction l generalizing acc with
  | nil => exact absurd hi List.not_mem_nil
  | cons j t ih =>
      have hnd' := List.nodup_cons.mp hnd
      by_cases hji : j = i
      · subst j
        change ((Hw.seqAll (t.map a)).run σ ((a i).run σ acc)).regs rn w = v
        rw [seqAll_actions_frame σ _ a t rn]
        · exact hat acc
        · intro k hk
          exact hframe k (List.mem_cons_of_mem i hk)
            (fun h => hnd'.1 (h ▸ hk))
      · have hit : i ∈ t := (List.mem_cons.mp hi).resolve_left
          (fun h => hji h.symm)
        change ((Hw.seqAll (t.map a)).run σ ((a j).run σ acc)).regs rn w = v
        exact ih _ hit hnd'.2
          (fun k hk hki => hframe k (List.mem_cons_of_mem j hk) hki)

private def rvInitPEx (i : Hw.NodeId) : Expr 1 :=
  let c := Hw.nDom i
  let s := Hw.nSlot i
  let linE : Expr 4 := .reg 4 (Hw.dcapLin c s)
  Hw.andAll [.reg 1 (Hw.dcapV c s), .reg 1 (Hw.dcapLinV c s),
    Hw.cellVAt c linE]

private def rvInitPEnc (i : Hw.NodeId) : Expr 14 :=
  Hw.cellParAt (Hw.nDom i) (.reg 4 (Hw.dcapLin (Hw.nDom i) (Hw.nSlot i)))

private def rvInitRootE : Expr 14 :=
  let hw := Hw.muxFin (fun d => Hw.readReg d Hw.rs1E) (.reg 2 "if_dom")
  Hw.encRefE (.reg 2 "if_dom") (Hw.field hw 0 4) (Hw.field hw 4 8)

private def rvInitNodeA (i : Hw.NodeId) : Act :=
  let pEx := rvInitPEx i
  let pEnc := rvInitPEnc i
  let pIdx : Expr 6 := Hw.field pEnc 8 6
  Hw.seqAll
    [ .write 6 (Hw.rvJ i) pIdx,
      .write 1 (Hw.rvV i)
        (.and pEx (.eq (Hw.genAt pIdx) (Hw.field pEnc 0 8))),
      .write 1 (Hw.rvR i) (.and pEx (.eq pEnc rvInitRootE)) ]

private theorem rvInit_eq_nodes :
    Hw.rvInit = Hw.seqAll
      ((List.finRange (numDomains * numSlots)).map rvInitNodeA) := by
  rfl

private theorem rvInitNodeA_run_r_same (σ acc : Loom.Hw.St)
    (i : Hw.NodeId) :
    ((rvInitNodeA i).run σ acc).regs (Hw.rvR i) 1 =
      (Expr.and (rvInitPEx i) (.eq (rvInitPEnc i) rvInitRootE)).eval σ := by
  simp [rvInitNodeA, Hw.seqAll, Act.run, RegEnv.set]

private theorem rvInitNodeA_run_block_frame (m : Manifest)
    (σ acc : Loom.Hw.St) (i q : Hw.NodeId) (hne : i ≠ q)
    (rn : String) (w : Nat) (hrn : rn ∈ rvNameBlock q) :
    ((rvInitNodeA i).run σ acc).regs rn w = acc.regs rn w := by
  have hd := rvNameBlock_disjoint m q i (Ne.symm hne)
  have hnot : rn ∉ rvNameBlock i := by
    intro hm
    exact (List.disjoint_left.mp hd) hrn hm
  simp [rvNameBlock] at hnot
  simp [rvInitNodeA, Hw.seqAll, Act.run, RegEnv.set, hnot]

private theorem rvInitNodeA_run_r_frame (m : Manifest) (σ acc : Loom.Hw.St)
    (i q : Hw.NodeId) (hne : i ≠ q) :
    ((rvInitNodeA i).run σ acc).regs (Hw.rvR q) 1 =
      acc.regs (Hw.rvR q) 1 :=
  rvInitNodeA_run_block_frame m σ acc i q hne (Hw.rvR q) 1
    (by simp [rvNameBlock])

private theorem rvInitNodeA_run_v_same (m : Manifest) (σ acc : Loom.Hw.St)
    (i : Hw.NodeId) :
    ((rvInitNodeA i).run σ acc).regs (Hw.rvV i) 1 =
      (Expr.and (rvInitPEx i)
        (.eq (Hw.genAt (Hw.field (rvInitPEnc i) 8 6))
          (Hw.field (rvInitPEnc i) 0 8))).eval σ := by
  have hb := rvNameBlock_nodup m i
  simp [rvNameBlock] at hb
  simp [rvInitNodeA, Hw.seqAll, Act.run, RegEnv.set, hb]

private theorem rvInitNodeA_run_j_same (m : Manifest) (σ acc : Loom.Hw.St)
    (i : Hw.NodeId) :
    ((rvInitNodeA i).run σ acc).regs (Hw.rvJ i) 6 =
      (Hw.field (rvInitPEnc i) 8 6).eval σ := by
  have hb := rvNameBlock_nodup m i
  simp [rvNameBlock] at hb
  simp [rvInitNodeA, Hw.seqAll, Act.run, RegEnv.set, hb]

/-- `rvInit` writes the direct-root predicate to each node's `rv_r` bit.
The proof selects the unique writer structurally from the globally-nodup
register-name suffix. -/
theorem rvInit_run_r (m : Manifest) (σ acc : Loom.Hw.St) (i : Hw.NodeId) :
    (Hw.rvInit.run σ acc).regs (Hw.rvR i) 1 =
      (Expr.and (rvInitPEx i) (.eq (rvInitPEnc i) rvInitRootE)).eval σ := by
  rw [rvInit_eq_nodes]
  apply seqAll_actions_at σ acc rvInitNodeA
    (List.finRange (numDomains * numSlots)) i
    (List.mem_finRange i) (List.nodup_finRange _) (Hw.rvR i)
  · intro acc'
    exact rvInitNodeA_run_r_same σ acc' i
  · intro j _ hji acc'
    exact rvInitNodeA_run_r_frame m σ acc' j i hji

/-- `rvInit` writes one-edge generation liveness to each `rv_v` bit. -/
theorem rvInit_run_v (m : Manifest) (σ acc : Loom.Hw.St) (i : Hw.NodeId) :
    (Hw.rvInit.run σ acc).regs (Hw.rvV i) 1 =
      (Expr.and (rvInitPEx i)
        (.eq (Hw.genAt (Hw.field (rvInitPEnc i) 8 6))
          (Hw.field (rvInitPEnc i) 0 8))).eval σ := by
  rw [rvInit_eq_nodes]
  apply seqAll_actions_at σ acc rvInitNodeA
    (List.finRange (numDomains * numSlots)) i
    (List.mem_finRange i) (List.nodup_finRange _) (Hw.rvV i)
  · intro acc'
    exact rvInitNodeA_run_v_same m σ acc' i
  · intro j _ hji acc'
    exact rvInitNodeA_run_block_frame m σ acc' j i hji (Hw.rvV i) 1
      (by simp [rvNameBlock])

/-- `rvInit` writes the direct parent-node endpoint to each `rv_j` word. -/
theorem rvInit_run_j (m : Manifest) (σ acc : Loom.Hw.St) (i : Hw.NodeId) :
    (Hw.rvInit.run σ acc).regs (Hw.rvJ i) 6 =
      (Hw.field (rvInitPEnc i) 8 6).eval σ := by
  rw [rvInit_eq_nodes]
  apply seqAll_actions_at σ acc rvInitNodeA
    (List.finRange (numDomains * numSlots)) i
    (List.mem_finRange i) (List.nodup_finRange _) (Hw.rvJ i)
  · intro acc'
    exact rvInitNodeA_run_j_same m σ acc' i
  · intro j _ hji acc'
    exact rvInitNodeA_run_block_frame m σ acc' j i hji (Hw.rvJ i) 6
      (by simp [rvNameBlock])

private def rvStepNodeA (i : Hw.NodeId) : Act :=
  let j : Expr 6 := .reg 6 (Hw.rvJ i)
  Hw.seqAll
    [ .write 1 (Hw.rvR i) (.or (.reg 1 (Hw.rvR i))
        (.and (.reg 1 (Hw.rvV i))
          (Hw.muxFin (fun k : Hw.NodeId => .reg 1 (Hw.rvR k)) j))),
      .write 1 (Hw.rvV i) (.and (.reg 1 (Hw.rvV i))
        (Hw.muxFin (fun k : Hw.NodeId => .reg 1 (Hw.rvV k)) j)),
      .write 6 (Hw.rvJ i)
        (Hw.muxFin (fun k : Hw.NodeId => .reg 6 (Hw.rvJ k)) j) ]

private theorem rvStep_eq_nodes :
    Hw.rvStep = Hw.seqAll
      ((List.finRange (numDomains * numSlots)).map rvStepNodeA) := by
  rfl

private theorem rvStepNodeA_run_r_same (m : Manifest) (σ acc : Loom.Hw.St)
    (i : Hw.NodeId) :
    ((rvStepNodeA i).run σ acc).regs (Hw.rvR i) 1 =
      (σ.regs (Hw.rvR i) 1 |||
        (σ.regs (Hw.rvV i) 1 &&&
          (Hw.muxFin (fun k : Hw.NodeId => .reg 1 (Hw.rvR k))
            (.reg 6 (Hw.rvJ i))).eval σ)) := by
  have hb := rvNameBlock_nodup m i
  simp [rvNameBlock] at hb
  have hrv : Hw.rvR i ≠ Hw.rvV i := Ne.symm hb.2
  simp [rvStepNodeA, Hw.seqAll, Act.run, RegEnv.set, Expr.eval, hrv]

private theorem rvStepNodeA_run_v_same (m : Manifest)
    (σ acc : Loom.Hw.St) (i : Hw.NodeId) :
    ((rvStepNodeA i).run σ acc).regs (Hw.rvV i) 1 =
      (σ.regs (Hw.rvV i) 1 &&&
        (Hw.muxFin (fun k : Hw.NodeId => .reg 1 (Hw.rvV k))
          (.reg 6 (Hw.rvJ i))).eval σ) := by
  have hb := rvNameBlock_nodup m i
  simp [rvNameBlock] at hb
  simp [rvStepNodeA, Hw.seqAll, Act.run, RegEnv.set, Expr.eval, hb]

private theorem rvStepNodeA_run_j_same (m : Manifest)
    (σ acc : Loom.Hw.St) (i : Hw.NodeId) :
    ((rvStepNodeA i).run σ acc).regs (Hw.rvJ i) 6 =
      (Hw.muxFin (fun k : Hw.NodeId => .reg 6 (Hw.rvJ k))
        (.reg 6 (Hw.rvJ i))).eval σ := by
  have hb := rvNameBlock_nodup m i
  simp [rvNameBlock] at hb
  simp [rvStepNodeA, Hw.seqAll, Act.run, RegEnv.set, hb]

private theorem rvStepNodeA_run_block_frame (m : Manifest)
    (σ acc : Loom.Hw.St) (i q : Hw.NodeId) (hne : i ≠ q)
    (rn : String) (w : Nat) (hrn : rn ∈ rvNameBlock q) :
    ((rvStepNodeA i).run σ acc).regs rn w = acc.regs rn w := by
  have hd := rvNameBlock_disjoint m q i (Ne.symm hne)
  have hnot : rn ∉ rvNameBlock i := by
    intro hm
    exact (List.disjoint_left.mp hd) hrn hm
  simp [rvNameBlock] at hnot
  simp [rvStepNodeA, Hw.seqAll, Act.run, RegEnv.set, hnot]

/-- One full `rvStep` computes `R := R ∨ (V ∧ R[J])` from the pre-state. -/
theorem rvStep_run_r (m : Manifest) (σ acc : Loom.Hw.St) (i : Hw.NodeId) :
    (Hw.rvStep.run σ acc).regs (Hw.rvR i) 1 =
      (σ.regs (Hw.rvR i) 1 |||
        (σ.regs (Hw.rvV i) 1 &&&
          (Hw.muxFin (fun k : Hw.NodeId => .reg 1 (Hw.rvR k))
            (.reg 6 (Hw.rvJ i))).eval σ)) := by
  rw [rvStep_eq_nodes]
  apply seqAll_actions_at σ acc rvStepNodeA
    (List.finRange (numDomains * numSlots)) i
    (List.mem_finRange i) (List.nodup_finRange _) (Hw.rvR i)
  · intro acc'
    exact rvStepNodeA_run_r_same m σ acc' i
  · intro j _ hji acc'
    exact rvStepNodeA_run_block_frame m σ acc' j i hji (Hw.rvR i) 1
      (by simp [rvNameBlock])

/-- One full `rvStep` computes `V := V ∧ V[J]` from the pre-state. -/
theorem rvStep_run_v (m : Manifest) (σ acc : Loom.Hw.St) (i : Hw.NodeId) :
    (Hw.rvStep.run σ acc).regs (Hw.rvV i) 1 =
      (σ.regs (Hw.rvV i) 1 &&&
        (Hw.muxFin (fun k : Hw.NodeId => .reg 1 (Hw.rvV k))
          (.reg 6 (Hw.rvJ i))).eval σ) := by
  rw [rvStep_eq_nodes]
  apply seqAll_actions_at σ acc rvStepNodeA
    (List.finRange (numDomains * numSlots)) i
    (List.mem_finRange i) (List.nodup_finRange _) (Hw.rvV i)
  · intro acc'
    exact rvStepNodeA_run_v_same m σ acc' i
  · intro j _ hji acc'
    exact rvStepNodeA_run_block_frame m σ acc' j i hji (Hw.rvV i) 1
      (by simp [rvNameBlock])

/-- One full `rvStep` computes `J := J[J]` from the pre-state. -/
theorem rvStep_run_j (m : Manifest) (σ acc : Loom.Hw.St) (i : Hw.NodeId) :
    (Hw.rvStep.run σ acc).regs (Hw.rvJ i) 6 =
      (Hw.muxFin (fun k : Hw.NodeId => .reg 6 (Hw.rvJ k))
        (.reg 6 (Hw.rvJ i))).eval σ := by
  rw [rvStep_eq_nodes]
  apply seqAll_actions_at σ acc rvStepNodeA
    (List.finRange (numDomains * numSlots)) i
    (List.mem_finRange i) (List.nodup_finRange _) (Hw.rvJ i)
  · intro acc'
    exact rvStepNodeA_run_j_same m σ acc' i
  · intro j _ hji acc'
    exact rvStepNodeA_run_block_frame m σ acc' j i hji (Hw.rvJ i) 6
      (by simp [rvNameBlock])

/-- A node-indexed mux selects the named node when its index expression is
the canonical `nodeOf` encoding. -/
theorem muxNode_eval_of_nodeOf {w : Nat} (f : Hw.NodeId → Expr w)
    (j : Expr 6) (σ : Loom.Hw.St) (c : DomainId) (s : Slot)
    (hj : j.eval σ = BitVec.ofNat 6 (Hw.nodeOf c s).val) :
    (Hw.muxFin f j).eval σ = (f (Hw.nodeOf c s)).eval σ := by
  rw [muxFin_eval (by decide : 2 ^ 6 = numDomains * numSlots)]
  have hi : finOfBv (by decide : 2 ^ 6 = numDomains * numSlots) (j.eval σ) =
      Hw.nodeOf c s := by
    rw [hj, finOfBv_ofNat]
  rw [hi]

private theorem nDom_nodeOf (c : DomainId) (s : Slot) :
    Hw.nDom (Hw.nodeOf c s) = c := by
  exact (nDom_pack c.val s.val c.isLt s.isLt).1

private theorem nSlot_nodeOf (c : DomainId) (s : Slot) :
    Hw.nSlot (Hw.nodeOf c s) = s := by
  exact (nDom_pack c.val s.val c.isLt s.isLt).2

/-- The initialization circuit's parent-exists bit and packed parent decode
exactly characterize `MachineState.parentOf` on the abstraction. -/
theorem rvInit_parent_some_iff (σ : Loom.Hw.St) (c : DomainId) (s : Slot)
    (p : CapRef) :
    ((rvInitPEx (Hw.nodeOf c s)).eval σ = 1#1 ∧
      Hw.decRef ((rvInitPEnc (Hw.nodeOf c s)).eval σ) = p) ↔
      (Hw.abs σ).parentOf c s = some p := by
  rw [rvInitPEx, rvInitPEnc, nDom_nodeOf, nSlot_nodeOf]
  change
    ((σ.regs (Hw.dcapV c s) 1 &&&
        (σ.regs (Hw.dcapLinV c s) 1 &&&
          (Hw.cellVAt c (Expr.reg 4 (Hw.dcapLin c s))).eval σ) = 1#1 ∧
        Hw.decRef ((Hw.cellParAt c
          (Expr.reg 4 (Hw.dcapLin c s))).eval σ) = p) ↔
      (Hw.abs σ).parentOf c s = some p)
  by_cases hv : σ.regs (Hw.dcapV c s) 1 = 1#1
  · by_cases hlv : σ.regs (Hw.dcapLinV c s) 1 = 1#1
    · let L : LineageId := finOfBv (by decide)
        (σ.regs (Hw.dcapLin c s) 4)
      have hlin : (Expr.reg 4 (Hw.dcapLin c s)).eval σ =
          BitVec.ofNat 4 L.val := (bv4_slot_iff _ L).mpr rfl
      rw [cellVAt_eval σ c _ L hlin, cellParAt_eval σ c _ L hlin]
      by_cases hcv : σ.regs (Hw.dcellV c L) 1 = 1#1
      · simp [hv, hlv, hcv, MachineState.parentOf,
          Hw.abs, Hw.absDom, L]
      · have hcv0 := bv1_ne_one.mp hcv
        simp [hv, hlv, hcv0,
          MachineState.parentOf, Hw.abs, Hw.absDom, L]
    · have hlv0 := bv1_ne_one.mp hlv
      simp [hv, hlv0, MachineState.parentOf,
        Hw.abs, Hw.absDom]
  · have hv0 := bv1_ne_one.mp hv
    simp [hv0, MachineState.parentOf,
      Hw.abs, Hw.absDom]

/-- The equivalent packed form of `rvInit_parent_some_iff`. -/
theorem rvInit_parent_packed_iff (σ : Loom.Hw.St) (c : DomainId) (s : Slot)
    (p : CapRef) :
    ((rvInitPEx (Hw.nodeOf c s)).eval σ = 1#1 ∧
      (rvInitPEnc (Hw.nodeOf c s)).eval σ = Hw.encRef p) ↔
      (Hw.abs σ).parentOf c s = some p := by
  rw [← rvInit_parent_some_iff σ c s p]
  constructor
  · rintro ⟨hex, hp⟩
    exact ⟨hex, by rw [hp, decRef_encRef]⟩
  · rintro ⟨hex, hp⟩
    refine ⟨hex, ?_⟩
    calc
      (rvInitPEnc (Hw.nodeOf c s)).eval σ =
          Hw.encRef (Hw.decRef ((rvInitPEnc (Hw.nodeOf c s)).eval σ)) :=
        (encRef_decRef _).symm
      _ = Hw.encRef p := congrArg Hw.encRef hp

private theorem encRef_nodeField (p : CapRef) :
    (Hw.encRef p).extractLsb' 8 6 =
      BitVec.ofNat 6 (Hw.nodeOf p.dom p.slot).val := by
  obtain ⟨d, s, g⟩ := p
  revert d s g
  decide +kernel

private theorem encRef_genField (p : CapRef) :
    (Hw.encRef p).extractLsb' 0 8 = p.gen := by
  obtain ⟨d, s, g⟩ := p
  revert d s g
  decide +kernel

/-- If initialization sees parent `p`, its packed parent-index field is
exactly `nodeOf p.dom p.slot`. -/
theorem rvInit_parent_index_eval (σ : Loom.Hw.St) (c : DomainId) (s : Slot)
    (p : CapRef) (hp : (Hw.abs σ).parentOf c s = some p) :
    (Hw.field (rvInitPEnc (Hw.nodeOf c s)) 8 6).eval σ =
      BitVec.ofNat 6 (Hw.nodeOf p.dom p.slot).val := by
  have hpack := (rvInit_parent_packed_iff σ c s p).mpr hp
  change ((rvInitPEnc (Hw.nodeOf c s)).eval σ).extractLsb' 8 6 = _
  rw [hpack.2, encRef_nodeField]

/-- If initialization sees parent `p`, its packed generation field is
exactly `p.gen`. -/
theorem rvInit_parent_gen_eval (σ : Loom.Hw.St) (c : DomainId) (s : Slot)
    (p : CapRef) (hp : (Hw.abs σ).parentOf c s = some p) :
    (Hw.field (rvInitPEnc (Hw.nodeOf c s)) 0 8).eval σ = p.gen := by
  have hpack := (rvInit_parent_packed_iff σ c s p).mpr hp
  change ((rvInitPEnc (Hw.nodeOf c s)).eval σ).extractLsb' 0 8 = _
  rw [hpack.2, encRef_genField]

/-- The generation lookup selected by an initialized parent index reads the
abstract parent node's current slot generation. -/
theorem rvInit_genAt_eval (σ : Loom.Hw.St) (c : DomainId) (s : Slot)
    (p : CapRef) (hp : (Hw.abs σ).parentOf c s = some p) :
    (Hw.genAt (Hw.field (rvInitPEnc (Hw.nodeOf c s)) 8 6)).eval σ =
      ((Hw.abs σ).doms p.dom).slotGen p.slot := by
  have hidx := rvInit_parent_index_eval σ c s p hp
  rw [Hw.genAt, muxFin_eval (by decide : 2 ^ 6 = numDomains * numSlots)]
  have hi : finOfBv (by decide : 2 ^ 6 = numDomains * numSlots)
      ((Hw.field (rvInitPEnc (Hw.nodeOf c s)) 8 6).eval σ) =
      Hw.nodeOf p.dom p.slot := by
    rw [hidx, finOfBv_ofNat]
  rw [hi, nDom_nodeOf, nSlot_nodeOf]
  rfl

/-- Is the parent edge of `x` generation-live, and where does it go? -/
def liveParent (τ : MachineState) (x : DomainId × Slot) :
    Option (DomainId × Slot) := do
  let p ← τ.parentOf x.1 x.2
  if p.gen = (τ.doms p.dom).slotGen p.slot then pure (p.dom, p.slot)
  else none

/-- A live parent chain of length `< n` from `x` ends in an edge pointing
at `root` (the mark semantics of `rv_r` after `log₂ n` rounds; matches
`Kernel.markStep` unfolded along one chain). -/
def reachRootN (τ : MachineState) (root : CapRef) :
    Nat → DomainId × Slot → Bool
  | 0, _ => false
  | n + 1, x =>
      reachRootN τ root n x ||
        match τ.parentOf x.1 x.2 with
        | some p =>
            p = root ||
            (decide (p.gen = (τ.doms p.dom).slotGen p.slot)
              && reachRootN τ root n (p.dom, p.slot))
        | none => false

/-- The `n`-step parent chain from `x` exists with every edge
generation-live (the semantics of `rv_v`). -/
def liveChainN (τ : MachineState) : Nat → DomainId × Slot → Bool
  | 0, _ => true
  | n + 1, x =>
      match liveParent τ x with
      | some y => liveChainN τ n y
      | none => false

/-- The endpoint of the `n`-step live parent chain (meaningful only where
`liveChainN` holds; the semantics of `rv_j`). -/
def chainEndN (τ : MachineState) : Nat → DomainId × Slot → DomainId × Slot
  | 0, x => x
  | n + 1, x =>
      match liveParent τ x with
      | some y => chainEndN τ n y
      | none => x

/-- A missing live parent leaves the pointer-jump endpoint fixed. -/
theorem chainEndN_of_liveParent_none (τ : MachineState)
    (x : DomainId × Slot) (hx : liveParent τ x = none) (n : Nat) :
    chainEndN τ n x = x := by
  induction n with
  | zero => rfl
  | succ n _ => simp [chainEndN, hx]

/-- Pointer-jump endpoints compose across consecutive horizons. -/
theorem chainEndN_add (τ : MachineState) (m n : Nat)
    (x : DomainId × Slot) :
    chainEndN τ (m + n) x =
      chainEndN τ n (chainEndN τ m x) := by
  induction m generalizing x with
  | zero => simp [chainEndN]
  | succ m ih =>
      simp only [Nat.succ_add, chainEndN]
      cases hp : liveParent τ x with
      | none =>
          rw [chainEndN_of_liveParent_none τ x hp n]
      | some p => exact ih p

/-- Live parent-chain validity composes across consecutive horizons. -/
theorem liveChainN_add (τ : MachineState) (m n : Nat)
    (x : DomainId × Slot) :
    liveChainN τ (m + n) x =
      (liveChainN τ m x &&
        liveChainN τ n (chainEndN τ m x)) := by
  induction m generalizing x with
  | zero => simp [liveChainN, chainEndN]
  | succ m ih =>
      simp only [Nat.succ_add, liveChainN, chainEndN]
      cases hp : liveParent τ x with
      | none => simp
      | some p => exact ih p

/-- A live-parent lookup depends only on capability, lineage, and generation
tables. -/
theorem liveParent_congr (τ τ' : MachineState) (ht : TablesEq τ τ')
    (x : DomainId × Slot) :
    liveParent τ' x = liveParent τ x := by
  unfold liveParent
  rw [parentOf_congr τ τ' ht]
  cases hp : τ.parentOf x.1 x.2 with
  | none => rfl
  | some p =>
      change (if p.gen = (τ'.doms p.dom).slotGen p.slot then
          some (p.dom, p.slot) else none) =
        (if p.gen = (τ.doms p.dom).slotGen p.slot then
          some (p.dom, p.slot) else none)
      rw [(ht p.dom).2.2]

/-- Bounded reachability depends only on the capability tables. -/
theorem reachRootN_congr (τ τ' : MachineState) (ht : TablesEq τ τ')
    (root : CapRef) (n : Nat) (x : DomainId × Slot) :
    reachRootN τ' root n x = reachRootN τ root n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [reachRootN]
      rw [ih]
      rw [parentOf_congr τ τ' ht]
      cases hp : τ.parentOf x.1 x.2 with
      | none => rfl
      | some p =>
          simp only []
          rw [(ht p.dom).2.2]
          exact congrArg (fun b => reachRootN τ root n x ||
            (decide (p = root) ||
              (decide (p.gen = (τ.doms p.dom).slotGen p.slot) && b)))
            (ih (p.dom, p.slot))

/-- Live-chain validity depends only on the capability tables. -/
theorem liveChainN_congr (τ τ' : MachineState) (ht : TablesEq τ τ')
    (n : Nat) (x : DomainId × Slot) :
    liveChainN τ' n x = liveChainN τ n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [liveChainN]
      rw [liveParent_congr τ τ' ht]
      cases liveParent τ x with
      | none => rfl
      | some p => exact ih p

/-- Pointer-jump endpoints depend only on the capability tables. -/
theorem chainEndN_congr (τ τ' : MachineState) (ht : TablesEq τ τ')
    (n : Nat) (x : DomainId × Slot) :
    chainEndN τ' n x = chainEndN τ n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [chainEndN]
      rw [liveParent_congr τ τ' ht]
      cases liveParent τ x with
      | none => rfl
      | some p => exact ih p

/-- A specification countdown cycle changes no capability, lineage, or
generation table. -/
theorem tablesEq_step_countdown (m : Manifest) (τ : MachineState)
    (fl : InFlight) (hfl : τ.inflight = some fl)
    (hcl2 : 2 ≤ fl.cyclesLeft) :
    TablesEq τ (step m τ) := by
  have hfl' : (refillPhase m τ).inflight = some fl := by
    simpa using hfl
  have hc := corePhase_countdown m (refillPhase m τ) fl hfl' (by omega)
  intro d
  change
    ((moverPhase (corePhase m (refillPhase m τ))).doms d).caps =
        (τ.doms d).caps ∧
      ((moverPhase (corePhase m (refillPhase m τ))).doms d).lineage =
        (τ.doms d).lineage ∧
      ((moverPhase (corePhase m (refillPhase m τ))).doms d).slotGen =
        (τ.doms d).slotGen
  rw [moverPhase_doms, hc]
  exact ⟨refillPhase_caps m τ d, refillPhase_lineage m τ d,
    refillPhase_slotGen m τ d⟩

/-- With no parent edge, no bounded marking horizon can reach the root. -/
theorem reachRootN_of_parent_none (τ : MachineState) (root : CapRef)
    (x : DomainId × Slot) (hx : τ.parentOf x.1 x.2 = none) (n : Nat) :
    reachRootN τ root n x = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reachRootN, hx, ih]

/-- Bounded root reachability is persistent as the horizon grows. -/
theorem reachRootN_succ_of_true (τ : MachineState) (root : CapRef)
    (n : Nat) (x : DomainId × Slot)
    (h : reachRootN τ root n x = true) :
    reachRootN τ root (n + 1) x = true := by
  simp [reachRootN, h]

/-- Across a live non-root edge, adding the first step shifts bounded
reachability to the parent node. -/
theorem reachRootN_succ_of_parent_live_ne_root (τ : MachineState)
    (root p : CapRef) (x : DomainId × Slot)
    (hp : τ.parentOf x.1 x.2 = some p) (hroot : p ≠ root)
    (hgen : p.gen = (τ.doms p.dom).slotGen p.slot) (n : Nat) :
    reachRootN τ root (n + 1) x =
      reachRootN τ root n (p.dom, p.slot) := by
  induction n with
  | zero => simp [reachRootN, hp, hroot, hgen]
  | succ n ih =>
      change (reachRootN τ root (n + 1) x ||
        match τ.parentOf x.1 x.2 with
        | some q => q = root ||
            (decide (q.gen = (τ.doms q.dom).slotGen q.slot) &&
              reachRootN τ root (n + 1) (q.dom, q.slot))
        | none => false) = reachRootN τ root (n + 1) (p.dom, p.slot)
      rw [hp, ih]
      by_cases h : reachRootN τ root n (p.dom, p.slot) = true
      · have hs := reachRootN_succ_of_true τ root n (p.dom, p.slot) h
        simp [h, hs, hroot, hgen]
      · have h0 : reachRootN τ root n (p.dom, p.slot) = false := by
          exact Bool.eq_false_of_not_eq_true h
        simp [h0, hroot, hgen]

/-- A dead non-root parent edge can never reach the root. -/
theorem reachRootN_succ_of_parent_dead_ne_root (τ : MachineState)
    (root p : CapRef) (x : DomainId × Slot)
    (hp : τ.parentOf x.1 x.2 = some p) (hroot : p ≠ root)
    (hgen : p.gen ≠ (τ.doms p.dom).slotGen p.slot) (n : Nat) :
    reachRootN τ root (n + 1) x = false := by
  induction n with
  | zero => simp [reachRootN, hp, hroot, hgen]
  | succ n ih =>
      change (reachRootN τ root (n + 1) x ||
        match τ.parentOf x.1 x.2 with
        | some q => q = root ||
            (decide (q.gen = (τ.doms q.dom).slotGen q.slot) &&
              reachRootN τ root (n + 1) (q.dom, q.slot))
        | none => false) = false
      rw [hp, ih]
      simp [hroot, hgen]

/-- Bounded root reachability composes across consecutive horizons. This is
the semantic recurrence implemented by one `rvStep` pointer-doubling round. -/
theorem reachRootN_add (τ : MachineState) (root : CapRef) (m n : Nat)
    (x : DomainId × Slot) :
    reachRootN τ root (m + n) x =
      (reachRootN τ root m x ||
        (liveChainN τ m x &&
          reachRootN τ root n (chainEndN τ m x))) := by
  induction m generalizing x with
  | zero => simp [reachRootN, liveChainN, chainEndN]
  | succ m ih =>
      rw [Nat.succ_add]
      cases hp : τ.parentOf x.1 x.2 with
      | none =>
          simp [reachRootN_of_parent_none τ root x hp,
            reachRootN, liveChainN, liveParent, chainEndN, hp]
      | some p =>
          by_cases hroot : p = root
          · simp [reachRootN, liveChainN, liveParent, chainEndN, hp, hroot]
          · by_cases hgen : p.gen = (τ.doms p.dom).slotGen p.slot
            · rw [reachRootN_succ_of_parent_live_ne_root τ root p x hp hroot
                  hgen (m + n),
                reachRootN_succ_of_parent_live_ne_root τ root p x hp hroot
                  hgen m]
              simpa [liveChainN, liveParent, chainEndN, hp, hgen] using
                ih (p.dom, p.slot)
            · rw [reachRootN_succ_of_parent_dead_ne_root τ root p x hp hroot
                  hgen (m + n),
                reachRootN_succ_of_parent_dead_ne_root τ root p x hp hroot
                  hgen m]
              simp [liveChainN, liveParent, hp, hgen]

/-! ## Sequential marking and bounded saturation -/

/-- The specification's sequential marking iterate is exactly bounded
parent-chain reachability. This needs no acyclicity assumption: both sides
obey the same one-edge recurrence. -/
theorem iterMark_eq_reachRootN (τ : MachineState) (root : CapRef) (k : Nat)
    (d : DomainId) (s : Slot) :
    τ.iterMark root k d s = reachRootN τ root k (d, s) := by
  induction k generalizing d s with
  | zero => rfl
  | succ k ih =>
      rw [iterMark_succ]
      unfold MachineState.markStep reachRootN
      cases hp : τ.parentOf d s with
      | none => simpa [hp] using ih d s
      | some p => simp [ih]

/-- The kernel's `marks` function is bounded parent-chain reachability at
the machine's finite node count. -/
theorem marks_eq_reachRootN (τ : MachineState) (root : CapRef)
    (d : DomainId) (s : Slot) :
    τ.marks root d s =
      reachRootN τ root (numDomains * numSlots) (d, s) := by
  rw [marks_eq_iter, iterMark_eq_reachRootN]

/-- Once the generic finite-state marking bound has been reached, every
larger parent-chain horizon computes the same mark bit. -/
theorem reachRootN_eq_marks_of_nodeCount_le (τ : MachineState)
    (root : CapRef) (n : Nat) (hn : numDomains * numSlots ≤ n)
    (d : DomainId) (s : Slot) :
    reachRootN τ root n (d, s) = τ.marks root d s := by
  let N := numDomains * numSlots
  have hfix : τ.iterMark root (N + 1) = τ.iterMark root N := by
    rw [iterMark_succ]
    change τ.markStep root (τ.iterMark root (numDomains * numSlots)) =
      τ.iterMark root (numDomains * numSlots)
    rw [← marks_eq_iter, marks_fixpoint]
  rw [← iterMark_eq_reachRootN, marks_eq_iter,
    iterMark_stable τ root hfix n (by simpa [N] using hn)]

/-- The revoked root: the in-flight word's issuing domain and the handle
fields of its `rs1` register (what `rvInit`'s `rootEnc` samples). -/
def rvRoot (σ : Loom.Hw.St) : CapRef :=
  let e : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2)
  let hw := ((Hw.abs σ).doms e).reg
    (operandsOf (σ.regs "if_word" 32)).rs1
  { dom := e
    slot := finOfBv (by decide) (hw.extractLsb' 0 4)
    gen := hw.extractLsb' 4 8 }

/-- The three hidden pointer-jump vectors represent an abstract traversal
horizon `n` over `τ`, rooted at `root`. -/
def RvVectors (τ : MachineState) (root : CapRef) (n : Nat)
    (σ : Loom.Hw.St) : Prop :=
  ∀ (c : DomainId) (s : Slot),
    (σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 =
      if reachRootN τ root n (c, s) then 1#1 else 0#1)
    ∧ (σ.regs (Hw.rvV (Hw.nodeOf c s)) 1 =
      if liveChainN τ n (c, s) then 1#1 else 0#1)
    ∧ (liveChainN τ n (c, s) = true →
      σ.regs (Hw.rvJ (Hw.nodeOf c s)) 6 =
        BitVec.ofNat 6 (Hw.nodeOf
          (chainEndN τ n (c, s)).1
          (chainEndN τ n (c, s)).2).val)

/-- Two hardware states agree on the hidden revoke vector registers. -/
def RvRegsEq (σ σ' : Loom.Hw.St) : Prop :=
  ∀ (c : DomainId) (s : Slot),
    σ'.regs (Hw.rvR (Hw.nodeOf c s)) 1 =
      σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 ∧
    σ'.regs (Hw.rvV (Hw.nodeOf c s)) 1 =
      σ.regs (Hw.rvV (Hw.nodeOf c s)) 1 ∧
    σ'.regs (Hw.rvJ (Hw.nodeOf c s)) 6 =
      σ.regs (Hw.rvJ (Hw.nodeOf c s)) 6

/-- The vector relation transports across table-equivalent abstract states
and hardware states with identical hidden vectors. -/
theorem RvVectors.congr (τ τ' : MachineState) (root : CapRef) (n : Nat)
    (σ σ' : Loom.Hw.St) (ht : TablesEq τ τ') (hr : RvRegsEq σ σ')
    (hvec : RvVectors τ root n σ) :
    RvVectors τ' root n σ' := by
  intro c s
  have hv := hvec c s
  have hreg := hr c s
  refine ⟨?_, ?_, ?_⟩
  · rw [hreg.1, hv.1, reachRootN_congr τ τ' ht]
  · rw [hreg.2.1, hv.2.1, liveChainN_congr τ τ' ht]
  · intro hlive
    have hlive' : liveChainN τ n (c, s) = true := by
      rw [← liveChainN_congr τ τ' ht]
      exact hlive
    rw [hreg.2.2, hv.2.2 hlive', chainEndN_congr τ τ' ht]

/-- The packed root sampled by `rvInit` is the encoding of `rvRoot`. -/
theorem rvInitRootE_eval (σ : Loom.Hw.St) (hz : R0Zero σ) :
    rvInitRootE.eval σ = Hw.encRef (rvRoot σ) := by
  let E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2)
  have hmux : (Hw.muxFin (fun d => Hw.readReg d Hw.rs1E)
      (.reg 2 "if_dom")).eval σ = (Hw.readReg E Hw.rs1E).eval σ := by
    rw [muxFin_eval (by decide : 2 ^ 2 = numDomains)]
    rfl
  have hreg : (Hw.readReg E Hw.rs1E).eval σ =
      ((Hw.abs σ).doms E).reg
        (operandsOf (σ.regs "if_word" 32)).rs1 :=
    readReg_eval σ hz E Hw.rs1E
      (operandsOf (σ.regs "if_word" 32)).rs1 rfl
  have hdom : σ.regs "if_dom" 2 = BitVec.ofNat 2 E.val :=
    (bv2_lit_iff _ E).mpr rfl
  unfold rvInitRootE
  dsimp only
  change
    (((((Hw.muxFin (fun d => Hw.readReg d Hw.rs1E)
          (.reg 2 "if_dom")).eval σ).extractLsb' 4 8).setWidth 14) |||
      (((((Hw.muxFin (fun d => Hw.readReg d Hw.rs1E)
          (.reg 2 "if_dom")).eval σ).extractLsb' 0 4).setWidth 14 <<< 8) |||
        ((σ.regs "if_dom" 2).setWidth 14 <<< 12))) = _
  rw [hmux, hdom]
  change (Hw.encRefE (Hw.dLit E)
    (Hw.field (Hw.readReg E Hw.rs1E) 0 4)
    (Hw.field (Hw.readReg E Hw.rs1E) 4 8)).eval σ = _
  have henc : (Hw.encRefE (Hw.dLit E)
      (Hw.field (Hw.readReg E Hw.rs1E) 0 4)
      (Hw.field (Hw.readReg E Hw.rs1E) 4 8)).eval σ =
      Hw.encRef ⟨E, finOfBv (by decide)
        (BitVec.extractLsb' 0 4 ((Hw.readReg E Hw.rs1E).eval σ)),
        BitVec.extractLsb' 4 8 ((Hw.readReg E Hw.rs1E).eval σ)⟩ := by
    simpa [Hw.capSel] using
      (encRefE_sel_eval σ E (Hw.readReg E Hw.rs1E))
  rw [henc]
  unfold rvRoot
  rw [hreg]

/-- `rvInit`'s root bit is exactly one-step bounded root reachability. -/
theorem rvInit_run_r_semantic (m : Manifest) (σ acc : Loom.Hw.St)
    (hz : R0Zero σ) (c : DomainId) (s : Slot) :
    (Hw.rvInit.run σ acc).regs (Hw.rvR (Hw.nodeOf c s)) 1 =
      if reachRootN (Hw.abs σ) (rvRoot σ) 1 (c, s)
        then 1#1 else 0#1 := by
  rw [rvInit_run_r m]
  change
    ((rvInitPEx (Hw.nodeOf c s)).eval σ &&&
      (if (rvInitPEnc (Hw.nodeOf c s)).eval σ = rvInitRootE.eval σ
        then 1#1 else 0#1)) = _
  rw [rvInitRootE_eval σ hz]
  cases hp : (Hw.abs σ).parentOf c s with
  | none =>
      have hex : (rvInitPEx (Hw.nodeOf c s)).eval σ ≠ 1#1 := by
        intro hex
        let p := Hw.decRef ((rvInitPEnc (Hw.nodeOf c s)).eval σ)
        have hs := (rvInit_parent_some_iff σ c s p).mp ⟨hex, rfl⟩
        rw [hp] at hs
        contradiction
      rw [bv1_ne_one.mp hex]
      simp [reachRootN, hp]
  | some p =>
      have hpack := (rvInit_parent_packed_iff σ c s p).mpr hp
      rw [hpack.1, hpack.2]
      by_cases hroot : p = rvRoot σ
      · simp [reachRootN, hp, hroot]
      · have henc : Hw.encRef p ≠ Hw.encRef (rvRoot σ) := by
          intro h
          apply hroot
          have := congrArg Hw.decRef h
          simpa [decRef_encRef] using this
        simp [reachRootN, hp, hroot, henc]

/-- `rvInit`'s validity bit is exactly one live parent edge. -/
theorem rvInit_run_v_semantic (m : Manifest) (σ acc : Loom.Hw.St)
    (c : DomainId) (s : Slot) :
    (Hw.rvInit.run σ acc).regs (Hw.rvV (Hw.nodeOf c s)) 1 =
      if liveChainN (Hw.abs σ) 1 (c, s) then 1#1 else 0#1 := by
  rw [rvInit_run_v m]
  change
    ((rvInitPEx (Hw.nodeOf c s)).eval σ &&&
      (if (Hw.genAt (Hw.field (rvInitPEnc (Hw.nodeOf c s)) 8 6)).eval σ =
          (Hw.field (rvInitPEnc (Hw.nodeOf c s)) 0 8).eval σ
        then 1#1 else 0#1)) = _
  cases hp : (Hw.abs σ).parentOf c s with
  | none =>
      have hex : (rvInitPEx (Hw.nodeOf c s)).eval σ ≠ 1#1 := by
        intro hex
        let p := Hw.decRef ((rvInitPEnc (Hw.nodeOf c s)).eval σ)
        have hs := (rvInit_parent_some_iff σ c s p).mp ⟨hex, rfl⟩
        rw [hp] at hs
        contradiction
      rw [bv1_ne_one.mp hex]
      simp [liveChainN, liveParent, hp]
  | some p =>
      have hpack := (rvInit_parent_packed_iff σ c s p).mpr hp
      have hgenAt := rvInit_genAt_eval σ c s p hp
      have hgen := rvInit_parent_gen_eval σ c s p hp
      rw [hpack.1, hgenAt, hgen]
      by_cases hlive : p.gen = ((Hw.abs σ).doms p.dom).slotGen p.slot
      · simp [liveChainN, liveParent, hp, hlive]
      · have hne : ((Hw.abs σ).doms p.dom).slotGen p.slot ≠ p.gen :=
          Ne.symm hlive
        simp [liveChainN, liveParent, hp, hlive, hne]

/-- On a live initialized edge, `rvInit`'s jump word names its endpoint. -/
theorem rvInit_run_j_semantic (m : Manifest) (σ acc : Loom.Hw.St)
    (c : DomainId) (s : Slot) (p : CapRef)
    (hp : (Hw.abs σ).parentOf c s = some p) :
    (Hw.rvInit.run σ acc).regs (Hw.rvJ (Hw.nodeOf c s)) 6 =
      BitVec.ofNat 6 (Hw.nodeOf p.dom p.slot).val := by
  rw [rvInit_run_j m, rvInit_parent_index_eval σ c s p hp]

/-- The complete per-node semantic base case established by `rvInit`. -/
theorem rvInit_establishes_horizon_one (m : Manifest) (σ acc : Loom.Hw.St)
    (hz : R0Zero σ) (c : DomainId) (s : Slot) :
    ((Hw.rvInit.run σ acc).regs (Hw.rvR (Hw.nodeOf c s)) 1 =
      if reachRootN (Hw.abs σ) (rvRoot σ) 1 (c, s)
        then 1#1 else 0#1)
    ∧ ((Hw.rvInit.run σ acc).regs (Hw.rvV (Hw.nodeOf c s)) 1 =
      if liveChainN (Hw.abs σ) 1 (c, s) then 1#1 else 0#1)
    ∧ (liveChainN (Hw.abs σ) 1 (c, s) = true →
      (Hw.rvInit.run σ acc).regs (Hw.rvJ (Hw.nodeOf c s)) 6 =
        BitVec.ofNat 6 (Hw.nodeOf
          (chainEndN (Hw.abs σ) 1 (c, s)).1
          (chainEndN (Hw.abs σ) 1 (c, s)).2).val) := by
  refine ⟨rvInit_run_r_semantic m σ acc hz c s,
    rvInit_run_v_semantic m σ acc c s, ?_⟩
  intro hlive
  cases hp : (Hw.abs σ).parentOf c s with
  | none => simp [liveChainN, liveParent, hp] at hlive
  | some p =>
      by_cases hgen : p.gen = ((Hw.abs σ).doms p.dom).slotGen p.slot
      · simpa [chainEndN, liveParent, hp, hgen] using
          (rvInit_run_j_semantic m σ acc c s p hp)
      · simp [liveChainN, liveParent, hp, hgen] at hlive

/-- `rvInit` establishes the complete vector relation at horizon one. -/
theorem rvInit_establishes_vectors (m : Manifest) (σ acc : Loom.Hw.St)
    (hz : R0Zero σ) :
    RvVectors (Hw.abs σ) (rvRoot σ) 1 (Hw.rvInit.run σ acc) := by
  intro c s
  exact rvInit_establishes_horizon_one m σ acc hz c s

/-- One circuit pointer-jump round doubles the represented traversal
horizon. All right-hand sides of `rvStep` read the same pre-state `σ`. -/
theorem rvStep_doubles_vectors (m : Manifest) (τ : MachineState)
    (root : CapRef) (n : Nat) (σ acc : Loom.Hw.St)
    (hvec : RvVectors τ root n σ) :
    RvVectors τ root (n + n) (Hw.rvStep.run σ acc) := by
  intro c s
  let x : DomainId × Slot := (c, s)
  let y := chainEndN τ n x
  have hx := hvec c s
  have hy := hvec y.1 y.2
  have hR : (Hw.rvStep.run σ acc).regs (Hw.rvR (Hw.nodeOf c s)) 1 =
      if reachRootN τ root (n + n) x then 1#1 else 0#1 := by
    rw [rvStep_run_r m]
    by_cases hlive : liveChainN τ n x = true
    · have hj := hx.2.2 hlive
      have hmux := muxNode_eval_of_nodeOf
        (fun k : Hw.NodeId => Expr.reg 1 (Hw.rvR k))
        (.reg 6 (Hw.rvJ (Hw.nodeOf c s))) σ y.1 y.2 hj
      have hmux' :
          (Hw.muxFin (fun k : Hw.NodeId => Expr.reg 1 (Hw.rvR k))
            (.reg 6 (Hw.rvJ (Hw.nodeOf c s)))).eval σ =
            σ.regs (Hw.rvR (Hw.nodeOf y.1 y.2)) 1 := by
        simpa only [Expr.eval] using hmux
      rw [hmux', hx.1, hx.2.1, hy.1, reachRootN_add]
      by_cases hrx : reachRootN τ root n x = true <;>
        by_cases hry : reachRootN τ root n y = true <;>
        simp [x, y, hlive, hrx, hry]
    · have hlive0 : liveChainN τ n x = false :=
        Bool.eq_false_of_not_eq_true hlive
      rw [hx.1, hx.2.1, reachRootN_add]
      simp [x, hlive0]
  have hV : (Hw.rvStep.run σ acc).regs (Hw.rvV (Hw.nodeOf c s)) 1 =
      if liveChainN τ (n + n) x then 1#1 else 0#1 := by
    rw [rvStep_run_v m]
    by_cases hlive : liveChainN τ n x = true
    · have hj := hx.2.2 hlive
      have hmux := muxNode_eval_of_nodeOf
        (fun k : Hw.NodeId => Expr.reg 1 (Hw.rvV k))
        (.reg 6 (Hw.rvJ (Hw.nodeOf c s))) σ y.1 y.2 hj
      have hmux' :
          (Hw.muxFin (fun k : Hw.NodeId => Expr.reg 1 (Hw.rvV k))
            (.reg 6 (Hw.rvJ (Hw.nodeOf c s)))).eval σ =
            σ.regs (Hw.rvV (Hw.nodeOf y.1 y.2)) 1 := by
        simpa only [Expr.eval] using hmux
      rw [hmux', hx.2.1, hy.2.1, liveChainN_add]
      by_cases hliveY : liveChainN τ n y = true <;>
        simp [x, y, hlive, hliveY]
    · have hlive0 : liveChainN τ n x = false :=
        Bool.eq_false_of_not_eq_true hlive
      rw [hx.2.1, liveChainN_add]
      simp [x, hlive0]
  refine ⟨hR, hV, ?_⟩
  intro hdouble
  have hdouble' : liveChainN τ (n + n) x = true := by
    simpa [x] using hdouble
  rw [liveChainN_add] at hdouble'
  change (liveChainN τ n x && liveChainN τ n y) = true at hdouble'
  have hlive : liveChainN τ n x = true :=
    (Bool.and_eq_true_iff.mp hdouble').1
  have hliveY : liveChainN τ n y = true :=
    (Bool.and_eq_true_iff.mp hdouble').2
  have hj := hx.2.2 hlive
  have hmux := muxNode_eval_of_nodeOf
    (fun k : Hw.NodeId => Expr.reg 6 (Hw.rvJ k))
    (.reg 6 (Hw.rvJ (Hw.nodeOf c s))) σ y.1 y.2 hj
  have hmux' :
      (Hw.muxFin (fun k : Hw.NodeId => Expr.reg 6 (Hw.rvJ k))
        (.reg 6 (Hw.rvJ (Hw.nodeOf c s)))).eval σ =
        σ.regs (Hw.rvJ (Hw.nodeOf y.1 y.2)) 6 := by
    simpa only [Expr.eval] using hmux
  rw [rvStep_run_j m, hmux', hy.2.2 hliveY]
  rw [chainEndN_add]

/-- The ISA table fixes the revoke latency, hence the pointer-doubling
budget, at 24 cycles. -/
theorem revokeCost_eq_24 : revokeCost = 24 := by
  decide +kernel

/-- On the first revoke countdown cycle, `coreAct` selects `rvInit` after
decrementing `if_cl` in the accumulator. -/
theorem coreAct_run_revoke_init_eq (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat = revokeCost) :
    (Hw.coreAct m).run σ acc =
      Hw.rvInit.run σ
        ((Act.write 8 "if_cl" (.sub (.reg 8 "if_cl") (.lit 1))).run σ acc) := by
  have hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat := by
    rw [hcl, revokeCost_eq_24]
    omega
  rw [coreAct_run_countdown_eq m σ acc hifv hcl2]
  have his : (Hw.isMn "cap_revoke").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "cap_revoke" = 18#6).symm
  have hclbv : σ.regs "if_cl" 8 = BitVec.ofNat 8 revokeCost := by
    apply BitVec.eq_of_toNat_eq
    rw [hcl, BitVec.toNat_ofNat, revokeCost_eq_24]
  have heq : (Expr.eq (.reg 8 "if_cl")
      (.lit (BitVec.ofNat 8 revokeCost))).eval σ = 1#1 :=
    eqE_eval _ _ σ |>.mpr hclbv
  simp [Act.run, his, heq]

/-- On every later non-retiring revoke countdown cycle, `coreAct` selects
one `rvStep` pointer-doubling round. -/
theorem coreAct_run_revoke_step_eq (m : Manifest) (σ acc : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat)
    (hcllt : (σ.regs "if_cl" 8).toNat < revokeCost) :
    (Hw.coreAct m).run σ acc =
      Hw.rvStep.run σ
        ((Act.write 8 "if_cl" (.sub (.reg 8 "if_cl") (.lit 1))).run σ acc) := by
  rw [coreAct_run_countdown_eq m σ acc hifv hcl2]
  have his : (Hw.isMn "cap_revoke").eval σ = 1#1 := by
    rw [isMn_eval, hopc]
    exact (by decide +kernel : Hw.opcodeOf "cap_revoke" = 18#6).symm
  have hne : (Expr.eq (.reg 8 "if_cl")
      (.lit (BitVec.ofNat 8 revokeCost))).eval σ ≠ 1#1 := by
    intro he
    have h := (eqE_eval _ _ σ).mp he
    have ht := congrArg BitVec.toNat h
    change (σ.regs "if_cl" 8).toNat =
      (BitVec.ofNat 8 revokeCost).toNat at ht
    rw [BitVec.toNat_ofNat, revokeCost_eq_24] at ht
    rw [revokeCost_eq_24] at hcllt
    omega
  simp [Act.run, his, bv1_ne_one.mp hne]

/-- The first revoke countdown core action establishes the vector base case. -/
theorem coreAct_revoke_init_establishes_vectors (m : Manifest)
    (σ acc : Loom.Hw.St) (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat = revokeCost) :
    RvVectors (Hw.abs σ) (rvRoot σ) 1 ((Hw.coreAct m).run σ acc) := by
  rw [coreAct_run_revoke_init_eq m σ acc hifv hopc hcl]
  exact rvInit_establishes_vectors m σ _ hz

/-- A later revoke countdown core action doubles the represented horizon. -/
theorem coreAct_revoke_step_doubles_vectors (m : Manifest)
    (τ : MachineState) (root : CapRef) (n : Nat) (σ acc : Loom.Hw.St)
    (hvec : RvVectors τ root n σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat)
    (hcllt : (σ.regs "if_cl" 8).toNat < revokeCost) :
    RvVectors τ root (n + n) ((Hw.coreAct m).run σ acc) := by
  rw [coreAct_run_revoke_step_eq m σ acc hifv hopc hcl2 hcllt]
  exact rvStep_doubles_vectors m τ root n σ _ hvec

/-- Refill supplies the accumulator before `coreAct`; mover and tick frame
all hidden revoke-vector registers afterward. -/
theorem cycle_rvRegsEq_coreAct (m : Manifest) (σ : Loom.Hw.St) :
    RvRegsEq
      ((Hw.coreAct m).run σ ((Hw.refillAct m).run σ σ))
      ((Hw.core m).cycle σ) := by
  intro c s
  rw [core_cycle_unfold]
  refine ⟨?_, ?_, ?_⟩
  · rw [frame (show (Hw.rvR (Hw.nodeOf c s), 1) ∉ Hw.tickAct.regWrites by
      simp [Hw.tickAct, Act.regWrites, Hw.rvR])]
    rw [run_WritesPrefixed (by
      fin_cases c <;> fin_cases s <;> decide +kernel) 1 _ mover_prefixed]
  · rw [frame (show (Hw.rvV (Hw.nodeOf c s), 1) ∉ Hw.tickAct.regWrites by
      simp [Hw.tickAct, Act.regWrites, Hw.rvV])]
    rw [run_WritesPrefixed (by
      fin_cases c <;> fin_cases s <;> decide +kernel) 1 _ mover_prefixed]
  · rw [frame (show (Hw.rvJ (Hw.nodeOf c s), 6) ∉ Hw.tickAct.regWrites by
      simp [Hw.tickAct, Act.regWrites, Hw.rvJ])]
    rw [run_WritesPrefixed (by
      fin_cases c <;> fin_cases s <;> decide +kernel) 6 _ mover_prefixed]

/-- A non-vector, non-countdown register framed by refill, core countdown,
mover, and tick is unchanged by the full hardware cycle. -/
theorem cycle_reg_countdown (m : Manifest) (σ : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat)
    (rn : String) (w : Nat)
    (hrv : rn.startsWith "rv_" = false)
    (hmov : rn.startsWith "mov_" = false)
    (hcl : rn ≠ "if_cl") (hcyc : ¬(rn = "cycle" ∧ w = 32))
    (hrefill : (rn, w) ∉
      ([ ("d0_budget", 32), ("d0_rctr", 32),
         ("d1_budget", 32), ("d1_rctr", 32),
         ("d2_budget", 32), ("d2_rctr", 32),
         ("d3_budget", 32), ("d3_rctr", 32) ] :
        List (String × Nat))) :
    ((Hw.core m).cycle σ).regs rn w = σ.regs rn w := by
  rw [core_cycle_unfold]
  rw [frame (show (rn, w) ∉ Hw.tickAct.regWrites by
    intro hm
    simp only [Hw.tickAct, Act.regWrites, List.mem_singleton,
      Prod.mk.injEq] at hm
    exact hcyc hm)]
  rw [run_WritesPrefixed hmov w _ mover_prefixed]
  rw [countdown_regs m σ _ hifv hcl2 rn w hrv hcl]
  exact refill_pres m σ hrefill

/-- The revoked root sampled from `if_dom`, `if_word`, and the issuing
domain's register file is stable throughout a countdown cycle. -/
theorem rvRoot_cycle_countdown (m : Manifest) (σ : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    rvRoot ((Hw.core m).cycle σ) = rvRoot σ := by
  have hdom : ((Hw.core m).cycle σ).regs "if_dom" 2 =
      σ.regs "if_dom" 2 :=
    cycle_reg_countdown m σ hifv hcl2 "if_dom" 2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have hword : ((Hw.core m).cycle σ).regs "if_word" 32 =
      σ.regs "if_word" 32 :=
    cycle_reg_countdown m σ hifv hcl2 "if_word" 32
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have hreg : ∀ (d : DomainId) (r : RegId),
      ((Hw.core m).cycle σ).regs (Hw.dreg d r) 32 =
        σ.regs (Hw.dreg d r) 32 := by
    intro d r
    apply cycle_reg_countdown m σ hifv hcl2 (Hw.dreg d r) 32
    · fin_cases d <;> fin_cases r <;> decide +kernel
    · fin_cases d <;> fin_cases r <;> decide +kernel
    · fin_cases d <;> fin_cases r <;> decide +kernel
    · fin_cases d <;> fin_cases r <;> decide +kernel
    · fin_cases d <;> fin_cases r <;> decide +kernel
  unfold rvRoot
  rw [hdom, hword]
  simp only [Hw.abs, Hw.absDom, DomainState.reg]
  rw [hreg]

/-- Through a hardware countdown square, the abstraction's capability
tables are unchanged. -/
theorem tablesEq_abs_cycle_countdown (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    TablesEq (Hw.abs σ) (Hw.abs ((Hw.core m).cycle σ)) := by
  let fl : InFlight :=
    { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
      word := σ.regs "if_word" 32
      cyclesLeft := (σ.regs "if_cl" 8).toNat }
  have hfl : (Hw.abs σ).inflight = some fl := by
    show Hw.absInflight σ = some fl
    rw [Hw.absInflight, if_pos (show σ.regs "if_v" 1 = 1 from hifv)]
  rw [square_countdown m hwf hfit σ hsync hifv hcl2]
  exact tablesEq_step_countdown m (Hw.abs σ) fl hfl hcl2

/-- The first full revoke countdown cycle establishes horizon-one vectors
against the post-cycle abstraction. -/
theorem cycle_revoke_init_establishes_vectors (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat = revokeCost) :
    RvVectors (Hw.abs ((Hw.core m).cycle σ))
      (rvRoot ((Hw.core m).cycle σ)) 1 ((Hw.core m).cycle σ) := by
  have hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat := by
    rw [hcl, revokeCost_eq_24]
    omega
  have hbase := coreAct_revoke_init_establishes_vectors m σ
    ((Hw.refillAct m).run σ σ) hz hifv hopc hcl
  have ht := tablesEq_abs_cycle_countdown m hwf hfit σ hsync hifv hcl2
  have htrans := RvVectors.congr (Hw.abs σ)
    (Hw.abs ((Hw.core m).cycle σ)) (rvRoot σ) 1 _ _ ht
    (cycle_rvRegsEq_coreAct m σ) hbase
  rw [rvRoot_cycle_countdown m σ hifv hcl2]
  exact htrans

/-- Every later full revoke countdown cycle doubles the represented horizon
against the post-cycle abstraction. -/
theorem cycle_revoke_step_doubles_vectors (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St) (n : Nat)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hvec : RvVectors (Hw.abs σ) (rvRoot σ) n σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat)
    (hcllt : (σ.regs "if_cl" 8).toNat < revokeCost) :
    RvVectors (Hw.abs ((Hw.core m).cycle σ))
      (rvRoot ((Hw.core m).cycle σ)) (n + n) ((Hw.core m).cycle σ) := by
  have hdouble := coreAct_revoke_step_doubles_vectors m
    (Hw.abs σ) (rvRoot σ) n σ ((Hw.refillAct m).run σ σ)
    hvec hifv hopc hcl2 hcllt
  have ht := tablesEq_abs_cycle_countdown m hwf hfit σ hsync hifv hcl2
  have htrans := RvVectors.congr (Hw.abs σ)
    (Hw.abs ((Hw.core m).cycle σ)) (rvRoot σ) (n + n) _ _ ht
    (cycle_rvRegsEq_coreAct m σ) hdouble
  rw [rvRoot_cycle_countdown m σ hifv hcl2]
  exact htrans

/-- The countdown latch's full-cycle value is the pre-cycle value minus one. -/
theorem cycle_ifcl_countdown (m : Manifest) (σ : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    ((Hw.core m).cycle σ).regs "if_cl" 8 = σ.regs "if_cl" 8 - 1 := by
  rw [core_cycle_unfold]
  rw [frame (show (("if_cl", 8) : String × Nat) ∉ Hw.tickAct.regWrites by
    decide +kernel)]
  rw [run_WritesPrefixed (by decide +kernel) 8 _ mover_prefixed]
  exact countdown_ifcl m σ _ hifv hcl2

/-- `if_v` and `if_word`, which form the revoke guard, are stable on a
countdown cycle. -/
theorem cycle_ifv_ifword_countdown (m : Manifest) (σ : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    ((Hw.core m).cycle σ).regs "if_v" 1 = σ.regs "if_v" 1 ∧
    ((Hw.core m).cycle σ).regs "if_word" 32 = σ.regs "if_word" 32 := by
  constructor
  · exact cycle_reg_countdown m σ hifv hcl2 "if_v" 1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact cycle_reg_countdown m σ hifv hcl2 "if_word" 32
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem ifv_notin_retireFor (E : DomainId) :
    (("if_v", 1) : String × Nat) ∉ (Hw.retireFor E).regWrites := by
  fin_cases E <;> decide +kernel

/-- A retiring core cycle clears the in-flight-valid latch. Refill, the
Mover, and tick do not write it, and the selected retirement circuit runs
after the retirement skeleton's unconditional clear. -/
theorem cycle_ifv_retire_zero (m : Manifest) (σ : Loom.Hw.St)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2) :
    ((Hw.core m).cycle σ).regs "if_v" 1 = 0#1 := by
  rw [core_cycle_unfold]
  rw [frame (show (("if_v", 1) : String × Nat) ∉ Hw.tickAct.regWrites by
    decide +kernel)]
  rw [run_WritesPrefixed (by decide +kernel) 1 _ mover_prefixed]
  rw [coreAct_run_retire_eq m σ _ hifv hcl]
  let E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2)
  rw [retireAct_run_regs σ _ E rfl "if_v" 1]
  rw [frame (ifv_notin_retireFor E)]
  rfl

/-- Starting from an idle abstract core, any revoke that appears in flight
after one step is freshly issued at the instruction's full WCET. In
particular it cannot already satisfy the post-initialization `RvSync`
guard. -/
theorem step_idle_revoke_full_cost (m : Manifest) (τ : MachineState)
    (hidle : τ.inflight = none) (fl : InFlight)
    (hfl : (step m τ).inflight = some fl)
    (hopc : Machines.Lnp64u.sig.opcodeOf fl.word = 18#6) :
    fl.cyclesLeft = revokeCost := by
  have hcore : (corePhase m (refillPhase m τ)).inflight = some fl := by
    rw [← Wip.step_inflight_reduce m τ]
    exact hfl
  have hrefill : (refillPhase m τ).inflight = none := by
    rw [Wip.refillPhase_inflight, hidle]
  rcases corePhase_cases m (refillPhase m τ) with
      hcount | hretire | hstall | hfault | hburn | hissue
  · obtain ⟨fl', hsome, -⟩ := hcount
    rw [hrefill] at hsome
    cases hsome
  · obtain ⟨fl', hsome, -⟩ := hretire
    rw [hrefill] at hsome
    cases hsome
  · rw [hstall.2.2, hrefill] at hcore
    cases hcore
  · obtain ⟨e, f, _, _, hhalt⟩ := hfault
    rw [hhalt, haltWith, haltDom_inflight, hrefill] at hcore
    cases hcore
  · obtain ⟨e, w, instr, _, _, _, _, _, _, hset⟩ := hburn
    rw [hset, setDom_inflight, hrefill] at hcore
    cases hcore
  · obtain ⟨e, w, instr, _, _, _, hdec, _, hissued, _⟩ := hissue
    rw [hissued] at hcore
    injection hcore with hfl'
    subst fl
    have hfind : isa.find? (fun d => d.opcode == (18#6 : BitVec 6)) =
        some (Machines.Lnp64u.Isa.system.get ⟨2, by decide⟩) := by
      rfl
    rw [decode_eq_find, hopc, hfind] at hdec
    injection hdec with hi
    subst instr
    rw [revokeCost_eq_24]
    rfl

private theorem bv8_sub_one_toNat (x : BitVec 8) (h : 1 ≤ x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub]
  have hlt := x.isLt
  change (2 ^ 8 - 1 + x.toNat) % 2 ^ 8 = x.toNat - 1
  omega

/-- The doubling rounds completed at pre-cycle countdown value `cl`. -/
def rvRounds (cl : Nat) : Nat := revokeCost - 1 - cl

/-- Decrementing a later-round countdown advances the round number by one. -/
theorem rvRounds_pred_succ (cl : Nat) (h2 : 2 ≤ cl)
    (hlt : cl < revokeCost) :
    rvRounds (cl - 1) = rvRounds cl + 1 := by
  unfold rvRounds
  rw [revokeCost_eq_24] at hlt ⊢
  omega

/-- The horizon after a later countdown cycle is twice its pre-cycle
horizon. -/
theorem rvHorizon_pred_double (cl : Nat) (h2 : 2 ≤ cl)
    (hlt : cl < revokeCost) :
    2 ^ rvRounds (cl - 1) =
      2 ^ rvRounds cl + 2 ^ rvRounds cl := by
  rw [rvRounds_pred_succ cl h2 hlt, pow_succ]
  omega

/-- At either retirement countdown value, the completed doubling horizon
dominates all 64 capability nodes. -/
theorem nodeCount_le_revokeRetireHorizon (cl : Nat) (hcl : cl < 2) :
    numDomains * numSlots ≤ 2 ^ rvRounds cl := by
  interval_cases cl <;>
    decide +kernel

/-- **The rv-coupling invariant** (statement; preservation is the tier-4
obligation). With an in-flight `cap_revoke` past its first countdown
cycle, the hidden mark-engine vectors are `2^k`-round descendant marking
from the revoked root on the abstraction. -/
def RvSync (σ : Loom.Hw.St) : Prop :=
  σ.regs "if_v" 1 = 1#1 →
  (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6 →
  (σ.regs "if_cl" 8).toNat < revokeCost →
  RvVectors (Hw.abs σ) (rvRoot σ)
    (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) σ

/-- `RvSync` is preserved by every non-retiring countdown cycle. The first
revoke cycle establishes horizon one; every later cycle doubles it. -/
theorem rvSync_cycle_countdown (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ) (hrv : RvSync σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat) :
    RvSync ((Hw.core m).cycle σ) := by
  intro _hifv' hopc' hcllt'
  have hguard := cycle_ifv_ifword_countdown m σ hifv hcl2
  have hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6 := by
    rw [← hguard.2]
    exact hopc'
  have hclreg := cycle_ifcl_countdown m σ hifv hcl2
  have hclnat : (((Hw.core m).cycle σ).regs "if_cl" 8).toNat =
      (σ.regs "if_cl" 8).toNat - 1 := by
    rw [hclreg, bv8_sub_one_toNat _ (by omega)]
  have hcle : (σ.regs "if_cl" 8).toNat ≤ revokeCost := by
    rw [hclnat] at hcllt'
    rw [revokeCost_eq_24] at hcllt' ⊢
    omega
  by_cases hinit : (σ.regs "if_cl" 8).toNat = revokeCost
  · have hv := cycle_revoke_init_establishes_vectors m hwf hfit σ
      hsync hz hifv hopc hinit
    change RvVectors (Hw.abs ((Hw.core m).cycle σ))
      (rvRoot ((Hw.core m).cycle σ))
      (2 ^ rvRounds (((Hw.core m).cycle σ).regs "if_cl" 8).toNat)
      ((Hw.core m).cycle σ)
    rw [hclnat, hinit, revokeCost_eq_24]
    simpa [rvRounds, revokeCost_eq_24] using hv
  · have hcllt : (σ.regs "if_cl" 8).toNat < revokeCost := by
      rw [revokeCost_eq_24] at hcle hinit ⊢
      omega
    have hvec := hrv hifv hopc hcllt
    have hv := cycle_revoke_step_doubles_vectors m hwf hfit σ
      (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) hsync hvec
      hifv hopc hcl2 hcllt
    change RvVectors (Hw.abs ((Hw.core m).cycle σ))
      (rvRoot ((Hw.core m).cycle σ))
      (2 ^ rvRounds (((Hw.core m).cycle σ).regs "if_cl" 8).toNat)
      ((Hw.core m).cycle σ)
    rw [hclnat, rvHorizon_pred_double _ hcl2 hcllt]
    exact hv

/-- `RvSync` is preserved by an arbitrary core cycle. Active countdown
cycles initialize or advance the bounded mark engine; retirement clears
the latch; and an idle cycle can only introduce a freshly issued revoke at
`revokeCost`, where the invariant's strict-cost guard is still false. -/
theorem rvSync_cycle (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hrun : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2)
    (hz : R0Zero σ) (hrv : RvSync σ) :
    RvSync ((Hw.core m).cycle σ) := by
  by_cases hifv : σ.regs "if_v" 1 = 1#1
  · by_cases hcl2 : 2 ≤ (σ.regs "if_cl" 8).toNat
    · exact rvSync_cycle_countdown m hwf hfit σ hsync hz hrv hifv hcl2
    · intro hifv' _ _
      have hzero := cycle_ifv_retire_zero m σ hifv (by omega)
      rw [hzero] at hifv'
      contradiction
  · have hsquare : Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
      cases hs : schedule m (refillPhase m (Hw.abs σ)) with
      | none =>
          exact square_idle_stall m hwf hfit σ hsync hrun hifv hs
      | some e =>
          exact square_idle_issue m hwf hfit σ hsync hrun hifv e hs
    intro hifv' hopc' hcllt'
    let fl : InFlight :=
      { dom := finOfBv (by decide)
          (((Hw.core m).cycle σ).regs "if_dom" 2)
        word := ((Hw.core m).cycle σ).regs "if_word" 32
        cyclesLeft := (((Hw.core m).cycle σ).regs "if_cl" 8).toNat }
    have habsPost : (Hw.abs ((Hw.core m).cycle σ)).inflight = some fl := by
      simpa [fl] using absInflight_some ((Hw.core m).cycle σ) hifv'
    have hstep : (step m (Hw.abs σ)).inflight = some fl := by
      rw [← hsquare]
      exact habsPost
    have habsIdle : (Hw.abs σ).inflight = none := by
      show Hw.absInflight σ = none
      rw [Hw.absInflight,
        if_neg (show ¬ σ.regs "if_v" 1 = 1 from hifv)]
    have hcost := step_idle_revoke_full_cost m (Hw.abs σ) (fl := fl)
      habsIdle hstep
      (show Machines.Lnp64u.sig.opcodeOf fl.word = 18#6 from hopc')
    change (((Hw.core m).cycle σ).regs "if_cl" 8).toNat = revokeCost at hcost
    omega

/-- At retirement, `RvSync` turns every hidden `rv_r` bit into the exact
kernel `marks` bit consumed by `destroyMarked`. -/
theorem rvR_eq_marks_of_sync (σ : Loom.Hw.St) (hrv : RvSync σ)
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (c : DomainId) (s : Slot) :
    σ.regs (Hw.rvR (Hw.nodeOf c s)) 1 =
      if (Hw.abs σ).marks (rvRoot σ) c s then 1#1 else 0#1 := by
  have hlt : (σ.regs "if_cl" 8).toNat < revokeCost := by
    rw [revokeCost_eq_24]
    omega
  have hr := (hrv hifv hopc hlt c s).1
  rw [reachRootN_eq_marks_of_nodeCount_le (Hw.abs σ) (rvRoot σ)
    (2 ^ rvRounds (σ.regs "if_cl" 8).toNat)
    (nodeCount_le_revokeRetireHorizon _ hcl) c s] at hr
  exact hr

/- The convergence chain is complete: `rvInit` establishes horizon one,
`rvStep` doubles it, `rvSync_cycle` handles all cycle boundaries, and
`rvR_eq_marks_of_sync` exposes the saturated vector as the kernel `marks`
fixpoint consumed by the revoke retirement arm. -/

end Machines.Lnp64u.Theorems.RMC
