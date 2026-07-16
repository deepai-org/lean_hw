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
  simp only [List.map_append, List.map_flatMap, List.map_map] at h
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

private theorem seqAll_actions_frame {I : Type} {w : Nat}
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

private theorem seqAll_actions_at {I : Type} {w : Nat}
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

/-- With no parent edge, no bounded marking horizon can reach the root. -/
theorem reachRootN_of_parent_none (τ : MachineState) (root : CapRef)
    (x : DomainId × Slot) (hx : τ.parentOf x.1 x.2 = none) (n : Nat) :
    reachRootN τ root n x = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reachRootN, hx, ih]

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

/-- The doubling rounds completed at pre-cycle countdown value `cl`. -/
def rvRounds (cl : Nat) : Nat := revokeCost - 1 - cl

/-- The ISA table fixes the revoke latency, hence the pointer-doubling
budget, at 24 cycles. -/
theorem revokeCost_eq_24 : revokeCost = 24 := by
  decide +kernel

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
  ∀ (c : DomainId) (s : Slot),
    (σ.regs (Hw.rvR (Hw.nodeOf c s)) 1
      = if reachRootN (Hw.abs σ) (rvRoot σ)
            (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s)
        then 1#1 else 0#1)
    ∧ (σ.regs (Hw.rvV (Hw.nodeOf c s)) 1
      = if liveChainN (Hw.abs σ)
            (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s)
        then 1#1 else 0#1)
    ∧ (liveChainN (Hw.abs σ)
        (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s) = true →
      σ.regs (Hw.rvJ (Hw.nodeOf c s)) 6
        = BitVec.ofNat 6 (Hw.nodeOf
            (chainEndN (Hw.abs σ)
              (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s)).1
            (chainEndN (Hw.abs σ)
              (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s)).2).val)

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

/- Deferred obligations (tier 4, NEXTSTEPS §1.6):

1. `rvInit` establishes `RvSync` at `k = 0` (chains of length < 1:
   exactly the direct parent-is-root test `rvInit` computes; `2^0`-step
   chain = one live edge; `rv_j` = the parent's node index).
2. `rvStep` doubles: `reachRootN (2^k) ∨ (liveChainN (2^k) ∧
   reachRootN (2^k) at chainEndN (2^k)) = reachRootN (2^(k+1))`, and
   likewise for `liveChainN`/`chainEndN` composition.
3. Frame preservation by refill/mover/tick and vacuity at issue/retire.
4. The retirement arm uses the proved `rvR_eq_marks_of_sync` bridge so
   `revKilled = marksAt` reads the kernel fixpoint exactly.
-/

end Machines.Lnp64u.Theorems.RMC
