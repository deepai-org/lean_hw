-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Epoch.Engine
import Machines.Epoch.Protocol
import Machines.Epoch.Bounded
import Loom.Hw.Footprint
import Loom.Core.Bounded

/-!
# Layer 3 — `epochengine` refines the mechanized §3 protocol

Appendix F makes the mechanized protocol spec the normative behavioral
definition and requires each generation's RTL to discharge a *refinement
obligation* against it. This file is that obligation, for machine 1
("epoch coherence — bump, broadcast, ack reduction"):
`Machines/Epoch/Engine.lean`'s Loom `Design` refines
`Machines/Epoch/Protocol.lean`'s frozen §3 protocol, and §3's safety
theorems become theorems about the hardware.

What is here, in the order it is built:

1. **Frame lemmas + a cycle-level case analysis.** One cycle is the six read
   latches, the two check units, then the bump sequencer (D9: all reads are
   pre-cycle). `cyc_idle`/`cyc_rd`/`cyc_up`/`cyc_ack_*`/`cyc_ret`/`cyc_junk`
   evaluate `Design.cycleOpen` in each state of the sequencer's encoding —
   including the states outside it, where the engine must (and does) sit
   still.
2. **The abstraction function** `abs`: cells and replicas read straight out
   of the four BRAM banks, `pending` reconstructed from the sequencer.
3. **The stuttering simulation** `sim` (D17), whose square is
   `square_cycle`: every clock cycle, from every state, under **every** input
   valuation, is either a stutter or exactly one §3 event — `bump` at
   `B_UP → B_ACK`, `ack k` at each `B_ACK`, `bumpReturn` at `B_RET`.
4. **Transport** (`invariant_pullback`): `Protocol.Inv` and the T-E1/T-E2/
   T-E3/T-E6 analogues, as statements about every reachable state of the
   design, quantified over all input traces — i.e. over all core behaviour,
   adversarial included. The check units' answer is tied to `Protocol.
   useLocal` by `chk_resp_0`/`chk_resp_1` (§3's precedence in the RTL's own
   mux cone), and `emitted_cycleOpen` carries the whole thing to the emitted
   µVerilog.
5. **D28**: the spec bound of `Machines/Epoch/Bounded.lean` expressed in
   CLOCK CYCLES, both as the free transported bound (15) and as the exact one
   (4), with `EPOCH_SPEC.md` deviation F8 explaining how each relates to
   Layer 2's measured 5.

`EPOCH_SPEC.md` §"Deviations (Layer 3)" records every departure; F1 and F4
are the ones to read first — there is no hypothesis about core behaviour
anywhere in this file, which is what §"Consequence bound NOW" demands.

No `sorry`, no `native_decide`, no new axioms.
-/

namespace Machines.Epoch.Refines

open Loom Loom.Hw

/-! ## Frame lemmas over a rule list -/

theorem foldl_regs_notin (σ : Hw.St) (n : String) (w : Nat) :
    ∀ (rs : List Rule) (acc : Hw.St),
      (∀ r ∈ rs, (n, w) ∉ r.body.regWrites) →
      ((rs.foldl (fun acc r => r.body.run σ acc) acc).regs n w) = acc.regs n w := by
  intro rs
  induction rs with
  | nil => intro acc _; rfl
  | cons r rs ih =>
    intro acc h
    have hr : (n, w) ∉ r.body.regWrites := h r (by simp)
    have := ih (r.body.run σ acc) (fun r' hr' => h r' (by simp [hr']))
    simpa [Act.run_regs_notin n w r.body hr σ acc] using this

theorem foldl_mems_notin (σ : Hw.St) (mn : String) :
    ∀ (rs : List Rule) (acc : Hw.St),
      (∀ r ∈ rs, mn ∉ r.body.memWrites) →
      ∀ (a w : Nat),
      ((rs.foldl (fun acc r => r.body.run σ acc) acc).mems mn a w) = acc.mems mn a w := by
  intro rs
  induction rs with
  | nil => intro acc _ a w; rfl
  | cons r rs ih =>
    intro acc h a w
    have hr : mn ∉ r.body.memWrites := h r (by simp)
    have := ih (r.body.run σ acc) (fun r' hr' => h r' (by simp [hr'])) a w
    simpa [Act.run_mems_notin mn r.body hr σ acc] using this

/-! ## Name normalisation

The engine builds its signal names by interpolation (`Engine.vn`, `Engine.rn`,
`Engine.replMem`); these `rfl` lemmas put them in literal form so that the
name-based `RegEnv.set` / `MemEnv.set` lookups reduce. -/

@[simp] theorem vn_0_st : Engine.vn 0 "st" = "c0_st" := rfl
@[simp] theorem vn_0_a : Engine.vn 0 "a" = "c0_a" := rfl
@[simp] theorem vn_0_e : Engine.vn 0 "e" = "c0_e" := rfl
@[simp] theorem vn_0_f : Engine.vn 0 "f" = "c0_f" := rfl
@[simp] theorem vn_0_flags_q : Engine.vn 0 "flags_q" = "c0_flags_q" := rfl
@[simp] theorem vn_0_repl_q : Engine.vn 0 "repl_q" = "c0_repl_q" := rfl
@[simp] theorem vn_0_busy : Engine.vn 0 "busy" = "c0_busy" := rfl
@[simp] theorem rn_0_valid : Engine.rn 0 "valid" = "req0_valid" := rfl
@[simp] theorem rn_0_op : Engine.rn 0 "op" = "req0_op" := rfl
@[simp] theorem rn_0_cell : Engine.rn 0 "cell" = "req0_cell" := rfl
@[simp] theorem rn_0_epoch : Engine.rn 0 "epoch" = "req0_epoch" := rfl
@[simp] theorem rn_0_policy : Engine.rn 0 "policy" = "req0_policy" := rfl
@[simp] theorem rn_0_flags : Engine.rn 0 "flags" = "req0_flags" := rfl
@[simp] theorem replMem_0 : Engine.replMem 0 = "repl0" := rfl
@[simp] theorem resp_valid_0 : (s!"resp{0}_valid" : String) = "resp0_valid" := rfl
@[simp] theorem resp_code_0 : (s!"resp{0}_code" : String) = "resp0_code" := rfl
@[simp] theorem vn_1_st : Engine.vn 1 "st" = "c1_st" := rfl
@[simp] theorem vn_1_a : Engine.vn 1 "a" = "c1_a" := rfl
@[simp] theorem vn_1_e : Engine.vn 1 "e" = "c1_e" := rfl
@[simp] theorem vn_1_f : Engine.vn 1 "f" = "c1_f" := rfl
@[simp] theorem vn_1_flags_q : Engine.vn 1 "flags_q" = "c1_flags_q" := rfl
@[simp] theorem vn_1_repl_q : Engine.vn 1 "repl_q" = "c1_repl_q" := rfl
@[simp] theorem vn_1_busy : Engine.vn 1 "busy" = "c1_busy" := rfl
@[simp] theorem rn_1_valid : Engine.rn 1 "valid" = "req1_valid" := rfl
@[simp] theorem rn_1_op : Engine.rn 1 "op" = "req1_op" := rfl
@[simp] theorem rn_1_cell : Engine.rn 1 "cell" = "req1_cell" := rfl
@[simp] theorem rn_1_epoch : Engine.rn 1 "epoch" = "req1_epoch" := rfl
@[simp] theorem rn_1_policy : Engine.rn 1 "policy" = "req1_policy" := rfl
@[simp] theorem rn_1_flags : Engine.rn 1 "flags" = "req1_flags" := rfl
@[simp] theorem replMem_1 : Engine.replMem 1 = "repl1" := rfl
@[simp] theorem resp_valid_1 : (s!"resp{1}_valid" : String) = "resp1_valid" := rfl
@[simp] theorem resp_code_1 : (s!"resp{1}_code" : String) = "resp1_code" := rfl

/-! ## The design, split into its prelude and its bump rule -/

section
variable (cfg : Engine.Cfg)

/-- The six memory-read latches and the two check units: every rule of the
engine except the bump sequencer. None of them writes a memory, and none of
them writes a coordinate the abstraction reads. -/
def preRules : List Rule :=
  Engine.latchRules cfg ++ [Engine.chkRule cfg 0, Engine.chkRule cfg 1]

/-- The state after the prelude rules of one cycle (all reads are pre-cycle,
D9, so this is just the accumulator the bump rule starts from). -/
def pre (σ : Hw.St) : Hw.St :=
  (preRules cfg).foldl (fun acc r => r.body.run σ acc) σ

theorem rules_eq :
    (Engine.mkDesign cfg).rules = preRules cfg ++ [Engine.bumpRule cfg] := by
  simp [Engine.mkDesign, preRules]

/-- One cycle = the prelude, then the bump sequencer. -/
theorem cycle_eq (σ : Hw.St) :
    (Engine.mkDesign cfg).cycle σ = (Engine.bumpRule cfg).body.run σ (pre cfg σ) := by
  simp [Design.cycle, rules_eq, pre, List.foldl_append]

/-! ### The prelude touches nothing the abstraction reads -/

theorem pre_mems (σ : Hw.St) : (pre cfg σ).mems = σ.mems := by
  funext mn a w
  refine foldl_mems_notin σ mn (preRules cfg) σ ?_ a w
  intro r hr
  simp [preRules, Engine.latchRules, Engine.chkRule, Engine.actSeq,
    Act.memWrites] at hr ⊢
  rcases hr with h | h | h | h | h | h | h | h <;> simp [h, Act.memWrites]

theorem pre_regs (σ : Hw.St) (n : String) (w : Nat)
    (h : ∀ r ∈ preRules cfg, (n, w) ∉ r.body.regWrites) :
    (pre cfg σ).regs n w = σ.regs n w :=
  foldl_regs_notin σ n w (preRules cfg) σ h

/-- Every register the prelude rules can write: the six read latches and the
two check units' own state. Disjoint from the bump sequencer's registers,
which is the whole content of E3 ("one check unit per volume"). -/
def preWritten : List String :=
  ["b_epoch_q", "b_flags_q", "c0_flags_q", "c1_flags_q", "c0_repl_q", "c1_repl_q",
   "resp0_valid", "c0_a", "c0_e", "c0_f", "c0_busy", "c0_st", "resp0_code",
   "resp1_valid", "c1_a", "c1_e", "c1_f", "c1_busy", "c1_st", "resp1_code"]

theorem pre_regs_of (σ : Hw.St) (n : String) (w : Nat) (h : n ∉ preWritten) :
    (pre cfg σ).regs n w = σ.regs n w := by
  refine pre_regs cfg σ _ _ ?_
  intro r hr
  simp only [preWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [preRules, Engine.latchRules, Engine.chkRule] at hr
  rcases hr with h' | h' | h' | h' | h' | h' | h' | h' <;>
    subst h' <;> simp_all [Act.regWrites, Engine.actSeq]

theorem pre_b_st (σ : Hw.St) : (pre cfg σ).regs "b_st" 3 = σ.regs "b_st" 3 :=
  pre_regs_of cfg σ _ _ (by decide)
theorem pre_b_a (σ : Hw.St) : (pre cfg σ).regs "b_a" cfg.aw = σ.regs "b_a" cfg.aw :=
  pre_regs_of cfg σ _ _ (by decide)
theorem pre_b_pol (σ : Hw.St) : (pre cfg σ).regs "b_pol" 1 = σ.regs "b_pol" 1 :=
  pre_regs_of cfg σ _ _ (by decide)
theorem pre_b_target (σ : Hw.St) :
    (pre cfg σ).regs "b_target" cfg.ew = σ.regs "b_target" cfg.ew :=
  pre_regs_of cfg σ _ _ (by decide)
theorem pre_b_acked (σ : Hw.St) : (pre cfg σ).regs "b_acked" 2 = σ.regs "b_acked" 2 :=
  pre_regs_of cfg σ _ _ (by decide)

/-! ## The abstraction function (Layer 3 (a))

`Protocol.St` read straight out of the design's memories and the bump
sequencer's registers. Nothing is invented: cells and replicas are the four
BRAM banks, and `pending` is the sequencer's own state. -/

/-- Cell `i` of the protocol state, read out of `cell_epoch` / `cell_flags`.
`rc` is `0`: §3's `referent_count` carries no safety obligation and the
engine does not implement `acquire`/`release` (deviation E5). -/
def absCells (σ : Hw.St) (i : Fin (2 ^ cfg.aw)) : Protocol.Cell cfg.ew where
  epoch := σ.mems "cell_epoch" i.val cfg.ew
  rc := 0
  poison := (σ.mems "cell_flags" i.val 3).getLsbD 0
  dead := (σ.mems "cell_flags" i.val 3).getLsbD 1
  -- E13: occupancy is not stored. v1 has no install/free op, so every
  -- slot is occupied for all time and the check unit uses the constant.
  occupied := true

/-- Volume `k`'s replica bank. -/
def replName : Fin 2 → String := fun k => if k = 0 then "repl0" else "repl1"

@[simp] theorem replName_0 : replName 0 = "repl0" := rfl
@[simp] theorem replName_1 : replName 1 = "repl1" := rfl

def absRepl (σ : Hw.St) (k : Fin 2) (i : Fin (2 ^ cfg.aw)) : BitVec cfg.ew :=
  σ.mems (replName k) i.val cfg.ew

/-- The bump sequencer's state register. -/
def bst (σ : Hw.St) : BitVec 3 := σ.regs "b_st" 3

/-- The cell the in-flight bump names. -/
def bcell (σ : Hw.St) : Fin (2 ^ cfg.aw) :=
  ⟨(σ.regs "b_a" cfg.aw).toNat, (σ.regs "b_a" cfg.aw).isLt⟩

/-- The in-flight bump's policy. -/
def bpol (σ : Hw.St) : Protocol.Policy :=
  if σ.regs "b_pol" 1 = 1#1 then .poison else .lazy

/-- §3's one in-flight bump, reconstructed from the sequencer. It exists
exactly in `B_ACK` and `B_RET`: the protocol's `bump` event is the cycle in
which the home increment and the broadcast are committed together
(`B_UP → B_ACK`), so `B_RD`/`B_UP` are still `pending = none`. -/
def absPending (σ : Hw.St) : Option (Protocol.Bump cfg.ew (2 ^ cfg.aw) 2) :=
  if bst σ = 3#3 ∨ bst σ = 4#3 then
    some { cell := bcell cfg σ
           target := σ.regs "b_target" cfg.ew
           policy := bpol σ
           acked := fun k => (σ.regs "b_acked" 2).getLsbD k.val }
  else none

/-- **The abstraction function.** -/
def abs (σ : Hw.St) : Protocol.St cfg.ew (2 ^ cfg.aw) 2 where
  cells := absCells cfg σ
  repl := absRepl cfg σ
  pending := absPending cfg σ

/-! ## Cycle-by-cycle evaluation of the bump sequencer -/

/-- The engine's saturating increment, as a value. -/
def satI (σ : Hw.St) : BitVec cfg.ew :=
  if σ.regs "b_epoch_q" cfg.ew = BitVec.allOnes cfg.ew then σ.regs "b_epoch_q" cfg.ew
  else σ.regs "b_epoch_q" cfg.ew + 1#cfg.ew

/-! ### The simp set that evaluates one cycle of the bump sequencer -/

attribute [local simp] Engine.bumpRule Engine.actSeq Engine.acceptBump
  Engine.L1 Engine.L2 Engine.L3 Engine.L16 Engine.LE Engine.LA
  Engine.B_IDLE Engine.B_RD Engine.B_UP Engine.B_ACK Engine.B_RET
  Engine.satIncE Engine.bumpedFlags Engine.maxEpoch Engine.FLAG_POISON
  Engine.FLAG_DEAD Act.run Expr.eval RegEnv.set

/-- `B_IDLE`: at most a bump acceptance — no memory is written and the
sequencer cannot reach `B_ACK`/`B_RET` in one cycle. -/
theorem cyc_idle (σ : Hw.St) (h : σ.regs "b_st" 3 = 0#3) :
    (((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 0#3 ∨
      ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 1#3) ∧
    ((Engine.mkDesign cfg).cycle σ).mems = σ.mems := by
  rw [cycle_eq]
  refine ⟨?_, ?_⟩ <;>
    (simp [h, pre_b_st, pre_mems]
     try (split_ifs <;> simp [pre_b_st, pre_mems, h]))

/-- `B_RD`: the home read is in the memory's read stage; nothing else moves. -/
theorem cyc_rd (σ : Hw.St) (h : σ.regs "b_st" 3 = 1#3) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 2#3 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_a" cfg.aw = σ.regs "b_a" cfg.aw ∧
    ((Engine.mkDesign cfg).cycle σ).mems = σ.mems := by
  rw [cycle_eq]
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp [h, pre_b_a, pre_mems]
     try (split_ifs <;> simp [pre_b_a, pre_mems]))

/-- The post-bump flag word the engine writes (`Protocol.Cell.bumped`'s
three dispositions, bit-packed). -/
def bflags (σ : Hw.St) : BitVec 3 :=
  σ.regs "b_flags_q" 3 |||
    ((if σ.regs "b_pol" 1 = 1#1 then 1#3 else 0#3) |||
     (if satI cfg σ = BitVec.allOnes cfg.ew then 2#3 else 0#3))

@[local simp] theorem ite_bv1_eq_one {P : Prop} [Decidable P] :
    ((if P then (1#1 : BitVec 1) else 0#1) = 1#1) ↔ P := by
  split <;> simp_all

/-- `B_UP`: §3's O(1) home increment with saturation and the policy's
disposition, the broadcast raised, the ack vector cleared. This is the cycle
that carries the protocol's `bump` event. -/
theorem cyc_up (σ : Hw.St) (h : σ.regs "b_st" 3 = 2#3) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 3#3 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_a" cfg.aw = σ.regs "b_a" cfg.aw ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_pol" 1 = σ.regs "b_pol" 1 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_acked" 2 = 0#2 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_target" cfg.ew = satI cfg σ ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "cell_epoch" x cfg.ew =
      if x = (σ.regs "b_a" cfg.aw).toNat then satI cfg σ
      else σ.mems "cell_epoch" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "cell_flags" x 3 =
      if x = (σ.regs "b_a" cfg.aw).toNat then bflags cfg σ
      else σ.mems "cell_flags" x 3) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "repl0" x cfg.ew =
      σ.mems "repl0" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "repl1" x cfg.ew =
      σ.mems "repl1" x cfg.ew) := by
  rw [cycle_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intros
     simp [h, satI, bflags, pre_b_a, pre_b_pol, pre_mems, MemEnv.set]
     try (split_ifs <;> simp_all [satI, bflags, pre_b_a, pre_b_pol, pre_mems]))

/-- `B_ACK` with no volume acked: volume 0 adopts the broadcast and acks. -/
theorem cyc_ack_0 (σ : Hw.St) (h : σ.regs "b_st" 3 = 3#3)
    (ha : σ.regs "b_acked" 2 = 0#2) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 3#3 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_a" cfg.aw = σ.regs "b_a" cfg.aw ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_pol" 1 = σ.regs "b_pol" 1 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_target" cfg.ew = σ.regs "b_target" cfg.ew ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_acked" 2 = 1#2 ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "repl0" x cfg.ew =
      if x = (σ.regs "b_a" cfg.aw).toNat then σ.regs "b_target" cfg.ew
      else σ.mems "repl0" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "repl1" x cfg.ew =
      σ.mems "repl1" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "cell_epoch" x cfg.ew =
      σ.mems "cell_epoch" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "cell_flags" x 3 =
      σ.mems "cell_flags" x 3) := by
  rw [cycle_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intros
     simp [h, ha, pre_b_st, pre_b_a, pre_b_pol, pre_b_target, pre_mems, MemEnv.set]
     try (split_ifs <;> simp_all [pre_b_st, pre_b_a, pre_b_pol, pre_b_target, pre_mems]))

/-- `B_ACK` with only volume 1 acked: volume 0 adopts and acks. -/
theorem cyc_ack_2 (σ : Hw.St) (h : σ.regs "b_st" 3 = 3#3)
    (ha : σ.regs "b_acked" 2 = 2#2) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 3#3 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_a" cfg.aw = σ.regs "b_a" cfg.aw ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_pol" 1 = σ.regs "b_pol" 1 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_target" cfg.ew = σ.regs "b_target" cfg.ew ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_acked" 2 = 3#2 ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "repl0" x cfg.ew =
      if x = (σ.regs "b_a" cfg.aw).toNat then σ.regs "b_target" cfg.ew
      else σ.mems "repl0" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "repl1" x cfg.ew =
      σ.mems "repl1" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "cell_epoch" x cfg.ew =
      σ.mems "cell_epoch" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "cell_flags" x 3 =
      σ.mems "cell_flags" x 3) := by
  rw [cycle_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intros
     simp [h, ha, pre_b_st, pre_b_a, pre_b_pol, pre_b_target, pre_mems, MemEnv.set]
     try (split_ifs <;> simp_all [pre_b_st, pre_b_a, pre_b_pol, pre_b_target, pre_mems]))

/-- `B_ACK` with only volume 0 acked: volume 1 adopts and acks. -/
theorem cyc_ack_1 (σ : Hw.St) (h : σ.regs "b_st" 3 = 3#3)
    (ha : σ.regs "b_acked" 2 = 1#2) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 3#3 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_a" cfg.aw = σ.regs "b_a" cfg.aw ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_pol" 1 = σ.regs "b_pol" 1 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_target" cfg.ew = σ.regs "b_target" cfg.ew ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_acked" 2 = 3#2 ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "repl1" x cfg.ew =
      if x = (σ.regs "b_a" cfg.aw).toNat then σ.regs "b_target" cfg.ew
      else σ.mems "repl1" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "repl0" x cfg.ew =
      σ.mems "repl0" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "cell_epoch" x cfg.ew =
      σ.mems "cell_epoch" x cfg.ew) ∧
    (∀ x, ((Engine.mkDesign cfg).cycle σ).mems "cell_flags" x 3 =
      σ.mems "cell_flags" x 3) := by
  rw [cycle_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intros
     simp [h, ha, pre_b_st, pre_b_a, pre_b_pol, pre_b_target, pre_mems, MemEnv.set]
     try (split_ifs <;> simp_all [pre_b_st, pre_b_a, pre_b_pol, pre_b_target, pre_mems]))

/-- `B_ACK` with the whole referent span acked: move to the return state.
Nothing observable changes — this is the engine's one stutter cycle. -/
theorem cyc_ack_done (σ : Hw.St) (h : σ.regs "b_st" 3 = 3#3)
    (ha : σ.regs "b_acked" 2 = 3#2) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 4#3 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_a" cfg.aw = σ.regs "b_a" cfg.aw ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_pol" 1 = σ.regs "b_pol" 1 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_target" cfg.ew = σ.regs "b_target" cfg.ew ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_acked" 2 = 3#2 ∧
    ((Engine.mkDesign cfg).cycle σ).mems = σ.mems := by
  rw [cycle_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp [h, ha, pre_b_a, pre_b_pol, pre_b_target, pre_b_acked, pre_mems]
     try (split_ifs <;> simp_all [pre_b_a, pre_b_pol, pre_b_target, pre_b_acked,
       pre_mems]))

/-- `B_RET`: §3's linearization point. The sequencer returns to idle; no
freshness state moves. -/
theorem cyc_ret (σ : Hw.St) (h : σ.regs "b_st" 3 = 4#3) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = 0#3 ∧
    ((Engine.mkDesign cfg).cycle σ).mems = σ.mems := by
  rw [cycle_eq]
  refine ⟨?_, ?_⟩ <;>
    (simp [h, pre_mems]
     try (split_ifs <;> simp_all [pre_mems]))

/-- Off the reachable encoding (`b_st ≥ 5`) the sequencer is a no-op: the
state register holds and no memory moves. -/
theorem cyc_junk (σ : Hw.St) (h0 : σ.regs "b_st" 3 ≠ 0#3) (h1 : σ.regs "b_st" 3 ≠ 1#3)
    (h2 : σ.regs "b_st" 3 ≠ 2#3) (h3 : σ.regs "b_st" 3 ≠ 3#3)
    (h4 : σ.regs "b_st" 3 ≠ 4#3) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_st" 3 = σ.regs "b_st" 3 ∧
    ((Engine.mkDesign cfg).cycle σ).mems = σ.mems := by
  rw [cycle_eq]
  refine ⟨?_, ?_⟩ <;>
    (simp [h0, h1, h2, h3, h4, pre_b_st, pre_mems]
     try (split_ifs <;> simp_all [pre_b_st, pre_mems]))

/-! ### The read latches, and the design invariant -/

/-- The engine's increment is §3's `satInc`. -/
theorem add_one_eq {w : Nat} (e : BitVec w) : e + 1#w = BitVec.ofNat w (e.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem satI_eq (σ : Hw.St) :
    satI cfg σ = Protocol.satInc (σ.regs "b_epoch_q" cfg.ew) := by
  unfold satI Protocol.satInc Protocol.maxE
  split <;> simp [add_one_eq]

/-- The state after the six read latches alone. -/
def preL (σ : Hw.St) : Hw.St :=
  (Engine.latchRules cfg).foldl (fun acc r => r.body.run σ acc) σ

theorem pre_eq (σ : Hw.St) :
    pre cfg σ = (Engine.chkRule cfg 1).body.run σ
      ((Engine.chkRule cfg 0).body.run σ (preL cfg σ)) := by
  simp [pre, preRules, preL, List.foldl_append]

/-- The home-cell read latches (D19's sync-read shape) are unconditional:
after every cycle they hold the memory word addressed by `b_a`. -/
theorem cyc_latch (σ : Hw.St) :
    ((Engine.mkDesign cfg).cycle σ).regs "b_epoch_q" cfg.ew =
      σ.mems "cell_epoch" (σ.regs "b_a" cfg.aw).toNat cfg.ew ∧
    ((Engine.mkDesign cfg).cycle σ).regs "b_flags_q" 3 =
      σ.mems "cell_flags" (σ.regs "b_a" cfg.aw).toNat 3 := by
  rw [cycle_eq]
  constructor <;>
    (rw [Act.run_regs_notin _ _ _ (by simp [Act.regWrites]) σ (pre cfg σ), pre_eq,
       Act.run_regs_notin _ _ _ (by simp [Engine.chkRule, Act.regWrites]) σ _,
       Act.run_regs_notin _ _ _ (by simp [Engine.chkRule, Act.regWrites]) σ _]
     simp [preL, Engine.latchRules])

/-! ## The design invariant (Layer 3, the only one needed)

Two facts, both about the bump sequencer's own encoding. `latched` is the
D19 read-stage discipline: in `B_UP` the latched home word is the memory's.
`retAcked` is the ack reduction: `B_RET` is reachable only with the whole
referent span acked. Nothing here is a hypothesis about cores. -/
structure DInv (σ : Hw.St) : Prop where
  latched : σ.regs "b_st" 3 = 2#3 →
    σ.regs "b_epoch_q" cfg.ew = σ.mems "cell_epoch" (σ.regs "b_a" cfg.aw).toNat cfg.ew ∧
    σ.regs "b_flags_q" 3 = σ.mems "cell_flags" (σ.regs "b_a" cfg.aw).toNat 3
  retAcked : σ.regs "b_st" 3 = 4#3 →
    (σ.regs "b_acked" 2).getLsbD 0 = true ∧ (σ.regs "b_acked" 2).getLsbD 1 = true

/-- The eight-way case split on the sequencer's state register. -/
theorem bst_cases (x : BitVec 3) :
    x = 0#3 ∨ x = 1#3 ∨ x = 2#3 ∨ x = 3#3 ∨ x = 4#3 ∨
      (x ≠ 0#3 ∧ x ≠ 1#3 ∧ x ≠ 2#3 ∧ x ≠ 3#3 ∧ x ≠ 4#3) := by
  revert x; decide

/-- The two-bit ack vector, enumerated. -/
theorem acked_cases (x : BitVec 2) : x = 0#2 ∨ x = 1#2 ∨ x = 2#2 ∨ x = 3#2 := by
  revert x; decide

/-- `DInv` holds after **every** cycle, from any state whatsoever. -/
theorem dinv_cycle (σ : Hw.St) : DInv cfg ((Engine.mkDesign cfg).cycle σ) := by
  rcases bst_cases (σ.regs "b_st" 3) with h | h | h | h | h | ⟨h0, h1, h2, h3, h4⟩
  · obtain ⟨hst, hm⟩ := cyc_idle cfg σ h
    constructor
    · intro hup; rcases hst with hs | hs <;> rw [hs] at hup <;> simp at hup
    · intro hret; rcases hst with hs | hs <;> rw [hs] at hret <;> simp at hret
  · obtain ⟨hst, ha, hm⟩ := cyc_rd cfg σ h
    refine ⟨fun _ => ?_, fun hret => ?_⟩
    · rw [ha, hm]; exact cyc_latch cfg σ
    · rw [hst] at hret; simp at hret
  · obtain ⟨hst, _⟩ := cyc_up cfg σ h
    exact ⟨fun hup => by rw [hst] at hup; simp at hup,
           fun hret => by rw [hst] at hret; simp at hret⟩
  · rcases acked_cases (σ.regs "b_acked" 2) with ha | ha | ha | ha
    · obtain ⟨hst, _⟩ := cyc_ack_0 cfg σ h ha
      exact ⟨fun hup => by rw [hst] at hup; simp at hup,
             fun hret => by rw [hst] at hret; simp at hret⟩
    · obtain ⟨hst, _⟩ := cyc_ack_1 cfg σ h ha
      exact ⟨fun hup => by rw [hst] at hup; simp at hup,
             fun hret => by rw [hst] at hret; simp at hret⟩
    · obtain ⟨hst, _⟩ := cyc_ack_2 cfg σ h ha
      exact ⟨fun hup => by rw [hst] at hup; simp at hup,
             fun hret => by rw [hst] at hret; simp at hret⟩
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_done cfg σ h ha
      exact ⟨fun hup => by rw [hst] at hup; simp at hup, fun _ => by rw [hak]; decide⟩
  · obtain ⟨hst, _⟩ := cyc_ret cfg σ h
    exact ⟨fun hup => by rw [hst] at hup; simp at hup,
           fun hret => by rw [hst] at hret; simp at hret⟩
  · obtain ⟨hst, _⟩ := cyc_junk cfg σ h0 h1 h2 h3 h4
    exact ⟨fun hup => by rw [hst] at hup; exact absurd hup h2,
           fun hret => by rw [hst] at hret; exact absurd hret h4⟩

/-! ## The environment drives only the request ports (D15, deviation E2)

The engine's *only* inputs are the two request ports. No input name is a
freshness coordinate, so an input trace — an adversarial pair of cores —
cannot move a single bit the abstraction reads. This is the mechanized form
of `EPOCH_SPEC.md` §"Consequence bound NOW". -/

theorem foldl_inputs_notin (n : String) (w : Nat) (ι : InEnv) :
    ∀ (ins : List InputDecl) (ρ : RegEnv), (∀ i ∈ ins, n ≠ i.name) →
      (ins.foldl (fun ρ i => ρ.set i.name (ι i.name i.width)) ρ) n w = ρ n w := by
  intro ins
  induction ins with
  | nil => intro ρ _; rfl
  | cons i ins ih =>
    intro ρ h
    rw [List.foldl_cons, ih _ (fun i' hi' => h i' (by simp [hi']))]
    have : ¬ (n = i.name) := h i (by simp)
    simp [RegEnv.set, this]

/-- The names the environment owns. -/
def inputNames : List String :=
  ["req0_valid", "req0_op", "req0_cell", "req0_epoch", "req0_policy", "req0_flags",
   "req1_valid", "req1_op", "req1_cell", "req1_epoch", "req1_policy", "req1_flags"]

theorem setInputs_regs (σ : Hw.St) (ι : InEnv) (n : String) (w : Nat)
    (h : n ∉ inputNames) :
    (σ.setInputs (Engine.mkDesign cfg).inputs ι).regs n w = σ.regs n w := by
  refine foldl_inputs_notin n w ι _ σ.regs ?_
  simp only [inputNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  intro i hi
  simp [Engine.mkDesign, Engine.volInputs] at hi
  rcases hi with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
    subst h' <;> simp_all

@[simp] theorem setInputs_mems (σ : Hw.St) (ι : InEnv) (ins : List InputDecl) :
    (σ.setInputs ins ι).mems = σ.mems := rfl

/-- **Inputs are invisible to the abstraction.** -/
theorem abs_setInputs (σ : Hw.St) (ι : InEnv) :
    abs cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) = abs cfg σ := by
  have hb : ∀ (n : String) (w : Nat),
      n ∈ ["b_st", "b_a", "b_pol", "b_target", "b_acked"] →
      (σ.setInputs (Engine.mkDesign cfg).inputs ι).regs n w = σ.regs n w := by
    intro n w hn
    refine setInputs_regs cfg σ ι n w ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h | h | h <;> subst h <;> decide
  have hc : absCells cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) = absCells cfg σ := by
    funext i; simp [absCells]
  have hr : absRepl cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) = absRepl cfg σ := by
    funext k i; simp [absRepl]
  have hp : absPending cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) = absPending cfg σ := by
    simp [absPending, bst, bcell, bpol, hb "b_st" 3 (by simp), hb "b_a" cfg.aw (by simp),
      hb "b_pol" 1 (by simp), hb "b_target" cfg.ew (by simp), hb "b_acked" 2 (by simp)]
  simp [abs, hc, hr, hp]

theorem dinv_setInputs (σ : Hw.St) (ι : InEnv) (h : DInv cfg σ) :
    DInv cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) := by
  have hb : ∀ (n : String) (w : Nat),
      n ∈ ["b_st", "b_a", "b_acked", "b_epoch_q", "b_flags_q"] →
      (σ.setInputs (Engine.mkDesign cfg).inputs ι).regs n w = σ.regs n w := by
    intro n w hn
    refine setInputs_regs cfg σ ι n w ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h' | h' | h' | h' | h' <;> subst h' <;> decide
  constructor
  · intro hup
    rw [hb "b_st" 3 (by simp)] at hup
    rw [hb "b_epoch_q" cfg.ew (by simp), hb "b_flags_q" 3 (by simp),
      hb "b_a" cfg.aw (by simp), setInputs_mems]
    exact h.latched hup
  · intro hret
    rw [hb "b_st" 3 (by simp)] at hret
    rw [hb "b_acked" 2 (by simp)]
    exact h.retAcked hret

/-! ## The commuting square (Layer 3 (b))

One clock cycle of the engine is either a protocol event or a stutter. The
case analysis is the sequencer's own state register; nothing else. -/

theorem St_ext {W N K : Nat} {a b : Protocol.St W N K} (hc : a.cells = b.cells)
    (hr : a.repl = b.repl) (hp : a.pending = b.pending) : a = b := by
  cases a; cases b; simp_all

/-- Two states with the same memories and no bump in flight abstract equally. -/
theorem abs_stutter (σ σ' : Hw.St) (hm : σ'.mems = σ.mems)
    (h1 : σ'.regs "b_st" 3 ≠ 3#3) (h1' : σ'.regs "b_st" 3 ≠ 4#3)
    (h2 : σ.regs "b_st" 3 ≠ 3#3) (h2' : σ.regs "b_st" 3 ≠ 4#3) :
    abs cfg σ' = abs cfg σ := by
  refine St_ext ?_ ?_ ?_
  · funext i; simp [abs, absCells, hm]
  · funext k i; simp [abs, absRepl, hm]
  · simp [abs, absPending, bst, h1, h1', h2, h2']

/-- Two states with the same memories and the same in-flight bump abstract
equally — the engine's one genuinely stuttering cycle (`B_ACK → B_RET`). -/
theorem abs_stutter_pend (σ σ' : Hw.St) (hm : σ'.mems = σ.mems)
    (h1 : σ'.regs "b_st" 3 = 3#3 ∨ σ'.regs "b_st" 3 = 4#3)
    (h2 : σ.regs "b_st" 3 = 3#3 ∨ σ.regs "b_st" 3 = 4#3)
    (ha : σ'.regs "b_a" cfg.aw = σ.regs "b_a" cfg.aw)
    (ht : σ'.regs "b_target" cfg.ew = σ.regs "b_target" cfg.ew)
    (hp : σ'.regs "b_pol" 1 = σ.regs "b_pol" 1)
    (hk : σ'.regs "b_acked" 2 = σ.regs "b_acked" 2) :
    abs cfg σ' = abs cfg σ := by
  refine St_ext ?_ ?_ ?_
  · funext i; simp [abs, absCells, hm]
  · funext k i; simp [abs, absRepl, hm]
  · simp [abs, absPending, bst, bcell, bpol, h1, h2, ha, ht, hp, hk]

/-- The `B_UP → B_ACK` cycle is §3's `bump`: the O(1) saturating home
increment, the policy's disposition, and the broadcast, committed together. -/
theorem square_up (τ : Hw.St) (hd : DInv cfg τ) (h : τ.regs "b_st" 3 = 2#3) :
    Protocol.stepEv (abs cfg τ) (.bump (bcell cfg τ) (bpol τ))
      = some (abs cfg ((Engine.mkDesign cfg).cycle τ)) := by
  obtain ⟨he, hf⟩ := hd.latched h
  obtain ⟨hst, ha, hpo, hak, htg, hce, hcf, hr0, hr1⟩ := cyc_up cfg τ h
  have hpend : (abs cfg τ).pending = none := by
    simp [abs, absPending, bst, h]
  have hba : (bcell cfg τ).val = (τ.regs "b_a" cfg.aw).toNat := rfl
  simp only [Protocol.stepEv, hpend]
  refine congrArg some (St_ext ?_ ?_ ?_).symm
  · funext j
    dsimp only
    rw [Function.update_apply]
    by_cases hj : j = bcell cfg τ
    · subst hj
      rw [if_pos rfl]
      have hcls : (abs cfg ((Engine.mkDesign cfg).cycle τ)).cells (bcell cfg τ) =
          { epoch := satI cfg τ, rc := 0, poison := (bflags cfg τ).getLsbD 0,
            dead := (bflags cfg τ).getLsbD 1, occupied := true } := by
        simp [abs, absCells, hce, hcf, hba]
      have hcell : (abs cfg τ).cells (bcell cfg τ) =
          { epoch := τ.regs "b_epoch_q" cfg.ew, rc := 0,
            poison := (τ.regs "b_flags_q" 3).getLsbD 0,
            dead := (τ.regs "b_flags_q" 3).getLsbD 1,
            occupied := true } := by
        simp [abs, absCells, hba, ← he, ← hf]
      rw [hcls, hcell]
      by_cases hpol : τ.regs "b_pol" 1 = 1#1 <;>
        by_cases hsat : BitVec.ofNat cfg.ew ((τ.regs "b_epoch_q" cfg.ew).toNat + 1)
          = BitVec.allOnes cfg.ew <;>
        by_cases hmax : τ.regs "b_epoch_q" cfg.ew = BitVec.allOnes cfg.ew <;>
        simp [Protocol.Cell.bumped, bflags, bpol, satI, Protocol.satInc, Protocol.maxE,
          Protocol.Policy.isPoison, hpol, hsat, hmax, BitVec.getLsbD_or, add_one_eq]
    · rw [if_neg hj]
      have hne : ¬ (j.val = (τ.regs "b_a" cfg.aw).toNat) := by
        intro hv; exact hj (Fin.ext (by rw [hv, hba]))
      simp [abs, absCells, hce, hcf, hne]
  · funext k i
    fin_cases k <;> simp [abs, absRepl, hr0, hr1]
  · simp only [abs, absPending, bst, hst, bcell, bpol, ha, hpo, htg, hak]
    refine congrArg some ?_
    have : (fun k : Fin 2 => (0#2 : BitVec 2).getLsbD k.val) = (fun _ : Fin 2 => false) := by
      funext k; simp
    simp [this, satI_eq, he, absCells]

/-- Each `B_ACK` cycle is one volume's `ack`: it adopts the broadcast epoch
into that volume's replica bank and records the acknowledgement. The acks are
engine-internal — no core is consulted (deviation E2). -/
theorem square_ack (τ : Hw.St) (k : Fin 2) (h : τ.regs "b_st" 3 = 3#3)
    (bank : String) (hbank : bank = Refines.replName k)
    (hst : ((Engine.mkDesign cfg).cycle τ).regs "b_st" 3 = 3#3)
    (ha : ((Engine.mkDesign cfg).cycle τ).regs "b_a" cfg.aw = τ.regs "b_a" cfg.aw)
    (hpo : ((Engine.mkDesign cfg).cycle τ).regs "b_pol" 1 = τ.regs "b_pol" 1)
    (htg : ((Engine.mkDesign cfg).cycle τ).regs "b_target" cfg.ew = τ.regs "b_target" cfg.ew)
    (hak : ∀ k' : Fin 2, (((Engine.mkDesign cfg).cycle τ).regs "b_acked" 2).getLsbD k'.val =
      Function.update (fun k' : Fin 2 => (τ.regs "b_acked" 2).getLsbD k'.val) k true k')
    (hbw : ∀ x, ((Engine.mkDesign cfg).cycle τ).mems bank x cfg.ew =
      if x = (τ.regs "b_a" cfg.aw).toNat then τ.regs "b_target" cfg.ew
      else τ.mems bank x cfg.ew)
    (hother : ∀ (k' : Fin 2), k' ≠ k → ∀ x,
      ((Engine.mkDesign cfg).cycle τ).mems (Refines.replName k') x cfg.ew =
        τ.mems (Refines.replName k') x cfg.ew)
    (hce : ∀ x, ((Engine.mkDesign cfg).cycle τ).mems "cell_epoch" x cfg.ew =
      τ.mems "cell_epoch" x cfg.ew)
    (hcf : ∀ x, ((Engine.mkDesign cfg).cycle τ).mems "cell_flags" x 3 =
      τ.mems "cell_flags" x 3) :
    Protocol.stepEv (abs cfg τ) (.ack k)
      = some (abs cfg ((Engine.mkDesign cfg).cycle τ)) := by
  have hpend : (abs cfg τ).pending =
      some { cell := bcell cfg τ, target := τ.regs "b_target" cfg.ew, policy := bpol τ,
             acked := fun k' => (τ.regs "b_acked" 2).getLsbD k'.val } := by
    simp [abs, absPending, bst, h]
  have hba : (bcell cfg τ).val = (τ.regs "b_a" cfg.aw).toNat := rfl
  simp only [Protocol.stepEv, hpend]
  refine congrArg some (St_ext ?_ ?_ ?_).symm
  · funext j; simp [abs, absCells, hce, hcf]
  · funext k' i
    dsimp only
    rw [Function.update_apply]
    by_cases hk : k' = k
    · subst hk
      rw [if_pos rfl, Function.update_apply]
      by_cases hi : i = bcell cfg τ
      · subst hi
        rw [if_pos rfl]
        simp only [abs, absRepl, ← hbank, hbw, hba, if_true]
      · rw [if_neg hi]
        have hne : ¬ (i.val = (τ.regs "b_a" cfg.aw).toNat) := by
          intro hv; exact hi (Fin.ext (by rw [hv, hba]))
        simp only [abs, absRepl, ← hbank, hbw, if_neg hne]
    · rw [if_neg hk]
      simp only [abs, absRepl, hother k' hk]
  · simp only [abs, absPending, bst, hst, bcell, bpol, ha, hpo, htg]
    refine congrArg some ?_
    simp only [Protocol.Bump.mk.injEq, true_and]
    funext k'
    exact hak k'

/-- The `B_RET` cycle is §3's `bumpReturn` — the architected linearization
point. It is *enabled* only because the whole referent span has acked, which
is `DInv.retAcked`, a fact about the sequencer, not a promise from software. -/
theorem square_ret (τ : Hw.St) (hd : DInv cfg τ) (h : τ.regs "b_st" 3 = 4#3) :
    Protocol.stepEv (abs cfg τ) .bumpReturn
      = some (abs cfg ((Engine.mkDesign cfg).cycle τ)) := by
  obtain ⟨ha0, ha1⟩ := hd.retAcked h
  obtain ⟨hst, hm⟩ := cyc_ret cfg τ h
  have hpend : (abs cfg τ).pending =
      some { cell := bcell cfg τ, target := τ.regs "b_target" cfg.ew, policy := bpol τ,
             acked := fun k' => (τ.regs "b_acked" 2).getLsbD k'.val } := by
    simp [abs, absPending, bst, h]
  have hall : ∀ k : Fin 2, (τ.regs "b_acked" 2).getLsbD k.val = true := by
    intro k; fin_cases k
    · exact ha0
    · exact ha1
  simp only [Protocol.stepEv, hpend, if_pos hall]
  refine congrArg some (St_ext ?_ ?_ ?_).symm
  · funext j; simp [abs, absCells, hm]
  · funext k' i; simp [abs, absRepl, hm]
  · simp [abs, absPending, bst, hst]

/-- **The commuting square.** Every cycle of the engine, from every state
satisfying the design invariant and under *every* input valuation, is either
a stutter or exactly one §3 protocol event. -/
theorem square_cycle (τ : Hw.St) (hd : DInv cfg τ) :
    abs cfg ((Engine.mkDesign cfg).cycle τ) = abs cfg τ ∨
    Protocol.Step (abs cfg τ) (abs cfg ((Engine.mkDesign cfg).cycle τ)) := by
  rcases bst_cases (τ.regs "b_st" 3) with h | h | h | h | h | ⟨h0, h1, h2, h3, h4⟩
  · -- B_IDLE: at most a bump acceptance
    obtain ⟨hst, hm⟩ := cyc_idle cfg τ h
    left
    rcases hst with hs | hs <;>
      exact abs_stutter cfg τ _ hm (by rw [hs]; decide) (by rw [hs]; decide)
        (by rw [h]; decide) (by rw [h]; decide)
  · -- B_RD: the read stage
    obtain ⟨hst, _, hm⟩ := cyc_rd cfg τ h
    exact Or.inl (abs_stutter cfg τ _ hm (by rw [hst]; decide) (by rw [hst]; decide)
      (by rw [h]; decide) (by rw [h]; decide))
  · -- B_UP: the bump event
    exact Or.inr ⟨Protocol.Ev.bump (bcell cfg τ) (bpol τ), square_up cfg τ hd h⟩
  · -- B_ACK: one ack per cycle, then the move to the return state
    rcases acked_cases (τ.regs "b_acked" 2) with ha | ha | ha | ha
    · obtain ⟨hst, hba, hpo, htg, hak, hbw, hoth, hce, hcf⟩ := cyc_ack_0 cfg τ h ha
      refine Or.inr ⟨Protocol.Ev.ack 0, square_ack cfg τ 0 h "repl0" rfl hst hba hpo htg
        ?_ hbw ?_ hce hcf⟩
      · intro k'; fin_cases k' <;> simp [hak, ha, Function.update]
      · intro k' hk' x; fin_cases k' <;> simp_all
    · obtain ⟨hst, hba, hpo, htg, hak, hbw, hoth, hce, hcf⟩ := cyc_ack_1 cfg τ h ha
      refine Or.inr ⟨Protocol.Ev.ack 1, square_ack cfg τ 1 h "repl1" rfl hst hba hpo htg
        ?_ hbw ?_ hce hcf⟩
      · intro k'; fin_cases k' <;> simp [hak, ha, Function.update]
      · intro k' hk' x; fin_cases k' <;> simp_all
    · obtain ⟨hst, hba, hpo, htg, hak, hbw, hoth, hce, hcf⟩ := cyc_ack_2 cfg τ h ha
      refine Or.inr ⟨Protocol.Ev.ack 0, square_ack cfg τ 0 h "repl0" rfl hst hba hpo htg
        ?_ hbw ?_ hce hcf⟩
      · intro k'; fin_cases k' <;> simp [hak, ha, Function.update]
      · intro k' hk' x; fin_cases k' <;> simp_all
    · obtain ⟨hst, hba, hpo, htg, hak, hm⟩ := cyc_ack_done cfg τ h ha
      exact Or.inl (abs_stutter_pend cfg τ _ hm (by rw [hst]; exact Or.inr rfl)
        (Or.inl h) hba htg hpo (by rw [hak, ha]))
  · -- B_RET: the return
    exact Or.inr ⟨Protocol.Ev.bumpReturn, square_ret cfg τ hd h⟩
  · -- off the encoding: a no-op
    obtain ⟨hst, hm⟩ := cyc_junk cfg τ h0 h1 h2 h3 h4
    exact Or.inl (abs_stutter cfg τ _ hm (by rw [hst]; exact h3) (by rw [hst]; exact h4)
      h3 h4)

/-! ## The design as an open transition system

`step σ σ'` is "some input valuation drives σ to σ' in one clock". The
existential over `ι` is what makes every theorem below **unconditional over
input traces**: the two request ports are the cores' only reach into the
engine, and the step relation admits every value they could present. -/

/-- The open design as a `TSys`: reset, and one clock edge under an
arbitrary input valuation. -/
def sysOpen (d : Design) : Loom.TSys where
  S := Hw.St
  init := fun σ => σ = d.reset
  step := fun σ σ' => ∃ ι, d.cycleOpen ι σ = σ'

/-- Any state a real input trace can produce is `Reachable`. -/
theorem reachable_runOpen (d : Design) (ιs : Nat → InEnv) :
    ∀ (n : Nat) (σ : Hw.St), (sysOpen d).Reachable σ →
      (sysOpen d).Reachable (d.runOpen ιs n σ) := by
  intro n
  induction n generalizing ιs with
  | zero => intro σ h; exact h
  | succ n ih =>
    intro σ h
    exact ih _ _ (.step h ⟨ιs 0, rfl⟩)

theorem reachable_runOpen_reset (d : Design) (ιs : Nat → InEnv) (n : Nat) :
    (sysOpen d).Reachable (d.runOpen ιs n d.reset) :=
  reachable_runOpen d ιs n d.reset (.init rfl)

/-- The square, at the open-system level. -/
theorem square_open (σ : Hw.St) (hd : DInv cfg σ) (ι : InEnv) :
    abs cfg ((Engine.mkDesign cfg).cycleOpen ι σ) = abs cfg σ ∨
    Protocol.Step (abs cfg σ) (abs cfg ((Engine.mkDesign cfg).cycleOpen ι σ)) := by
  have h := square_cycle cfg _ (dinv_setInputs cfg σ ι hd)
  rwa [abs_setInputs] at h

theorem dinv_cycleOpen (σ : Hw.St) (ι : InEnv) :
    DInv cfg ((Engine.mkDesign cfg).cycleOpen ι σ) := dinv_cycle cfg _

/-! ### The reset image is `Protocol.Init` -/

theorem reset_b_st : ((Engine.mkDesign cfg).reset).regs "b_st" 3 = 0#3 := by
  simp [Design.reset, Engine.mkDesign, Engine.volRegs, Engine.bumpRegs, RegEnv.set]

theorem reset_mem_epoch (x : Nat) (hx : x < 2 ^ cfg.aw) :
    ((Engine.mkDesign cfg).reset).mems "cell_epoch" x cfg.ew = 1#cfg.ew := by
  simp [Design.reset, Engine.mkDesign, Engine.mems, hx]

theorem reset_mem_flags (x : Nat) (hx : x < 2 ^ cfg.aw) :
    ((Engine.mkDesign cfg).reset).mems "cell_flags" x 3 = 0#3 := by
  simp [Design.reset, Engine.mkDesign, Engine.mems, hx]

theorem reset_mem_repl (k : Fin 2) (x : Nat) (hx : x < 2 ^ cfg.aw) :
    ((Engine.mkDesign cfg).reset).mems (Refines.replName k) x cfg.ew = 1#cfg.ew := by
  fin_cases k <;>
    simp [Design.reset, Engine.mkDesign, Engine.mems, hx, Refines.replName]

theorem one_ne_allOnes (w : Nat) (hw : 2 ≤ w) :
    (1#w : BitVec w) ≠ BitVec.allOnes w := by
  intro he
  have h1 : (1#w : BitVec w).toNat = 1 := by
    simp [BitVec.toNat_ofNat]
    omega
  have h2 : (BitVec.allOnes w).toNat = 2 ^ w - 1 := by simp
  have h3 : 4 ≤ 2 ^ w := by
    calc (4 : Nat) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  rw [he, h2] at h1
  omega

theorem one_ne_zero_bv (w : Nat) (hw : 2 ≤ w) : (1#w : BitVec w) ≠ 0#w := by
  intro he
  have h1 : (1#w : BitVec w).toNat = 1 := by
    simp [BitVec.toNat_ofNat]
    omega
  rw [he] at h1
  simp at h1

/-- **The reset image is exactly `Protocol.Init`** (deviation E4: there is no
core-visible install op, so this is the *only* way freshness state is ever
established). Needs `2 ≤ ew`, since at width 1 the reset epoch `1` would
already be the saturation value. -/
theorem init_ok (hw : 2 ≤ cfg.ew) : Protocol.Init (abs cfg ((Engine.mkDesign cfg).reset)) where
  quiet := by simp [abs, absPending, bst, reset_b_st]
  clean := fun i => by simp [abs, absCells, reset_mem_flags cfg i.val i.isLt]
  deadIffMax := fun i => by
    simp [abs, absCells, reset_mem_flags cfg i.val i.isLt,
      reset_mem_epoch cfg i.val i.isLt, Protocol.maxE, one_ne_allOnes cfg.ew hw]
  nonzero := fun i => by
    simp [abs, absCells, reset_mem_epoch cfg i.val i.isLt, one_ne_zero_bv cfg.ew hw]
  coherent := fun k i => by
    simp [abs, absCells, absRepl, reset_mem_epoch cfg i.val i.isLt,
      reset_mem_repl cfg k i.val i.isLt]

/-! ## The refinement (Layer 3 (b)) -/

/-- `DInv` at reset: the sequencer is idle. -/
theorem dinv_reset : DInv cfg ((Engine.mkDesign cfg).reset) :=
  ⟨fun hup => by rw [reset_b_st] at hup; simp at hup,
   fun hret => by rw [reset_b_st] at hret; simp at hret⟩

/-- `DInv` is an inductive invariant of the open design — and it needs no
help from the previous state: one cycle establishes it. -/
theorem dinv_invariant : (sysOpen (Engine.mkDesign cfg)).Invariant (DInv cfg) :=
  Loom.TSys.Inductive.invariant (M := sysOpen (Engine.mkDesign cfg)) (P := DInv cfg)
    { init := fun σ h => by rw [show σ = (Engine.mkDesign cfg).reset from h]
                            exact dinv_reset cfg
      step := fun σ σ' _ hs => by obtain ⟨ι, hc⟩ := hs; exact hc ▸ dinv_cycleOpen cfg σ ι }

/-- The design invariant holds at every reachable state. -/
theorem dinv_reachable (σ : Hw.St) (h : (sysOpen (Engine.mkDesign cfg)).Reachable σ) :
    DInv cfg σ := dinv_invariant cfg σ h

/-- **`epochengine` refines the mechanized §3 protocol**, as a stuttering
forward simulation: the engine spends several cycles per protocol event
(three per check, `B_RD → B_UP → B_ACK×K → B_RET` per bump), and every cycle
that is not a protocol event leaves the abstract state fixed. -/
def sim (hw : 2 ≤ cfg.ew) :
    StutterSimulation (Protocol.sys cfg.ew (2 ^ cfg.aw) 2)
      ((sysOpen (Engine.mkDesign cfg)).reachablePart) where
  abs := abs cfg
  init_ok := fun σ h => by
    rw [show σ = (Engine.mkDesign cfg).reset from h]; exact init_ok cfg hw
  square := fun σ σ' hstep => by
    obtain ⟨hreach, ι, hcyc⟩ := hstep
    subst hcyc
    exact square_open cfg σ (dinv_reachable cfg σ hreach) ι

/-! ## Transport (Layer 3 (c)): §3's safety theorems, about the RTL

Everything below quantifies over **all** input traces. There is no hypothesis
about core behaviour anywhere — by construction: `Engine.mkDesign`'s only
inputs are the two request ports, and `abs_setInputs` proves they cannot move
a single coordinate the abstraction reads (deviation E2). An adversarial core
may present any handle, any epoch and any bump it likes on any cycle. -/

/-- **The protocol invariant holds of every reachable state of the RTL.** -/
theorem design_inv (hw : 2 ≤ cfg.ew) (σ : Hw.St)
    (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ) : Protocol.Inv (abs cfg σ) :=
  (sim cfg hw).invariant_pullback
    (Protocol.inv_invariant cfg.ew (2 ^ cfg.aw) 2) σ
    ((Loom.TSys.reachablePart_reachable_iff (sysOpen (Engine.mkDesign cfg)) σ).2 hr)

/-- One clock cycle is a (possibly empty) protocol run. -/
theorem step_run (σ : Hw.St) (hd : DInv cfg σ) (ι : InEnv) :
    Protocol.Run (abs cfg σ) (abs cfg ((Engine.mkDesign cfg).cycleOpen ι σ)) := by
  rcases square_open cfg σ hd ι with heq | hstep
  · rw [heq]
  · exact Relation.ReflTransGen.single hstep

/-- **Cycles are protocol runs.** `n` clock cycles under *any* input trace
`ιs` — that is, under any behaviour of the two cores — carry the abstract
state along a genuine `Protocol.Run`. This is what makes §3's "forever"
theorems say something about the hardware's future. -/
theorem run_abs : ∀ (n : Nat) (ιs : Nat → InEnv) (σ : Hw.St), DInv cfg σ →
    Protocol.Run (abs cfg σ) (abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)) := by
  intro n
  induction n with
  | zero => intro ιs σ _; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro ιs σ hd
    exact Relation.ReflTransGen.trans (step_run cfg σ hd (ιs 0))
      (ih (fun k => ιs (k + 1)) _ (dinv_cycleOpen cfg σ (ιs 0)))

section Safety

/-- **T-E2 on the design — saturation is permanent death.** From any
reachable state in which cell `i` is dead, after any number of cycles under
any input trace the cell is still dead, its counter still saturated, and no
check at any volume can return `ok`. -/
theorem T_E2_design (hw : 2 ≤ cfg.ew) (σ : Hw.St)
    (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ) (ιs : Nat → InEnv) (n : Nat)
    (i : Fin (2 ^ cfg.aw))
    (hd : ((abs cfg σ).cells i).dead = true) :
    ((abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)).cells i).dead = true ∧
    ((abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)).cells i).epoch = Protocol.maxE cfg.ew ∧
    ∀ (k : Fin 2) (r : Protocol.Req cfg.ew), r.cellIx = i.val →
      Protocol.use (abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)) k r ≠ .ok :=
  Protocol.Theorems.T_E2_death_permanent (design_inv cfg hw σ hr)
    (run_abs cfg n ιs σ (dinv_reachable cfg σ hr)) i hd

/-- **T-E3 on the design — poison permanence.** After a poison bump, every
structurally valid reference to the cell — *current-epoch ones included* —
fails `-POISONED` at every volume, for every later cycle, under every input
trace. -/
theorem T_E3_design (hw : 2 ≤ cfg.ew) (σ : Hw.St)
    (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ) (ιs : Nat → InEnv) (n : Nat)
    (i : Fin (2 ^ cfg.aw))
    (hp : ((abs cfg σ).cells i).poison = true)
    (ho : ((abs cfg σ).cells i).occupied = true) :
    ((abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)).cells i).poison = true ∧
    ∀ (k : Fin 2) (r : Protocol.Req cfg.ew), r.cellIx = i.val → r.wellFormed = true →
      r.classOk = true →
      Protocol.use (abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)) k r = .poisoned :=
  Protocol.Theorems.T_E3_poison_permanent
    (run_abs cfg n ιs σ (dinv_reachable cfg σ hr)) i hp ho

/-- **T-E1 on the design — stale fails forever.** In a reachable state with
no bump in flight (the post-return condition), any epoch strictly below cell
`i`'s home epoch fails at every volume, at every later cycle, under every
input trace: `-STALE`, or `-POISONED` if the publishing bump also poisoned
the cell. This is §3's return guarantee, about the compiled RTL. -/
theorem T_E1_design (hw : 2 ≤ cfg.ew) (σ : Hw.St)
    (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ) (ιs : Nat → InEnv) (n : Nat)
    (hq : (abs cfg σ).pending = none) (i : Fin (2 ^ cfg.aw))
    (e₀ : BitVec cfg.ew) (hstale : e₀.toNat < ((abs cfg σ).cells i).epoch.toNat)
    (k : Fin 2) (r : Protocol.Req cfg.ew) (hri : r.cellIx = i.val) (hre : r.epoch = e₀)
    (hwf : r.wellFormed = true) (hc : r.classOk = true)
    (ho : ((abs cfg σ).cells i).occupied = true) :
    Protocol.use (abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)) k r = .stale ∨
    Protocol.use (abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)) k r = .poisoned :=
  Protocol.Theorems.T_E1_stale_fails_forever (design_inv cfg hw σ hr) hq
    (run_abs cfg n ιs σ (dinv_reachable cfg σ hr)) i e₀ hstale k r hri hre hwf hc ho

/-- The structure-free corollary: a stale reference never succeeds. -/
theorem T_E1_design_never_ok (hw : 2 ≤ cfg.ew) (σ : Hw.St)
    (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ) (ιs : Nat → InEnv) (n : Nat)
    (hq : (abs cfg σ).pending = none) (i : Fin (2 ^ cfg.aw))
    (e₀ : BitVec cfg.ew) (hstale : e₀.toNat < ((abs cfg σ).cells i).epoch.toNat)
    (k : Fin 2) (r : Protocol.Req cfg.ew) (hri : r.cellIx = i.val) (hre : r.epoch = e₀) :
    Protocol.use (abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)) k r ≠ .ok :=
  Protocol.Theorems.T_E1_never_ok (design_inv cfg hw σ hr) hq
    (run_abs cfg n ιs σ (dinv_reachable cfg σ hr)) i e₀ hstale k r hri hre

/-- **T-E6 on the design — monotonicity.** Home epochs and every volume's
replica are non-decreasing along any run of the hardware. -/
theorem T_E6_design (hw : 2 ≤ cfg.ew) (σ : Hw.St)
    (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ) (ιs : Nat → InEnv) (n : Nat)
    :
    (∀ i, ((abs cfg σ).cells i).epoch.toNat ≤
      ((abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)).cells i).epoch.toNat) ∧
    (∀ k i, ((abs cfg σ).repl k i).toNat ≤
      ((abs cfg ((Engine.mkDesign cfg).runOpen ιs n σ)).repl k i).toNat) :=
  Protocol.Theorems.T_E6_monotone (design_inv cfg hw σ hr)
    (run_abs cfg n ιs σ (dinv_reachable cfg σ hr))

end Safety

/-- The same statements, rooted at power-on: every state the fabric can be in
after `n` cycles of an arbitrary input trace is reachable. -/
theorem reachable_from_reset (ιs : Nat → InEnv) (n : Nat) :
    (sysOpen (Engine.mkDesign cfg)).Reachable
      ((Engine.mkDesign cfg).runOpen ιs n (Engine.mkDesign cfg).reset) :=
  reachable_runOpen_reset _ ιs n

/-! ## D28 — steps to cycles (Layer 3 (d))

`Machines/Epoch/Bounded.lean` proves the spec bound: under the ack-phase
schedule the bump has returned within `K + 1 = 3` *transition-system steps*.
Here that number becomes a number of **clock cycles**, which is the only form
in which a silicon measurement may be compared with it. The bridge is the
stutter budget `b` of `StutterSimulation.boundedResponse_pullback`. -/

/-- The concrete trigger: a bump is in flight (the sequencer is in `B_ACK` or
`B_RET`). -/
def inFlight (σ : Hw.St) : Prop := bst σ = 3#3 ∨ bst σ = 4#3

theorem inFlight_iff (σ : Hw.St) : inFlight σ ↔ (abs cfg σ).pending ≠ none := by
  unfold inFlight
  by_cases h : bst σ = 3#3 ∨ bst σ = 4#3 <;> simp [abs, absPending, h]

/-- The engine during a bump: one clock cycle per step, from a reachable
state with a bump in flight. Restricting the *source* of a step this way is
not a weakening — it is the window the bound is about, and the response
(`pending = none`) is exactly its exit. -/
def ackPhase : Loom.TSys where
  S := Hw.St
  init := fun σ => (sysOpen (Engine.mkDesign cfg)).Reachable σ ∧ inFlight σ
  step := fun σ σ' => (sysOpen (Engine.mkDesign cfg)).Reachable σ ∧ inFlight σ ∧
    ∃ ι, (Engine.mkDesign cfg).cycleOpen ι σ = σ'

theorem ackPhase_reachable (σ : Hw.St) (h : (ackPhase cfg).Reachable σ) :
    (sysOpen (Engine.mkDesign cfg)).Reachable σ :=
  Loom.TSys.Inductive.invariant (M := ackPhase cfg)
    (P := fun σ => (sysOpen (Engine.mkDesign cfg)).Reachable σ)
    { init := fun _ h0 => h0.1
      step := fun _ σ' _ hs => by
        obtain ⟨hr, _, ι, hc⟩ := hs; exact hc ▸ .step hr ⟨ι, rfl⟩ } σ h

/-- **Every cycle of an in-flight bump is an ack-phase step of the protocol**
(or a stutter). The acks are the engine's own — deviation E2 — so this is a
theorem, not a scheduling assumption imported from software. -/
theorem ackPhase_square (σ σ' : Hw.St) (hstep : (ackPhase cfg).step σ σ') :
    abs cfg σ' = abs cfg σ ∨ Bounded.AckStep (abs cfg σ) (abs cfg σ') := by
  obtain ⟨hr, hf, ι, hc⟩ := hstep
  subst hc
  have hd : DInv cfg σ := dinv_reachable cfg σ hr
  have hd' : DInv cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) :=
    dinv_setInputs cfg σ ι hd
  have habs : abs cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) = abs cfg σ :=
    abs_setInputs cfg σ ι
  have hf' : inFlight (σ.setInputs (Engine.mkDesign cfg).inputs ι) := by
    rw [inFlight_iff, habs]; exact (inFlight_iff cfg σ).1 hf
  have hcyc : (Engine.mkDesign cfg).cycleOpen ι σ
      = (Engine.mkDesign cfg).cycle (σ.setInputs (Engine.mkDesign cfg).inputs ι) := rfl
  rw [hcyc, ← habs]
  set τ := σ.setInputs (Engine.mkDesign cfg).inputs ι with hτ
  clear_value τ
  rcases hf' with h | h
  · have h3 : τ.regs "b_st" 3 = 3#3 := h
    rcases acked_cases (τ.regs "b_acked" 2) with ha | ha | ha | ha
    · obtain ⟨hst, hba, hpo, htg, hak, hbw, hoth, hce, hcf⟩ := cyc_ack_0 cfg τ h ha
      refine Or.inr (Or.inl ⟨0,
        { cell := bcell cfg τ, target := τ.regs "b_target" cfg.ew,
          policy := bpol τ, acked := fun k' => (τ.regs "b_acked" 2).getLsbD k'.val },
        by simp [abs, absPending, bst, h3], by simp [ha], ?_⟩)
      exact square_ack cfg τ 0 h "repl0" rfl hst hba hpo htg
        (by intro k'; fin_cases k' <;> simp [hak, ha, Function.update]) hbw
        (by intro k' hk' x; fin_cases k' <;> simp_all) hce hcf
    · obtain ⟨hst, hba, hpo, htg, hak, hbw, hoth, hce, hcf⟩ := cyc_ack_1 cfg τ h ha
      refine Or.inr (Or.inl ⟨1,
        { cell := bcell cfg τ, target := τ.regs "b_target" cfg.ew,
          policy := bpol τ, acked := fun k' => (τ.regs "b_acked" 2).getLsbD k'.val },
        by simp [abs, absPending, bst, h3], by simp [ha], ?_⟩)
      exact square_ack cfg τ 1 h "repl1" rfl hst hba hpo htg
        (by intro k'; fin_cases k' <;> simp [hak, ha, Function.update]) hbw
        (by intro k' hk' x; fin_cases k' <;> simp_all) hce hcf
    · obtain ⟨hst, hba, hpo, htg, hak, hbw, hoth, hce, hcf⟩ := cyc_ack_2 cfg τ h ha
      refine Or.inr (Or.inl ⟨0,
        { cell := bcell cfg τ, target := τ.regs "b_target" cfg.ew,
          policy := bpol τ, acked := fun k' => (τ.regs "b_acked" 2).getLsbD k'.val },
        by simp [abs, absPending, bst, h3], by simp [ha], ?_⟩)
      exact square_ack cfg τ 0 h "repl0" rfl hst hba hpo htg
        (by intro k'; fin_cases k' <;> simp [hak, ha, Function.update]) hbw
        (by intro k' hk' x; fin_cases k' <;> simp_all) hce hcf
    · obtain ⟨hst, hba, hpo, htg, hak, hm⟩ := cyc_ack_done cfg τ h ha
      exact Or.inl (abs_stutter_pend cfg τ _ hm (by rw [hst]; exact Or.inr rfl)
        (Or.inl h3) hba htg hpo (by rw [hak, ha]))
  · exact Or.inr (Or.inr (square_ret cfg τ hd' h))

/-- The ack-phase refinement: the schedule `Machines/Epoch/Bounded.lean`
assumes is the schedule the engine implements. -/
def simAck : StutterSimulation (Bounded.ackSys cfg.ew (2 ^ cfg.aw) 2) (ackPhase cfg) where
  abs := abs cfg
  init_ok := fun σ h => (inFlight_iff cfg σ).1 h.2
  square := fun σ σ' h => ackPhase_square cfg σ σ' h

/-! ### The stutter budget

`rank` counts what is left of the ack reduction: one per volume that has not
acknowledged, plus one for the `B_ACK → B_RET` transition, which is the
engine's only cycle that maps to no protocol event. It is bounded by
`b = 3 = K + 1`. -/

def rank (σ : Hw.St) : Nat :=
  (if (σ.regs "b_acked" 2).getLsbD 0 then 0 else 1) +
  (if (σ.regs "b_acked" 2).getLsbD 1 then 0 else 1) +
  (if bst σ = 3#3 then 1 else 0)

theorem rank_le (σ : Hw.St) : rank σ ≤ 3 := by
  unfold rank; split_ifs <;> omega

/-- Every cycle of an in-flight bump strictly decreases `rank`, except the
returning one — and that one changes the abstract state, so the stuttering
hypothesis is discharged either way. -/
theorem rank_stutter_cycle (τ : Hw.St) (hf : inFlight τ)
    (heq : abs cfg ((Engine.mkDesign cfg).cycle τ) = abs cfg τ) :
    rank ((Engine.mkDesign cfg).cycle τ) < rank τ := by
  rcases hf with h | h
  · have h3 : τ.regs "b_st" 3 = 3#3 := h
    rcases acked_cases (τ.regs "b_acked" 2) with ha | ha | ha | ha
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_0 cfg τ h ha
      simp [rank, bst, hst, hak, ha, h3]
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_1 cfg τ h ha
      simp [rank, bst, hst, hak, ha, h3]
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_2 cfg τ h ha
      simp [rank, bst, hst, hak, ha, h3]
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_done cfg τ h ha
      simp [rank, bst, hst, hak, ha, h3]
  · -- the returning cycle: the abstract state does change, so `heq` is absurd
    exfalso
    obtain ⟨hst, _⟩ := cyc_ret cfg τ h
    have h1 : (abs cfg ((Engine.mkDesign cfg).cycle τ)).pending = none := by
      simp [abs, absPending, bst, hst]
    exact ((inFlight_iff cfg τ).1 (Or.inr h)) (by rw [← heq]; exact h1)

theorem rank_stutter (σ σ' : Hw.St) (hstep : (ackPhase cfg).step σ σ')
    (heq : abs cfg σ' = abs cfg σ) : rank σ' < rank σ := by
  obtain ⟨hr, hf, ι, hc⟩ := hstep
  subst hc
  have habs : abs cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) = abs cfg σ :=
    abs_setInputs cfg σ ι
  have hrank : rank (σ.setInputs (Engine.mkDesign cfg).inputs ι) = rank σ := by
    have h1 : (σ.setInputs (Engine.mkDesign cfg).inputs ι).regs "b_acked" 2
        = σ.regs "b_acked" 2 := setInputs_regs cfg σ ι _ _ (by decide)
    have h2 : (σ.setInputs (Engine.mkDesign cfg).inputs ι).regs "b_st" 3
        = σ.regs "b_st" 3 := setInputs_regs cfg σ ι _ _ (by decide)
    simp [rank, bst, h1, h2]
  have h := rank_stutter_cycle cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι)
    (by rw [inFlight_iff, habs]; exact (inFlight_iff cfg σ).1 hf)
    (by rw [habs]; exact heq)
  rw [hrank] at h
  exact h

/-- The engine is never stuck while a bump is in flight. -/
theorem ackPhase_enabled (σ : Hw.St) (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ)
    (hq : ¬ (abs cfg σ).pending = none) : ∃ t, (ackPhase cfg).step σ t :=
  ⟨_, hr, (inFlight_iff cfg σ).2 hq, fun _ w => 0#w, rfl⟩

theorem ackPhase_closed (σ σ' : Hw.St)
    (hd : (sysOpen (Engine.mkDesign cfg)).Reachable σ) (hstep : (ackPhase cfg).step σ σ') :
    (sysOpen (Engine.mkDesign cfg)).Reachable σ' := by
  obtain ⟨hr, _, ι, hc⟩ := hstep
  exact hc ▸ .step hr ⟨ι, rfl⟩

/-- **D28, the transported bound.** The spec bound of
`Machines/Epoch/Bounded.lean` — `bumpReturn` within `K + 1 = 3` protocol
steps — becomes, through this refinement with stutter budget `b = 3`, a bound
of `3 * (3 + 1) + 3 = 15` **clock cycles** of the emitted RTL: from any
reachable state with a bump in flight, on every path, under every input
trace, the bump has returned within 15 cycles and the engine never stalls
before it does. This is the number a silicon measurement may be compared
against. -/
theorem bump_returns_within_15_cycles (σ : Hw.St)
    (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ) :
    (ackPhase cfg).MustReach (fun τ => (abs cfg τ).pending = none) 15 σ :=
  StutterSimulation.mustReach_pullback_budget (simAck cfg)
    (rank := rank) (b := 3)
    (fun s t hd hstep => ackPhase_closed cfg s t hd hstep)
    (fun s _ => rank_le s)
    (fun s t _ hstep heq => rank_stutter cfg s t hstep heq)
    (fun s hd hq => ackPhase_enabled cfg s hd hq)
    (K := 3) hr
    (Bounded.Theorems.T_E8_bumpReturn_within (K := 2) (abs cfg σ)).toOrBlock

/-- The same bound as a `BoundedResponse` of the cycle-accurate system: the
trigger is "a bump is in flight", the response is "it has returned", the
bound is 15 cycles. -/
theorem bump_bounded_response :
    (ackPhase cfg).BoundedResponse (fun τ => (abs cfg τ).pending ≠ none)
      (fun τ => (abs cfg τ).pending = none) 15 :=
  StutterSimulation.boundedResponse_pullback (simAck cfg) (rank := rank) (b := 3)
    (fun s _ => rank_le s)
    (fun s t _ hstep heq => rank_stutter cfg s t hstep heq)
    (fun s hrs hq => ackPhase_enabled cfg s (ackPhase_reachable cfg s hrs) hq)
    (Bounded.Theorems.T_E8_bounded_response (K := 2))

/-! ### The exact bound, for comparison with silicon

The transported bound is a sound over-approximation: `(b+1)` cycles are
charged for every protocol step, whether or not the design spends them. The
engine's ack reduction is in fact one volume per cycle, so the exact bound is
`K + 2 = 4` cycles. Both are proved; the 15 is the one that comes for free
from the spec, the 4 is the one to hold silicon to. -/

/-- Cycles left before the bump has returned. -/
def mu (σ : Hw.St) : Nat := if bst σ = 3#3 ∨ bst σ = 4#3 then rank σ + 1 else 0

theorem mu_le (σ : Hw.St) : mu σ ≤ 4 := by
  unfold mu; have := rank_le σ; split_ifs <;> omega

theorem mu_decrease_cycle (τ : Hw.St) (hf : inFlight τ) :
    mu ((Engine.mkDesign cfg).cycle τ) < mu τ := by
  rcases hf with h | h
  · have h3 : τ.regs "b_st" 3 = 3#3 := h
    rcases acked_cases (τ.regs "b_acked" 2) with ha | ha | ha | ha
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_0 cfg τ h ha
      simp [mu, rank, inFlight, bst, hst, hak, ha, h3]
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_1 cfg τ h ha
      simp [mu, rank, inFlight, bst, hst, hak, ha, h3]
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_2 cfg τ h ha
      simp [mu, rank, inFlight, bst, hst, hak, ha, h3]
    · obtain ⟨hst, _, _, _, hak, _⟩ := cyc_ack_done cfg τ h ha
      simp [mu, rank, inFlight, bst, hst, hak, ha, h3]
  · have h4 : τ.regs "b_st" 3 = 4#3 := h
    obtain ⟨hst, _⟩ := cyc_ret cfg τ h
    simp [mu, rank, bst, hst, h4]

theorem mu_decrease (σ σ' : Hw.St) (hstep : (ackPhase cfg).step σ σ') : mu σ' < mu σ := by
  obtain ⟨hr, hf, ι, hc⟩ := hstep
  subst hc
  have h1 : (σ.setInputs (Engine.mkDesign cfg).inputs ι).regs "b_acked" 2
      = σ.regs "b_acked" 2 := setInputs_regs cfg σ ι _ _ (by decide)
  have h2 : (σ.setInputs (Engine.mkDesign cfg).inputs ι).regs "b_st" 3
      = σ.regs "b_st" 3 := setInputs_regs cfg σ ι _ _ (by decide)
  have hmu : mu (σ.setInputs (Engine.mkDesign cfg).inputs ι) = mu σ := by
    simp [mu, rank, inFlight, bst, h1, h2]
  have hf' : inFlight (σ.setInputs (Engine.mkDesign cfg).inputs ι) := by
    unfold inFlight bst; rw [h2]; exact hf
  have h := mu_decrease_cycle cfg (σ.setInputs (Engine.mkDesign cfg).inputs ι) hf'
  rw [hmu] at h
  exact h

/-- The exact ranking: one cycle per outstanding ack, one for the move to
`B_RET`, one for the return itself. -/
theorem tight_ranking :
    (ackPhase cfg).Ranking (fun τ => (abs cfg τ).pending = none)
      (fun τ => (sysOpen (Engine.mkDesign cfg)).Reachable τ) mu where
  progress := fun s hd hq => ackPhase_enabled cfg s hd hq
  closed := fun s t hd _ hstep => ackPhase_closed cfg s t hd hstep
  decrease := fun s t _ _ hstep => mu_decrease cfg s t hstep

/-- **The exact cycle bound.** From any reachable state, the bump has
returned within `4` clock cycles of the abstract bump event, on every path,
with no stall — `K = 2` acks, the move to `B_RET`, and the return. -/
theorem bump_returns_within_4_cycles (σ : Hw.St)
    (hr : (sysOpen (Engine.mkDesign cfg)).Reachable σ) :
    (ackPhase cfg).MustReach (fun τ => (abs cfg τ).pending = none) 4 σ :=
  (tight_ranking cfg).mustReach 4 σ hr (mu_le σ)

/-! ## The check units compute `useLocal` exactly (design-level T-E4)

The transported theorems above are about the engine's freshness *state*. This
one is about what a core is actually told: the 3-bit `resp{k}_code` the check
unit emits is `Protocol.useLocal` — §3's failure precedence, in the RTL's own
mux cone — applied to the latched request and the volume-local replica. -/

theorem slice1_iff {w : Nat} (x : BitVec w) (i : Nat) :
    (x.extractLsb' i 1 = 1#1) ↔ x.getLsbD i = true := by
  constructor
  · intro h
    have := congrArg (fun y => BitVec.getLsbD y 0) h
    simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa using h

theorem slice1_iff0 {w : Nat} (x : BitVec w) (i : Nat) :
    (~~~(x.extractLsb' i 1) = 1#1) ↔ x.getLsbD i = false := by
  constructor
  · intro h
    have := congrArg (fun y => BitVec.getLsbD y 0) h
    simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa using h

/-- `Protocol.Outcome` in the engine's encoding (`Engine.OUT_*`). -/
def outcomeCode : Protocol.Outcome → BitVec 3
  | .ok => 0#3
  | .badref => 1#3
  | .poisoned => 2#3
  | .stale => 3#3
  | .denied => 4#3

/-- The home cell as check unit `k` latched it. `epoch` is unused by
`useLocal` (deviation D2: only the replica carries freshness). -/
def chkCell (σ : Hw.St) (k : Nat) : Protocol.Cell cfg.ew where
  epoch := σ.regs (Engine.vn k "repl_q") cfg.ew
  rc := 0
  poison := (σ.regs (Engine.vn k "flags_q") 3).getLsbD 0
  dead := (σ.regs (Engine.vn k "flags_q") 3).getLsbD 1
  occupied := true

/-- §3's `Req` as check unit `k` latched it (Layer-1 deviation D4 for the
structural/rights booleans). -/
def chkReq (σ : Hw.St) (k : Nat) : Protocol.Req cfg.ew where
  cellIx := (σ.regs (Engine.vn k "a") cfg.aw).toNat
  epoch := σ.regs (Engine.vn k "e") cfg.ew
  wellFormed := (σ.regs (Engine.vn k "f") 3).getLsbD 0
  classOk := (σ.regs (Engine.vn k "f") 3).getLsbD 1
  rights := (σ.regs (Engine.vn k "f") 3).getLsbD 2

set_option maxHeartbeats 1000000 in
/-- **The check cone is `useLocal`.** All 128 combinations of the six
structural/disposition bits and the epoch compare. -/
theorem outcome_eval (σ : Hw.St) (k : Nat) :
    Expr.eval σ (Engine.outcome cfg k)
      = outcomeCode (Protocol.useLocal (chkCell cfg σ k)
          (σ.regs (Engine.vn k "repl_q") cfg.ew) (chkReq cfg σ k)) := by
  by_cases hwf : (σ.regs (Engine.vn k "f") 3).getLsbD 0 = true <;>
  by_cases hcls : (σ.regs (Engine.vn k "f") 3).getLsbD 1 = true <;>
  by_cases hpoi : (σ.regs (Engine.vn k "flags_q") 3).getLsbD 0 = true <;>
  by_cases hdea : (σ.regs (Engine.vn k "flags_q") 3).getLsbD 1 = true <;>
  by_cases hrts : (σ.regs (Engine.vn k "f") 3).getLsbD 2 = true <;>
  by_cases hhit : σ.regs (Engine.vn k "repl_q") cfg.ew = σ.regs (Engine.vn k "e") cfg.ew <;>
  simp_all [Engine.outcome, Engine.bit3, Protocol.useLocal, outcomeCode, chkCell, chkReq,
    slice1_iff, slice1_iff0, Engine.OUT_OK, Engine.OUT_BADREF, Engine.OUT_POISONED,
    Engine.OUT_STALE, Engine.OUT_DENIED]

/-- Check unit 0 in `C_DO` answers on the next clock edge, and its answer
is `useLocal` against volume 0's replica — never any other volume's (E6). -/
theorem chk_resp_0 (σ : Hw.St) (h : σ.regs "c0_st" 2 = 2#2) :
    ((Engine.mkDesign cfg).cycle σ).regs "resp0_valid" 1 = 1#1 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "resp0_code" 3 =
      outcomeCode (Protocol.useLocal (chkCell cfg σ 0)
        (σ.regs "c0_repl_q" cfg.ew) (chkReq cfg σ 0)) := by
  have hcode : ((Engine.mkDesign cfg).cycle σ).regs "resp0_code" 3
      = Expr.eval σ (Engine.outcome cfg 0) := by
    rw [cycle_eq, Act.run_regs_notin _ _ _ (by simp [Act.regWrites]) σ (pre cfg σ), pre_eq,
      Act.run_regs_notin _ _ _ (by simp [Engine.chkRule, Act.regWrites]) σ _]
    simp [Engine.chkRule, h, Engine.C_IDLE, Engine.C_RD, Engine.C_DO]
  refine ⟨?_, ?_⟩
  · rw [cycle_eq, Act.run_regs_notin _ _ _ (by simp [Act.regWrites]) σ (pre cfg σ), pre_eq,
      Act.run_regs_notin _ _ _ (by simp [Engine.chkRule, Act.regWrites]) σ _]
    simp [Engine.chkRule, h, Engine.C_IDLE, Engine.C_RD, Engine.C_DO]
  · rw [hcode, outcome_eval]
    simp

/-- Check unit 1 in `C_DO` answers on the next clock edge, and its answer
is `useLocal` against volume 1's replica — never any other volume's (E6). -/
theorem chk_resp_1 (σ : Hw.St) (h : σ.regs "c1_st" 2 = 2#2) :
    ((Engine.mkDesign cfg).cycle σ).regs "resp1_valid" 1 = 1#1 ∧
    ((Engine.mkDesign cfg).cycle σ).regs "resp1_code" 3 =
      outcomeCode (Protocol.useLocal (chkCell cfg σ 1)
        (σ.regs "c1_repl_q" cfg.ew) (chkReq cfg σ 1)) := by
  have hcode : ((Engine.mkDesign cfg).cycle σ).regs "resp1_code" 3
      = Expr.eval σ (Engine.outcome cfg 1) := by
    rw [cycle_eq, Act.run_regs_notin _ _ _ (by simp [Act.regWrites]) σ (pre cfg σ), pre_eq]
    simp [Engine.chkRule, h, Engine.C_IDLE, Engine.C_RD, Engine.C_DO]
  refine ⟨?_, ?_⟩
  · rw [cycle_eq, Act.run_regs_notin _ _ _ (by simp [Act.regWrites]) σ (pre cfg σ), pre_eq]
    simp [Engine.chkRule, h, Engine.C_IDLE, Engine.C_RD, Engine.C_DO]
  · rw [hcode, outcome_eval]
    simp

end

/-! ## The shipped instances

Both engine geometries satisfy `2 ≤ ew`, so every theorem above applies to
the emitted RTL of `epochengine` (32-bit epochs, 512 cells) and of
`epochengine_tiny` (3-bit epochs, 4 cells — the width at which §3's
saturation is reachable). -/

theorem cfg32_hw : 2 ≤ Engine.cfg32.ew := by decide
theorem cfgTiny_hw : 2 ≤ Engine.cfgTiny.ew := by decide

/-- `Engine.design` is `mkDesign cfg32`. -/
theorem design_eq : Engine.design = Engine.mkDesign Engine.cfg32 := rfl

/-- **The refinement, at the shipped geometry.** -/
def sim32 : StutterSimulation (Protocol.sys 32 (2 ^ 9) 2)
    ((sysOpen Engine.design).reachablePart) := sim Engine.cfg32 cfg32_hw

/-- **`epochengine`'s freshness state satisfies §3's protocol invariant at
every cycle**, from power-on, under every input trace — i.e. whatever the two
cores do. -/
theorem epochengine_inv (ιs : Nat → InEnv) (n : Nat) :
    Protocol.Inv (abs Engine.cfg32 (Engine.design.runOpen ιs n Engine.design.reset)) :=
  design_inv Engine.cfg32 cfg32_hw _ (reachable_from_reset Engine.cfg32 ιs n)

/-- **T-E1 on `epochengine`.** Run the fabric `m` cycles from power-on under
any input trace; if no bump is in flight there (§3's post-return condition),
then for any further `n` cycles under any input trace, a reference carrying
an epoch below cell `i`'s home epoch never validates — at either volume,
however the cores behave. -/
theorem epochengine_stale_never_ok (ιs js : Nat → InEnv) (m n : Nat)
    (hq : (abs Engine.cfg32 (Engine.design.runOpen ιs m Engine.design.reset)).pending = none)
    (i : Fin (2 ^ 9)) (e₀ : BitVec 32)
    (hstale : e₀.toNat <
      ((abs Engine.cfg32 (Engine.design.runOpen ιs m Engine.design.reset)).cells i).epoch.toNat)
    (k : Fin 2) (r : Protocol.Req 32) (hri : r.cellIx = i.val) (hre : r.epoch = e₀) :
    Protocol.use (abs Engine.cfg32
      (Engine.design.runOpen js n (Engine.design.runOpen ιs m Engine.design.reset))) k r ≠ .ok :=
  T_E1_design_never_ok Engine.cfg32 cfg32_hw _
    (reachable_from_reset Engine.cfg32 ιs m) js n hq i e₀ hstale k r hri hre

/-- **T-E2 on `epochengine_tiny`.** Saturation is permanent death, at the
width where saturation is reachable (Layer-2 deviation E7). -/
theorem epochtiny_death_permanent (ιs js : Nat → InEnv) (m n : Nat) (i : Fin (2 ^ 2))
    (hd : ((abs Engine.cfgTiny (Engine.tiny.runOpen ιs m Engine.tiny.reset)).cells i).dead
      = true) :
    ∀ (k : Fin 2) (r : Protocol.Req 3), r.cellIx = i.val →
      Protocol.use (abs Engine.cfgTiny
        (Engine.tiny.runOpen js n (Engine.tiny.runOpen ιs m Engine.tiny.reset))) k r ≠ .ok :=
  (T_E2_design Engine.cfgTiny cfgTiny_hw _
    (reachable_from_reset Engine.cfgTiny ιs m) js n i hd).2.2

/-! ### …and the emitted RTL

Every theorem above is stated about `Design.cycleOpen`. The D-series emission
theorem carries it, cycle for cycle, to the µVerilog that `lake exe emit`
writes out — so "every reachable state of the compiled RTL" is literal. -/

theorem design_wf : Loom.Hw.Compile.DesignWF Engine.design :=
  Loom.Hw.Compile.designWFCheck_sound _ (by decide)

theorem tiny_wf : Loom.Hw.Compile.DesignWF Engine.tiny :=
  Loom.Hw.Compile.designWFCheck_sound _ (by decide)

/-- One cycle of the emitted module is one cycle of the `Design` these
theorems are about, under the same input valuation. -/
theorem emitted_cycleOpen (ι : InEnv) (σ : Hw.St) :
    Loom.Hw.Compile.forgetSt
        ((Loom.Hw.Compile.compile Engine.design).cycleOpen ι (Loom.Hw.Compile.convSt σ))
      = Engine.design.cycleOpen ι σ :=
  Loom.Hw.Compile.compile_cycleOpen Engine.design design_wf ι σ

/-! ## Axiom closures — the 3-axiom kernel closure on every headline. -/

#print axioms sim
#print axioms design_inv
#print axioms T_E1_design
#print axioms T_E1_design_never_ok
#print axioms T_E2_design
#print axioms T_E3_design
#print axioms T_E6_design
#print axioms run_abs
#print axioms square_cycle
#print axioms init_ok
#print axioms simAck
#print axioms bump_returns_within_15_cycles
#print axioms bump_bounded_response
#print axioms bump_returns_within_4_cycles
#print axioms epochengine_inv
#print axioms epochengine_stale_never_ok
#print axioms epochtiny_death_permanent
#print axioms chk_resp_0
#print axioms chk_resp_1
#print axioms outcome_eval
#print axioms emitted_cycleOpen


end Machines.Epoch.Refines
