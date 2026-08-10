-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Semantics
import Loom.Hw.FastEval
import Loom.Hw.DagEval
import Loom.Hw.SyncRead
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

/-!
# `epochengine` — the LNP64 §3 epoch engine as a Loom `Design` (Layer 2)

Layer 1 (`Machines/Epoch/Protocol.lean`) is the mechanized §3 protocol;
this is the hardware that Layer 3 will refine to it. `EPOCH_SPEC.md`
§"Engine design (Layer 2)" fixes the shape, and the file's two doctrine
sections fix the **binding constraint**:

> the ENGINE owns the per-volume epoch replicas (one bank per volume in
> engine memory) and the ack is engine-internal; cores may only REQUEST
> checks and bumps, never write freshness state.

So there are no `ack_core0`/`ack_core1` *inputs* (`EPOCH_SPEC.md`'s
Layer-2 port sketch predates its own superseding doctrine — recorded as
deviation E2). The acks are produced by the engine's own broadcast
sequencer, one referent volume per cycle, and `bump` returns only when the
whole span has acked. Every safety statement Layer 3 will make is
therefore unconditional over *all* core behaviour: an adversarial core can
present any handle it likes and can ask for any bump, and it still cannot
make a stale epoch validate.

## Structure

```
                 cell table (home)            per-volume replicas
        cell_epoch[2^aw] : ew          repl0[2^aw] : ew   repl1[2^aw] : ew
        cell_flags[2^aw] : 3                 |                  |
              |    |    |                    |                  |
        bump sequencer  +--- check unit 0 ---+                  |
              |              check unit 1 --------------------- +
        req0/req1 (op=bump)   req0/req1 (op=check)
```

* **Check unit per volume** (§3 class 0: "one compare, local,
  tile-bounded, never a fabric transaction"). Unit `k` reads *only*
  `repl{k}` for the freshness value and the home `cell_flags` for the
  dispositions — exactly `Protocol.useLocal`, whose replica argument is
  `s.repl k i` and whose `Cell` argument is the home cell (Layer-1
  deviation D2). A check is never blocked by an in-flight bump, which is
  what makes §3's in-flight liberty (`T_E7`) physically realizable.
* **One bump sequencer**, one bump in flight (v1), round-robin-free
  fixed priority (volume 0 wins a tie). It performs §3's O(1) home
  increment with saturation into permanent death, applies the policy's
  poison disposition, raises the broadcast (`inval_*`), collects one
  engine-internal ack per referent volume, and returns only when
  `b_acked` covers the span.
* **A cycle counter** (`bump_cyc`) runs while a bump is in flight and is
  latched into `bump_cycles` at the return — the demo's
  bump-issue → all-acked → fail-closed latency measurement.

## Memories are BRAM-shaped (D19/D20)

Every memory is read only through a dedicated unconditional register
latch (`Loom/Hw/SyncRead.lean` (S1)–(S4)), with pairwise-distinct address
expressions per memory (`b_a`, `c0_a`, `c1_a`), so `Design.syncReadOkB`
holds for all four banks and `yosys` infers block RAM.

**Cross-port collision obligation, and why it is architecturally free
here.** `repl{k}` can be read by check unit `k` in the same cycle the ack
sequencer writes it. D9 gives read-first (pre-cycle) semantics; Xilinx
silicon leaves a cross-port same-address collision indeterminate. That
cycle is *always* inside an in-flight bump (writes happen only in `B_ACK`,
and `bump_busy` is still high), and §3 explicitly permits a use concurrent
with a bump to observe either the old or the new epoch (`T_E7`). After
`bump` returns, no replica write is outstanding, so no observation after
the return point can be affected. The collision is therefore unobservable
*by architecture*, not merely by timing luck.

## Outcome encoding

Identical to `Protocol.Outcome`'s constructor order, so Layer 3's
refinement can read it off:
`ok = 0`, `badref = 1`, `poisoned = 2`, `stale = 3`, `denied = 4`.
-/

namespace Machines.Epoch.Engine

open Loom.Hw

/-! ## Configuration -/

/-- Engine geometry. `ew` is the epoch width (§3's capability-slot cell is
39 bits; v1 ships 32 — deviation E1), `aw` the cell-index width
(`2 ^ aw` cells). The referent span is fixed at the two cores, per
`EPOCH_SPEC.md` §Scope ("the minimum honest distributed instance"). -/
structure Cfg where
  /-- Emitted module name. -/
  name : String
  /-- Epoch width. -/
  ew : Nat
  /-- Cell-index width. -/
  aw : Nat

/-! ## Architected constants -/

/-- `Protocol.Outcome.ok`. -/
def OUT_OK : Nat := 0
/-- `Protocol.Outcome.badref`. -/
def OUT_BADREF : Nat := 1
/-- `Protocol.Outcome.poisoned`. -/
def OUT_POISONED : Nat := 2
/-- `Protocol.Outcome.stale`. -/
def OUT_STALE : Nat := 3
/-- `Protocol.Outcome.denied`. -/
def OUT_DENIED : Nat := 4

/-- `req_op` encoding: a freshness check (§3's `use`). -/
def OP_CHECK : Nat := 0
/-- `req_op` encoding: a bump (§3's architected bump). -/
def OP_BUMP : Nat := 1

/-- Check-unit FSM: idle. -/
def C_IDLE : Nat := 0
/-- Check-unit FSM: the cell/replica read is in the memory's read stage. -/
def C_RD : Nat := 1
/-- Check-unit FSM: latched data present, emit the outcome. -/
def C_DO : Nat := 2

/-- Bump FSM: idle (no bump in flight). -/
def B_IDLE : Nat := 0
/-- Bump FSM: home cell read in the memory's read stage. -/
def B_RD : Nat := 1
/-- Bump FSM: increment / saturate / poison, raise the broadcast. -/
def B_UP : Nat := 2
/-- Bump FSM: collect one engine-internal ack per referent volume. -/
def B_ACK : Nat := 3
/-- Bump FSM: the span has acked — return (§3's linearization point). -/
def B_RET : Nat := 4

/-- `cell_flags` bit 0. -/
def FLAG_POISON : Nat := 1
/-- `cell_flags` bit 1 (saturated death). -/
def FLAG_DEAD : Nat := 2
/-- `cell_flags` bit 2 is **reserved and always zero** (deviation E13).

v1 has no install/free op (deviation E4), so §3's slot-occupancy bit can
never change after reset: it would be a memory-resident constant whose only
source is the configuration-time reset image. Making it a stored constant
made the engine's correctness depend on a *non-zero* memory reset image,
which the openXC7 target flow silently fails to deliver for any bank it
maps to distributed LUT RAM (see `EPOCH_SPEC.md` §E13). The check unit now
sources occupancy from the constant `1` instead, and the bank's reset image
is all-zero — an image every configuration path delivers. Bit 2 stays
reserved for the v2 install/free op. -/
def FLAG_RESERVED : Nat := 4

/-! ## EDSL helpers -/

/-- Right-fold a list of actions into a `.seq` chain. -/
def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

/-- 1-bit literal. -/
def L1 (n : Nat) : Expr 1 := .lit (BitVec.ofNat 1 n)
/-- 2-bit literal. -/
def L2 (n : Nat) : Expr 2 := .lit (BitVec.ofNat 2 n)
/-- 3-bit literal. -/
def L3 (n : Nat) : Expr 3 := .lit (BitVec.ofNat 3 n)
/-- 16-bit literal. -/
def L16 (n : Nat) : Expr 16 := .lit (BitVec.ofNat 16 n)

/-- Bit `i` of a 3-bit flag/request word. -/
def bit3 (e : Expr 3) (i : Nat) : Expr 1 := .slice e i 1

section
variable (cfg : Cfg)

/-- Epoch-width literal. -/
def LE (n : Nat) : Expr cfg.ew := .lit (BitVec.ofNat cfg.ew n)
/-- The saturation value `maxE` (`Protocol.maxE`). -/
def maxEpoch : Expr cfg.ew := .lit (BitVec.allOnes cfg.ew)
/-- Cell-index-width literal. -/
def LA (n : Nat) : Expr cfg.aw := .lit (BitVec.ofNat cfg.aw n)

/-! ### Names -/

/-- Per-volume register name. -/
def vn (k : Nat) (s : String) : String := s!"c{k}_{s}"
/-- Per-volume request-port input name. -/
def rn (k : Nat) (s : String) : String := s!"req{k}_{s}"
/-- The replica bank of volume `k`. -/
def replMem (k : Nat) : String := s!"repl{k}"

/-! ## The check unit (§3 class 0)

`Protocol.useLocal c re r` written as a mux cone over the *replica*
`re = repl{k}[i]`, the home cell's dispositions and the request-level
structural/rights booleans (Layer-1 deviation D4). The precedence is
§3's, in §3's order: structural → poison → freshness → rights. -/

/-- The outcome of check unit `k`, as a 3-bit `Protocol.Outcome` code. -/
def outcome (k : Nat) : Expr 3 :=
  let fq : Expr 3 := .reg 3 (vn k "flags_q")
  let rq : Expr 3 := .reg 3 (vn k "f")
  let re : Expr cfg.ew := .reg cfg.ew (vn k "repl_q")
  let pe : Expr cfg.ew := .reg cfg.ew (vn k "e")
  let wf := bit3 rq 0
  let cls := bit3 rq 1
  let rts := bit3 rq 2
  let poi := bit3 fq 0
  let dea := bit3 fq 1
  let hit : Expr 1 := .eq re pe
  -- structural. §3's empty-slot clause is *not* a cone input: v1 has no
  -- install/free op (E4), so every slot is occupied for all time and the
  -- clause is unreachable. Sourcing it from the constant is what keeps the
  -- engine's reset image all-zero in `cell_flags` (E13).
  .mux (.not wf) (L3 OUT_BADREF) <|
  .mux (.not cls) (L3 OUT_BADREF) <|
  -- poison
  .mux poi (L3 OUT_POISONED) <|
  -- freshness (saturated death is a freshness failure — deviation D3)
  .mux dea (L3 OUT_STALE) <|
  .mux (.not hit) (L3 OUT_STALE) <|
  -- rights, strictly last
  .mux (.not rts) (L3 OUT_DENIED) (L3 OUT_OK)

/-- Check unit `k`: accept → read stage → outcome. Never gated on the
bump sequencer (that is `T_E7`'s physical content). -/
def chkRule (k : Nat) : Rule :=
  ⟨s!"chk{k}",
    actSeq [
      .write 1 (s!"resp{k}_valid") (L1 0),
      .ite (.eq (.reg 2 (vn k "st")) (L2 C_IDLE))
        (.ite (.and (.reg 1 (rn k "valid")) (.not (.reg 1 (rn k "op"))))
          (actSeq [
            .write cfg.aw (vn k "a") (.reg cfg.aw (rn k "cell")),
            .write cfg.ew (vn k "e") (.reg cfg.ew (rn k "epoch")),
            .write 3 (vn k "f") (.reg 3 (rn k "flags")),
            .write 1 (vn k "busy") (L1 1),
            .write 2 (vn k "st") (L2 C_RD) ])
          .skip) <|
      .ite (.eq (.reg 2 (vn k "st")) (L2 C_RD))
        (.write 2 (vn k "st") (L2 C_DO)) <|
      .ite (.eq (.reg 2 (vn k "st")) (L2 C_DO))
        (actSeq [
          .write 1 (s!"resp{k}_valid") (L1 1),
          .write 3 (s!"resp{k}_code") (outcome cfg k),
          .write 1 (vn k "busy") (L1 0),
          .write 2 (vn k "st") (L2 C_IDLE) ])
        .skip ]⟩

/-! ## The bump sequencer -/

/-- §3's saturating increment (`Protocol.satInc`): at the maximum the
counter stands still, so it never rolls back to a live value. -/
def satIncE : Expr cfg.ew :=
  let e : Expr cfg.ew := .reg cfg.ew "b_epoch_q"
  .mux (.eq e (maxEpoch cfg)) e (.add e (LE cfg 1))

/-- The post-bump flag word: poison is set-only, death is set exactly at
saturation, occupancy is untouched (`Protocol.Cell.bumped`). -/
def bumpedFlags : Expr 3 :=
  let fq : Expr 3 := .reg 3 "b_flags_q"
  .or fq
    (.or (.mux (.reg 1 "b_pol") (L3 FLAG_POISON) (L3 0))
         (.mux (.eq (satIncE cfg) (maxEpoch cfg)) (L3 FLAG_DEAD) (L3 0)))

/-- Latch a bump request from volume `k`. -/
def acceptBump (k : Nat) : Act :=
  actSeq [
    .write cfg.aw "b_a" (.reg cfg.aw (rn k "cell")),
    .write 1 "b_pol" (.reg 1 (rn k "policy")),
    .write 1 "b_owner" (L1 k),
    .write 1 "bump_busy" (L1 1),
    .write 16 "bump_cyc" (L16 0),
    .write 3 "b_st" (L3 B_RD) ]

/-- The one-in-flight bump sequencer: home increment (saturating, with the
policy's poison disposition), broadcast, engine-internal per-volume ack
collection, and the return that §3 makes the linearization point. -/
def bumpRule : Rule :=
  ⟨"bump",
    actSeq [
      .write 1 "bump_done0" (L1 0),
      .write 1 "bump_done1" (L1 0),
      .ite (.reg 1 "bump_busy")
        (.write 16 "bump_cyc" (.add (.reg 16 "bump_cyc") (L16 1))) .skip,
      .ite (.eq (.reg 3 "b_st") (L3 B_IDLE))
        (.ite (.and (.reg 1 (rn 0 "valid")) (.reg 1 (rn 0 "op")))
          (acceptBump cfg 0)
          (.ite (.and (.reg 1 (rn 1 "valid")) (.reg 1 (rn 1 "op")))
            (acceptBump cfg 1) .skip)) <|
      .ite (.eq (.reg 3 "b_st") (L3 B_RD))
        (.write 3 "b_st" (L3 B_UP)) <|
      .ite (.eq (.reg 3 "b_st") (L3 B_UP))
        (actSeq [
          .memWrite cfg.aw cfg.ew "cell_epoch" 0 (.reg cfg.aw "b_a") (satIncE cfg),
          .memWrite cfg.aw 3 "cell_flags" 0 (.reg cfg.aw "b_a") (bumpedFlags cfg),
          .write cfg.ew "b_target" (satIncE cfg),
          .write cfg.ew "inval_epoch" (satIncE cfg),
          .write cfg.aw "inval_cell" (.reg cfg.aw "b_a"),
          .write 1 "inval_valid" (L1 1),
          .write 2 "b_acked" (L2 0),
          .write 3 "b_st" (L3 B_ACK) ]) <|
      .ite (.eq (.reg 3 "b_st") (L3 B_ACK))
        (.ite (.not (.slice (.reg 2 "b_acked") 0 1))
          (.seq
            (.memWrite cfg.aw cfg.ew (replMem 0) 0 (.reg cfg.aw "b_a")
              (.reg cfg.ew "b_target"))
            (.write 2 "b_acked" (.or (.reg 2 "b_acked") (L2 1))))
          (.ite (.not (.slice (.reg 2 "b_acked") 1 1))
            (.seq
              (.memWrite cfg.aw cfg.ew (replMem 1) 0 (.reg cfg.aw "b_a")
                (.reg cfg.ew "b_target"))
              (.write 2 "b_acked" (.or (.reg 2 "b_acked") (L2 2))))
            (.write 3 "b_st" (L3 B_RET)))) <|
      .ite (.eq (.reg 3 "b_st") (L3 B_RET))
        (actSeq [
          .write 16 "bump_cycles" (.reg 16 "bump_cyc"),
          .ite (.reg 1 "b_owner")
            (.write 1 "bump_done1" (L1 1))
            (.write 1 "bump_done0" (L1 1)),
          .write 1 "bump_busy" (L1 0),
          .write 1 "inval_valid" (L1 0),
          .write 3 "b_st" (L3 B_IDLE) ])
        .skip ]⟩

/-! ## Memory read latches (D19 sync-read shape)

Six unconditional register latches, three distinct address expressions
(`b_a`, `c0_a`, `c1_a`), one destination register each and exactly one
syntactic write site per destination — `Design.syncReadOkB` for all four
banks. -/

/-- The six sanctioned read sites. -/
def latchRules : List Rule :=
  [ ⟨"lat_b_epoch",
      .write cfg.ew "b_epoch_q" (.memRead cfg.ew "cell_epoch" (.reg cfg.aw "b_a"))⟩,
    ⟨"lat_b_flags",
      .write 3 "b_flags_q" (.memRead 3 "cell_flags" (.reg cfg.aw "b_a"))⟩,
    ⟨"lat_c0_flags",
      .write 3 (vn 0 "flags_q") (.memRead 3 "cell_flags" (.reg cfg.aw (vn 0 "a")))⟩,
    ⟨"lat_c1_flags",
      .write 3 (vn 1 "flags_q") (.memRead 3 "cell_flags" (.reg cfg.aw (vn 1 "a")))⟩,
    ⟨"lat_c0_repl",
      .write cfg.ew (vn 0 "repl_q")
        (.memRead cfg.ew (replMem 0) (.reg cfg.aw (vn 0 "a")))⟩,
    ⟨"lat_c1_repl",
      .write cfg.ew (vn 1 "repl_q")
        (.memRead cfg.ew (replMem 1) (.reg cfg.aw (vn 1 "a")))⟩ ]

/-! ## Declarations -/

/-- Per-volume check-unit registers. -/
def volRegs (k : Nat) : List RegDecl :=
  [ ⟨vn k "st", 2, 0⟩, ⟨vn k "a", cfg.aw, 0⟩, ⟨vn k "e", cfg.ew, 0⟩,
    ⟨vn k "f", 3, 0⟩, ⟨vn k "flags_q", 3, 0⟩, ⟨vn k "repl_q", cfg.ew, 0⟩,
    ⟨vn k "busy", 1, 0⟩,
    ⟨s!"resp{k}_valid", 1, 0⟩, ⟨s!"resp{k}_code", 3, 0⟩ ]

def bumpRegs : List RegDecl :=
  [ ⟨"b_st", 3, 0⟩, ⟨"b_a", cfg.aw, 0⟩, ⟨"b_pol", 1, 0⟩, ⟨"b_owner", 1, 0⟩,
    ⟨"b_epoch_q", cfg.ew, 0⟩, ⟨"b_flags_q", 3, 0⟩,
    ⟨"b_target", cfg.ew, 0⟩, ⟨"b_acked", 2, 0⟩,
    ⟨"bump_busy", 1, 0⟩, ⟨"bump_done0", 1, 0⟩, ⟨"bump_done1", 1, 0⟩,
    ⟨"bump_cyc", 16, 0⟩, ⟨"bump_cycles", 16, 0⟩,
    ⟨"inval_valid", 1, 0⟩, ⟨"inval_cell", cfg.aw, 0⟩,
    ⟨"inval_epoch", cfg.ew, 0⟩ ]

/-- Per-volume request port (D15 inputs). Cores drive these; they carry
§3's `Req` (handle index, presented epoch, the structural/rights booleans)
and the op/policy — and **nothing else**. No freshness state is
core-writable. -/
def volInputs (k : Nat) : List InputDecl :=
  [ ⟨rn k "valid", 1⟩, ⟨rn k "op", 1⟩, ⟨rn k "cell", cfg.aw⟩,
    ⟨rn k "epoch", cfg.ew⟩, ⟨rn k "policy", 1⟩, ⟨rn k "flags", 3⟩ ]

/-- Cells reset live: epoch 1 (§3 reserves epoch 0 as invalid), occupied,
unpoisoned, and both replicas in step with their home — exactly
`Protocol.Init`. There is no core-visible *install* op in v1 (deviation
E4), so the reset image is the only way freshness state is ever
established, and `Protocol.Init` holds by construction.

`cell_flags` resets to **all zero** (E13): occupancy is not stored (see
`FLAG_RESERVED`), poison and death both reset clear, so the only banks
carrying a non-zero reset image are the three epoch banks — and those are
exactly the banks the target flow maps to block RAM, whose INIT it does
deliver. `scripts/check_mem_init.py` is the standing guard on that. -/
def mems : List MemDecl :=
  [ ⟨"cell_epoch", cfg.aw, cfg.ew, fun _ => 1⟩,
    ⟨"cell_flags", cfg.aw, 3, fun _ => 0⟩,
    ⟨replMem 0, cfg.aw, cfg.ew, fun _ => 1⟩,
    ⟨replMem 1, cfg.aw, cfg.ew, fun _ => 1⟩ ]

/-- The open `Design`. -/
def mkDesign : Design where
  name := cfg.name
  regs := volRegs cfg 0 ++ volRegs cfg 1 ++ bumpRegs cfg
  -- D39a: outputs are mandatory and explicit, like inputs. This design's
  -- whole register set IS its interface, so it says so rather than
  -- relying on a default that exported everything silently.
  outputs := (volRegs cfg 0 ++ volRegs cfg 1 ++ bumpRegs cfg).map (·.name)
  mems := mems cfg
  rules := latchRules cfg ++ [chkRule cfg 0, chkRule cfg 1, bumpRule cfg]
  inputs := volInputs cfg 0 ++ volInputs cfg 1

end

/-! ## The shipped instances -/

/-- The SoC instance: 32-bit epochs, 512 cells. -/
def cfg32 : Cfg := { name := "epochengine", ew := 32, aw := 9 }

/-- The saturation instance: 3-bit epochs, 4 cells. Saturation at
`allOnes 32` is not reachable in a testbench, so the ladder exercises §3's
"saturation is permanent death" at a width where it is (`Protocol`'s
theorems are proved for *all* `W`, deviation D9). -/
def cfgTiny : Cfg := { name := "epochengine_tiny", ew := 3, aw := 2 }

/-- `epochengine` — the shipped engine. -/
def design : Design := mkDesign cfg32

/-- `epochengine_tiny` — the narrow-epoch twin. -/
def tiny : Design := mkDesign cfgTiny

/-! ## Obligations -/

/-- The four banks are D19 sync-read shaped, so they infer as block RAM. -/
def syncReadOkB (d : Design) : Bool :=
  d.syncReadOkB "cell_epoch" && d.syncReadOkB "cell_flags"
    && d.syncReadOkB "repl0" && d.syncReadOkB "repl1"

def syncReadReport (d : Design) : String :=
  String.intercalate "\n"
    (["cell_epoch", "cell_flags", "repl0", "repl1"].map d.syncReadReport)

theorem design_syncReadOk : syncReadOkB design = true := by rfl

theorem tiny_syncReadOk : syncReadOkB tiny = true := by rfl

/-- The FastEval side condition, discharged in the kernel, so `fastCycleOpen`
is a *proved* stand-in for `Design.cycleOpen` on this design (D18). -/
theorem design_fastWF : design.fastWFB = true := by rfl

theorem tiny_fastWF : tiny.fastWFB = true := by rfl

/-- The public generated simulator for `design`; its evaluator and reset are
derived from the design, and `wf` connects them to the reference semantics. -/
def simulator : FastEval.VerifiedSimulator design := ⟨design_fastWF⟩

def tinySimulator : FastEval.VerifiedSimulator tiny := ⟨tiny_fastWF⟩

/-- The instantiated open-design theorem: replaying any input trace through
`fastCycleOpen` agrees with the reference semantics on every declared
coordinate. This is why the selftest below is evidence about the `Design`
and not about a hand-written mirror of it. -/
theorem fastRunOpen_agrees (n : Nat) (ιs : Nat → InEnv) :
    Agree design
      (simulator.runOpen ιs n simulator.reset)
      (design.runOpen ιs n design.reset) :=
  simulator.runOpenFromReset_eq n ιs

theorem tiny_fastRunOpen_agrees (n : Nat) (ιs : Nat → InEnv) :
    Agree tiny
      (tinySimulator.runOpen ιs n tinySimulator.reset)
      (tiny.runOpen ιs n tiny.reset) :=
  tinySimulator.runOpenFromReset_eq n ιs

/-! ## The selftest (D18: the verified fast evaluator *is* the oracle)

There is no hand-written ISS here, by design: `fastRunOpen_agrees` above
makes `fastCycleOpen` a proved stand-in for `Design.cycleOpen`, so the
scenarios below are statements about the `Design` itself. -/

/-- One volume's request port for one cycle. -/
structure Req where
  /-- Assert the request. -/
  valid : Bool := false
  /-- `OP_CHECK` or `OP_BUMP`. -/
  op : Nat := OP_CHECK
  /-- Cell index. -/
  cell : Nat := 0
  /-- The presented reference epoch (§3's `ref.epoch`). -/
  epoch : Nat := 0
  /-- `poison` policy for a bump. -/
  policy : Bool := false
  /-- `{rights, classOk, wellFormed}` — §3's structural/rights facts. -/
  flags : Nat := 7
  deriving Repr

/-- Both request ports for one cycle. -/
structure Stim where
  /-- Volume 0's port. -/
  r0 : Req := {}
  /-- Volume 1's port. -/
  r1 : Req := {}
  deriving Repr

def idle : Stim := {}

def Req.drive (r : Req) (k : Nat) (n : String) (w : Nat) : Option (BitVec w) :=
  if n = s!"req{k}_valid" then some ((BitVec.ofBool r.valid).setWidth w)
  else if n = s!"req{k}_op" then some ((BitVec.ofNat 1 r.op).setWidth w)
  else if n = s!"req{k}_cell" then some ((BitVec.ofNat 32 r.cell).setWidth w)
  else if n = s!"req{k}_epoch" then some ((BitVec.ofNat 64 r.epoch).setWidth w)
  else if n = s!"req{k}_policy" then some ((BitVec.ofBool r.policy).setWidth w)
  else if n = s!"req{k}_flags" then some ((BitVec.ofNat 3 r.flags).setWidth w)
  else none

def Stim.toEnv (s : Stim) : InEnv := fun n w =>
  match s.r0.drive 0 n w with
  | some v => v
  | none => match s.r1.drive 1 n w with
    | some v => v
    | none => 0#w

/-- What the ladder watches each cycle. -/
structure Obs where
  /-- Cycle index. -/
  k : Nat
  /-- Volume 0 response pulse / code. -/
  r0v : Nat
  /-- Volume 0 outcome code. -/
  r0c : Nat
  /-- Volume 1 response pulse. -/
  r1v : Nat
  /-- Volume 1 outcome code. -/
  r1c : Nat
  /-- Bump return pulse to volume 0. -/
  bd0 : Nat
  /-- Bump return pulse to volume 1. -/
  bd1 : Nat
  /-- Latched bump-issue → all-acked latency. -/
  bcyc : Nat
  /-- The engine-internal ack vector. -/
  acked : Nat
  /-- Broadcast in flight. -/
  inval : Nat
  deriving Repr

def peekN (d : Design) (fs : FastSt) (n : String) : Nat :=
  ((d.fastRegs fs).lookup n).getD 0

private def runTraceWith (d : Design) (step : InEnv → FastSt → FastSt)
    (reset : FastSt) (ss : List Stim) : List Obs := Id.run do
  let mut fs := reset
  let mut out : List Obs := []
  let mut k := 0
  for s in ss do
    fs := step s.toEnv fs
    out := out ++ [{ k := k
                     r0v := peekN d fs "resp0_valid", r0c := peekN d fs "resp0_code"
                     r1v := peekN d fs "resp1_valid", r1c := peekN d fs "resp1_code"
                     bd0 := peekN d fs "bump_done0", bd1 := peekN d fs "bump_done1"
                     bcyc := peekN d fs "bump_cycles"
                     acked := peekN d fs "b_acked", inval := peekN d fs "inval_valid" }]
    k := k + 1
  return out

/-- Run a stimulus list through the verified tree evaluator, recording the
observation after every cycle. -/
def runTrace (d : Design) (ss : List Stim) : List Obs :=
  runTraceWith d (fastCycleOpen d.elaborate) d.fastReset ss

/-- The same trace runner through an already certified DAG. Keeping the DAG
as an argument makes certificate failure explicit at the IO boundary and
amortizes preparation across every scenario in the acceptance ladder. -/
def runTraceDag {d : Design} (dag : DagEval.VerifiedSimulator d)
    (ss : List Stim) : List Obs :=
  runTraceWith d dag.cycleOpen dag.reset ss

/-- The outcome codes volume `k` reported, in order. -/
def codes (obs : List Obs) (k : Nat) : List Nat :=
  (obs.filter (fun o => if k = 0 then o.r0v = 1 else o.r1v = 1)).map
    (fun o => if k = 0 then o.r0c else o.r1c)

def chk (k cell ep : Nat) (flags : Nat := 7) : Stim :=
  if k = 0 then { r0 := { valid := true, op := OP_CHECK, cell := cell, epoch := ep, flags := flags } }
  else { r1 := { valid := true, op := OP_CHECK, cell := cell, epoch := ep, flags := flags } }

def bmp (k cell : Nat) (poison : Bool := false) : Stim :=
  if k = 0 then { r0 := { valid := true, op := OP_BUMP, cell := cell, policy := poison } }
  else { r1 := { valid := true, op := OP_BUMP, cell := cell, policy := poison } }

/-- `n` idle cycles. -/
def gap (n : Nat) : List Stim := List.replicate n idle

/-- A check followed by enough idle cycles to see the response. -/
def chkSeq (k cell ep : Nat) (flags : Nat := 7) : List Stim := chk k cell ep flags :: gap 3

/-- A bump followed by enough idle cycles for the whole broadcast/ack/return. -/
def bmpSeq (k cell : Nat) (poison : Bool := false) : List Stim := bmp k cell poison :: gap 9

private def expect (name : String) (got want : List Nat) : IO Nat := do
  if got = want then
    IO.println s!"  OK   {name}: {got}"
    return 0
  else
    IO.println s!"  FAIL {name}: got {got} want {want}"
    return 1

/-- The engine acceptance ladder. Each scenario is named for the §3
sentence / Layer-1 theorem it exercises. -/
def selftest : IO Unit := do
  let dag ← DagEval.prepareSimulator simulator "epochengine"
  let tinyDag ← DagEval.prepareSimulator tinySimulator "epochengine_tiny"
  let run := runTraceDag dag
  let runTiny := runTraceDag tinyDag
  let mut bad := 0
  -- (1) check-hit: the reset image is coherent (`Protocol.Init`), so a
  -- reference carrying the reset epoch validates.
  bad := bad + (← expect "check-hit          (ok)"
    (codes (run (chkSeq 0 5 1)) 0) [OUT_OK])
  -- (1b) precedence: the four failure classes, in §3's order.
  bad := bad + (← expect "check-badref (¬wf)  "
    (codes (run (chkSeq 0 5 1 6)) 0) [OUT_BADREF])
  bad := bad + (← expect "check-denied(¬rts)  "
    (codes (run (chkSeq 0 5 1 3)) 0) [OUT_DENIED])
  bad := bad + (← expect "check-stale (ep≠)   "
    (codes (run (chkSeq 0 5 9)) 0) [OUT_STALE])
  -- (2) bump → broadcast → per-volume ack → return, then the old epoch is
  -- stale at BOTH volumes and the new one validates (T-E1).
  let t2 := run (bmpSeq 0 5 ++ chkSeq 0 5 1 ++ chkSeq 1 5 1
                              ++ chkSeq 0 5 2 ++ chkSeq 1 5 2)
  bad := bad + (← expect "post-bump vol0      " (codes t2 0) [OUT_STALE, OUT_OK])
  bad := bad + (← expect "post-bump vol1      " (codes t2 1) [OUT_STALE, OUT_OK])
  bad := bad + (← expect "ack vector 0→1→3    "
    ((t2.map (·.acked)).eraseReps.take 3) [0, 1, 3])
  bad := bad + (← expect "one bump return     "
    [(t2.filter (fun o => o.bd0 = 1)).length] [1])
  -- (3) poison permanence (T-E3): a poison bump fails *current-epoch*
  -- references too, forever.
  let t3 := run (bmpSeq 0 7 true ++ chkSeq 0 7 2 ++ chkSeq 1 7 2
                              ++ gap 20 ++ chkSeq 0 7 2 ++ chkSeq 0 7 1)
  bad := bad + (← expect "poison vol0 forever "
    (codes t3 0) [OUT_POISONED, OUT_POISONED, OUT_POISONED])
  bad := bad + (← expect "poison vol1         " (codes t3 1) [OUT_POISONED])
  -- (4) saturation is permanent death (T-E2), at a width where the
  -- saturation point is reachable.
  let sat := (List.replicate 6 (bmpSeq 0 1)).flatten
  let t4 := runTiny (sat ++ chkSeq 0 1 7 ++ chkSeq 1 1 7
                            ++ bmpSeq 0 1 ++ chkSeq 0 1 7)
  bad := bad + (← expect "saturated ⇒ stale   "
    (codes t4 0) [OUT_STALE, OUT_STALE])
  bad := bad + (← expect "saturated vol1      " (codes t4 1) [OUT_STALE])
  -- (5) in-flight liberty (T-E7): a use concurrent with the bump MAY
  -- succeed — volume 1 checks the pre-bump epoch while the broadcast is
  -- still in flight and gets `ok`; after the return the same check is
  -- `-STALE`.
  let t5 := run ([{ r0 := (bmp 0 3).r0, r1 := (chk 1 3 1).r1 }]
                              ++ gap 12 ++ chkSeq 1 3 1)
  bad := bad + (← expect "in-flight ok→stale  " (codes t5 1) [OUT_OK, OUT_STALE])
  -- (6) both volumes may check while a bump is in flight and afterwards.
  if bad = 0 then
    IO.println "EPOCH ENGINE SELFTEST OK — check/bump/ack/return, precedence, poison, saturation, in-flight liberty"
  else
    IO.println s!"EPOCH ENGINE SELFTEST FAILED ({bad})"

/-- Report the measured bump latency (bump issue → all volumes acked →
return), which is the demo's headline number. -/
def latency : IO Unit := do
  let t := runTrace design (bmpSeq 0 5)
  let ret := t.filter (fun o => o.bd0 = 1)
  IO.println s!"bump latency (issue→all-acked→return): {(ret.map (·.bcyc))} cycles"
  IO.println s!"broadcast in flight for {(t.filter (fun o => o.inval = 1)).length} cycles"

/-- `fastCycleOpen` ≡ the reference `Design.cycleOpen` on the acceptance
stimulus — the D18 corroboration leg beside the proof. -/
def refCheck : IO Unit := do
  let ss := bmpSeq 0 5 true ++ chkSeq 0 5 1 ++ chkSeq 1 5 2 ++ bmpSeq 1 5
  let ok ← tiny.lockstep ss.length (fun c => (ss.getD c idle).toEnv)
  if ok then IO.println "EPOCH ENGINE REF LOCKSTEP OK (fastCycleOpen ≡ Design.cycleOpen)"
  else IO.println "EPOCH ENGINE REF LOCKSTEP FAILED"

/-- Emit the ladder's expected `resp`/`bump` observations, so the iverilog
testbench checks the *same* oracle the Lean selftest does. -/
def predict (nm : String) (d : Design) (ss : List Stim) : IO Unit := do
  IO.println s!"--- {nm} ---"
  for o in runTrace d ss do
    if o.r0v = 1 || o.r1v = 1 || o.bd0 = 1 || o.bd1 = 1 then
      IO.println s!"{o.k} r0v={o.r0v} r0c={o.r0c} r1v={o.r1v} r1c={o.r1c} bd0={o.bd0} bd1={o.bd1} bcyc={o.bcyc}"

/-! ### The iverilog testbench's stimulus, as one continuous run

`rtl/tb_epochengine.v` replays *exactly* these two traces (memories are
not reset by `rst`, so the scenarios are chained on distinct cells rather
than restarted) and prints the same event lines, which makes the RTL leg a
literal `diff` against the verified fast evaluator. -/

/-- The 32-bit engine's acceptance trace. -/
def tbTrace : List Stim :=
  chkSeq 0 5 1                                     -- (a) check-hit        → ok
  ++ chkSeq 0 5 9                                  -- (b) epoch mismatch   → stale
  ++ chkSeq 0 5 1 6                                -- (c) ¬wellFormed      → badref
  ++ chkSeq 0 5 1 3                                -- (d) ¬rights          → denied
  ++ [{ r0 := (bmp 0 5).r0, r1 := (chk 1 5 1).r1 }] ++ gap 3
                                                   -- (e) in-flight use    → ok (T-E7)
  ++ gap 9
  ++ chkSeq 0 5 1 ++ chkSeq 1 5 1                  -- (f) post-return stale at BOTH volumes
  ++ chkSeq 0 5 2 ++ chkSeq 1 5 2                  -- (g) the new epoch validates
  ++ bmpSeq 0 7 true                               -- (h) poison bump
  ++ chkSeq 0 7 2 ++ chkSeq 1 7 2                  -- (i) poisoned at the *current* epoch
  ++ gap 20 ++ chkSeq 0 7 2                        -- (j) …forever

/-- The narrow-epoch twin's saturation trace. -/
def tbTraceTiny : List Stim :=
  (List.replicate 6 (bmpSeq 0 1)).flatten          -- epoch 1 → 7 = allOnes
  ++ chkSeq 0 1 7 ++ chkSeq 1 1 7                  -- dead ⇒ -STALE at both volumes
  ++ bmpSeq 0 1 ++ chkSeq 0 1 7                    -- no bump revives it

end Machines.Epoch.Engine
