-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Trees
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO
import Loom.Hw.SyncRead

/-!
# Lnp64mini — the DDR-backed MINI LNP64 soft-core, ported to Loom (open design)

Faithful, bug-for-bug port of
`remote-fpga/fpga/substrate0/rtl/lnp64mini3_regs.v` (the 685-line spec).
Every register, FSM state (S_IDLE..S_GPS), opcode branch, priority
encoder, the sleep scan and the single regfile write funnel are mirrored.

Everything clock-domain / AXI / BSCAN-CDC stays in the untrusted wrapper;
the wrapper delivers one BSCAN write per JTAG UPDATE as a one-cycle pulse
(`cmd_valid`,`cmd_idx`,`cmd_data` == wr_pulse/wr_addr_j/wr_data_j) and the
two AXI masters as handshake input ports (`m_done`/`m_rdata`/`m_busy`,
`gp_done`/`gp_rdata`/`gp_busy`).

See `Machines/Lnp64mini/PORTING_SPEC.md` for the binding decisions.
-/

namespace Machines.Lnp64mini

open Loom.Hw

/-! ## Constants (from the Verilog) -/

def ID_MAGIC   : Nat := 0x53301017
def TEXT_BASE  : Nat := 0x1000
def PROG_BASE  : Nat := 0x20000000
def DATA_BASE  : Nat := 0x10000000
def UART_ADDR    : Nat := 0x8000
def UART_RX_ADDR : Nat := 0x8008
def NT : Nat := 32
def CW : Nat := 5
def AW : Nat := 10

-- FSM states (localparams S_IDLE=0 .. S_GPS=20)
def S_IDLE : Nat := 0
def S_F0   : Nat := 1
def S_FW   : Nat := 2
def S_EX   : Nat := 3
def S_L0   : Nat := 4
def S_L1   : Nat := 5
def S_TRAP : Nat := 6
def S_DL   : Nat := 7
def S_DST  : Nat := 8
def S_DSW  : Nat := 9
def S_WAIT : Nat := 10
def S_CLONE2 : Nat := 11
def S_FTX1 : Nat := 12
def S_MUL  : Nat := 13
def S_RD   : Nat := 14
def S_RD2  : Nat := 15
def S_DIV  : Nat := 16
def S_PAUSE : Nat := 17
def S_CLONE3 : Nat := 18
def S_GPL  : Nat := 19
def S_GPS  : Nat := 20

/-! ## Input ports (D15) -/

def mDone    : Expr 1  := .reg 1  "m_done"
def mRdata   : Expr 64 := .reg 64 "m_rdata"
def mBusy    : Expr 1  := .reg 1  "m_busy"
def gpDone   : Expr 1  := .reg 1  "gp_done"
def gpRdata  : Expr 32 := .reg 32 "gp_rdata"
def gpBusy   : Expr 1  := .reg 1  "gp_busy"
def cmdValid : Expr 1  := .reg 1  "cmd_valid"
def cmdIdx   : Expr 7  := .reg 7  "cmd_idx"
def cmdData  : Expr 32 := .reg 32 "cmd_data"

/-! ### SMP extensions (DUAL_SPEC.md "Core extensions")

Four new D15 inputs (`res_kill`, `doorbell`, `hold`, `sc_fail`) and four
new registers (`wake_out`, `lr_req`, `sc_req`, `sc_pending`) turn the
single-core design into an SMP-capable node. Every input is inert at 0 and
`Soc.lean` ties all four off, so the single-core `lnp64mini_soc` behaves
exactly as before (silicon regression: `tb_lnp64mini_soc.v` on
`loomcheck.hex` is bit-identical to §63).

* `res_kill` — pulse clears `lr_valid` (the arbiter's global-LR/SC hook).
* `doorbell` — pulse moves every FUTEX-blocked thread (tstate=3) to READY.
  Spurious wakes are safe: a woken `FUTEX_WAIT` re-executes its DDR compare
  and re-blocks if the word is unchanged.
* `hold`     — while high the FSM is frozen **at the instruction boundary
  `S_F0`** (`fsmEn` gains `¬holdEn`) and the sleep scan pauses; CORE1_HOLD
  in the dual wrapper drives it. Freezing only in `S_F0` is what makes the
  hold safe: no DDR transaction is in flight there, so no `m_done` pulse can
  be missed while the core is stopped (a hold that froze `S_FW`/`S_DL`/
  `S_DSW` would drop the completion and wedge the core forever). -/
def resKill  : Expr 1  := .reg 1  "res_kill"
def doorbell : Expr 1  := .reg 1  "doorbell"

/-! ### EXT-4 — the park/wake directory (`EXTEND_SPEC.md` increment 4)

Appendix F #6; §3 calls it "the epoch machine's client annex". Mini had both
halves and they were not connected: `tfutex[i]` records *what* a parked
thread waits on, but the cross-core `doorbell` woke **every** thread with
`tstate = FUTEX` whatever key it was parked on. If a thread parked on key A
is observable to a wake on key B, "parked on" means nothing.

**The whole increment is: the comparator bank is SHARED, not duplicated.**
The first attempt gave the doorbell its own 32-slot bank beside the one
`FUTEX_WAKE` already has, and it cost 8 073 LUTs and would not route (58 %
utilisation, `sysclk` below the board clock). The added *state* was 32 flops;
every one of those LUTs was a second copy of a comparison the design already
computes. Narrowing that copy from 64 to 16 bits recovered 6 800 LUTs and
0.22 MHz — i.e. width was never the problem, **duplication** was.

So there is exactly one bank, in `smpRule`, and its operand is muxed:

* `wakeKey` = `rdval` for a local `FUTEX_WAKE`, `doorbell_key` for a remote
  one — one 64-bit 2:1 mux, not 32 more comparators.
* `wakeEn`  = local pulse ∨ doorbell.
* the `matchesBefore < a` count limit applies to the **local** wake only; a
  remote doorbell wakes every thread parked on that key, which is the
  ordinary futex broadcast-on-key.

The bank moved out of the `S_EX` branch into `smpRule`, which already ran
*after* `fsmRule` — so the commit order is unchanged (D9, last write wins)
and `sleepScanRule`, which is the only other `tstate` writer that could
collide, still runs before both. -/
def doorbell_key : Expr 64 := .reg 64 "doorbell_key"
def hold     : Expr 1  := .reg 1  "hold"

/-- `sc_fail` — the arbiter's verdict on a *global* `SC`, valid on the cycle
it completes the store-conditional (`m_done` while `sc_pending`). See
`HpArbiter` and DUAL_SPEC "Deviations": the reservation has to be validated
at the serialization point, not two cycles earlier in `S_EX`. The tag
registers `lr_req`/`sc_req` (pulses beside `core_rd`/`core_wr`) tell the
arbiter which read takes a reservation and which write is conditional. -/
def scFail   : Expr 1  := .reg 1  "sc_fail"

/-- `wake_out` pulses for one cycle when `FUTEX_WAKE` (S_EX, op 0xcc)
executes, regardless of local matches. In the dual SoC it is wired straight
into the *other* core's `doorbell` input — a register-to-input connection,
i.e. already a full register stage, no combinational cross-core path. -/
def wake_out : Expr 1  := .reg 1  "wake_out"

/-- EXT-4. The key `wake_out` is pulsing for, captured on the pulse cycle and
held otherwise; wired to the other core's `doorbell_key` in the dual SoC —
register output to input, so still no combinational cross-core path. -/
def wake_key : Expr 64 := .reg 64 "wake_key"

/-! ## Scalar register shorthands -/

def cur       : Expr 5  := .reg 5  "cur"
def pc        : Expr 64 := .reg 64 "pc"
def retire    : Expr 32 := .reg 32 "retire"
def running   : Expr 1  := .reg 1  "running"
def halted    : Expr 1  := .reg 1  "halted"
def st        : Expr 5  := .reg 5  "st"
def ir        : Expr 64 := .reg 64 "ir"
def a         : Expr 64 := .reg 64 "a"
def b         : Expr 64 := .reg 64 "b"
def rdval     : Expr 64 := .reg 64 "rdval"
def sel_t     : Expr 64 := .reg 64 "sel_t"
def sel_f     : Expr 64 := .reg 64 "sel_f"
def mem_is_store : Expr 1  := .reg 1  "mem_is_store"
def trap_active  : Expr 1  := .reg 1  "trap_active"
def trapped_op   : Expr 8  := .reg 8  "trapped_op"
def core_rd   : Expr 1  := .reg 1  "core_rd"
def core_wr   : Expr 1  := .reg 1  "core_wr"
def core_addr : Expr 32 := .reg 32 "core_addr"
def core_wdata: Expr 64 := .reg 64 "core_wdata"
def jtag_rd   : Expr 1  := .reg 1  "jtag_rd"
def jtag_wr   : Expr 1  := .reg 1  "jtag_wr"
def jtag_wdata: Expr 64 := .reg 64 "jtag_wdata"
def ddr_addr_j: Expr 32 := .reg 32 "ddr_addr_j"
def ddr_lo_j  : Expr 32 := .reg 32 "ddr_lo_j"
def ddr_rd_l  : Expr 64 := .reg 64 "ddr_rd_l"
def ddr_q     : Expr 64 := .reg 64 "ddr_q"
def bus_req   : Expr 1  := .reg 1  "bus_req"
def gp_rd     : Expr 1  := .reg 1  "gp_rd"
def gp_wr     : Expr 1  := .reg 1  "gp_wr"
def gp_addr_r : Expr 32 := .reg 32 "gp_addr_r"
def gp_wdata_r: Expr 32 := .reg 32 "gp_wdata_r"
def dmem_we   : Expr 1  := .reg 1  "dmem_we"
def dmem_a    : Expr 9  := .reg 9  "dmem_a"
def dmem_wd   : Expr 64 := .reg 64 "dmem_wd"
def dmem_rd   : Expr 64 := .reg 64 "dmem_rd"
def uart_wptr : Expr 9  := .reg 9  "uart_wptr"
def uart_ridx : Expr 8  := .reg 8  "uart_ridx"
def uart_byte : Expr 8  := .reg 8  "uart_byte"
def rx_wptr   : Expr 9  := .reg 9  "rx_wptr"
def rx_rptr   : Expr 9  := .reg 9  "rx_rptr"
def ld_boff_q : Expr 3  := .reg 3  "ld_boff_q"
def ld_op_q   : Expr 8  := .reg 8  "ld_op_q"
def ld_rd_q   : Expr 5  := .reg 5  "ld_rd_q"
def lr_addr   : Expr 64 := .reg 64 "lr_addr"
def lr_valid  : Expr 1  := .reg 1  "lr_valid"
/-- A global (DDR) `SC` is outstanding: `S_DSW` must consume `sc_fail`. -/
def sc_pending : Expr 1 := .reg 1 "sc_pending"
def futex_exp : Expr 64 := .reg 64 "futex_exp"
def futex_addr_q : Expr 64 := .reg 64 "futex_addr_q"
/-! ### EXT-1 — the preemption tick (`EXTEND_SPEC.md` increment 1)

`quantum` is the per-core reload value in **core cycles** and `qctr` the
running thread's remaining quantum. Both are 32 bits (the width of the
BSCAN `cmd_data` that loads them). `quantum = 0` — the reset value — means
**disabled**: `quantumOn` is false, so nothing decrements, nothing reloads
and nothing preempts, and the core is bit-for-bit the cooperative machine
of §63. -/
def quantum   : Expr 32 := .reg 32 "quantum"
def qctr      : Expr 32 := .reg 32 "qctr"

/-! ### EXT-2 — protection domains (`EXTEND_SPEC.md` increment 2)

A **domain** is the unit every later increment is scoped by: gates cross
between domains, capability transfer re-keys across them, and a VMA root is
a property of one. The tag itself is per *thread*, not per core, because
threads are what the scheduler moves — a core's domain is whatever its
current thread's is.

`tdom` (32x8) holds it. Two consequences make this a real mechanism rather
than a label:

* **The current domain is `tdom[cur]`, read combinationally — not a
  register.** A register would lag `cur` by a cycle, and the cycle after a
  context switch is exactly when a stale domain tag would be a privilege
  hole: the incoming thread's first instruction would execute under the
  outgoing thread's authority. An async `memRead` at `cur` is *always*
  right, costs one LUTRAM read port, and has no write sites to keep in sync
  with the eight places that assign `cur`.
* **A thread cannot leave its domain by spawning.** `CLONE` writes the
  parent's `tdom[cur]` into the child's slot (`tdomTriples` entry 2), so
  domain membership is inherited, never chosen. Without this a domain could
  escape itself with one instruction.

`droot` (16x64) is the per-domain root pointer — the capability-table root
today, the VMA root once EXT-7 lands. Sixteen domains is the width the
demo needs and keeps the table a single small LUTRAM.

**The guest does not notice.** Both memories reset to zero and `cmd 13`
sweeps every thread to domain 0, so NetBSD runs as domain 0 and every
comparison this increment adds is against a constant. That is
deliberate: EXT-2 installs the tag and its inheritance rule, and the
enforcement that consumes it arrives with gates (EXT-5) and the MMU
(EXT-7). -/
def tdomRd (idx : Expr 5) : Expr 8 := .memRead 8 "tdom" idx
/-- EXT-5: the gate table and the per-thread depth-1 continuation. -/
def gateEntRd (g : Expr 4) : Expr 64 := .memRead 64 "gate_ent" g
def gateDomRd (g : Expr 4) : Expr 8  := .memRead 8  "gate_dom" g
def tcontRd (idx : Expr 5) : Expr 64 := .memRead 64 "tcont" idx
def tcdomRd (idx : Expr 5) : Expr 8  := .memRead 8  "tcdom" idx
/-- EXT-6: the per-domain capability inbox. -/
def capIboxRd (d : Expr 4) : Expr 64 := .memRead 64 "cap_ibox" d
/-! EXT-7: the TLB. Four parallel arrays indexed by the VPN's low 3 bits
(direct-mapped), so a lookup is one read of each plus one comparison. -/
def tlbVpnRd  (i : Expr 3) : Expr 32 := .memRead 32 "tlb_vpn" i
def tlbPpnRd  (i : Expr 3) : Expr 32 := .memRead 32 "tlb_ppn" i
def tlbDomRd  (i : Expr 3) : Expr 8  := .memRead 8  "tlb_dom" i
/-- EXT-7: the valid bits are a **bitmap register**, not a memory. The §15
shootdown (`cmd 67`) invalidates *every* entry naming the bumped cell, i.e.
several slots in one cycle, and one memory write port cannot do that -- which
is exactly what `Design.emit` refused when this was a memory (D38/CE10). Same
shape as EXT-3's `poison` and EXT-6's `cap_ival`: state written at many
indices at once is a register bitmap. -/
def tlb_vld : Expr 8 := .reg 8 "tlb_vld"
def tlbVldRd  (i : Expr 3) : Expr 1  :=
  .eq (.slice (.shr tlb_vld (.zext i 8)) 0 1) (.lit (BitVec.ofNat 1 1))
def tlbCellRd (i : Expr 3) : Expr 8  := .memRead 8  "tlb_cell" i

/-- The domain the core is executing in **right now**: the current thread's
tag, combinationally. See the note above on why this is not a register. -/
def domCur : Expr 8 := tdomRd cur

/-! **Deliberately not here: the per-domain root table (`droot`).** A
domain's capability/VMA root is real state, but nothing in EXT-2 *reads*
it, and a write-only memory is dead silicon — yosys deletes it, and then
the emitted netlist no longer matches the design the proofs are about. It
lands with its first consumer (EXT-6/EXT-7), not before. -/

/-- Observation only: `cur_dom` mirrors `domCur` one cycle late so the BSCAN
debug path (which reads registers, not memories) can see the executing
domain. Nothing in the datapath reads it — the datapath uses `domCur`, which
does not lag. -/
def cur_dom : Expr 8 := .reg 8 "cur_dom"

/-! ### EXT-3 — fail-stop / poison (`EXTEND_SPEC.md` increment 3)

The architected disposition every later engine feeds. §3's epoch machine
and Appendix F's fail-stop rule both need one answer to "this thread's
authority is gone" that is not "raise a fault and hope the handler is
correct" — the machine must *stop the thread*, not trust software to.

`poison` is a 32-bit bitmap, one bit per thread slot. It buys two things,
and the first is why the bitmap shape was chosen:

* **A poisoned thread is never scheduled.** The mask lands on `readyBm`,
  the scheduler's single ready bitmap — so `next_ready`, `nr_any` and every
  picker downstream inherit it from one `and`. That is the whole reason
  poison is a *bitmap* and not a per-thread memory: the picker reads every
  slot at once (D20's rule), so the mask has to be readable at every index
  at once too.
* **A poisoned thread does not execute another instruction.** Masking the
  picker alone is not fail-stop: the *running* thread is not re-picked, so
  a thread poisoned mid-run would keep going until it happened to yield.
  `S_F0` therefore stops the core outright when `curPoisoned` — at the
  instruction boundary, with nothing fetched and no bus transaction
  outstanding, which is the same property that makes EXT-1's preemption
  point safe.

Stopping the core (rather than switching to another thread) is the
fail-*stop* reading of Appendix F: the disposition is "this machine has
lost the right to proceed", and quietly running someone else would hide it.
The host sees `running = 0` and the `poison` bitmap says which slot. -/
def poison : Expr 32 := .reg 32 "poison"

/-! ### EXT-5 — gates (`EXTEND_SPEC.md` increment 5; ISA §9, Law 1)

A gate is the *only* way a thread changes domain. That is the whole point,
and it is what makes EXT-2's tag mean something: after EXT-5 the writers of
`tdom` are exactly the `cmd 13` reset sweep, `CLONE` (which **inherits**, so
it cannot choose), `cmd 58` (host/debug), and gate call/return — which move
a thread only to a domain the host installed in the gate table. **There is
no instruction that lets a thread name a domain and go there.**

The gate table is two small memories: `gate_ent[g]` (entry PC) and
`gate_dom[g]` (target domain), 16 gates, loaded by the host. A gate call
saves the return point in the caller's own slot (`tcont[cur]`, `tcdom[cur]`)
and sets `in_gate[cur]`; a gate return restores them.

**Deviation — the continuation is depth 1, not a stack.** §9 has a
continuation *stack*; `in_gate` is a bitmap and a second `gate_call` from
inside a gate is refused (`rd = -1`, no state change) rather than nesting.
Per-thread stacks are 32 stacks, and EXT-4 just taught this campaign what
duplicating per-slot structure costs. Depth 1 is enough to demonstrate
mediation — the property that matters — and the shape generalises: making
`tcont`/`tcdom` two-deep is a width change, not a redesign.

**Deviation — opcodes.** §9 assigns `gate_call`/`gate_return` to 0xa0/0xa1,
but mini's decoder already uses 0xa0–0xba for ALU-immediate ops, so mini's
map diverges from the ISA in that whole block *before* this increment. Gates
take **0x60/0x61**, which are free in mini. Recorded here rather than
pretending the encodings match. -/
def in_gate : Expr 32 := .reg 32 "in_gate"
def gate_sel : Expr 4 := .reg 4 "gate_sel"

/-- Bit `cur` of `in_gate`: this thread is inside a gate. -/
def curInGate : Expr 1 :=
  .eq (.slice (.shr in_gate (.zext cur 32)) 0 1) (.lit (BitVec.ofNat 1 1))

/-- `cmd 61` loads `gate_ent[gate_sel]`; `cmd 62` sets `gate_sel` and
`gate_dom[gate_sel]` (`data[3:0]` = gate id, `data[15:8]` = domain). -/
def CMD_GATE_ENT : Nat := 61
def CMD_GATE_DOM : Nat := 62

/-! ### EXT-6 — cross-domain capability transfer (`EXTEND_SPEC.md` #6; §10.2)

A capability handle moves between domains through a **per-domain inbox**:
`cap_ibox[d]` holds one handle addressed to domain `d`, `cap_ival` says
whether it is occupied. `CAP_SEND` writes the inbox of the domain it names;
`CAP_RECV` reads **`cap_ibox[domCur]`** — the receiver's *own* domain, which
it cannot name and cannot forge, because `domCur` is `tdom[cur]` and EXT-5
made a gate the only way that changes.

**The re-keying is structural, not a check.** A handle addressed to domain 3
is not merely *flagged* for domain 3 — it is stored at an index no thread in
another domain can address, because the receive index is not an operand. A
domain-5 thread executing `CAP_RECV` reads inbox 5 and gets nothing; there
is no encoding of `CAP_RECV` that reaches inbox 3. That is the same shape as
EXT-3's fail-stop landing on `readyBm`: put the property where the datapath
cannot route around it, rather than testing for it.

**Deviation — one slot per domain, not a queue.** `CAP_SEND` to an occupied
inbox is refused (`rd = -1`, no state change) rather than queueing. Sixteen
queues is per-slot structure of exactly the kind EXT-4 measured the cost of;
one slot proves the transfer and the mediation, and depth is a width change.

**Deviation — no MAC re-computation.** CapWalk's engine authenticates a
handle with an on-chip key over `E(slot)`; a full transfer would re-key the
MAC to the receiving domain. Mini's inbox carries the handle bits only, and
the domain binding is the *index*. Recorded as the gap between this and
§10.2: the mediation is real, the cryptographic re-key is not implemented.
-/
def cap_ival : Expr 16 := .reg 16 "cap_ival"

/-! ### EXT-7 — VMA / translation (`EXTEND_SPEC.md` #7; ISA §15)

§15 line 160: loads and stores walk **one** VMA tree into a **domain-tagged
TLB entry**. Mini implements the *entry*, not the tree: an 8-entry
direct-mapped TLB whose tag includes the domain, filled by the host (the
walker is the deviation below). Two things follow, and they are the reason
this increment is the one worth having:

* **A translation cached by domain 3 is unusable by domain 5.** The domain
  is part of the tag, so a hit requires `tlb_dom[i] = domCur`. Same
  structural move as EXT-6's inbox index — `domCur` is `tdom[cur]` and EXT-5
  made a gate the only way that changes, so the tag cannot be forged.
* **Shootdown is the epoch cell, not a new mechanism.** §15 line 876: the
  cached translation's cell *is the VMA's cell*, and `map.protect`/`munmap`
  bump it. `tlb_cell[i]` records which cell an entry depends on;
  `MAP_PROTECT` invalidates every entry naming that cell. That is the
  bump-to-fail-closed shape already proven on silicon, pointed at a
  translation.

`mmu_en = 0` (reset) is **bypass**: `ddrEa` is the identity computation of
every previous increment, bit for bit, so NetBSD is untouched. That is
stage A — prove the mechanism, risk nothing. -/
def mmu_en : Expr 1 := .reg 1 "mmu_en"
def tlb_sel : Expr 3 := .reg 3 "tlb_sel"
def TLBN : Nat := 8

def CMD_MMU_EN   : Nat := 63
def CMD_TLB_SEL  : Nat := 64
def CMD_TLB_VPN  : Nat := 65
def CMD_TLB_PPN  : Nat := 66
/-- `cmd 67` = the §15 `map.protect`/`munmap` shootdown: invalidate every
TLB entry whose recorded cell equals `cmd_data[7:0]`. -/
def CMD_MAP_PROTECT : Nat := 67
def CAP_SEND_OP : Nat := 0x3e
def CAP_RECV_OP : Nat := 0x3f

/-- Bit `cur` of the poison bitmap: the running thread has been poisoned. -/
def curPoisoned : Expr 1 :=
  -- (the `L*` literal helpers are declared below this block)
  .eq (.slice (.shr poison (.zext cur 32)) 0 1) (.lit (BitVec.ofNat 1 1))

/-- EXT-3. `cmd 60` loads the whole 32-bit poison bitmap. Whole-word rather
than set/clear-one-bit because the raise is meant to be *atomic across
slots*: a domain losing authority poisons every thread it owns in one
cycle, and a read-modify-write from the host could interleave with a
`CLONE` that adds one. -/
def CMD_POISON : Nat := 60

def sleep_scan: Expr 5  := .reg 5  "sleep_scan"
def next_ready: Expr 5  := .reg 5  "next_ready"
def free_slot : Expr 5  := .reg 5  "free_slot"
def has_free  : Expr 1  := .reg 1  "has_free"
def clone_dst : Expr 5  := .reg 5  "clone_dst"
def clone_tid : Expr 5  := .reg 5  "clone_tid"
def mul_acc   : Expr 128:= .reg 128 "mul_acc"
def mul_aw    : Expr 128:= .reg 128 "mul_aw"
def mul_b     : Expr 64 := .reg 64 "mul_b"
def mul_kind  : Expr 2  := .reg 2  "mul_kind"
def div_rem   : Expr 64 := .reg 64 "div_rem"
def div_quo   : Expr 64 := .reg 64 "div_quo"
def div_d     : Expr 64 := .reg 64 "div_d"
def div_cnt   : Expr 7  := .reg 7  "div_cnt"
def div_isrem : Expr 1  := .reg 1  "div_isrem"
def div_negq  : Expr 1  := .reg 1  "div_negq"
def div_negr  : Expr 1  := .reg 1  "div_negr"
def zeroing   : Expr 1  := .reg 1  "zeroing"
def zctr      : Expr 10 := .reg 10 "zctr"
def reg_sel   : Expr 5  := .reg 5  "reg_sel"
def reg_wsel  : Expr 5  := .reg 5  "reg_wsel"
def reg_wlo   : Expr 32 := .reg 32 "reg_wlo"
def dmem_addr_j : Expr 32 := .reg 32 "dmem_addr_j"
def dmem_lo_j   : Expr 32 := .reg 32 "dmem_lo_j"
def reg_rd    : Expr 64 := .reg 64 "reg_rd"

/-! ## The thread table (D20)

`tstate` and `tfutex` stay **per-element registers**; `tpc`, `tsleep`,
`tp_arr` and `sigmask_arr` are **Loom memories** (32x64, one dynamic index).
See `DUAL_SPEC.md` §D20 for the per-array decision table and the cost
measurements. In one line: an array whose reads are *all* at one dynamic
index is a memory (the 32:1 read mux and — far more expensive — the 32
copies of the write data path collapse to one LUTRAM), while an array read
*at every index at once* (`tfutex`'s FUTEX_WAKE comparator bank, `tstate`'s
priority encoders) has to stay a register file of flops.

All reads of the four converted arrays are plain **asynchronous**
`memRead`s — D9 says they evaluate against the pre-cycle state at the
pre-cycle address, which is exactly what the 32-way mux over pre-cycle
registers computed. Nothing is restaged, so every register keeps its
cycle-by-cycle value and the ISS is unchanged except for the `cmd 13` reset
sweep (D20.3). µVerilog's async read is distributed RAM, which has no
cross-port collision hazard: the write lands on the clock edge, the read
sees the old contents, exactly as `Design.cycle` says. -/

def tstate  (i : Fin NT) : Expr 2  := .reg 2  s!"tstate{i.val}"
def tfutex  (i : Fin NT) : Expr 64 := .reg 64 s!"tfutex{i.val}"

/-- `tpc[idx]` — async read of the thread-PC memory. -/
def tpcRd (idx : Expr 5) : Expr 64 := .memRead 64 "tpc" idx
/-- `tsleep[idx]` — async read of the sleep-countdown memory. -/
def tsleepRd (idx : Expr 5) : Expr 64 := .memRead 64 "tsleep" idx

/-! ## Opcode mnemonics (PLATONIC W1.5)

Mini's opcodes were bare hex literals scattered across `opIs`, `opAny`
lists, `| 0x.. =>` arms and hand-written test programs. That made a
renumbering impossible to do safely: a two-hex-digit literal is
ambiguous with data, so any pattern broad enough to catch every opcode
context also caught things that were not opcodes -- which is exactly how
the first attempt at ISA conformance stage 2 drove the EDSL and the ISS
apart (261 sites touched, 1162 lockstep mismatches).

With names, a renumbering is one edit per constant and cannot touch a
data literal. Names are taken from the emulator's `Instr` variant at the
same opcode, so the two implementations are legible against each other.
-/

/-- An opcode implemented in **no** numbering, for test programs that need a
guaranteed trap. It must stay invalid across a renumbering: `0x7f` was used
for this and is NOT free after the ISA stage-2 assignment, so renumbering
turned the trap test into a valid instruction. 0x8c is in the ISA's reserved
"memory growth" range and is unoccupied before and after. -/
def OP_INVALID : Nat := 0x8c

def OP_NOP : Nat := 0x00
def OP_MOV : Nat := 0x02
def OP_LIU : Nat := 0x04
def OP_SLEEP : Nat := 0x07
def OP_LD_S : Nat := 0x09
def OP_ADD : Nat := 0x10
def OP_SUB : Nat := 0x11
def OP_MUL : Nat := 0x12
def OP_DIV : Nat := 0x13
def OP_AND : Nat := 0x14
def OP_OR : Nat := 0x15
def OP_XOR : Nat := 0x16
def OP_SREM : Nat := 0x17
def OP_LSL : Nat := 0x18
def OP_LSR : Nat := 0x19
def OP_ASR : Nat := 0x1a
def OP_SLT : Nat := 0x1b
def OP_SLTI : Nat := 0x1d
def OP_NOT : Nat := 0x1f
def OP_JMP : Nat := 0x20
def OP_BEQ : Nat := 0x21
def OP_BNE : Nat := 0x22
def OP_BLT : Nat := 0x23
def OP_BGE : Nat := 0x24
def OP_BLTU : Nat := 0x25
def OP_SLTU : Nat := 0x26
def OP_JAL : Nat := 0x27
def OP_JALR : Nat := 0x28
def OP_LD : Nat := 0x30
def OP_LD_31 : Nat := 0x31
def OP_LD_32 : Nat := 0x32
def OP_ST : Nat := 0x33
def OP_ST_34 : Nat := 0x34
def OP_ST_35 : Nat := 0x35
def OP_LD_36 : Nat := 0x36
def OP_ST_37 : Nat := 0x37
def OP_EXIT : Nat := 0x3a
def OP_THREAD_EXIT : Nat := 0x3b
def OP_MINI_GATE_CALL : Nat := 0x3c
def OP_MINI_GATE_RETURN : Nat := 0x3d
def OP_MINI_CAP_SEND : Nat := 0x3e
def OP_MINI_CAP_RECV : Nat := 0x3f
def OP_SEL : Nat := 0x40
def OP_SEL_41 : Nat := 0x41
def OP_SEL_42 : Nat := 0x42
def OP_SEL_43 : Nat := 0x43
def OP_SEL_44 : Nat := 0x44
def OP_SEL_45 : Nat := 0x45
def OP_LSRI : Nat := 0x4d
def OP_ASRI : Nat := 0x4e
def OP_SLTIU : Nat := 0x51
def OP_GET_PCR : Nat := 0x54
def OP_CLONE_SPAWN : Nat := 0x59
def OP_BGEU : Nat := 0x68
def OP_LD_S_70 : Nat := 0x70
def OP_LD_S_72 : Nat := 0x72
def OP_YIELD : Nat := 0x98
def OP_FUTEX_WAIT : Nat := 0x99
def OP_FUTEX_WAKE : Nat := 0x9a
def OP_ADDI : Nat := 0xa0
def OP_ANDI : Nat := 0xa1
def OP_ORI : Nat := 0xa2
def OP_XORI : Nat := 0xa3
def OP_LSLI : Nat := 0xa4
def OP_UDIV : Nat := 0xa7
def OP_UREM : Nat := 0xa9
def OP_MULH : Nat := 0xaa
def OP_MULHU : Nat := 0xab
def OP_SEXT_B : Nat := 0xad
def OP_SEXT_H : Nat := 0xae
def OP_SEXT_W : Nat := 0xaf
def OP_ZEXT_B : Nat := 0xb0
def OP_ZEXT_H : Nat := 0xb1
def OP_ZEXT_W : Nat := 0xb2
def OP_CTZ : Nat := 0xb4
def OP_ROL : Nat := 0xb6
def OP_ROR : Nat := 0xb7
def OP_BSWAP16 : Nat := 0xb8
def OP_BSWAP32 : Nat := 0xb9
def OP_BSWAP64 : Nat := 0xba
def OP_LR_D : Nat := 0xc5
def OP_SC_D : Nat := 0xc6
def OP_LR_D_ACQ : Nat := 0xc7
def OP_SC_D_REL : Nat := 0xc8
def OP_LR_D_ACQ_REL : Nat := 0xc9
def OP_SC_D_ACQ_REL : Nat := 0xca
def OP_FENCE : Nat := 0xcd
def OP_AUIPC : Nat := 0xd0
def OP_FENCE_D1 : Nat := 0xd1
def OP_FENCE_D2 : Nat := 0xd2
def OP_FENCE_D3 : Nat := 0xd3
def OP_FENCE_D4 : Nat := 0xd4

/-! ## Literal helpers -/

def L1  (n : Nat) : Expr 1  := .lit (BitVec.ofNat 1 n)
def L2  (n : Nat) : Expr 2  := .lit (BitVec.ofNat 2 n)
def L5  (n : Nat) : Expr 5  := .lit (BitVec.ofNat 5 n)
def L7  (n : Nat) : Expr 7  := .lit (BitVec.ofNat 7 n)
def L8  (n : Nat) : Expr 8  := .lit (BitVec.ofNat 8 n)
def L32 (n : Nat) : Expr 32 := .lit (BitVec.ofNat 32 n)
def L64 (n : Nat) : Expr 64 := .lit (BitVec.ofNat 64 n)

/-! ## Balanced-tree builders (timing; semantics-preserving)

The Verilog emitter turns a `foldr`/`foldl` over a list of guarded values
into a *linear* mux chain, so a 64-entry fold becomes a 64-level
combinational cone. The builders below produce the SAME function of the
same inputs with `O(log n)` depth. None of them needs the guards to be
mutually exclusive — see `priTree`. -/

/-! ### Balanced-tree builders — now `Loom/Hw/Builders.lean` (W3.1)

`priTree`, `reduceTree`, `orTree`, `orTreeW`, `addTree` and `actPriTree` used
to be defined here with their correctness in a comment. They are Loom's now,
and their eval-equality with the linear forms is proved (`priTree_eval`,
`reduceTree_eval`, `orTreeW_eval`). Mini just uses them. -/


/-! ## Decode (combinational wires) -/

def op   : Expr 8 := .slice ir 56 8
def rdf  : Expr 5 := .slice ir 51 5
def rs1f : Expr 5 := .slice ir 46 5
def rs2f : Expr 5 := .slice ir 41 5
def rs3f : Expr 5 := .slice ir 36 5
def rs4f : Expr 5 := .slice ir 31 5

/-- imm_i = {{32{ir[45]}}, ir[45:14]} — sext of ir[45:14] (32 bits) to 64. -/
def imm_i : Expr 64 := .sext (.slice ir 14 32) 64
/-- imm_s = sext ir[40:9]. -/
def imm_s : Expr 64 := .sext (.slice ir 9 32) 64
/-- imm_j = sext ir[50:19]. -/
def imm_j : Expr 64 := .sext (.slice ir 19 32) 64

def shamt_r : Expr 6 := .slice b 0 6
def shamt_i : Expr 6 := .slice imm_i 0 6
def pc8 : Expr 64 := .add pc (L64 8)

/-! `r1a`/`r2a` — the state-muxed shared read-port addresses
(`(st == S_RD2) ? rs3f : rs1f`) — are **gone** (D19). The `S_RD` and
`S_RD2` latch sites already key on `st`, so the mux was redundant there,
and one shared address net gave `a`/`sel_t` a single `rf[...]` expression
with fan-out two — which no downstream tool can merge into a block-RAM
read port. Each site now names its own field directly. -/

def mem_ea_l : Expr 64 := .add a imm_i
def mem_ea_s : Expr 64 := .add a imm_s
def ld_widx : Expr 9 := .slice mem_ea_l 3 9
def st_widx : Expr 9 := .slice mem_ea_s 3 9
def ld_boff : Expr 3 := .slice mem_ea_l 0 3
def st_boff : Expr 3 := .slice mem_ea_s 0 3
def l_is_zp : Expr 1 := .ult mem_ea_l (L64 0x1000)
def s_is_zp : Expr 1 := .ult mem_ea_s (L64 0x1000)
/-- l_is_gp: (mem_ea_l[31:16]==0xE000) || (mem_ea_l[31:20]==0x0A0). -/
def l_is_gp : Expr 1 :=
  .or (.eq (.slice mem_ea_l 16 16) (.lit (BitVec.ofNat 16 0xE000)))
      (.eq (.slice mem_ea_l 20 12) (.lit (BitVec.ofNat 12 0x0A0)))
def s_is_gp : Expr 1 :=
  .or (.eq (.slice mem_ea_s 16 16) (.lit (BitVec.ofNat 16 0xE000)))
      (.eq (.slice mem_ea_s 20 12) (.lit (BitVec.ofNat 12 0x0A0)))

/-! ### op predicates -/

def opIs (n : Nat) : Expr 1 := .eq op (L8 n)

/-- `orTree` over a list of opcode matches (was a linear `.or` fold). -/
def opAny (ns : List Nat) : Expr 1 := orTree (ns.map opIs)

def is_alu : Expr 1 :=
  opAny [OP_LIU,OP_MOV,OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR,OP_NOT,OP_LSL,OP_LSR,OP_ASR,OP_SLT,OP_SLTU,
   OP_ADDI,OP_ANDI,OP_ORI,OP_XORI,OP_LSLI,OP_LSRI,OP_ASRI,OP_SLTI,OP_SLTIU,OP_AUIPC,
   OP_SEXT_B,OP_SEXT_H,OP_SEXT_W,OP_ZEXT_B,OP_ZEXT_H,OP_ZEXT_W,OP_BSWAP16,OP_BSWAP32,OP_BSWAP64,OP_ROL,OP_ROR,OP_CTZ]

def is_load : Expr 1 := opAny [OP_LD,OP_LD_31,OP_LD_S_70,OP_LD_36,OP_LD_S,OP_LD_32,OP_LD_S_72]
def is_store : Expr 1 := opAny [OP_ST,OP_ST_34,OP_ST_37,OP_ST_35]
/-- is_branch: op in [0x21,0x26]. -/
def is_branch : Expr 1 := opAny [OP_BEQ,OP_BNE,OP_BLT,OP_BGE,OP_BLTU,OP_BGEU]
def is_lr : Expr 1 := opAny [OP_LR_D,OP_LR_D_ACQ,OP_LR_D_ACQ_REL]
def is_sc : Expr 1 := opAny [OP_SC_D,OP_SC_D_REL,OP_SC_D_ACQ_REL]
/-- is_fence: op==0xcd || (0xd1<=op<=0xd4). -/
def is_fence : Expr 1 := opAny [OP_FENCE,OP_FENCE_D1,OP_FENCE_D2,OP_FENCE_D3,OP_FENCE_D4]
/-- is_sel: 0x40<=op<=0x45. -/
def is_sel : Expr 1 := opAny [OP_SEL,OP_SEL_41,OP_SEL_42,OP_SEL_43,OP_SEL_44,OP_SEL_45]
def is_div : Expr 1 := opAny [OP_DIV,OP_UDIV,OP_SREM,OP_UREM]
def is_mulh : Expr 1 := .or (opIs OP_MULH) (opIs OP_MULHU)
def div_sgn : Expr 1 := .or (opIs OP_DIV) (opIs OP_SREM)

/-! ### ALU (combinational mux chain) -/

/-- $signed(a) >>> sh — arithmetic right shift by a 6-bit amount. -/
def asr (x : Expr 64) (sh : Expr 6) : Expr 64 :=
  -- sign-preserving: emulate via (x >> sh) with sign fill.
  -- Loom .shr is logical; build arithmetic by mux on sign bit.
  .mux (.eq (.slice x 63 1) (L1 1))
    (.not (.shr (.not x) (.zext sh 64)))
    (.shr x (.zext sh 64))

/-- ROL/ROR helper: `6'd0 - amt` (6-bit wrap). -/
def negShamt (amt : Expr 6) : Expr 6 := .sub (.lit (BitVec.ofNat 6 0)) amt

/-- CTZ: lowest set bit index (64 if a==0). Downward scan, index 0 outermost
— built as a balanced `priTree` (first-match-wins ⇒ lowest set bit still
wins), depth 64 → ~2·log₂64. -/
def ctzE : Expr 64 :=
  priTree ((List.range 64).map (fun i => (.eq (.slice a i 1) (L1 1), L64 i))) (L64 64)

/-- The ALU mux chain, balanced. `opIs` guards are mutually exclusive, but
`priTree` preserves first-match-wins regardless, so this is exactly the old
35-deep chain. -/
def aluE : Expr 64 :=
  priTree
  [ (opIs OP_MOV, a)
  , (opIs OP_ADD, .add a b)
  , (opIs OP_SUB, .sub a b)
  , (opIs OP_LIU, .or (.zext (.slice a 0 32) 64) (.shl (.zext (.slice imm_i 0 32) 64) (L64 32)))
  , (opIs OP_AND, .and a b)
  , (opIs OP_OR, .or a b)
  , (opIs OP_XOR, .xor a b)
  , (opIs OP_NOT, .not a)
  , (opIs OP_LSL, .shl a (.zext shamt_r 64))
  , (opIs OP_LSR, .shr a (.zext shamt_r 64))
  , (opIs OP_ASR, asr a shamt_r)
  , (opIs OP_SLT, .mux (.slt a b) (L64 1) (L64 0))
  , (opIs OP_SLTU, .mux (.ult a b) (L64 1) (L64 0))
  , (opIs OP_ADDI, .add a imm_i)
  , (opIs OP_ANDI, .and a imm_i)
  , (opIs OP_ORI, .or a imm_i)
  , (opIs OP_XORI, .xor a imm_i)
  , (opIs OP_LSLI, .shl a (.zext shamt_i 64))
  , (opIs OP_LSRI, .shr a (.zext shamt_i 64))
  , (opIs OP_ASRI, asr a shamt_i)
  , (opIs OP_SLTI, .mux (.slt a imm_i) (L64 1) (L64 0))
  , (opIs OP_SLTIU, .mux (.ult a imm_i) (L64 1) (L64 0))
  , (opIs OP_AUIPC, .add pc imm_j)
  , (opIs OP_SEXT_B, .sext (.slice a 0 8) 64)
  , (opIs OP_SEXT_H, .sext (.slice a 0 16) 64)
  , (opIs OP_SEXT_W, .sext (.slice a 0 32) 64)
  , (opIs OP_ZEXT_B, .zext (.slice a 0 8) 64)
  , (opIs OP_ZEXT_H, .zext (.slice a 0 16) 64)
  , (opIs OP_ZEXT_W, .zext (.slice a 0 32) 64)
  , (opIs OP_BSWAP16, bswap16)
  , (opIs OP_BSWAP32, bswap32)
  , (opIs OP_BSWAP64, bswap64)
  , (opIs OP_CTZ, ctzE)
  , (opIs OP_ROL, .or (.shl a (.zext shamt_r 64)) (.shr a (.zext (negShamt shamt_r) 64)))
  , (opIs OP_ROR, .or (.shr a (.zext shamt_r 64)) (.shl a (.zext (negShamt shamt_r) 64)))
  ] (L64 0)
where
  -- 0xb8: {48'd0, a[7:0], a[15:8]} = bytes swapped in low 16
  bswap16 : Expr 64 :=
    .or (.shl (.zext (.slice a 0 8) 64) (L64 8)) (.zext (.slice a 8 8) 64)
  bswap32 : Expr 64 :=
    -- {32'd0, a[7:0],a[15:8],a[23:16],a[31:24]}
    .zext (byteRev4 (.slice a 0 32)) 64
  bswap64 : Expr 64 := byteRev8 a
  byteRev4 (x : Expr 32) : Expr 32 :=
    .or (.shl (.zext (.slice x 0 8) 32) (.lit (BitVec.ofNat 32 24)))
    (.or (.shl (.zext (.slice x 8 8) 32) (.lit (BitVec.ofNat 32 16)))
    (.or (.shl (.zext (.slice x 16 8) 32) (.lit (BitVec.ofNat 32 8)))
         (.zext (.slice x 24 8) 32)))
  -- the 8 lanes are disjoint, so the linear OR fold re-associates freely
  byteRev8 (x : Expr 64) : Expr 64 :=
    orTreeW ((List.range 8).map
      (fun i => .shl (.zext (.slice x (i*8) 8) 64) (L64 ((7-i)*8))))

/-! ### branch / sel conditions -/

def br_take : Expr 1 :=
  priTree
  [ (opIs OP_BEQ, .eq a b)
  , (opIs OP_BNE, .not (.eq a b))
  , (opIs OP_BLT, .slt a b)
  , (opIs OP_BGE, .not (.slt a b))
  , (opIs OP_BLTU, .ult a b)
  , (opIs OP_BGEU, .not (.ult a b)) ] (L1 0)

/-- sel_cond keys on op[2:0] (0x40-0x45). -/
def sel_cond : Expr 1 :=
  let o3 := (.slice op 0 3 : Expr 3)
  priTree
  [ (.eq o3 (.lit (BitVec.ofNat 3 0)), .eq a b)
  , (.eq o3 (.lit (BitVec.ofNat 3 1)), .not (.eq a b))
  , (.eq o3 (.lit (BitVec.ofNat 3 2)), .slt a b)
  , (.eq o3 (.lit (BitVec.ofNat 3 3)), .not (.slt a b))
  , (.eq o3 (.lit (BitVec.ofNat 3 4)), .ult a b) ] (.not (.ult a b))

/-! ### load writeback / store merge -/

def mem_src : Expr 64 := .mux (.eq st (L5 S_L1)) dmem_rd ddr_q
def lw_shift : Expr 64 := .shr mem_src (.shl (.zext ld_boff_q 64) (L64 3))

/-- Load write-back: narrow the fetched word to the load's width and extend.

These arms were raw hex, and TWO of them were stale after the renumbering:
`0x05` and `0x08` were `lw` and `lb` under the td-anchored map, and those ops
now live at `0x70` (`OP_LD_S_70`) and `0x72` (`OP_LD_S_72`). Both therefore fell
through to the default and returned the **raw 64-bit word instead of
sign-extending** — every signed byte and word load in the design was wrong, in
the EDSL, so in the RTL and in the bitstream.

Found by the generated EDSL≡ISS matrix once it covered loads:
`lb @0x40: rf[4] edsl=255 iss=18446744073709551615`. Storing 255 and loading it
as a signed byte is −1; the design returned 255.

Named constants now, so a renumbering moves them. -/
def ld_wb : Expr 64 :=
  priTree
  [ (.eq ld_op_q (L8 OP_LD),      mem_src)
  , (.eq ld_op_q (L8 OP_LD_31),   .zext (.slice lw_shift 0 32) 64)   -- lwu
  , (.eq ld_op_q (L8 OP_LD_S_70), .sext (.slice lw_shift 0 32) 64)   -- lw
  , (.eq ld_op_q (L8 OP_LD_36),   .zext (.slice lw_shift 0 16) 64)   -- lhu
  , (.eq ld_op_q (L8 OP_LD_S),    .sext (.slice lw_shift 0 16) 64)   -- lh
  , (.eq ld_op_q (L8 OP_LD_32),   .zext (.slice lw_shift 0 8) 64)    -- lbu
  , (.eq ld_op_q (L8 OP_LD_S_72), .sext (.slice lw_shift 0 8) 64) ]  -- lb
  mem_src

def st_width : Expr 4 :=
  priTree
  [ (opIs OP_ST_35, .lit (BitVec.ofNat 4 1))
  , (opIs OP_ST_37, .lit (BitVec.ofNat 4 2))
  , (opIs OP_ST_34, .lit (BitVec.ofNat 4 4)) ] (.lit (BitVec.ofNat 4 8))

/-- st_merge: overlay b bytes into mem_src by byte lane. Lane `bi` takes
`b[(bi-st_boff)]` if `st_boff <= bi < st_boff+st_width`, else `mem_src`'s
own byte `bi`.

Timing: the old `foldl` threaded an 8-deep and/or/mux chain through `acc`,
but **each step rewrites a distinct byte lane** (`laneMask` are pairwise
disjoint and cover the word), so `acc`'s lane `bi` at step `bi` is still
`mem_src`'s lane `bi`. The chain is therefore exactly the disjoint OR of
eight independent 1-level lane muxes — depth 8 → 1 (+ the OR tree). -/
def st_merge : Expr 64 :=
  orTreeW ((List.range 8).map (fun bi =>
    let boffN := (.zext st_boff 32 : Expr 32)
    let inRange : Expr 1 :=
      .and (.not (.ult (.lit (BitVec.ofNat 32 bi)) boffN))
           (.ult (.lit (BitVec.ofNat 32 bi)) (.add boffN (.zext st_width 32)))
    -- source byte index (bi - st_boff), as shift amount into b
    let srcByte : Expr 64 := .shr b (.shl (.sub (.lit (BitVec.ofNat 64 bi)) (.zext st_boff 64)) (L64 3))
    let laneVal : Expr 64 := .shl (.zext (.slice srcByte 0 8) 64) (L64 (bi*8))
    let laneMask : Expr 64 := .lit (BitVec.ofNat 64 (0xFF <<< (bi*8)))
    .mux inRange laneVal (.and mem_src laneMask)))

/-! ### div abs helpers -/

def div_a_abs : Expr 64 :=
  .mux (.and div_sgn (.eq (.slice a 63 1) (L1 1))) (.add (.not a) (L64 1)) a
def div_b_abs : Expr 64 :=
  .mux (.and div_sgn (.eq (.slice b 63 1) (L1 1))) (.add (.not b) (L64 1)) b

/-! ### scheduler bitmaps / priority encoders -/

/-- ready bitmap as a 32-bit Expr (bit i = tstate_i == 1). Disjoint bit
lanes ⇒ the OR fold re-associates into a tree. -/
def readyBm : Expr 32 :=
  -- EXT-3: fail-stop. A poisoned slot is not READY, so it is never picked
  -- -- by `next_ready`, by `nr_any`, or by anything downstream of them.
  -- One `and` at the one place the scheduler asks "who can run".
  .and (.not poison)
    (orTreeW ((List.finRange NT).map
      (fun i => .shl (.zext (.eq (tstate i) (L2 1)) 32) (.lit (BitVec.ofNat 32 i.val)))))
def freeBm : Expr 32 :=
  orTreeW ((List.finRange NT).map
    (fun i => .shl (.zext (.eq (tstate i) (L2 0)) 32) (.lit (BitVec.ofNat 32 i.val))))

/-- rbm2 = ({ready,ready} >> (cur+1))[63:0]. -/
def rbm2 : Expr 64 :=
  .shr (.or (.zext readyBm 64) (.shl (.zext readyBm 64) (L64 32)))
       (.zext (.add cur (L5 1)) 64)

/-- Downward scan over rbm2[31:0]: lowest set bit index wins (0 outermost).
Balanced priority tree — first-match-wins is preserved by `priTree`, so
"lowest set bit wins" is unchanged. -/
def nr_off : Expr 5 :=
  priTree ((List.range NT).map (fun i => (.eq (.slice rbm2 i 1) (L1 1), L5 i))) (L5 0)
def nr_any : Expr 1 :=
  orTree ((List.range NT).map (fun i => (.slice rbm2 i 1 : Expr 1)))
def fs_off : Expr 5 :=
  priTree ((List.range NT).map (fun i => (.eq (.slice freeBm i 1) (L1 1), L5 i))) (L5 0)
def hf_c : Expr 1 :=
  orTree ((List.range NT).map (fun i => (.slice freeBm i 1 : Expr 1)))

/-! ## Ownership expr -/

/-- hp_core_owns = running && st∉{S_TRAP,S_WAIT,S_PAUSE}. -/
def hp_core_owns : Expr 1 :=
  .and running
    (.and (.not (.eq st (L5 S_TRAP)))
      (.and (.not (.eq st (L5 S_WAIT))) (.not (.eq st (L5 S_PAUSE)))))

/-! ## {cur,reg} 10-bit index helpers -/

def cat55 (hi lo : Expr 5) : Expr 10 :=
  .or (.shl (.zext hi 10) (.lit (BitVec.ofNat 10 5))) (.zext lo 10)

/-! ## The rf write funnel

A list of `(guard, wa, wd)` triples in Verilog textual order (zeroing,
cmd52, then the mutually-exclusive FSM writes). Later sites win → fold so
the LAST matching guard's data is selected. `rfWeE` ORs the guards.

FSM writes are guarded additionally by (running ∧ ¬halted ∧ ¬zeroing ∧
st==X ∧ the branch predicate).  We name the S_EX predicate cascade to
reproduce the if-else priority exactly. -/

/-- The *effective* hold: `hold` only bites at the instruction boundary
`S_F0`, so the core stops with no bus transaction outstanding. -/
def holdEn : Expr 1 := .and hold (.eq st (L5 S_F0))

/-- running ∧ ¬halted ∧ ¬zeroing ∧ ¬holdEn — the FSM enable. `hold` (D15
input, DUAL_SPEC extension 4) freezes the FSM: with `hold` tied 0 this is
the original `running ∧ ¬halted ∧ ¬zeroing`. -/
def fsmEn : Expr 1 :=
  .and (.not holdEn) (.and running (.and (.not halted) (.not zeroing)))

/-- S_EX branch reached iff earlier branches all missed. We inline each
branch's own predicate ANDed with fsmEn ∧ st==S_EX; mutual exclusion holds
because the ISA opcodes are disjoint, so we do not need the full negation
chain for the rf funnel (order among FSM writes is free per spec). -/
def exG (p : Expr 1) : Expr 1 := .and fsmEn (.and (.eq st (L5 S_EX)) p)

/-! ## EXT-1 — the preemption tick (Law 5)

`lnp64_isa.md` Law 5: *"Every instruction boundary is a preemption point.
Unconditionally. The machine contains no non-preemptible region."* The
ported core was **cooperative** — every write of `cur` sat at a voluntary
yield (`YIELD`/`SLEEP`/`THREAD_EXIT`/`FUTEX_WAIT`/`S_WAIT`) — which
`PORTING_SPEC.md` records as a fidelity gap. This closes it.

Three predicates, and every one of them is only ever true at `S_F0`:

* `qExpired` — the quantum is enabled and has run out.
* `preemptAtF0` — the **preemption point**: `fsmEn` (so never while
  `zeroing`, never while `hold`, never when stopped), `st = S_F0` (so never
  mid-instruction: no fetch, load, store, multiply, divide or DDR
  transaction is in flight there — the same argument that makes `hold` safe,
  D15/DUAL_SPEC extension 4), not `bus_req` (the host owns the DDR window;
  that arm goes to `S_PAUSE` and the expiry is simply still pending when the
  core comes back), and not `trap_active`. `S_WAIT`/`S_PAUSE`/`S_TRAP` are
  excluded because they are not `S_F0`.
* `preemptFire` — `preemptAtF0` **and there is somewhere else to go**
  (`next_ready ≠ cur`). Preempting to yourself is a no-op, not a stall: the
  `¬preemptFire` path reloads `qctr` and issues the fetch in the very same
  cycle, so a single-threaded core with a quantum runs cycle-for-cycle like
  a core without one.

`qTick` is the timebase. It counts down only while the core is *running the
current thread's instructions* (`hp_core_owns` excludes `S_TRAP`, `S_WAIT`
and `S_PAUSE`), so a thread is not charged for time the core spent parked
or handing the bus to the host. It stops at 0 and waits for the reload,
which keeps the counter from wrapping past a missed boundary. -/
def quantumOn : Expr 1 := .not (.eq quantum (L32 0))
def qExpired  : Expr 1 := .and quantumOn (.eq qctr (L32 0))

def preemptAtF0 : Expr 1 :=
  .and fsmEn (.and (.eq st (L5 S_F0))
    (.and (.not bus_req) (.and (.not trap_active) qExpired)))

def preemptFire : Expr 1 := .and preemptAtF0 (.not (.eq next_ready cur))

def qTick : Expr 1 :=
  .and fsmEn (.and hp_core_owns
    (.and (.not trap_active) (.and quantumOn (.not (.eq qctr (L32 0))))))

/-- The BSCAN command index that loads `quantum` (and arms `qctr` with the
same value). Writing 0 disables preemption and restores the cooperative
machine exactly.

**Why 57 and not 56.** The core's own surface uses 13–19, 40–43 and 50–55,
so 56 is the first free *core* index — but `fpga/zc702/lnp64mini_dual_top.v`
and `lnp64mini_epoch_top.v` already claim **56 as a WRAPPER register**
(`CORE1_HOLD`) and swallow it before the cmd pulse ever reaches a core.
Taking 56 would have made the quantum unreachable on exactly the two
bitstreams the demo runs on, and (worse) would have made a future wrapper
that forwarded it silently retime the guest. 57 is free in every wrapper's
write decode and in every readback mux. -/
def CMD_QUANTUM : Nat := 57

/-- EXT-2. `cmd 58` sets one thread's domain: `cmd_data[4:0]` is the thread
slot, `cmd_data[15:8]` the domain id. 56 is the dual wrapper's `CORE1_HOLD`
and 57 is EXT-1's quantum, so 58 is the next free index. -/
def CMD_SETDOM : Nat := 58

/-! ### EXT-6 — send/recv predicates.

`capRecvSlot` is `domCur[3:0]` — the receiver's own domain. It is NOT an
operand, which is the whole mediation argument. -/
def capRecvSlot : Expr 4 := .slice domCur 0 4
def capSendSlot : Expr 4 := .slice b 0 4
/-- inbox occupancy bit for a slot. -/
def capOcc (d : Expr 4) : Expr 1 :=
  .eq (.slice (.shr cap_ival (.zext d 16)) 0 1) (.lit (BitVec.ofNat 1 1))
/-- A send lands only if the target inbox is free. -/
def capSendFire : Expr 1 := exG (.and (opIs CAP_SEND_OP) (.not (capOcc capSendSlot)))
/-- A receive lands only if this domain's inbox is occupied. -/
def capRecvFire : Expr 1 := exG (.and (opIs CAP_RECV_OP) (capOcc capRecvSlot))

/-- Funnel triples. -/
def rfTriples : List (Expr 1 × Expr 10 × Expr 64) :=
  -- 1. zeroing
  [ (zeroing, .zext zctr 10, L64 0)
  -- 2. cmd 52 (wins over zeroing)
  , (.and cmdValid (.and (.eq cmdIdx (L7 52)) (.not (.eq reg_wsel (L5 0)))),
       cat55 cur reg_wsel, .or (.shl (.zext cmdData 64) (L64 32)) (.zext reg_wlo 64))
  -- 3. FSM writes (mutually exclusive)
  -- S_EX is_sel
  , (exG (.and is_sel (.not (.eq rdf (L5 0)))), cat55 cur rdf, .mux sel_cond sel_t sel_f)
  -- EXT-6: CAP_SEND result -- 0 on success, all-ones on a full inbox.
  , (exG (.and (opIs CAP_SEND_OP) (.not (.eq rdf (L5 0)))), cat55 cur rdf,
       .mux (capOcc capSendSlot) (L64 0xFFFFFFFFFFFFFFFF) (L64 0))
  -- EXT-6: CAP_RECV result -- the handle addressed to THIS domain, or
  -- all-ones when this domain's inbox is empty. The index is `domCur`, not
  -- an operand, so no encoding reaches another domain's inbox.
  , (exG (.and (opIs CAP_RECV_OP) (.not (.eq rdf (L5 0)))), cat55 cur rdf,
       .mux (capOcc capRecvSlot) (capIboxRd capRecvSlot) (L64 0xFFFFFFFFFFFFFFFF))
  -- S_EX GET_PCR Tid (op 0x54, rs1f==2)
  , (exG (.and (opIs OP_GET_PCR) (.and (.eq rs1f (L5 2)) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, .add (.zext cur 64) (L64 1))
  -- S_EX is_alu
  , (exG (.and is_alu (.not (.eq rdf (L5 0)))), cat55 cur rdf, aluE)
  -- S_EX JAL (0x27)
  , (exG (.and (opIs OP_JAL) (.not (.eq rdf (L5 0)))), cat55 cur rdf, pc8)
  -- S_EX JALR (0x28)
  , (exG (.and (opIs OP_JALR) (.not (.eq rdf (L5 0)))), cat55 cur rdf, pc8)
  -- S_EX CLONE has_free: child r2 = b
  , (exG (.and (opIs OP_CLONE_SPAWN) has_free), cat55 free_slot (L5 2), b)
  -- S_EX CLONE no-free: rd = -1
  , (exG (.and (opIs OP_CLONE_SPAWN) (.and (.not has_free) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, L64 0xFFFFFFFFFFFFFFFF)
  -- S_EX SC ok
  , (exG (.and is_sc (.and (.and lr_valid (.eq lr_addr a)) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, L64 0)
  -- S_EX SC fail
  , (exG (.and is_sc (.and (.not (.and lr_valid (.eq lr_addr a))) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, L64 1)
  -- S_EX UART_RX load
  , (exG (.and is_load (.and (.eq mem_ea_l (L64 UART_RX_ADDR)) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf,
       .or (.zext (.memRead 8 "rx_mem" (.slice rx_rptr 0 8)) 64)
           (.mux (.not (.eq rx_rptr rx_wptr)) (.shl (L64 1) (L64 8)) (L64 0)))
  -- S_L1 load writeback
  , (.and fsmEn (.and (.eq st (L5 S_L1)) (.and (.not mem_is_store) (.not (.eq ld_rd_q (L5 0))))),
       cat55 cur ld_rd_q, ld_wb)
  -- S_DST load writeback (S_DST runs unconditionally; no m_done gate)
  , (.and fsmEn (.and (.eq st (L5 S_DST)) (.and (.not mem_is_store) (.not (.eq ld_rd_q (L5 0))))),
       cat55 cur ld_rd_q, ld_wb)
  -- S_CLONE2 child sp
  , (.and fsmEn (.eq st (L5 S_CLONE2)), cat55 clone_tid (L5 31),
       .add (L64 0x1800000) (.shl (.add (.zext clone_tid 64) (L64 1)) (L64 18)))
  -- S_CLONE3 parent dst
  , (.and fsmEn (.and (.eq st (L5 S_CLONE3)) (.not (.eq clone_dst (L5 0)))),
       cat55 cur clone_dst, .add (.zext clone_tid 64) (L64 1))
  -- S_MUL done
  , (.and fsmEn (.and (.eq st (L5 S_MUL)) (.and (.eq mul_b (L64 0)) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, mulDoneWd)
  -- S_DIV done
  , (.and fsmEn (.and (.eq st (L5 S_DIV)) (.and (.eq div_cnt (.lit (BitVec.ofNat 7 64))) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, divDoneWd)
  -- S_GPL done
  , (.and fsmEn (.and (.eq st (L5 S_GPL)) (.and gpDone (.not (.eq ld_rd_q (L5 0))))),
       cat55 cur ld_rd_q, .zext gpRdata 64)
  -- S_DSW: a GLOBAL SC the arbiter refused. `ir` still holds the SC, so
  -- `rdf`/`cur` are the ones `S_EX` optimistically wrote 0 to; overwrite
  -- with 1 (= failed) on the completion cycle. Guard is disjoint from every
  -- triple above (they all key on a different `st`).
  , (.and fsmEn (.and (.eq st (L5 S_DSW))
       (.and sc_pending (.and mDone (.and scFail (.not (.eq rdf (L5 0))))))),
       cat55 cur rdf, L64 1)
  ]
where
  mulDoneWd : Expr 64 :=
    priTree
    [ (.eq mul_kind (L2 0), .slice mul_acc 0 64)
    , (.eq mul_kind (L2 1),
        .sub (.sub (.slice mul_acc 64 64) (.mux (.eq (.slice a 63 1) (L1 1)) b (L64 0)))
             (.mux (.eq (.slice b 63 1) (L1 1)) a (L64 0))) ]
      (.slice mul_acc 64 64)
  divDoneWd : Expr 64 :=
    .mux div_isrem (.mux div_negr (.add (.not div_rem) (L64 1)) div_rem)
                   (.mux div_negq (.add (.not div_quo) (L64 1)) div_quo)

/-- Fold the triples: last matching guard wins. Balanced (`priTreeLast` =
`priTree` on the reversed list = the old `foldl` chain, 19 levels → ~5). -/
def rfWeE : Expr 1 := orTree (rfTriples.map (fun t => t.1))
def rfWaE : Expr 10 := priTreeLast (rfTriples.map (fun t => (t.1, t.2.1))) (.lit 0)
def rfWdE : Expr 64 := priTreeLast (rfTriples.map (fun t => (t.1, t.2.2))) (L64 0)

/-! ## Rules -/

/-- (1) registered priority encoders (separate always block). -/
def encRule : Rule :=
  ⟨"enc", .seq (.write 5 "next_ready" (.mux nr_any (.add (.add cur (L5 1)) nr_off) cur))
    (.seq (.write 5 "free_slot" fs_off) (.write 1 "has_free" hf_c))⟩

/-- (2) serialized sleep scan.

**D20.** `tsleep` is a memory, so the scan reads it once, at the scanned
index, instead of instantiating 32 comparators and 32 64-bit decrementers.
`tsl_s = tsleep[sleep_scan]` (async, pre-cycle) is *by definition* the
`tsleep i` the per-element chain used, because that chain only ever ran the
arm with `sleep_scan == i`. The `tstate` write stays per-element (`tstate`
is a register file); the countdown becomes one guarded `memWrite` on write
port **0** — the design's first syntactic `tsleep` write, so
`MemWriteWF`'s ascending-port condition is met by the `S_EX SLEEP` write
taking port 1 in `tarrFunnelRule` (a later rule). -/
def sleepScanRule : Rule :=
  ⟨"sleepdec", .ite (.and (.not holdEn) (.and running (.not halted)))
    (let tsl_s : Expr 64 := tsleepRd sleep_scan
     let scanHit : Expr 1 :=
       priTree ((List.finRange NT).map
         (fun i => (.eq sleep_scan (L5 i.val), .eq (tstate i) (L2 2)))) (L1 0)
     .seq (.write 5 "sleep_scan" (.add sleep_scan (L5 1)))
      (.seq
        ((List.finRange NT).foldr (fun i acc =>
          .seq (.ite (.and (.eq sleep_scan (L5 i.val)) (.eq (tstate i) (L2 2)))
            (.ite (.not (.ult (L64 1) tsl_s))       -- tsleep[sleep_scan] <= 1
              (.write 2 s!"tstate{i.val}" (L2 1)) .skip)
            .skip) acc) .skip)
        (.ite (.and scanHit (.ult (L64 1) tsl_s))
          (.memWrite 5 64 "tsleep" 0 sleep_scan (.sub tsl_s (L64 1))) .skip)))
    .skip⟩

/-- (3) latches: dmem_rd/reg_rd/uart_byte from pre-cycle state, plus the
dmem sync-write block `if (dmem_we) dmem[dmem_a]<=dmem_wd` (pre-cycle regs). -/
def latchRule : Rule :=
  ⟨"latches",
    .seq (.ite dmem_we (.memWrite 9 64 "dmem" 0 dmem_a dmem_wd) .skip)
      (.seq (.write 64 "dmem_rd" (.memRead 64 "dmem" dmem_a))
        (.seq (.write 64 "reg_rd" (.memRead 64 "rf" (cat55 cur reg_sel)))
              (.write 8 "uart_byte" (.memRead 8 "uart_mem" uart_ridx))))⟩

/-- (4) pulse defaults. -/
def pulseDefaultsRule : Rule :=
  ⟨"pulse_defaults",
    [("dmem_we",1),("core_rd",1),("core_wr",1),("jtag_wr",1),("jtag_rd",1),("gp_rd",1),("gp_wr",1),
      ("lr_req",1),("sc_req",1)].foldr
      (fun (nm,_) acc => .seq (.write 1 nm (L1 0)) acc) .skip⟩

/-- (5) zeroing engine (rf write is in the funnel; here dmem + counters). -/
def zeroingRule : Rule :=
  ⟨"zeroing", .ite zeroing
    (.seq (.ite (.ult zctr (.lit (BitVec.ofNat 10 512)))
            (.seq (.write 1 "dmem_we" (L1 1))
              (.seq (.write 9 "dmem_a" (.slice zctr 0 9)) (.write 64 "dmem_wd" (L64 0)))) .skip)
      (.ite (.eq zctr (.lit (BitVec.ofNat 10 (32*NT-1))))
        (.write 1 "zeroing" (L1 0))
        (.write 10 "zctr" (.add zctr (.lit (BitVec.ofNat 10 1))))))
    .skip⟩

/-- (6) cmd (wr_pulse) surface — rf write (idx 52) is in the funnel. -/
def cmdRule : Rule :=
  ⟨"cmd", .ite cmdValid cmdBody .skip⟩
where
  ci (n : Nat) : Expr 1 := .eq cmdIdx (L7 n)
  L9 (n : Nat) : Expr 9 := .lit (BitVec.ofNat 9 n)
  L32 (n : Nat) : Expr 32 := .lit (BitVec.ofNat 32 n)
  cmd13reset : Act :=
    .seq (.write 64 "pc" (L64 TEXT_BASE)) <|
    .seq (.write 32 "retire" (L32 0)) <|
    .seq (.write 1 "halted" (L1 0)) <|
    .seq (.write 1 "running" (L1 0)) <|
    .seq (.write 5 "st" (L5 S_IDLE)) <|
    .seq (.write 9 "uart_wptr" (L9 0)) <|
    .seq (.write 9 "rx_rptr" (L9 0)) <|
    .seq (.write 9 "rx_wptr" (L9 0)) <|
    .seq (.write 1 "trap_active" (L1 0)) <|
    .seq (.write 5 "cur" (L5 0)) <|
    .seq (.write 1 "lr_valid" (L1 0)) <|
    .seq (.write 1 "zeroing" (L1 1)) <|
    -- D20: `tpc` is a memory, so its 32-entry reset is *swept* by the
    -- zeroing engine (`tpcTriples` entry 1) over the first 32 of the 1024
    -- zeroing cycles instead of being written all at once here. Nothing
    -- reads `tpc` while `zeroing` is high (every read sits under `fsmEn`,
    -- which contains `¬zeroing`), so the transient is unobservable and the
    -- post-sweep contents are identical.
    .seq (.write 10 "zctr" (.lit (BitVec.ofNat 10 0)))
      ((List.finRange NT).foldr (fun i acc =>
        .seq (.write 2 s!"tstate{i.val}" (if i.val = 0 then L2 1 else L2 0)) acc) .skip)
  cmdBody : Act :=
    .seq (.ite (ci 14) (.write 5 "reg_sel" (.slice cmdData 0 5)) .skip) <|
    .seq (.ite (ci 15) (.write 32 "dmem_addr_j" cmdData) .skip) <|
    .seq (.ite (ci 16) (.write 32 "dmem_lo_j" cmdData) .skip) <|
    .seq (.ite (ci 17)
      (.seq (.write 1 "dmem_we" (L1 1))
        (.seq (.write 9 "dmem_a" (.slice dmem_addr_j 0 9))
              (.write 64 "dmem_wd" (.or (.shl (.zext cmdData 64) (L64 32)) (.zext dmem_lo_j 64))))) .skip) <|
    .seq (.ite (ci 18) (.write 8 "uart_ridx" (.slice cmdData 0 8)) .skip) <|
    .seq (.ite (ci 19)
      (.seq (.memWrite 8 8 "rx_mem" 0 (.slice rx_wptr 0 8) (.slice cmdData 0 8))
            (.write 9 "rx_wptr" (.add rx_wptr (L9 1)))) .skip) <|
    .seq (.ite (ci 40) (.write 32 "ddr_addr_j" cmdData) .skip) <|
    .seq (.ite (ci 41) (.write 32 "ddr_lo_j" cmdData) .skip) <|
    .seq (.ite (ci 42)
      (.seq (.write 1 "jtag_wr" (L1 1))
        (.seq (.write 64 "jtag_wdata" (.or (.shl (.zext cmdData 64) (L64 32)) (.zext ddr_lo_j 64)))
              (.write 32 "ddr_addr_j" (.add ddr_addr_j (L32 8))))) .skip) <|
    .seq (.ite (ci 43) (.write 1 "jtag_rd" (L1 1)) .skip) <|
    .seq (.ite (ci 50) (.write 5 "reg_wsel" (.slice cmdData 0 5)) .skip) <|
    .seq (.ite (ci 51) (.write 32 "reg_wlo" cmdData) .skip) <|
    .seq (.ite (ci 53) (.write 64 "pc" (.zext cmdData 64)) .skip) <|
    .seq (.ite (.and (ci 54) (.eq (.slice cmdData 0 1) (L1 1)))
      (.seq (.write 1 "trap_active" (L1 0))
        (.seq (.write 32 "retire" (.add retire (L32 1)))
              (.write 5 "st" (L5 S_F0)))) .skip) <|
    .seq (.ite (ci 55) (.write 1 "bus_req" (.slice cmdData 0 1)) .skip) <|
    -- EXT-1: the quantum reload value (0 = preemption disabled). `qctr` is
    -- armed from the same word in `quantumRule`, which owns that register.
    .seq (.ite (ci CMD_QUANTUM) (.write 32 "quantum" cmdData) .skip) <|
    -- EXT-3: the poison bitmap, whole-word (see `CMD_POISON`).
    .seq (.ite (ci CMD_POISON) (.write 32 "poison" cmdData) .skip) <|
    -- EXT-7: MMU enable and the TLB entry selector.
    .seq (.ite (ci CMD_MMU_EN) (.write 1 "mmu_en" (.slice cmdData 0 1)) .skip) <|
    .seq (.ite (ci CMD_TLB_SEL) (.write 3 "tlb_sel" (.slice cmdData 0 3)) .skip) <|
    -- EXT-5: `cmd 62` selects the gate whose entry `cmd 61` then loads.
    .seq (.ite (ci CMD_GATE_DOM) (.write 4 "gate_sel" (.slice cmdData 0 4)) .skip) <|
      (.ite (ci 13)
        (.seq (.ite (.eq (.slice cmdData 0 1) (L1 1)) cmd13reset .skip)
              (.ite (.eq (.slice cmdData 1 1) (L1 1))
                (.seq (.write 1 "running" (L1 1)) (.write 5 "st" (L5 S_F0))) .skip)) .skip)

/-- (7) ddr_rd_l latch. -/
def ddrRdLRule : Rule :=
  ⟨"ddr_rd_l", .ite (.and mDone (.not hp_core_owns)) (.write 64 "ddr_rd_l" mRdata) .skip⟩

/-! ### FSM rules (rf writes live in the funnel) -/

/-- One FSM arm as `(st == x, body)` data, so the whole state dispatch can
be emitted as one balanced tree (see `fsmRule`). The `fsmEn` half of the
old per-rule guard `fsmEn ∧ st==x` is hoisted into `fsmRule`. -/
def stArm (x : Nat) (a : Act) : Expr 1 × Act := (.eq st (L5 x), a)

/-! ### EXT-7 — the translation itself

The page is 4 KiB, so the VPN is `ea[31:12]` and the index is `ea[14:12]`
(direct-mapped, 8 entries). A **hit** requires the entry valid, its VPN
equal, **and its domain equal to `domCur`** — the last conjunct is the whole
security content, and `domCur` is not an operand.

A miss under `mmu_en` **fails closed**: the address becomes `DATA_BASE`,
which carries no mapping, rather than falling through to the untranslated
address. Failing open would make the MMU decorative — the property to
demonstrate is that revoking a mapping *stops* an access, so a miss must not
quietly succeed. (Mini has no page-fault trap to raise here; the fail-closed
address is the deviation, recorded below.)

With `mmu_en = 0` this is the identity computation of every increment before
it, bit for bit — a `mux` on a register that is 0 at reset. -/
def tlbIdx (ea : Expr 64) : Expr 3 := .slice ea 12 3
def tlbVpnOf (ea : Expr 64) : Expr 32 := .zext (.slice ea 12 20) 32

def tlbHit (ea : Expr 64) : Expr 1 :=
  let i := tlbIdx ea
  .and (tlbVldRd i)
    (.and (.eq (tlbVpnRd i) (tlbVpnOf ea))
          (.eq (tlbDomRd i) domCur))

/-- Untranslated (bypass) DDR effective address — DATA_BASE + word-aligned
ea, the pre-EXT-7 computation unchanged. -/
def ddrEaRaw (ea : Expr 64) : Expr 32 :=
  .add (.lit (BitVec.ofNat 32 DATA_BASE)) (.shl (.slice ea 3 29 |> fun w => .zext w 32) (.lit (BitVec.ofNat 32 3)))

/-- Translated address: the entry's PPN concatenated with the page offset. -/
def ddrEaXlat (ea : Expr 64) : Expr 32 :=
  .add (.lit (BitVec.ofNat 32 DATA_BASE))
    (.or (.shl (tlbPpnRd (tlbIdx ea)) (.lit (BitVec.ofNat 32 12)))
         (.zext (.slice ea 0 12) 32))

def ddrEa (ea : Expr 64) : Expr 32 :=
  .mux mmu_en
    (.mux (tlbHit ea) (ddrEaXlat ea) (.lit (BitVec.ofNat 32 DATA_BASE)))
    (ddrEaRaw ea)
def ddrPc : Expr 32 := .add (.lit (BitVec.ofNat 32 DATA_BASE)) (.slice pc 0 32)

def retireInc : Act := .write 32 "retire" (.add retire (.lit (BitVec.ofNat 32 1)))
def goF0 : Act := .write 5 "st" (L5 S_F0)
def stepPc : Act := .write 64 "pc" pc8

/-- Cons for an if/else-if chain kept as *data*, so `actPriTree` can
re-associate it into a balanced dispatch instead of a linear one. -/
def gcons (g : Expr 1) (a : Act) (rest : List (Expr 1 × Act)) : List (Expr 1 × Act) :=
  (g, a) :: rest

/-- Right-nested sequence of a list of actions. -/
def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

/-! ### S_EX helpers (dynamic per-thread writes; scheduler switches) -/

/-- `pc <= tpc[idx]`. **D20**: one async memory read instead of a balanced
32-way select over 32 registers. Same function of the same pre-cycle state
(D9: `memRead` evaluates against `σ`). -/
def setPcFromTpc (idx : Expr 5) : Act := .write 64 "pc" (tpcRd idx)
def tstateDynWrite (v : Expr 2) (idx : Expr 5) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (.write 2 s!"tstate{i.val}" v) .skip) acc) .skip
def tfutexDynWrite (idx : Expr 5) (v : Expr 64) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (.write 64 s!"tfutex{i.val}" v) .skip) acc) .skip
/-- dynamic tstate[idx]==v test as a (balanced) mux chain. -/
def tstateEq (idx : Expr 5) (v : Expr 2) : Expr 1 :=
  priTree ((List.finRange NT).map (fun i => (.eq idx (L5 i.val), .eq (tstate i) v))) (L1 0)
/-- any thread not FREE. -/
def anyLive : Expr 1 :=
  orTree ((List.finRange NT).map (fun i => .not (.eq (tstate i) (L2 0))))

/-! ### EXT-4 — the shared wake bank's operands

`wakeLocal` is the one-cycle `FUTEX_WAKE` pulse; `doorbell` is the remote
request. `wakeKey` selects which address the single comparator bank compares
against, and `wakeEn` says whether it does anything at all. Local wins a tie
— a doorbell arriving on the same cycle as a local `FUTEX_WAKE` is dropped
rather than merged, which is safe because a futex waiter must re-check its
condition after waking and the waker retries; merging two keys into one bank
pass is the thing that cannot be done with one comparator. -/
def wakeLocal : Expr 1 := .and fsmEn (.and (.eq st (L5 S_EX)) (opIs OP_FUTEX_WAKE))
def wakeEn    : Expr 1 := .or wakeLocal doorbell
def wakeKey   : Expr 64 := .mux wakeLocal rdval doorbell_key

/-- FUTEX_WAKE: wake matching FUTEX threads. EXT-4 made this the design's
ONE wake comparator bank, shared by the local `FUTEX_WAKE` and the remote
doorbell via `wakeKey`/`wakeEn`; the count limit `a` applies to the local
wake only. Per-element guard: `wakeEn ∧ tstate_i==3 ∧ tfutex_i==wakeKey
∧ (¬local ∨ matches-before-i < a)`. -/
def wakeMatch (i : Fin NT) : Expr 1 :=
  .and wakeEn
    (.and (.eq (tstate i) (L2 3))
      (.and (.eq (tfutex i) wakeKey)
        -- EXT-4: the count limit is the LOCAL wake's; a remote doorbell
        -- wakes everything parked on the key.
        (.or (.not wakeLocal) (.ult (matchesBefore i.val) a))))
where
  /-- `tstate_j == FUTEX ∧ tfutex_j == wakeKey`. -/
  fmatch (j : Nat) : Expr 1 :=
    .and (.eq (.reg 2 s!"tstate{j}") (L2 3)) (.eq (.reg 64 s!"tfutex{j}") wakeKey)
  /-- popcount of `fmatch j` for `j < i`, zero-extended to 64 for the
  `< a` test. Was a linear chain of up to 31 **64-bit** adds; the count is
  bounded by NT = 32, so a 6-bit balanced adder tree carries the exact same
  value (no truncation) at depth ~log₂32 with 6-bit — not 64-bit — carry
  chains. -/
  matchesBefore (i : Nat) : Expr 64 :=
    .zext (addTree ((List.range i).map (fun j => (.zext (fmatch j) 6 : Expr 6)))) 64

/-! ### EXT-4 — the wake is REGISTERED, to keep the bank off the critical path

The shared bank cut area hard (53 888 → 44 809 LUTs) but moved `sysclk` from
33.96 MHz to 25.25 MHz against a 25 MHz clock — 1 % margin, thinner than the
~4 % this file already calls dangerous. The reason is placement, not size:
in EXT-3 the bank sat inside the `S_EX` arm of the FSM's guarded chain, so
the comparators were behind the FSM decode; sharing it moved it into
`smpRule`, which runs *last*, putting `tfutex → 64-bit eq → popcount tree →
tstate mux` in one combinational path every cycle.

So the decision is registered: `wake_bm` holds the per-slot match computed
this cycle and the promotion to READY happens next cycle. The long path now
ends at a flop (`… → popcount → wake_bm`) and the path that survives into
`tstate` is a single bit test.

**A one-cycle-late wake is sound, and by the increment's own argument.** A
futex wake may be *spurious* but never *missed*: every waiter re-checks its
condition after waking. A slot that re-parks in the intervening cycle can be
woken on a stale match — that is a spurious wake, which is legal — while a
slot parked on the woken key at match time is still parked at apply time
unless something else already woke it. This is the same over-approximation
licence that lets the directory exist at all. -/
def wake_bm : Expr 32 := .reg 32 "wake_bm"

/-- The per-slot match as a bitmap (disjoint lanes, so the OR folds to a
tree). This is the combinational half; `wake_bm` registers it. -/
def wakeBmE : Expr 32 :=
  orTreeW ((List.finRange NT).map
    (fun i => .shl (.zext (wakeMatch i) 32) (.lit (BitVec.ofNat 32 i.val))))

/-- The registered half: promote every slot whose bit survived, guarded on
still being parked so a slot that was woken and re-parked on another key in
the intervening cycle is not silently re-stated. -/
def wakeApply : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.and (.eq (.slice (.shr wake_bm (.lit (BitVec.ofNat 32 i.val))) 0 1)
                          (.lit (BitVec.ofNat 1 1)))
                     (.eq (tstate i) (L2 3)))
           (.write 2 s!"tstate{i.val}" (L2 1)) .skip) acc) .skip

/-- `S_F0` — the instruction boundary, and (EXT-1) the preemption point.

The new middle arm is exactly the switch `YIELD` performs, moved to the
boundary: save the outgoing thread's resume pc into `tpc[cur]` (in
`tpcTriples`, the single `tpc` write funnel), `cur <= next_ready`,
`pc <= tpc[next_ready]`.

**The saved pc is `pc`, not `pc8`.** At `S_EX` a `YIELD` has already
consumed the instruction at `pc`, so its resume point is `pc+8`. At `S_F0`
*nothing has been consumed* — `pc` is the instruction about to be fetched —
so `pc` is the resume point. Writing `pc8` here would silently skip one
instruction of the preempted thread on every tick (see `EXTEND_SPEC.md`
deviations).

`st` is **not** written, so the core stays in `S_F0` and fetches the new
thread's instruction on the next cycle: a preemption costs exactly one
cycle and issues no bus transaction from the old context. -/
def s_f0 : Expr 1 × Act := stArm S_F0
  (.ite bus_req (.write 5 "st" (L5 S_PAUSE))
    -- EXT-3: fail-stop, checked BEFORE the preemption point and before the
    -- fetch. Nothing has been fetched at `S_F0` and `bus_req` is already
    -- excluded above, so the core stops with no transaction outstanding
    -- and `pc` still addressing the un-executed instruction.
    (.ite curPoisoned (.write 1 "running" (L1 0))
    (.ite preemptFire
      (.seq (.write 5 "cur" next_ready) (setPcFromTpc next_ready))
      (.seq (.write 32 "core_addr" ddrPc)
        (.seq (.write 1 "core_rd" (L1 1)) (.write 5 "st" (L5 S_FW)))))))

def s_pause : Expr 1 × Act := stArm S_PAUSE  (.ite (.not bus_req) goF0 .skip)

def s_fw : Expr 1 × Act := stArm S_FW
  (.ite mDone (.seq (.write 64 "ir" mRdata) (.write 5 "st" (L5 S_RD))) .skip)

/-- `S_RD`: latch the three source operands. **D19 sync-read sites** —
each written value is a bare `memRead` of `rf` (no zero-mux, no shared
address net), so `Design.syncReadOkB "rf"` holds and the compiled
`a <= n_k` / `wire n_k = rf[n_a];` pair is block-RAM shaped.

The `(rsNf == 0) ? 0 : ...` zero-muxes the Verilog original carried are
deleted, not moved: by invariant Z (`Loom/Hw/D19_SPEC.md` — every triple
of `rfTriples` either writes a low-index that is guarded nonzero, or is
the zeroing sweep writing 0) `rf[{t,0}]` is 0 in every reachable state,
so the mux was the identity. Every register keeps its exact cycle-by-cycle
value and the ISS is untouched. -/
def s_rd : Expr 1 × Act := stArm S_RD
  (.seq (.write 64 "a" (.memRead 64 "rf" (cat55 cur rs1f)))
    (.seq (.write 64 "b" (.memRead 64 "rf" (cat55 cur rs2f)))
      (.seq (.write 64 "rdval" (.memRead 64 "rf" (cat55 cur rdf)))
            (.write 5 "st" (.mux is_sel (L5 S_RD2) (L5 S_EX))))))

/-- `S_RD2`: the two extra operands of a SELECT. Same D19 shape; the
addresses name `rs3f`/`rs4f` directly (they are what `r1a`/`r2a` reduced
to in this state). -/
def s_rd2 : Expr 1 × Act := stArm S_RD2
  (.seq (.write 64 "sel_t" (.memRead 64 "rf" (cat55 cur rs3f)))
    (.seq (.write 64 "sel_f" (.memRead 64 "rf" (cat55 cur rs4f)))
          (.write 5 "st" (L5 S_EX))))

-- S_EX: if-else priority tree mirroring the Verilog (rf writes in the
-- funnel; here: pc/retire/st/scheduler-array/master-handshake side effects).

/-- The S_EX opcode dispatch, kept as an explicit (guard, action) list in
the Verilog's textual if/else-if order. `actPriTree` re-associates it into
a balanced else-if tree: identical first-match-wins behaviour (see
`actPriPair`), but the mux cone every register sees shrinks from ~29
levels to ~5. -/
def s_ex_branches : List (Expr 1 × Act) :=
  -- 0x3a EXIT
  gcons (opIs OP_EXIT) (.seq (.write 1 "halted" (L1 1)) (.seq (.write 1 "running" (L1 0)) retireInc)) <|
  -- 0x3b THREAD_EXIT
  gcons (opIs OP_THREAD_EXIT)
    (.seq (tstateDynWrite (L2 0) cur)
      (.seq (.ite (.not (.eq next_ready cur))
              (.seq (.write 5 "cur" next_ready) (.seq (setPcFromTpc next_ready) goF0))
              (.write 5 "st" (L5 S_WAIT)))
            retireInc)) <|
  -- 0x00 NOP
  gcons (opIs OP_NOP) (.seq stepPc (.seq retireInc goF0)) <|
  -- fence
  gcons is_fence (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x12 MUL
  gcons (opIs OP_MUL)
    (.seq (.write 128 "mul_acc" (.lit (BitVec.ofNat 128 0)))
      (.seq (.write 128 "mul_aw" (.zext a 128))
        (.seq (.write 64 "mul_b" b) (.seq (.write 2 "mul_kind" (L2 0)) (.write 5 "st" (L5 S_MUL)))))) <|
  -- mulh
  gcons is_mulh
    (.seq (.write 128 "mul_acc" (.lit (BitVec.ofNat 128 0)))
      (.seq (.write 128 "mul_aw" (.zext a 128))
        (.seq (.write 64 "mul_b" b)
          (.seq (.write 2 "mul_kind" (.mux (opIs OP_MULH) (L2 1) (L2 2))) (.write 5 "st" (L5 S_MUL)))))) <|
  -- div
  gcons is_div
    (.ite (.eq b (L64 0))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))
      (.seq (.write 64 "div_rem" (L64 0))
        (.seq (.write 64 "div_quo" div_a_abs)
          (.seq (.write 64 "div_d" div_b_abs)
            (.seq (.write 7 "div_cnt" (.lit (BitVec.ofNat 7 0)))
              (.seq (.write 1 "div_isrem" (.or (opIs OP_SREM) (opIs OP_UREM)))
                (.seq (.write 1 "div_negq" (.and div_sgn (.xor (.slice a 63 1) (.slice b 63 1))))
                  (.seq (.write 1 "div_negr" (.and div_sgn (.slice a 63 1))) (.write 5 "st" (L5 S_DIV)))))))))) <|
  -- sel
  gcons is_sel (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x54 GET_PCR
  gcons (opIs OP_GET_PCR)
    (.ite (.eq rs1f (L5 2)) (.seq stepPc (.seq retireInc goF0))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))) <|
  -- alu
  gcons is_alu (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x20 J
  gcons (opIs OP_JMP) (.seq (.write 64 "pc" (.add pc (.shl imm_j (L64 3)))) (.seq retireInc goF0)) <|
  -- 0x27 JAL
  gcons (opIs OP_JAL) (.seq (.write 64 "pc" (.add pc (.shl imm_j (L64 3)))) (.seq retireInc goF0)) <|
  -- 0x28 JALR
  gcons (opIs OP_JALR) (.seq (.write 64 "pc" (.add a imm_i)) (.seq retireInc goF0)) <|
  -- branch
  gcons is_branch (.seq (.write 64 "pc" (.mux br_take (.add pc (.shl imm_s (L64 3))) pc8)) (.seq retireInc goF0)) <|
  -- 0x06 YIELD
  gcons (opIs OP_YIELD)
    (.seq (.ite (.eq next_ready cur) stepPc
            (.seq (.write 5 "cur" next_ready) (setPcFromTpc next_ready)))
          (.seq retireInc goF0)) <|
  -- 0x07 SLEEP
  gcons (opIs OP_SLEEP)
    (.seq (tstateDynWrite (L2 2) cur)
      (.seq (.ite (.not (.eq next_ready cur))
              (.seq (.write 5 "cur" next_ready) (.seq (setPcFromTpc next_ready) goF0))
              (.write 5 "st" (L5 S_WAIT)))
            retireInc)) <|
  -- 0xcb FUTEX_WAIT
  gcons (opIs OP_FUTEX_WAIT)
    (.seq (.write 32 "core_addr" (.add (.lit (BitVec.ofNat 32 DATA_BASE)) (.shl (.zext (.slice rdval 3 29) 32) (.lit (BitVec.ofNat 32 3)))))
      (.seq (.write 1 "core_rd" (L1 1))
        (.seq (.write 64 "futex_addr_q" rdval) (.seq (.write 64 "futex_exp" a) (.write 5 "st" (L5 S_FTX1)))))) <|
  -- 0xcc FUTEX_WAKE (per-element wake; count via matches-before-i < a)
  -- EXT-4: the wake bank moved to `smpRule` (one shared bank); S_EX keeps
  -- only the sequencing half of FUTEX_WAKE.
  gcons (opIs OP_FUTEX_WAKE) (.seq stepPc (.seq retireInc goF0)) <|
  -- EXT-6: 0x62 CAP_SEND (a = handle, b = target domain) and 0x63 CAP_RECV.
  -- Both just sequence here; the inbox, the occupancy bitmap and `rd` are
  -- written in their funnels.
  gcons (opIs CAP_SEND_OP) (.seq stepPc (.seq retireInc goF0)) <|
  gcons (opIs CAP_RECV_OP) (.seq stepPc (.seq retireInc goF0)) <|
  -- EXT-5: 0x60 GATE_CALL. `a` is the gate id. Refused (rd = -1, no state
  -- change) if this thread is already inside a gate -- the continuation is
  -- depth 1. Otherwise: save the return point, mark in-gate, and jump to
  -- the gate's entry in the gate's domain. `tdom`/`tcont`/`tcdom`/`in_gate`
  -- are written in their funnels; this arm owns pc and rd.
  gcons (opIs OP_MINI_GATE_CALL)
    (.ite curInGate
      (.seq (.ite (.not (.eq rdf (L5 0))) .skip .skip)
        (.seq stepPc (.seq retireInc goF0)))
      (.seq (.write 64 "pc" (gateEntRd (.slice a 0 4)))
        (.seq retireInc goF0))) <|
  -- EXT-5: 0x61 GATE_RETURN. Restores the saved pc; the domain and the
  -- in-gate bit are restored in their funnels. A return with no gate open
  -- is a no-op (it just steps), which is the fail-quiet reading: a thread
  -- cannot leave a domain it never entered.
  gcons (opIs OP_MINI_GATE_RETURN)
    (.ite curInGate
      (.seq (.write 64 "pc" (tcontRd cur)) (.seq retireInc goF0))
      (.seq stepPc (.seq retireInc goF0))) <|
  -- 0x59 CLONE
  gcons (opIs OP_CLONE_SPAWN)
    (.ite has_free
      (.seq (tstateDynWrite (L2 1) free_slot)
        (.seq (.write 5 "clone_dst" rdf) (.seq (.write 5 "clone_tid" free_slot) (.write 5 "st" (L5 S_CLONE2)))))
      (.seq stepPc (.seq retireInc goF0))) <|
  -- LR
  gcons is_lr
    (actSeq [.write 64 "lr_addr" a, .write 1 "lr_valid" (L1 1),
      .write 3 "ld_boff_q" (.lit (BitVec.ofNat 3 0)), .write 8 "ld_op_q" (L8 OP_LD),
      .write 5 "ld_rd_q" rdf, .write 1 "mem_is_store" (L1 0),
      .ite (.ult a (L64 0x1000))
        (actSeq [.write 9 "dmem_a" (.slice a 3 9), .write 5 "st" (L5 S_L0)])
        (actSeq [.write 32 "core_addr" (ddrEa a), .write 1 "core_rd" (L1 1),
                 .write 1 "lr_req" (L1 1),          -- tag: this read takes a reservation
                 .write 5 "st" (L5 S_DL)])]) <|
  -- SC
  gcons is_sc
    (.seq (.ite (.and lr_valid (.eq lr_addr a))
            (.ite (.ult a (L64 0x1000))
              (.seq (.write 1 "dmem_we" (L1 1)) (.seq (.write 9 "dmem_a" (.slice a 3 9)) (.seq (.write 64 "dmem_wd" b) (.seq stepPc (.seq retireInc goF0)))))
              (actSeq [.write 32 "core_addr" (ddrEa a), .write 64 "core_wdata" b,
                       .write 1 "core_wr" (L1 1),
                       .write 1 "sc_req" (L1 1),      -- tag: conditional store
                       .write 1 "sc_pending" (L1 1),  -- the verdict is due at S_DSW
                       .write 5 "st" (L5 S_DSW)]))
            (.seq stepPc (.seq retireInc goF0)))
          (.write 1 "lr_valid" (L1 0))) <|
  -- UART_RX load
  gcons (.and is_load (.eq mem_ea_l (L64 UART_RX_ADDR)))
    (.seq (.ite (.not (.eq rx_rptr rx_wptr)) (.write 9 "rx_rptr" (.add rx_rptr (.lit (BitVec.ofNat 9 1)))) .skip)
          (.seq stepPc (.seq retireInc goF0))) <|
  -- GP load
  gcons (.and is_load l_is_gp)
    (.ite (opIs OP_LD_31)
      (.seq (.write 32 "gp_addr_r" (.and (.slice mem_ea_l 0 32) (.lit (BitVec.ofNat 32 0xFFFFFFFC))))
        (.seq (.write 1 "gp_rd" (L1 1)) (.seq (.write 5 "ld_rd_q" rdf) (.write 5 "st" (L5 S_GPL)))))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))) <|
  -- zp load
  gcons (.and is_load l_is_zp)
    (.seq (.write 9 "dmem_a" ld_widx) (.seq (.write 3 "ld_boff_q" ld_boff)
      (.seq (.write 8 "ld_op_q" op) (.seq (.write 5 "ld_rd_q" rdf) (.seq (.write 1 "mem_is_store" (L1 0)) (.write 5 "st" (L5 S_L0))))))) <|
  -- DDR load
  gcons is_load
    (.seq (.write 32 "core_addr" (ddrEa mem_ea_l)) (.seq (.write 1 "core_rd" (L1 1))
      (.seq (.write 3 "ld_boff_q" ld_boff) (.seq (.write 8 "ld_op_q" op) (.seq (.write 5 "ld_rd_q" rdf) (.seq (.write 1 "mem_is_store" (L1 0)) (.write 5 "st" (L5 S_DL)))))))) <|
  -- UART store
  gcons (.and is_store (.eq mem_ea_s (L64 UART_ADDR)))
    (.seq (.memWrite 8 8 "uart_mem" 0 (.slice uart_wptr 0 8) (.slice b 0 8))
      (.seq (.write 9 "uart_wptr" (.add uart_wptr (.lit (BitVec.ofNat 9 1)))) (.seq stepPc (.seq retireInc goF0)))) <|
  -- GP store
  gcons (.and is_store s_is_gp)
    (.ite (opIs OP_ST_34)
      (.seq (.write 32 "gp_addr_r" (.and (.slice mem_ea_s 0 32) (.lit (BitVec.ofNat 32 0xFFFFFFFC))))
        (.seq (.write 32 "gp_wdata_r" (.slice b 0 32)) (.seq (.write 1 "gp_wr" (L1 1)) (.write 5 "st" (L5 S_GPS)))))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))) <|
  -- zp store
  gcons (.and is_store s_is_zp)
    (.seq (.write 9 "dmem_a" st_widx) (.seq (.write 1 "mem_is_store" (L1 1)) (.write 5 "st" (L5 S_L0)))) <|
  -- DDR store
  gcons is_store
    (actSeq [.write 32 "core_addr" (ddrEa mem_ea_s), .write 1 "core_rd" (L1 1),
             .write 1 "mem_is_store" (L1 1), .write 1 "sc_pending" (L1 0),
             .write 5 "st" (L5 S_DL)]) <|
  []

/-- default: trap on an unknown opcode. -/
def s_ex_trap : Act :=
  .seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP)))

def s_ex_body : Act := actPriTree s_ex_branches s_ex_trap

def s_ex : Expr 1 × Act := stArm S_EX  s_ex_body

def s_l0 : Expr 1 × Act := stArm S_L0  (.write 5 "st" (L5 S_L1))

/-- S_L1: load-wb (rf in funnel) or store commit; then advance. -/
def s_l1 : Expr 1 × Act := stArm S_L1
  (actSeq [.ite (.not mem_is_store) .skip
            (actSeq [.write 1 "dmem_we" (L1 1), .write 9 "dmem_a" st_widx, .write 64 "dmem_wd" st_merge]),
           stepPc, retireInc, goF0])

def s_dl : Expr 1 × Act := stArm S_DL
  (.ite mDone (.seq (.write 64 "ddr_q" mRdata) (.write 5 "st" (L5 S_DST))) .skip)

/-- S_DST: load-wb (rf in funnel) + advance, or issue the DDR store. -/
def s_dst : Expr 1 × Act := stArm S_DST
  (.ite (.not mem_is_store)
    (actSeq [stepPc, retireInc, goF0])
    (actSeq [.write 32 "core_addr" (ddrEa mem_ea_s), .write 64 "core_wdata" st_merge,
             .write 1 "core_wr" (L1 1), .write 5 "st" (L5 S_DSW)]))

def s_dsw : Expr 1 × Act := stArm S_DSW
  (.ite mDone (actSeq [stepPc, retireInc, goF0]) .skip)

/-- S_CLONE2: child sp (rf in funnel) + fresh tp/sigmask (both in
`tarrFunnelRule`, D20) + advance. -/
def s_clone2 : Expr 1 × Act := stArm S_CLONE2 (.write 5 "st" (L5 S_CLONE3))

def s_clone3 : Expr 1 × Act := stArm S_CLONE3  (actSeq [stepPc, retireInc, goF0])

/-- S_FTX1: FUTEX_WAIT DDR-compare. -/
def s_ftx1 : Expr 1 × Act := stArm S_FTX1
  (.ite mDone
    (actSeq [.ite (.eq mRdata futex_exp)
              (actSeq [tstateDynWrite (L2 3) cur, tfutexDynWrite cur futex_addr_q,
                       .ite (.not (.eq next_ready cur))
                         (actSeq [.write 5 "cur" next_ready, setPcFromTpc next_ready, goF0])
                         (.write 5 "st" (L5 S_WAIT))])
              (actSeq [stepPc, goF0]),
             retireInc])
    .skip)

/-- S_WAIT: pick next ready or halt if all free. -/
def s_wait : Expr 1 × Act := stArm S_WAIT
  (.ite (tstateEq next_ready (L2 1))
    (actSeq [.write 5 "cur" next_ready, setPcFromTpc next_ready, goF0])
    (.ite (.not anyLive) (.seq (.write 1 "halted" (L1 1)) (.write 1 "running" (L1 0))) .skip))

/-- S_MUL: shift-add step or done (rf in funnel). -/
def s_mul : Expr 1 × Act := stArm S_MUL
  (.ite (.eq mul_b (L64 0))
    (actSeq [stepPc, retireInc, goF0])
    (actSeq [.ite (.eq (.slice mul_b 0 1) (L1 1)) (.write 128 "mul_acc" (.add mul_acc mul_aw)) .skip,
             .write 128 "mul_aw" (.shl mul_aw (.lit (BitVec.ofNat 128 1))),
             .write 64 "mul_b" (.shr mul_b (L64 1))]))

/-- S_DIV: restoring divide step or done (rf in funnel). 65-bit partial. -/
def s_div : Expr 1 × Act := stArm S_DIV
  (.ite (.eq div_cnt (.lit (BitVec.ofNat 7 64)))
    (actSeq [stepPc, retireInc, goF0])
    (let prem : Expr 65 := .or (.shl (.zext div_rem 65) (.lit (BitVec.ofNat 65 1))) (.zext (.slice div_quo 63 1) 65)
     let divd65 : Expr 65 := .zext div_d 65
     actSeq [
       .ite (.not (.ult prem divd65))
         (actSeq [.write 64 "div_rem" (.slice (.sub prem divd65) 0 64),
                  .write 64 "div_quo" (.or (.shl div_quo (L64 1)) (L64 1))])
         (actSeq [.write 64 "div_rem" (.slice prem 0 64),
                  .write 64 "div_quo" (.shl div_quo (L64 1))]),
       .write 7 "div_cnt" (.add div_cnt (.lit (BitVec.ofNat 7 1)))]))

def s_gpl : Expr 1 × Act := stArm S_GPL
  (.ite gpDone (actSeq [stepPc, retireInc, goF0]) .skip)
def s_gps : Expr 1 × Act := stArm S_GPS
  (.ite gpDone (actSeq [stepPc, retireInc, goF0]) .skip)

/-- S_TRAP: hold. default state: go F0. -/
def s_default : Expr 1 × Act := (.ult (L5 S_GPS) st, goF0)

/-- (8) the whole `st` dispatch as ONE rule.

Previously these were 20 sibling rules in `design.rules`; the compiler
chains rules linearly, so every register they touch (`st`, `pc`, `retire`,
…) grew a ~20-level mux chain *on top of* its intra-rule cone. The arm
guards `st == S_F0 … st == S_GPS` and the default arm `S_GPS < st` are
pairwise disjoint, so at most one arm ever fires: running them as a single
balanced first-match dispatch commits exactly the same writes as the
ordered rule list (last-write-wins never had two writers to disambiguate).
`fsmEn` is hoisted out of the arms — it was ANDed into every `stG` guard.
The only memory write below `fsmEn` is `uart_mem` (S_EX UART store), so no
`memWrite` port ordering changes. -/
def fsmRule : Rule :=
  ⟨"fsm", .ite fsmEn
    (actPriTree
      [s_f0, s_pause, s_fw, s_rd, s_rd2, s_ex, s_l0, s_l1, s_dl, s_dst, s_dsw,
       s_clone2, s_clone3, s_ftx1, s_wait, s_mul, s_div, s_gpl, s_gps, s_default]
      .skip)
    .skip⟩

/-- (8b) the SMP cross-core rule (DUAL_SPEC extensions 1–3).

Runs **after** `fsmRule` so both overrides are deterministic:

* `wake_out` is written unconditionally, so it is a true one-cycle pulse:
  1 exactly on the cycle `FUTEX_WAKE` retires (`fsmEn ∧ st=S_EX ∧ op=0xcc`;
  op 0xcc is disjoint from every earlier S_EX guard, so that predicate
  characterises the branch exactly).
* `doorbell` promotes every thread whose **pre-cycle** state is FUTEX(3) to
  READY(1). A thread the FSM blocks *this* cycle had pre-cycle state 1, so
  its guard is false — the doorbell never cancels a fresh block, it only
  ever wakes threads that were already parked.
* `res_kill` clears `lr_valid` last, so it also cancels an `LR` issued the
  same cycle (a spurious kill only makes the matching `SC` fail → retry). -/
def smpRule : Rule :=
  ⟨"smp", actSeq
    [ .write 1 "wake_out" wakeLocal
      -- EXT-4: publish the key we woke on (hold otherwise).
    , .ite wakeLocal (.write 64 "wake_key" rdval) .skip
      -- EXT-4: THE one comparator bank. Local FUTEX_WAKE and the remote
      -- doorbell share it via `wakeKey`/`wakeEn`; previously the local wake
      -- had a bank here in S_EX and the doorbell woke every parked thread
      -- unkeyed.
      -- EXT-4: compute the match this cycle, promote next cycle (see above).
    , .write 32 "wake_bm" wakeBmE
    , wakeApply
    , .ite resKill (.write 1 "lr_valid" (L1 0)) .skip ]⟩

/-! ### (9a) The thread-table write funnels (D20)

The four converted arrays (`tpc`, `tsleep`, `tp_arr`, `sigmask_arr`) get
their writes hoisted out of the FSM into one funnel rule, exactly the way
`rfTriples`/`rfFunnelRule` hoists the regfile's — so each array has **one**
syntactic `memWrite` site here (`tsleep` has a second, earlier one in
`sleepScanRule`), which keeps `Compile.MemWriteWF`'s "port indices strictly
increase along the syntactic write order" trivially true.

The guards reproduce each FSM branch's reachability condition. As with
`rfTriples`, the `S_EX` opcode guards need no negation chain: the opcodes
`0x06`/`0x07`/`0x59` appear in no earlier branch predicate of
`s_ex_branches`, so `exG (opIs …)` characterises the branch exactly.

`tpc` entry 1 is the `cmd 13` reset, re-expressed as a 32-cycle sweep off
the zeroing counter (see `cmd13reset`). `zeroing` forces `fsmEn` low, so it
is disjoint from entries 2–5 and the funnel's priority is immaterial. -/
def tpcTriples : List (Expr 1 × Expr 5 × Expr 64) :=
  -- 1. cmd-13 reset sweep (rides the zeroing engine's counter)
  [ (.and zeroing (.ult zctr (.lit (BitVec.ofNat 10 NT))), .slice zctr 0 5, L64 TEXT_BASE)
  -- 2. S_EX YIELD (0x06), only when actually switching away
  , (exG (.and (opIs OP_YIELD) (.not (.eq next_ready cur))), cur, pc8)
  -- 3. S_EX SLEEP (0x07)
  , (exG (opIs OP_SLEEP), cur, pc8)
  -- 4. S_EX CLONE (0x59) with a free slot: the child's entry PC
  , (exG (.and (opIs OP_CLONE_SPAWN) has_free), free_slot, a)
  -- 5. S_FTX1, FUTEX_WAIT that blocks (DDR word still equals the expected)
  , (.and fsmEn (.and (.eq st (L5 S_FTX1)) (.and mDone (.eq mRdata futex_exp))), cur, pc8)
  -- 6. EXT-1 preemption at the instruction boundary. Guard is disjoint from
  -- 2–5 (they are all `st = S_EX` or `st = S_FTX1`) and from 1 (`zeroing`
  -- forces `fsmEn` low). The datum is `pc`, NOT `pc8`: at `S_F0` the
  -- instruction at `pc` has not been fetched yet (see `s_f0`).
  , (preemptFire, cur, pc) ]

def tpcWeE : Expr 1 := orTree (tpcTriples.map (fun t => t.1))
def tpcWaE : Expr 5 := priTree (tpcTriples.map (fun t => (t.1, t.2.1))) (L5 0)
def tpcWdE : Expr 64 := priTree (tpcTriples.map (fun t => (t.1, t.2.2))) (L64 0)

/-- `S_CLONE2` — the only writer of `tp_arr`/`sigmask_arr`. -/
def cloneFresh : Expr 1 := .and fsmEn (.eq st (L5 S_CLONE2))

/-! ### EXT-2 — the `tdom` write funnel

Three writers, one syntactic `memWrite` site, same discipline as `tpc`:

1. **`cmd 13` reset** rides the zeroing sweep and puts every thread in
   domain 0. This is what makes "the guest is domain 0" true by
   construction rather than by the reset image (D37: the constant lives in
   the sweep, not in the bank).
2. **`CLONE` inheritance** — the child gets `domCur`, the parent's domain.
   The guard is the same `has_free` branch that allocates `free_slot` and
   writes the child's `tpc`, so the child's domain and entry PC are written
   in the same cycle and cannot disagree.
3. **`cmd 58`** is the only way a domain tag changes to something new, and
   it is a debug/host operation — no instruction moves a thread between
   domains. Entry 1 is disjoint from 2–3 (`zeroing` forces `fsmEn` low). -/
def tdomTriples : List (Expr 1 × Expr 5 × Expr 8) :=
  [ (.and zeroing (.ult zctr (.lit (BitVec.ofNat 10 NT))), .slice zctr 0 5, L8 0)
  , (exG (.and (opIs OP_CLONE_SPAWN) has_free), free_slot, domCur)
  , (.and cmdValid (.eq cmdIdx (L7 CMD_SETDOM)), .slice cmdData 0 5, .slice cmdData 8 8)
  -- EXT-5: a gate call moves the thread to the GATE's domain -- a domain
  -- the host installed, never one the instruction names. A return restores
  -- the caller's. These two are the only instruction-driven `tdom` writes.
  , (exG (.and (opIs OP_MINI_GATE_CALL) (.not curInGate)), cur, gateDomRd (.slice a 0 4))
  , (exG (.and (opIs OP_MINI_GATE_RETURN) curInGate), cur, tcdomRd cur) ]

def tdomWeE : Expr 1 := orTree (tdomTriples.map (fun t => t.1))
def tdomWaE : Expr 5 := priTree (tdomTriples.map (fun t => (t.1, t.2.1))) (L5 0)
def tdomWdE : Expr 8 := priTree (tdomTriples.map (fun t => (t.1, t.2.2))) (L8 0)

/-! ### EXT-5 — the gate write funnels

`gateCall`/`gateRet` are the two guards; each memory gets ONE syntactic
`memWrite`, the `tpc` discipline. `in_gate` is a bitmap register (like
EXT-3's `poison`) because nothing reads it at a dynamic index -- only at
`cur` -- but it must be *set and cleared* per slot, and a 32-bit
set/clear on a register is one mux where a memory would be a port. -/
def gateCall : Expr 1 := exG (.and (opIs OP_MINI_GATE_CALL) (.not curInGate))
def gateRet  : Expr 1 := exG (.and (opIs OP_MINI_GATE_RETURN) curInGate)

/-- `in_gate` after this cycle: set bit `cur` on a gate call, clear it on a
gate return, plus the `cmd 13` reset. -/
def inGateNext : Expr 32 :=
  .mux (.and zeroing (.eq zctr (.lit (BitVec.ofNat 10 0)))) (L32 0)
    (.mux gateCall (.or in_gate (.shl (L32 1) (.zext cur 32)))
      (.mux gateRet (.and in_gate (.not (.shl (L32 1) (.zext cur 32)))) in_gate))

/-- EXT-6: occupancy after this cycle — set on a landing send, cleared on a
landing receive, zeroed by the `cmd 13` reset. Send and receive can only
collide on the same slot if a domain sends to itself, and then the send is
refused first (`capSendFire` requires the slot free), so the two are
disjoint by construction. -/
def capIvalNext : Expr 16 :=
  .mux (.and zeroing (.eq zctr (.lit (BitVec.ofNat 10 0)))) (.lit (BitVec.ofNat 16 0))
    (.mux capSendFire
      (.or cap_ival (.shl (.lit (BitVec.ofNat 16 1)) (.zext capSendSlot 16)))
      (.mux capRecvFire
        (.and cap_ival (.not (.shl (.lit (BitVec.ofNat 16 1)) (.zext capRecvSlot 16))))
        cap_ival))

/-- EXT-7: the valid bitmap after this cycle. `cmd 65` validates the selected
slot; `cmd 67` clears every slot whose `tlb_cell` equals the bumped cell;
`cmd 13`'s reset clears all. -/
def tlbVldNext : Expr 8 :=
  let clearMask : Expr 8 :=
    orTreeW ((List.finRange TLBN).map (fun i =>
      .mux (.and (.and cmdValid (.eq cmdIdx (L7 CMD_MAP_PROTECT)))
                 (.eq (tlbCellRd (.lit (BitVec.ofNat 3 i.val))) (.slice cmdData 0 8)))
        (.shl (.lit (BitVec.ofNat 8 1)) (.lit (BitVec.ofNat 8 i.val)))
        (.lit (BitVec.ofNat 8 0))))
  .mux (.and zeroing (.eq zctr (.lit (BitVec.ofNat 10 0)))) (.lit (BitVec.ofNat 8 0))
    (.mux (.and cmdValid (.eq cmdIdx (L7 CMD_TLB_VPN)))
      (.or tlb_vld (.shl (.lit (BitVec.ofNat 8 1)) (.zext tlb_sel 8)))
      (.and tlb_vld (.not clearMask)))

def tarrFunnelRule : Rule :=
  ⟨"tarr_funnel",
    .seq (.ite tdomWeE (.memWrite 5 8 "tdom" 0 tdomWaE tdomWdE) .skip) <|
    -- EXT-5: the depth-1 continuation, written only by a gate call.
    .seq (.ite gateCall (.memWrite 5 64 "tcont" 0 cur pc8) .skip) <|
    .seq (.ite gateCall (.memWrite 5 8 "tcdom" 0 cur domCur) .skip) <|
    .seq (.write 32 "in_gate" inGateNext) <|
    -- EXT-6: the inbox write (one syntactic site) and the occupancy bitmap.
    .seq (.ite capSendFire (.memWrite 4 64 "cap_ibox" 0 capSendSlot a) .skip) <|
    .seq (.write 16 "cap_ival" capIvalNext) <|
    -- EXT-7: TLB fill (cmd 65 sets vpn+domain for the selected entry and
    -- validates it; cmd 66 sets its ppn+cell). The shootdown (cmd 67)
    -- invalidates every entry naming the bumped cell -- the §15 line 876
    -- rule that the cached translation's cell IS the VMA's cell.
    .seq (.ite (.and cmdValid (.eq cmdIdx (L7 CMD_TLB_VPN)))
            -- Mask off the domain field in [31:24]: the stored tag must be
            -- the VPN alone, or it can never equal `tlbVpnOf ea`.
            (.memWrite 3 32 "tlb_vpn" 0 tlb_sel (.zext (.slice cmdData 0 24) 32)) .skip) <|
    .seq (.ite (.and cmdValid (.eq cmdIdx (L7 CMD_TLB_VPN)))
            (.memWrite 3 8 "tlb_dom" 0 tlb_sel (.slice cmdData 24 8)) .skip) <|
    .seq (.ite (.and cmdValid (.eq cmdIdx (L7 CMD_TLB_PPN)))
            (.memWrite 3 32 "tlb_ppn" 0 tlb_sel (.zext (.slice cmdData 0 24) 32)) .skip) <|
    .seq (.ite (.and cmdValid (.eq cmdIdx (L7 CMD_TLB_PPN)))
            (.memWrite 3 8 "tlb_cell" 0 tlb_sel (.slice cmdData 24 8)) .skip) <|
    -- EXT-7: the valid bitmap. Fill sets the selected slot; the §15
    -- shootdown clears every slot whose recorded cell was bumped -- several
    -- at once, which is why this is a register and not a memory.
    .seq (.write 8 "tlb_vld" tlbVldNext) <|
    -- EXT-5: the host-loaded gate table.
    .seq (.ite (.and cmdValid (.eq cmdIdx (L7 CMD_GATE_ENT)))
            (.memWrite 4 64 "gate_ent" 0 gate_sel (.zext cmdData 64)) .skip) <|
    .seq (.ite (.and cmdValid (.eq cmdIdx (L7 CMD_GATE_DOM)))
            (.memWrite 4 8 "gate_dom" 0 (.slice cmdData 0 4) (.slice cmdData 8 8)) .skip) <|
    .seq (.ite tpcWeE (.memWrite 5 64 "tpc" 0 tpcWaE tpcWdE) .skip)
      (.seq (.ite (exG (opIs OP_SLEEP))
              (.memWrite 5 64 "tsleep" 1 cur (.mux (.eq a (L64 0)) (L64 1) a)) .skip)
        (.seq (.ite cloneFresh (.memWrite 5 64 "tp_arr" 0 clone_tid (L64 0)) .skip)
              (.ite cloneFresh (.memWrite 5 64 "sigmask_arr" 0 clone_tid (L64 0)) .skip)))⟩

/-- (9) the single regfile write port. -/
def rfFunnelRule : Rule :=
  ⟨"rf_funnel", .ite rfWeE (.memWrite 10 64 "rf" 0 rfWaE rfWdE) .skip⟩

/-- (10) EXT-1 — the quantum counter, the design's **only** writer of
`qctr`, in strict priority:

1. `cmd CMD_QUANTUM` arms the counter with the word it just loaded into
   `quantum`, so a host that sets a quantum gets one immediately (and
   setting 0 disarms without waiting for anything);
2. the `cmd 13` **soft reset** re-arms a full quantum for the fresh thread
   0, so a run never inherits a half-spent counter from the previous one;
3. `preemptAtF0` — the boundary reload, taken on both the switching and the
   non-switching (nobody else is READY) case;
4. `qTick` — the countdown, which stops at 0 rather than wrapping.

Every read is pre-cycle (D9), so this rule's position in `rules` is
immaterial to its value; it sits last because it is the newest. -/
def quantumRule : Rule :=
  ⟨"quantum",
    .ite (.and cmdValid (.eq cmdIdx (L7 CMD_QUANTUM))) (.write 32 "qctr" cmdData)
      (.ite (.and cmdValid (.and (.eq cmdIdx (L7 13)) (.eq (.slice cmdData 0 1) (L1 1))))
        (.write 32 "qctr" quantum)
        (.ite preemptAtF0 (.write 32 "qctr" quantum)
          (.ite qTick (.write 32 "qctr" (.sub qctr (L32 1))) .skip)))⟩

/-! ## Register / memory / input declarations -/

def scalarRegs : List RegDecl :=
  [⟨"cur",5,0⟩, ⟨"pc",64,BitVec.ofNat 64 TEXT_BASE⟩, ⟨"retire",32,0⟩,
   ⟨"running",1,0⟩, ⟨"halted",1,0⟩, ⟨"st",5,0⟩, ⟨"ir",64,0⟩,
   ⟨"a",64,0⟩, ⟨"b",64,0⟩, ⟨"rdval",64,0⟩, ⟨"sel_t",64,0⟩, ⟨"sel_f",64,0⟩,
   ⟨"mem_is_store",1,0⟩, ⟨"trap_active",1,0⟩, ⟨"trapped_op",8,0⟩,
   ⟨"core_rd",1,0⟩, ⟨"core_wr",1,0⟩, ⟨"core_addr",32,0⟩, ⟨"core_wdata",64,0⟩,
   ⟨"jtag_rd",1,0⟩, ⟨"jtag_wr",1,0⟩, ⟨"jtag_wdata",64,0⟩, ⟨"ddr_addr_j",32,0⟩,
   ⟨"ddr_lo_j",32,0⟩, ⟨"ddr_rd_l",64,0⟩, ⟨"ddr_q",64,0⟩, ⟨"bus_req",1,0⟩,
   ⟨"gp_rd",1,0⟩, ⟨"gp_wr",1,0⟩, ⟨"gp_addr_r",32,0⟩, ⟨"gp_wdata_r",32,0⟩,
   ⟨"dmem_we",1,0⟩, ⟨"dmem_a",9,0⟩, ⟨"dmem_wd",64,0⟩, ⟨"dmem_rd",64,0⟩,
   ⟨"uart_wptr",9,0⟩, ⟨"uart_ridx",8,0⟩, ⟨"uart_byte",8,0⟩,
   ⟨"rx_wptr",9,0⟩, ⟨"rx_rptr",9,0⟩,
   ⟨"ld_boff_q",3,0⟩, ⟨"ld_op_q",8,0⟩, ⟨"ld_rd_q",5,0⟩,
   ⟨"lr_addr",64,0⟩, ⟨"lr_valid",1,0⟩, ⟨"futex_exp",64,0⟩, ⟨"futex_addr_q",64,0⟩,
   ⟨"sleep_scan",5,0⟩, ⟨"next_ready",5,0⟩, ⟨"free_slot",5,0⟩, ⟨"has_free",1,0⟩,
   ⟨"clone_dst",5,0⟩, ⟨"clone_tid",5,0⟩,
   ⟨"mul_acc",128,0⟩, ⟨"mul_aw",128,0⟩, ⟨"mul_b",64,0⟩, ⟨"mul_kind",2,0⟩,
   ⟨"div_rem",64,0⟩, ⟨"div_quo",64,0⟩, ⟨"div_d",64,0⟩, ⟨"div_cnt",7,0⟩,
   ⟨"div_isrem",1,0⟩, ⟨"div_negq",1,0⟩, ⟨"div_negr",1,0⟩,
   ⟨"zeroing",1,0⟩, ⟨"zctr",10,0⟩,
   ⟨"reg_sel",5,0⟩, ⟨"reg_wsel",5,0⟩, ⟨"reg_wlo",32,0⟩,
   ⟨"dmem_addr_j",32,0⟩, ⟨"dmem_lo_j",32,0⟩, ⟨"reg_rd",64,0⟩,
   ⟨"wake_out",1,0⟩, ⟨"wake_key",64,0⟩, ⟨"wake_bm",32,0⟩, ⟨"lr_req",1,0⟩, ⟨"sc_req",1,0⟩, ⟨"sc_pending",1,0⟩,
   -- EXT-1: both reset to 0 = preemption disabled = the cooperative machine
   ⟨"quantum",32,0⟩, ⟨"qctr",32,0⟩,
   -- EXT-2: observation mirror of `tdom[cur]` (the datapath uses `domCur`)
   ⟨"cur_dom",8,0⟩,
   -- EXT-3: fail-stop bitmap; 0 = nothing poisoned = the pre-EXT-3 machine
   ⟨"poison",32,0⟩,
   -- EXT-5: gates. `in_gate` = depth-1 continuation-present bitmap.
   ⟨"in_gate",32,0⟩, ⟨"gate_sel",4,0⟩,
   -- EXT-6: per-domain capability inbox occupancy
   ⟨"cap_ival",16,0⟩,
   -- EXT-7: mmu_en = 0 at reset = bypass = the pre-EXT-7 machine
   ⟨"mmu_en",1,0⟩, ⟨"tlb_sel",3,0⟩, ⟨"tlb_vld",8,0⟩]

/-- The two thread-table arrays that stay per-element registers (D20):
`tstate` (2-bit, multi-writer, read at every index by the ready/free
priority encoders) and `tfutex` (read at every index by `FUTEX_WAKE`'s
comparator bank). -/
def arrRegs : List RegDecl :=
  (List.finRange NT).map (fun i => ⟨s!"tstate{i.val}", 2, if i.val = 0 then 1 else 0⟩)
  ++ (List.finRange NT).map (fun i => ⟨s!"tfutex{i.val}", 64, 0⟩)

/-- (12) EXT-2 — the observation mirror. Unconditional: `cur_dom` is
`tdom[cur]` as of the previous cycle. It is the *only* writer of `cur_dom`
and `cur_dom` has no readers inside the design, so it cannot influence
behaviour — which is what makes it safe to let it lag. -/
def domainRule : Rule := ⟨"domain", .write 8 "cur_dom" domCur⟩

def design : Design where
  name := "lnp64mini"
  regs := scalarRegs ++ arrRegs
  -- D39a: outputs are mandatory and explicit, like inputs. This design's
  -- whole register set IS its interface, so it says so rather than
  -- relying on a default that exported everything silently.
  outputs := (scalarRegs ++ arrRegs).map (·.name)
  mems :=
    [⟨"rf", 10, 64, fun _ => 0⟩, ⟨"dmem", 9, 64, fun _ => 0⟩,
     ⟨"uart_mem", 8, 8, fun _ => 0⟩, ⟨"rx_mem", 8, 8, fun _ => 0⟩,
     -- D20: the thread table's single-dynamic-index arrays.
     -- **D37 (2026-08-01): `tpc`'s reset image is ALL-ZERO, not TEXT_BASE.**
     -- A non-zero image on a 32×64 bank is exactly the D30 defect: yosys
     -- maps it to distributed RAM and the configuration path does not carry
     -- the init, so the bank came up all-zero on the ZC702 while every
     -- model said `TEXT_BASE` (EPOCH_SPEC E13). The image was already
     -- redundant: D20.3 re-expressed `cmd 13`'s 32-entry reset as a sweep
     -- off the zeroing counter (`tpcTriples` entry 1), which writes
     -- TEXT_BASE into all 32 entries before anything can read them
     -- (`fsmEn` contains `¬zeroing`). Declaring zero makes the model agree
     -- with the silicon instead of the other way round — the epoch fix's
     -- shape: take the constant out of memory rather than add machinery to
     -- deliver it.
     ⟨"tpc", 5, 64, fun _ => 0⟩,
     ⟨"tsleep", 5, 64, fun _ => 0⟩,
     ⟨"tp_arr", 5, 64, fun _ => 0⟩, ⟨"sigmask_arr", 5, 64, fun _ => 0⟩,
     -- EXT-2: the per-thread domain tag. Zero image = every thread in
     -- domain 0; `cmd 13`'s sweep re-establishes that on every reset, so
     -- the constant does not have to survive the configuration path (D37).
     ⟨"tdom", 5, 8, fun _ => 0⟩,
     -- EXT-5: the gate table (host-loaded) and the depth-1 continuation.
     ⟨"gate_ent", 4, 64, fun _ => 0⟩, ⟨"gate_dom", 4, 8, fun _ => 0⟩,
     ⟨"tcont", 5, 64, fun _ => 0⟩, ⟨"tcdom", 5, 8, fun _ => 0⟩,
     -- EXT-6: one capability handle addressed to each domain
     ⟨"cap_ibox", 4, 64, fun _ => 0⟩,
     -- EXT-7: the domain-tagged TLB (§15 line 160)
     ⟨"tlb_vpn", 3, 32, fun _ => 0⟩, ⟨"tlb_ppn", 3, 32, fun _ => 0⟩,
     ⟨"tlb_dom", 3, 8, fun _ => 0⟩,
     ⟨"tlb_cell", 3, 8, fun _ => 0⟩]
  rules :=
    [encRule, sleepScanRule, latchRule, pulseDefaultsRule, zeroingRule, cmdRule, ddrRdLRule,
     fsmRule, smpRule, tarrFunnelRule, rfFunnelRule, quantumRule, domainRule]
  -- D19 (now a Loom obligation): `Design.emit` refuses to emit if any of
  -- these is read outside a register-latch site. `rx_mem` is deliberately
  -- absent — it is read combinationally inside the `rf` write data, so
  -- LUTRAM is the right implementation for it.
  syncReadMems := ["rf", "dmem", "uart_mem"]
  inputs :=
    [⟨"m_done",1⟩, ⟨"m_rdata",64⟩, ⟨"m_busy",1⟩,
     ⟨"gp_done",1⟩, ⟨"gp_rdata",32⟩, ⟨"gp_busy",1⟩,
     ⟨"cmd_valid",1⟩, ⟨"cmd_idx",7⟩, ⟨"cmd_data",32⟩,
     ⟨"res_kill",1⟩, ⟨"doorbell",1⟩, ⟨"doorbell_key",64⟩, ⟨"hold",1⟩, ⟨"sc_fail",1⟩]

/-! ## D19 — the sync-read (block RAM) obligation

`rf`, `dmem` and `uart_mem` must be read *only* through a register-latch
site, or `yosys` demotes them to distributed LUTRAM and the dual core does
not fit an XC7Z020 (`Loom/Hw/D19_SPEC.md`). The obligation is one
kernel-reducible Boolean per memory, discharged here and re-checked by
every emit path in `Emit.lean` (the D12/D13/D14 pattern).

`rx_mem` is deliberately *not* in the list: the UART_RX load reads it
combinationally inside the `rf` write data, so it stays LUTRAM — 256x8,
which is the right implementation for it anyway. -/
def syncReadMems : List String := design.syncReadMems

/-- The D19 check over `syncReadMems`. -/
def syncReadOk : Bool := syncReadMems.all (fun m => design.syncReadOkB m)

/-- Human-readable D19 report (one line per declared memory). -/
def syncReadReport : String :=
  String.intercalate "\n" (design.mems.map (fun md => design.syncReadReport md.name))

end Machines.Lnp64mini
