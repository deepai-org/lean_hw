-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Trees
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO
import Loom.Hw.SyncRead
import Loom.Hw.Declarations
import Loom.Hw.Dsl
import Machines.Lnp64mini.Interface

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
/-- §9: the gate continuation is a STACK, not depth-1. `MAXD` is the per-thread
gate-nesting depth (a bounded stack; §9's engine frame is bounds-checked). 4 is
enough for a gated write that itself crosses a boundary; overflow is a clean
refuse (domain-fatal in spirit). Must be a power of two so `cur*MAXD` is a shift. -/
def MAXD : Nat := 4
def CW : Nat := 5
def AW : Nat := 10

/-! ## Typed memory handles

The address/data widths and names below are the single source for memory
declarations and every core read/write site. -/

def rfBank      : Mem 10 64 := ⟨"rf"⟩
def dmemBank    : Mem 9 64  := ⟨"dmem"⟩
def tracePcBank : Mem 4 64  := ⟨"trace_pc"⟩
def traceWbBank : Mem 4 64  := ⟨"trace_wb"⟩
def uartBank    : Mem 8 8   := ⟨"uart_mem"⟩
def rxBank      : Mem 8 8   := ⟨"rx_mem"⟩
def icDataBank  : Mem 12 64 := ⟨"ic_data"⟩
def icTagBank   : Mem 12 42 := ⟨"ic_tag"⟩
def dcDataBank  : Mem 12 64 := ⟨"dc_data"⟩
def dcTagBank   : Mem 12 42 := ⟨"dc_tag"⟩
def tpcBank     : Mem 5 64  := ⟨"tpc"⟩
def tsleepBank  : Mem 5 64  := ⟨"tsleep"⟩
def tpBank      : Mem 5 64  := ⟨"tp_arr"⟩
def sigmaskBank : Mem 5 64  := ⟨"sigmask_arr"⟩
def tdomBank    : Mem 5 8   := ⟨"tdom"⟩
def tcontBank   : Mem 7 64  := ⟨"tcont"⟩
def tcdomBank   : Mem 7 8   := ⟨"tcdom"⟩
def gdepthBank  : Mem 5 3   := ⟨"gdepth"⟩

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
/-- **EXT-9**: the I-cache tag check. `S_F0` latches tag+data (the D19
sync-read sites) and lands here; a hit writes `ir` and goes straight to
`S_RD`, a miss issues exactly today's single-beat fetch. -/
def S_IC   : Nat := 21
/-- **§17 gate walk.** `S_GC0` waits for the descriptor's first word (the
entry PC), then issues the read of its second (the target domain); `S_GC1`
waits for that and commits the activation. -/
def S_GC0  : Nat := 22
def S_GC1  : Nat := 23
/-- **§17 cap walk.** Send: `S_CS0` waits for the target entry's flags word
and refuses or issues the handle write; `S_CS1` waits for that and issues
the flags write (occupied set); the store completes through `S_DSW`.
Receive: `S_CR0` waits for this domain's flags word and refuses or issues
the handle read; `S_CR1` writes `rd` from the handle and issues the flags
write (occupied cleared), completing through `S_DSW`. -/
def S_CS0  : Nat := 25
def S_CS1  : Nat := 26
def S_CR0  : Nat := 27
def S_CR1  : Nat := 28
/-- **EXT-10 `S_DC`**: the data-cache tag check. `S_EX` latches the banks
(D19 sync read) and lands here; a hit feeds `ddr_q` from the latched data
word and joins the existing `S_DST` writeback, a miss asserts `core_rd` on
the address `S_EX` already translated and joins `S_DL`. -/
def S_DC   : Nat := 24

/-! ## Input ports (D15) -/

def mDonePort    : Reg 1  := ⟨"m_done"⟩
def mRdataPort   : Reg 64 := ⟨"m_rdata"⟩
def mBusyPort    : Reg 1  := ⟨"m_busy"⟩
def gpDonePort   : Reg 1  := ⟨"gp_done"⟩
def gpRdataPort  : Reg 32 := ⟨"gp_rdata"⟩
def gpBusyPort   : Reg 1  := ⟨"gp_busy"⟩
def cmdValidPort : Reg 1  := ⟨"cmd_valid"⟩
def cmdIdxPort   : Reg 7  := ⟨"cmd_idx"⟩
def cmdDataPort  : Reg 32 := ⟨"cmd_data"⟩

def mDone    : Expr 1  := mDonePort.rd
def mRdata   : Expr 64 := mRdataPort.rd
def mBusy    : Expr 1  := mBusyPort.rd
def gpDone   : Expr 1  := gpDonePort.rd
def gpRdata  : Expr 32 := gpRdataPort.rd
def gpBusy   : Expr 1  := gpBusyPort.rd
def cmdValid : Expr 1  := cmdValidPort.rd
def cmdIdx   : Expr 7  := cmdIdxPort.rd
def cmdData  : Expr 32 := cmdDataPort.rd

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
def resKillPort  : Reg 1 := ⟨"res_kill"⟩
def doorbellPort : Reg 1 := ⟨"doorbell"⟩
def resKill  : Expr 1  := resKillPort.rd
def doorbell : Expr 1  := doorbellPort.rd

/-! ### EXT-4 — the park/wake directory (`EXTEND_SPEC.md` increment 4)

The current NT=32 implementation uses `wakeAllApply`: any local `FUTEX_WAKE`
or doorbell promotes every `tstate == FUTEX` slot. Spurious wakeups are
spec-legal and recheck the waited-on word. A keyed 64-bit comparator bank does
not fit alongside 32 thread slots on the target, so `doorbell_key` and
`wake_key` are informational cross-core wires and do not select wakees. -/
def doorbellKeyPort : Reg 64 := ⟨"doorbell_key"⟩
def holdPort        : Reg 1  := ⟨"hold"⟩
def doorbell_key : Expr 64 := doorbellKeyPort.rd
def hold     : Expr 1  := holdPort.rd

/-- `sc_fail` — the arbiter's verdict on a *global* `SC`, valid on the cycle
it completes the store-conditional (`m_done` while `sc_pending`). See
`HpArbiter` and DUAL_SPEC "Deviations": the reservation has to be validated
at the serialization point, not two cycles earlier in `S_EX`. The tag
registers `lr_req`/`sc_req` (pulses beside `core_rd`/`core_wr`) tell the
arbiter which read takes a reservation and which write is conditional. -/
def scFailPort : Reg 1 := ⟨"sc_fail"⟩
def scFail   : Expr 1  := scFailPort.rd

/-- `wake_out` pulses for one cycle when `FUTEX_WAKE` (S_EX, op 0xcc)
executes, regardless of local matches. In the dual SoC it is wired straight
into the *other* core's `doorbell` input — a register-to-input connection,
i.e. already a full register stage, no combinational cross-core path. -/
def wakeOutReg : Reg 1 := ⟨"wake_out"⟩
def wake_out : Expr 1  := wakeOutReg.rd

/-- EXT-4. The key `wake_out` is pulsing for, captured on the pulse cycle and
held otherwise; wired to the other core's `doorbell_key` in the dual SoC —
register output to input, so still no combinational cross-core path. -/
def wakeKeyReg : Reg 64 := ⟨"wake_key"⟩
def wake_key : Expr 64 := wakeKeyReg.rd

/-! ## Scalar register shorthands -/

def curReg : Reg 5 := ⟨"cur"⟩
def cur : Expr 5 := curReg.rd
def pcReg : Reg 64 := ⟨"pc"⟩
def pc : Expr 64 := pcReg.rd
def retireReg : Reg 32 := ⟨"retire"⟩
def retire : Expr 32 := retireReg.rd
def running : Expr 1 := runningReg.rd
def halted : Expr 1 := haltedReg.rd
def stReg : Reg 5 := ⟨"st"⟩
def st : Expr 5 := stReg.rd
def irReg : Reg 64 := ⟨"ir"⟩
def ir : Expr 64 := irReg.rd
def aReg : Reg 64 := ⟨"a"⟩
def a : Expr 64 := aReg.rd
def bReg : Reg 64 := ⟨"b"⟩
def b : Expr 64 := bReg.rd
def rdvalReg : Reg 64 := ⟨"rdval"⟩
def rdval : Expr 64 := rdvalReg.rd
/-! ### EXT-9 — the instruction cache (`EXTEND_SPEC.md`)

32 KB, direct-mapped, 1-word (8 B) lines: 4096 lines indexed by
`ddrPc[14:3]`, tag `{valid, ddrPc[31:15]}` packed into 18 bits. Stage 1
deliberately keeps the AXI side untouched — a miss is exactly today's
single-beat read — so the only new hardware is a compare, a mux and two
banks, and the fetch path gains one state.

Both banks are D19 sync-read: `S_F0` writes the two latch registers below
from a bare `memRead`, and `S_IC` consumes them the next cycle. That is
what makes them block RAM rather than 4096-deep read muxes (the D38/CE9
lesson, where the difference was 14x). -/
def icTagQReg : Reg 42 := ⟨"ic_tag_q"⟩
def ic_tag_q : Expr 42 := icTagQReg.rd
/-! ### EXT-9b — invalidation in O(1), not O(cache)

A virtually-tagged cache must be emptied when the mapping that gave its
lines meaning changes. The obvious implementation -- walk the tag bank and
clear it -- is **the wrong algorithm**: 4096 stalled cycles per map change,
cost proportional to the cache, paid by an OS every `mmap`/`map.protect`.
Growing the cache would make invalidation slower, which is backwards.

So lines carry a **generation** and the design keeps a global `ic_gen`. A
line is live only if its generation is the current one, and invalidating
everything is `ic_gen := ic_gen + 1` -- one cycle, no stall, independent of
cache size. This is the same primitive the spec uses for exactly this
problem (§3 epochs, "stale fails forever"), applied locally.

The honest part is the wrap: a 16-bit generation returns to a value some
line still carries after 65 536 invalidations, and that line would falsely
hit. Rather than assert it cannot happen, the wrap **triggers the sweep** --
so the sweep still exists, is still the thing that makes the design correct
rather than probable, and runs once per 65 536 invalidations instead of once
per one. Saturation handled by a fallback rather than by an assumption is
the same shape as the epoch engine's T-E2, where saturation is a defined
terminal state instead of an unstated hope. -/
/-! ### §17 — the gate table lives in memory, not in registers

`gate_ent`/`gate_dom` were 16-entry banks the HOST wrote over BSCAN
(`cmd 61`/`cmd 62`). That made the authority demo a demonstration that the
mechanism exists, not that the machine reads the architecture's own
structures. §17.1b puts the gate's facts in memory; this walks them.

An entry is 16 bytes at `gate_tbl_base + (index << 4)`:

    +0  entry PC   (64)
    +8  target domain in [7:0]   (the rest reserved zero)

`gate_tbl_base` is loaded once (`cmd 74`), the way a root pointer is: the
host says where the table is, and thereafter the machine reads it. That is
the difference the goal names -- the host stops supplying the *contents*. -/
def gateTblBaseReg : Reg 32 := ⟨"gate_tbl_base"⟩
def gate_tbl_base : Expr 32 := gateTblBaseReg.rd
/-- Latched descriptor words, D19 sync-read style (the bus is the source). -/
def gateEntQReg : Reg 64 := ⟨"gate_ent_q"⟩
def gate_ent_q : Expr 64 := gateEntQReg.rd
def gateDomQReg : Reg 8 := ⟨"gate_dom_q"⟩
def gate_dom_q : Expr 8 := gateDomQReg.rd
def icGenReg : Reg 16 := ⟨"ic_gen"⟩
def ic_gen : Expr 16 := icGenReg.rd
def icInvReg : Reg 1 := ⟨"ic_inv"⟩
def ic_inv : Expr 1 := icInvReg.rd
def icCtrReg : Reg 12 := ⟨"ic_ctr"⟩
def ic_ctr : Expr 12 := icCtrReg.rd
def icDataQReg : Reg 64 := ⟨"ic_data_q"⟩
def ic_data_q : Expr 64 := icDataQReg.rd
-- EXT-10 (the D-cache): the latched tag/data words and the allocate flag.
def dcTagQReg : Reg 42 := ⟨"dc_tag_q"⟩
def dc_tag_q : Expr 42 := dcTagQReg.rd
def dcDataQReg : Reg 64 := ⟨"dc_data_q"⟩
def dc_data_q : Expr 64 := dcDataQReg.rd
def dcAllocReg : Reg 1 := ⟨"dc_alloc"⟩
def dc_alloc : Expr 1 := dcAllocReg.rd
def selTReg : Reg 64 := ⟨"sel_t"⟩
def sel_t : Expr 64 := selTReg.rd
def selFReg : Reg 64 := ⟨"sel_f"⟩
def sel_f : Expr 64 := selFReg.rd
def memIsStoreReg : Reg 1 := ⟨"mem_is_store"⟩
def mem_is_store : Expr 1 := memIsStoreReg.rd
def trapActiveReg : Reg 1 := ⟨"trap_active"⟩
def trap_active : Expr 1 := trapActiveReg.rd
def trappedOpReg : Reg 8 := ⟨"trapped_op"⟩
def trapped_op : Expr 8 := trappedOpReg.rd
def coreRdReg : Reg 1 := ⟨"core_rd"⟩
def core_rd : Expr 1 := coreRdReg.rd
def coreWrReg : Reg 1 := ⟨"core_wr"⟩
def core_wr : Expr 1 := coreWrReg.rd
def coreAddrReg : Reg 32 := ⟨"core_addr"⟩
def core_addr : Expr 32 := coreAddrReg.rd
def coreWdataReg : Reg 64 := ⟨"core_wdata"⟩
def core_wdata : Expr 64 := coreWdataReg.rd
def jtagRdReg : Reg 1 := ⟨"jtag_rd"⟩
def jtag_rd : Expr 1 := jtagRdReg.rd
def jtagWrReg : Reg 1 := ⟨"jtag_wr"⟩
def jtag_wr : Expr 1 := jtagWrReg.rd
def jtagWdataReg : Reg 64 := ⟨"jtag_wdata"⟩
def jtag_wdata : Expr 64 := jtagWdataReg.rd
def ddrAddrJReg : Reg 32 := ⟨"ddr_addr_j"⟩
def ddr_addr_j : Expr 32 := ddrAddrJReg.rd
def ddrLoJReg : Reg 32 := ⟨"ddr_lo_j"⟩
def ddr_lo_j : Expr 32 := ddrLoJReg.rd
def ddrRdLReg : Reg 64 := ⟨"ddr_rd_l"⟩
def ddr_rd_l : Expr 64 := ddrRdLReg.rd
def ddrQReg : Reg 64 := ⟨"ddr_q"⟩
def ddr_q : Expr 64 := ddrQReg.rd
def busReqReg : Reg 1 := ⟨"bus_req"⟩
def bus_req : Expr 1 := busReqReg.rd
def gpRdReg : Reg 1 := ⟨"gp_rd"⟩
def gp_rd : Expr 1 := gpRdReg.rd
def gpWrReg : Reg 1 := ⟨"gp_wr"⟩
def gp_wr : Expr 1 := gpWrReg.rd
def gpAddrRReg : Reg 32 := ⟨"gp_addr_r"⟩
def gp_addr_r : Expr 32 := gpAddrRReg.rd
def gpWdataRReg : Reg 32 := ⟨"gp_wdata_r"⟩
def gp_wdata_r : Expr 32 := gpWdataRReg.rd
def dmemWeReg : Reg 1 := ⟨"dmem_we"⟩
def dmem_we : Expr 1 := dmemWeReg.rd
def dmemAReg : Reg 9 := ⟨"dmem_a"⟩
def dmem_a : Expr 9 := dmemAReg.rd
def dmemWdReg : Reg 64 := ⟨"dmem_wd"⟩
def dmem_wd : Expr 64 := dmemWdReg.rd
def dmemRdReg : Reg 64 := ⟨"dmem_rd"⟩
def dmem_rd : Expr 64 := dmemRdReg.rd
def uartWptrReg : Reg 9 := ⟨"uart_wptr"⟩
def uart_wptr : Expr 9 := uartWptrReg.rd
def uartRidxReg : Reg 8 := ⟨"uart_ridx"⟩
def uart_ridx : Expr 8 := uartRidxReg.rd
def uartByteReg : Reg 8 := ⟨"uart_byte"⟩
def uart_byte : Expr 8 := uartByteReg.rd
def rxWptrReg : Reg 9 := ⟨"rx_wptr"⟩
def rx_wptr : Expr 9 := rxWptrReg.rd
def rxRptrReg : Reg 9 := ⟨"rx_rptr"⟩
def rx_rptr : Expr 9 := rxRptrReg.rd
def ldBoffQReg : Reg 3 := ⟨"ld_boff_q"⟩
def ld_boff_q : Expr 3 := ldBoffQReg.rd
def ldOpQReg : Reg 8 := ⟨"ld_op_q"⟩
def ld_op_q : Expr 8 := ldOpQReg.rd
def ldRdQReg : Reg 5 := ⟨"ld_rd_q"⟩
def ld_rd_q : Expr 5 := ldRdQReg.rd
def lrAddrReg : Reg 64 := ⟨"lr_addr"⟩
def lr_addr : Expr 64 := lrAddrReg.rd
def lrValidReg : Reg 1 := ⟨"lr_valid"⟩
def lr_valid : Expr 1 := lrValidReg.rd
/-- A global (DDR) `SC` is outstanding: `S_DSW` must consume `sc_fail`. -/
def lrReqReg      : Reg 1 := ⟨"lr_req"⟩
def scReqReg      : Reg 1 := ⟨"sc_req"⟩
def scPendingReg  : Reg 1 := ⟨"sc_pending"⟩
def sc_pending : Expr 1 := scPendingReg.rd
def futexExpReg : Reg 64 := ⟨"futex_exp"⟩
def futex_exp : Expr 64 := futexExpReg.rd
def futexAddrQReg : Reg 64 := ⟨"futex_addr_q"⟩
def futex_addr_q : Expr 64 := futexAddrQReg.rd
/-! ### EXT-1 — the preemption tick (`EXTEND_SPEC.md` increment 1)

`quantum` is the per-core reload value in **core cycles** and `qctr` the
running thread's remaining quantum. Both are 32 bits (the width of the
BSCAN `cmd_data` that loads them). `quantum = 0` — the reset value — means
**disabled**: `quantumOn` is false, so nothing decrements, nothing reloads
and nothing preempts, and the core is bit-for-bit the cooperative machine
of §63. -/
def quantumReg : Reg 32 := ⟨"quantum"⟩
def quantum : Expr 32 := quantumReg.rd
def qctrReg : Reg 32 := ⟨"qctr"⟩
def qctr : Expr 32 := qctrReg.rd
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
def tdomRd (idx : Expr 5) : Expr 8 := tdomBank.rd idx
/-- EXT-5 (§9): the gate table and the per-thread continuation STACK. `tcont`/
`tcdom` are now `NT*MAXD` deep, indexed by `cur*MAXD + depth` — a bounded
push-down stack so a gate call from inside a gate NESTS (§9) instead of being
refused. The index is 7-bit (NT=32, MAXD=4). -/
def tcontRd (idx : Expr 7) : Expr 64 := tcontBank.rd idx
def tcdomRd (idx : Expr 7) : Expr 8  := tcdomBank.rd idx
/-- Per-thread gate depth (0..MAXD). `gdepth[cur] > 0` ⟺ inside a gate. -/
def gdepthRd (idx : Expr 5) : Expr 3 := gdepthBank.rd idx
/-- Stack address `cur*MAXD + off` for `tcont`/`tcdom` (MAXD=4 ⇒ `cur<<2 | off`).
`off` is the depth slot; the low 2 bits suffice since `off < MAXD = 4`. -/
def gcIdx (off : Expr 3) : Expr 7 :=
  .concat cur (.slice off 0 2)
/-- The stack is full: `gdepth[cur] >= MAXD`. A `gate_call` here is refused
(§9: a clean bounds-checked overflow), not silently overwriting a frame. -/
def gateFull : Expr 1 := .not (.ult (gdepthRd cur) (.lit (BitVec.ofNat 3 MAXD)))
/-- Push slot (current depth) and pop slot (depth-1) as `tcont`/`tcdom` indices. -/
def gPushIdx : Expr 7 := gcIdx (gdepthRd cur)
def gPopIdx  : Expr 7 := gcIdx (.sub (gdepthRd cur) (.lit (BitVec.ofNat 3 1)))
/-! EXT-7: the TLB. Four parallel arrays indexed by the VPN's low 3 bits
(direct-mapped), so a lookup is one read of each plus one comparison. -/
/-- EXT-7: TLB entries. Eight is what the guest's region count needs. -/
def TLBN : Nat := 8

def tlbBaseRegs  : RegArray 32 TLBN := ⟨"tlb_base"⟩
def tlbLimitRegs : RegArray 32 TLBN := ⟨"tlb_limit"⟩
def tlbPhysRegs  : RegArray 32 TLBN := ⟨"tlb_phys"⟩
def tlbDomRegs   : RegArray 8 TLBN  := ⟨"tlb_dom"⟩
def tlbCellRegs  : RegArray 8 TLBN  := ⟨"tlb_cell"⟩

/-! EXT-7 stage B: the TLB holds **VMA ranges**, not fixed pages, and the
lookup is **fully associative** — every entry is compared each cycle, so the
arrays are per-element registers rather than memories (D20: an array read at
every index at once is a register file, not a RAM). -/
def tlbBase  (i : Fin TLBN) : Expr 32 := tlbBaseRegs.rd i
def tlbLimit (i : Fin TLBN) : Expr 32 := tlbLimitRegs.rd i
def tlbPhys  (i : Fin TLBN) : Expr 32 := tlbPhysRegs.rd i
def tlbDom   (i : Fin TLBN) : Expr 8  := tlbDomRegs.rd i
def tlbCell  (i : Fin TLBN) : Expr 8  := tlbCellRegs.rd i
/-- EXT-7: the valid bits are a **bitmap register**, not a memory. The §15
shootdown (`cmd 67`) invalidates *every* entry naming the bumped cell, i.e.
several slots in one cycle, and one memory write port cannot do that -- which
is exactly what `Design.emit` refused when this was a memory (D38/CE10). Same
shape as EXT-3's `poison` (and EXT-6's retired `cap_ival`, before §17 moved
the inbox into memory): state written at many indices at once is a register
bitmap. -/
def tlbVldReg : Reg 8 := ⟨"tlb_vld"⟩
def tlb_vld : Expr 8 := tlbVldReg.rd
/-- Valid bit of entry `i` at a *static* index (the lookup is associative). -/
def tlbVldBit (i : Fin TLBN) : Expr 1 :=
  .eq (.slice (.shr tlb_vld (.lit (BitVec.ofNat 8 i.val))) 0 1) (.lit (BitVec.ofNat 1 1))

def tlbVldRd  (i : Expr 3) : Expr 1  :=
  .eq (.slice (.shr tlb_vld (.zext i 8)) 0 1) (.lit (BitVec.ofNat 1 1))

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
def curDomReg : Reg 8 := ⟨"cur_dom"⟩
def cur_dom : Expr 8 := curDomReg.rd
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
def poisonReg : Reg 32 := ⟨"poison"⟩
def poison : Expr 32 := poisonReg.rd
/-! ### EXT-5 — gates (`EXTEND_SPEC.md` increment 5; ISA §9, Law 1)

A gate is the *only* way a thread changes domain. That is the whole point,
and it is what makes EXT-2's tag mean something: after EXT-5 the writers of
`tdom` are exactly the `cmd 13` reset sweep, `CLONE` (which **inherits**, so
it cannot choose), `cmd 58` (host/debug), and gate call/return — which move
a thread only to a domain the host installed in the gate table. **There is
no instruction that lets a thread name a domain and go there.**

The gate descriptor table lives in memory and supplies the entry PC, target
domain, and validity state. A gate call pushes the return point and prior
domain on the caller's bounded continuation stack and sets `in_gate[cur]`; a
gate return pops and restores that frame. Calls fail closed on an invalid
descriptor or full continuation stack.

**Deviation — opcodes.** §9 assigns `gate_call`/`gate_return` to 0xa0/0xa1,
but mini's decoder already uses 0xa0–0xba for ALU-immediate ops, so mini's
map diverges from the ISA in that whole block *before* this increment. Gates
take **0x60/0x61**, which are free in mini. Recorded here rather than
pretending the encodings match. -/
def inGateReg : Reg 32 := ⟨"in_gate"⟩
def in_gate : Expr 32 := inGateReg.rd
/-! ### The fault record (spec 1235f201 conformance)

The mini has no fault vectors; its fault story is EXT-3 fail-stop. An
architectural fault therefore poisons the offending slot in-core, stops at
the instruction boundary, and records what/where/who. The faulting instruction
does not retire and `pc` remains at it.

Causes: 1 = `GATE_RETURN` with no continuation frame; 2 = illegal opcode 0. -/
def FAULT_GRET_EMPTY : Nat := 1
def FAULT_ILLEGAL_OP0 : Nat := 2
def fault_cause : Expr 8  := faultCauseReg.rd
def fault_pc    : Expr 64 := faultPcReg.rd
def fault_cur   : Expr 5  := faultCurReg.rd
-- Seam probe: bit i set when slot i took a HWTRAP while in a gate since its
-- the first no-op GATE_RETURN -- answers "was the failing slot resumed from a
-- trap mid-gate?" (the trap-server↔fabric seam hypothesis) in one readback.
/-- Bit `cur` of `in_gate`: this thread is inside a gate. -/
def curInGate : Expr 1 :=
  .eq (.slice (.shr in_gate (.zext cur 32)) 0 1) (.lit (BitVec.ofNat 1 1))

/-- Retired at §17. `cmd 61`/`cmd 62` used to poke the gate banks the host
owned; the descriptor now lives in guest memory and the machine walks it,
so the numbers are reserved and the banks are gone. -/
def CMD_GATE_ENT : Nat := 61
def CMD_GATE_DOM : Nat := 62

/-! ### EXT-6 — cross-domain capability transfer (`EXTEND_SPEC.md` #6; §10.2)

A capability handle moves between domains through a **per-domain inbox**.
Since §17 the inbox lives in **guest memory**, not in a core bank: entry `d`
is 16 bytes at `cap_tbl_base + (d << 4)` —

    +0  handle (64)
    +8  flags: bit 0 = occupied, bit 8 = valid (rest reserved zero)

`cap_tbl_base` is a root pointer the host installs once (`cmd 75`), the
same move as the gate table's `cmd 74`: the host says where the table is
and thereafter the machine reads and writes the *entries* itself. The old
`cap_ibox` bank and `cap_ival` bitmap — state only the host could audit —
are gone; a send is a flags-read, a handle-write and a flags-write on the
bus, a receive is a flags-read, a handle-read and a flags-write.

**The re-keying is structural, not a check.** `CAP_SEND` writes the entry
of the domain it names; `CAP_RECV` reads the entry of **`domCur`** — the
receiver's *own* domain, which is not an operand and cannot be forged,
because `domCur` is `tdom[cur]` and EXT-5 made a gate the only way that
changes. A domain-5 thread executing `CAP_RECV` walks entry 5 and gets
nothing; there is no encoding of `CAP_RECV` that reaches entry 3.

**§17 fail-closed, like the gate walk.** Bit 8 of the flags word is
`valid`. An entry that reads back zeros — absent table, revoked slot —
refuses both send and receive (`rd = -1`, no state change). Revoking a
domain's inbox is therefore zeroing 8 bytes of memory, no command, no host.

**Deviation — one slot per domain, not a queue.** `CAP_SEND` to an occupied
entry is refused (`rd = -1`) rather than queueing. One slot proves the
transfer and the mediation; depth is a layout change now, not a redesign.

**Deviation — no MAC re-computation.** CapWalk's engine authenticates a
handle with an on-chip key over `E(slot)`; a full transfer would re-key the
MAC to the receiving domain. Mini's entry carries the handle bits only, and
the domain binding is the *index*. Recorded as the gap between this and
§10.2: the mediation is real, the cryptographic re-key is not implemented.

**Deviation — the walk is not atomic across cores.** A send is three bus
transactions; the HP arbiter interleaves per-transaction, so two cores
racing the same entry could both observe it free. The selftests are
single-core; the cross-core story arrives with the D-cache's rung-5
invalidation work, and this note is here so the code does not imply
otherwise. -/
def capTblBaseReg : Reg 32 := ⟨"cap_tbl_base"⟩
def cap_tbl_base : Expr 32 := capTblBaseReg.rd
/-- Latched flags word of the entry being walked (D19 sync-read style). -/
def capFlQReg : Reg 64 := ⟨"cap_fl_q"⟩
def cap_fl_q : Expr 64 := capFlQReg.rd
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
def mmuEnReg : Reg 1 := ⟨"mmu_en"⟩
def mmu_en : Expr 1 := mmuEnReg.rd
def tlbSelReg : Reg 3 := ⟨"tlb_sel"⟩
def tlb_sel : Expr 3 := tlbSelReg.rd
def CMD_MMU_EN   : Nat := 63
def CMD_TLB_SEL  : Nat := 64
def CMD_TLB_VPN  : Nat := 65
def CMD_TLB_PPN  : Nat := 66
/-- `cmd 67` = the §15 `map.protect`/`munmap` shootdown: invalidate every
TLB entry whose recorded cell equals `cmd_data[7:0]`. -/
def CMD_TLB_PHYS : Nat := 68
/-- EXT-8: select which of the 16 commit-trace ring entries the readback
outputs expose. Host-only; nothing in the core reads the ring. -/
def CMD_TRACE_SEL : Nat := 69
/-- **§17**: where the gate table lives in guest memory. The host sets this
once, like a root pointer; the machine reads the entries. -/
def CMD_GATE_TBL : Nat := 74
/-- **§17**: where the capability-inbox table lives in guest memory. Same
root-pointer discipline as `cmd 74`. -/
def CMD_CAP_TBL : Nat := 75
def CMD_MAP_PROTECT : Nat := 67

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

def sleepScanReg : Reg 5 := ⟨"sleep_scan"⟩
def sleep_scan : Expr 5 := sleepScanReg.rd
def nextReadyReg : Reg 5 := ⟨"next_ready"⟩
def next_ready : Expr 5 := nextReadyReg.rd
def freeSlotReg : Reg 5 := ⟨"free_slot"⟩
def free_slot : Expr 5 := freeSlotReg.rd
def hasFreeReg : Reg 1 := ⟨"has_free"⟩
def has_free : Expr 1 := hasFreeReg.rd
def cloneDstReg : Reg 5 := ⟨"clone_dst"⟩
def clone_dst : Expr 5 := cloneDstReg.rd
def cloneTidReg : Reg 5 := ⟨"clone_tid"⟩
def clone_tid : Expr 5 := cloneTidReg.rd
def mulAccReg : Reg 128 := ⟨"mul_acc"⟩
def mul_acc : Expr 128 := mulAccReg.rd
def mulAwReg : Reg 128 := ⟨"mul_aw"⟩
def mul_aw : Expr 128 := mulAwReg.rd
def mulBReg : Reg 64 := ⟨"mul_b"⟩
def mul_b : Expr 64 := mulBReg.rd
def mulKindReg : Reg 2 := ⟨"mul_kind"⟩
def mul_kind : Expr 2 := mulKindReg.rd
def divRemReg : Reg 64 := ⟨"div_rem"⟩
def div_rem : Expr 64 := divRemReg.rd
def divQuoReg : Reg 64 := ⟨"div_quo"⟩
def div_quo : Expr 64 := divQuoReg.rd
def divDReg : Reg 64 := ⟨"div_d"⟩
def div_d : Expr 64 := divDReg.rd
def divCntReg : Reg 7 := ⟨"div_cnt"⟩
def div_cnt : Expr 7 := divCntReg.rd
def divIsremReg : Reg 1 := ⟨"div_isrem"⟩
def div_isrem : Expr 1 := divIsremReg.rd
def divNegqReg : Reg 1 := ⟨"div_negq"⟩
def div_negq : Expr 1 := divNegqReg.rd
def divNegrReg : Reg 1 := ⟨"div_negr"⟩
def div_negr : Expr 1 := divNegrReg.rd
def zeroingReg : Reg 1 := ⟨"zeroing"⟩
def zeroing : Expr 1 := zeroingReg.rd
def zctrReg : Reg 10 := ⟨"zctr"⟩
def zctr : Expr 10 := zctrReg.rd
def regSelReg : Reg 5 := ⟨"reg_sel"⟩
def reg_sel : Expr 5 := regSelReg.rd
def regWselReg : Reg 5 := ⟨"reg_wsel"⟩
def reg_wsel : Expr 5 := regWselReg.rd
def regWloReg : Reg 32 := ⟨"reg_wlo"⟩
def reg_wlo : Expr 32 := regWloReg.rd
def dmemAddrJReg : Reg 32 := ⟨"dmem_addr_j"⟩
def dmem_addr_j : Expr 32 := dmemAddrJReg.rd
def dmemLoJReg : Reg 32 := ⟨"dmem_lo_j"⟩
def dmem_lo_j : Expr 32 := dmemLoJReg.rd
def regRdReg : Reg 64 := ⟨"reg_rd"⟩
def reg_rd : Expr 64 := regRdReg.rd
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
cycle-by-cycle value except for the explicit `cmd 13` reset sweep (D20.3).
µVerilog's async read is distributed RAM, which has no
cross-port collision hazard: the write lands on the clock edge, the read
sees the old contents, exactly as `Design.cycle` says. -/

def tstateRegs : RegArray 2 NT := ⟨"tstate"⟩

def tstate  (i : Fin NT) : Expr 2  := tstateRegs.rd i

/-- `tpc[idx]` — async read of the thread-PC memory. -/
def tpcRd (idx : Expr 5) : Expr 64 := tpcBank.rd idx
/-- `tsleep[idx]` — async read of the sleep-countdown memory. -/
def tsleepRd (idx : Expr 5) : Expr 64 := tsleepBank.rd idx

/-! ## Opcode mnemonics (PLATONIC W1.5)

Opcode constants are the sole source used by dispatch and hand-written test
programs. Renumbering changes the named constant rather than ambiguous data
literals. Names follow the architecture's instruction variants.
-/

/-- An opcode implemented in **no** numbering, for test programs that need a
guaranteed trap. It must stay invalid across a renumbering: `0x7f` was used
for this and is NOT free after the ISA stage-2 assignment, so renumbering
turned the trap test into a valid instruction. 0x8c is in the ISA's reserved
"memory growth" range and is unoccupied before and after. -/
def OP_INVALID : Nat := 0x0f

def OP_NOP : Nat := 0xff
def OP_MOV : Nat := 0xfe
def OP_LIU : Nat := 0x52
def OP_SLEEP : Nat := 0xfd
def OP_LD_S : Nat := 0x72
def OP_ADD : Nat := 0x10
def OP_SUB : Nat := 0x11
def OP_MUL : Nat := 0x12
def OP_DIV : Nat := 0x15
def OP_AND : Nat := 0x19
def OP_OR : Nat := 0x1a
def OP_XOR : Nat := 0x1b
def OP_SREM : Nat := 0x17
def OP_LSL : Nat := 0x20
def OP_LSR : Nat := 0x21
def OP_ASR : Nat := 0x22
def OP_SLT : Nat := 0x25
def OP_SLTI : Nat := 0x50
def OP_NOT : Nat := 0x1f
def OP_JMP : Nat := 0x60
def OP_BEQ : Nat := 0x63
def OP_BNE : Nat := 0x64
def OP_BLT : Nat := 0x65
def OP_BGE : Nat := 0x66
def OP_BLTU : Nat := 0x67
def OP_SLTU : Nat := 0x26
def OP_JAL : Nat := 0x61
def OP_JALR : Nat := 0x62
def OP_LD : Nat := 0x76
def OP_LD_31 : Nat := 0x75
def OP_LD_32 : Nat := 0x71
def OP_ST : Nat := 0x7a
def OP_ST_34 : Nat := 0x79
def OP_ST_35 : Nat := 0x77
def OP_LD_36 : Nat := 0x73
def OP_ST_37 : Nat := 0x78
def OP_EXIT : Nat := 0xfc
def OP_THREAD_EXIT : Nat := 0xfb
def OP_MINI_GATE_CALL : Nat := 0xfa
def OP_MINI_GATE_RETURN : Nat := 0xf9
def OP_MINI_CAP_SEND : Nat := 0xf8
def OP_MINI_CAP_RECV : Nat := 0xf7

-- Compatibility aliases, not a second source of opcode truth.
def CAP_SEND_OP : Nat := OP_MINI_CAP_SEND
def CAP_RECV_OP : Nat := OP_MINI_CAP_RECV
def OP_SEL : Nat := 0x27
def OP_SEL_41 : Nat := 0xf6
def OP_SEL_42 : Nat := 0xf5
def OP_SEL_43 : Nat := 0xf4
def OP_SEL_44 : Nat := 0xf3
def OP_SEL_45 : Nat := 0xf2
def OP_LSRI : Nat := 0x4d
def OP_ASRI : Nat := 0x4e
def OP_SLTIU : Nat := 0x51
def OP_GET_PCR : Nat := 0xb7
def OP_CLONE_SPAWN : Nat := 0xf1
def OP_BGEU : Nat := 0x68
def OP_LD_S_70 : Nat := 0x74
def OP_LD_S_72 : Nat := 0x70
def OP_YIELD : Nat := 0x98
def OP_FUTEX_WAIT : Nat := 0x99
def OP_FUTEX_WAKE : Nat := 0x9a
def OP_ADDI : Nat := 0x48
def OP_ANDI : Nat := 0x49
def OP_ORI : Nat := 0x4a
def OP_XORI : Nat := 0x4b
def OP_LSLI : Nat := 0x4c
def OP_UDIV : Nat := 0x16
def OP_UREM : Nat := 0x18
def OP_MULH : Nat := 0x13
def OP_MULHU : Nat := 0x14
def OP_SEXT_B : Nat := 0x38
def OP_SEXT_H : Nat := 0x39
def OP_SEXT_W : Nat := 0x3a
def OP_ZEXT_B : Nat := 0x3b
def OP_ZEXT_H : Nat := 0x3c
def OP_ZEXT_W : Nat := 0x3d
/-- §4 pins `clz(0) = ctz(0) = 64`; the derived Appendix D suite checks both
the opcode's presence and this zero-input corner. -/
def OP_CLZ : Nat := 0x3e
def OP_CTZ : Nat := 0x3f
def OP_ROL : Nat := 0x23
def OP_ROR : Nat := 0x24
def OP_BSWAP16 : Nat := 0x41
def OP_BSWAP32 : Nat := 0x42
def OP_BSWAP64 : Nat := 0x43
def OP_LR_D : Nat := 0x7d
def OP_SC_D : Nat := 0x7e
def OP_LR_D_ACQ : Nat := 0xf0
def OP_SC_D_REL : Nat := 0xef
def OP_LR_D_ACQ_REL : Nat := 0xee
def OP_SC_D_ACQ_REL : Nat := 0xed
def OP_FENCE : Nat := 0x92
def OP_AUIPC : Nat := 0x53
def OP_FENCE_D1 : Nat := 0xec
def OP_FENCE_D2 : Nat := 0x9f
def OP_FENCE_D3 : Nat := 0x9e
def OP_FENCE_D4 : Nat := 0x9d

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

/-! ### Balanced-tree builders — now `Loom/Hw/Trees.lean` (D18)

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
  opAny [OP_LIU,OP_MOV,OP_ADD,OP_SUB,OP_MUL,OP_AND,OP_OR,OP_XOR,OP_NOT,OP_LSL,OP_LSR,OP_ASR,OP_SLT,OP_SLTU,
   OP_ADDI,OP_ANDI,OP_ORI,OP_XORI,OP_LSLI,OP_LSRI,OP_ASRI,OP_SLTI,OP_SLTIU,OP_AUIPC,
   OP_SEXT_B,OP_SEXT_H,OP_SEXT_W,OP_ZEXT_B,OP_ZEXT_H,OP_ZEXT_W,OP_BSWAP16,OP_BSWAP32,OP_BSWAP64,OP_ROL,OP_ROR,OP_CTZ,OP_CLZ]

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

/-- Ordinary low-half multiply is intentionally a direct combinational
operator. High-half variants retain the area-oriented `S_MUL` shift-add path. -/
def mulE : Expr 64 := .mul a b

/-- CTZ: lowest set bit index (64 if a==0). Downward scan, index 0 outermost
— built as a balanced `priTree` (first-match-wins ⇒ lowest set bit still
wins), depth 64 → ~2·log₂64. -/
def ctzE : Expr 64 :=
  priTree ((List.range 64).map (fun i => (.eq (.slice a i 1) (L1 1), L64 i))) (L64 64)

/-- CLZ: leading zero count (64 if a==0). The same scan from the other end --
index 63 outermost, so first-match-wins picks the HIGHEST set bit, and the
result is `63 - that index`. -/
def clzE : Expr 64 :=
  priTree ((List.range 64).map
    (fun i => (.eq (.slice a (63 - i) 1) (L1 1), L64 i))) (L64 64)

/-- The ALU mux chain, balanced. `opIs` guards are mutually exclusive, but
`priTree` preserves first-match-wins regardless, so this is exactly the old
35-deep chain. -/
def aluE : Expr 64 :=
  priTree
  [ (opIs OP_MOV, a)
  , (opIs OP_ADD, .add a b)
  , (opIs OP_SUB, .sub a b)
  , (opIs OP_MUL, mulE)
  , (opIs OP_LIU, .concat (.slice imm_i 0 32) (.slice a 0 32))
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
  , (opIs OP_CLZ, clzE)
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

/-- Selection condition keyed on named opcode constants. The family is not
assumed contiguous and no arithmetic property of opcode numbers is used. -/
def sel_cond : Expr 1 :=
  priTree
  [ (opIs OP_SEL,    .eq a b)
  , (opIs OP_SEL_41, .not (.eq a b))
  , (opIs OP_SEL_42, .slt a b)
  , (opIs OP_SEL_43, .not (.slt a b))
  , (opIs OP_SEL_44, .ult a b) ] (.not (.ult a b))

/-! ### load writeback / store merge -/

def mem_src : Expr 64 := .mux (.eq st (L5 S_L1)) dmem_rd ddr_q
def lw_shift : Expr 64 := .shr mem_src (.shl (.zext ld_boff_q 64) (L64 3))

/-- Load write-back narrows to the declared load width and applies the named
opcode's zero- or sign-extension contract. -/
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

/-- Wrap a thread index into `[0, NT)`. `NT` is a power of two, so the mask
makes the parameterization explicit even when the expression width is wider
than the configured thread table. -/
def tidWrap (x : Expr 5) : Expr 5 := .and x (L5 (NT - 1))

/-- rbm2 = ({ready,ready} >> (cur+1))[63:0] -- the round-robin rotate, done by
duplicating the ready bitmap and shifting.

**Coupling 1.** The duplication offset is `NT`, not 32: the bitmap is live in
bits `0..NT-1`, so a copy at bit 32 leaves `32-NT` zeros between the two and
the scan walks into them instead of wrapping round. -/
def rbm2 : Expr 64 :=
  .shr (.or (.zext readyBm 64) (.shl (.zext readyBm 64) (L64 NT)))
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
  .concat hi lo

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
  .and (.not holdEn) (.and running (.and (.not halted) (.and (.not zeroing) (.not ic_inv))))

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

/-! ### EXT-6 — send/recv predicates (§17: judged on the WALKED flags word).

`capRecvSlot` is `domCur[3:0]` — the receiver's own domain. It is NOT an
operand, which is the whole mediation argument. -/
def capRecvSlot : Expr 4 := .slice domCur 0 4
def capSendSlot : Expr 4 := .slice b 0 4
/-- The entry address of slot `d`: `DATA_BASE + cap_tbl_base + (d << 4)`. -/
def capEntryAddr (d : Expr 4) : Expr 32 :=
  .add (.add (.lit (BitVec.ofNat 32 DATA_BASE)) cap_tbl_base)
       (.shl (.zext d 32) (.lit (BitVec.ofNat 32 4)))
/-- §17 flags-word predicates, on the word the bus returned THIS cycle
(`mRdata`, not a latch — reads are pre-cycle, D9). Bit 8 is `valid`
(fail-closed, like `gateDescValid`), bit 0 is `occupied`. -/
def capFlValid : Expr 1 := .slice mRdata 8 1
def capFlOcc   : Expr 1 := .slice mRdata 0 1
/-- A send lands only on a valid, free entry. -/
def capSendOk : Expr 1 := .and capFlValid (.not capFlOcc)
/-- A receive lands only on a valid, occupied entry. -/
def capRecvOk : Expr 1 := .and capFlValid capFlOcc

/-- **§17 fail-closed.** Bit 8 of the descriptor's second word is `valid`.
A gate id with no descriptor reads back zeros, and zeros must not be an
activation -- without this the machine would enter domain 0 at PC 0, which
is the most privileged thing it can do, on the strength of memory nobody
wrote. Revocation is therefore just zeroing the entry, and it needs no
command and no host. -/
def gateDescValid : Expr 1 := .slice mRdata 8 1

/-- §17 activation validity = the flags word's valid bit AND a sane entry PC
(landed 1235f201: the entry is validated fail-closed at construction; the
mini has no seal step, so the walk is where construction meets the machine).
A misaligned or zero entry never activates -- the call REFUSES and steps
past, exactly like a zeroed descriptor. Before this check a clobbered entry
word (the §73 hammer accident: entry=1) sent fetch to a garbage address and
wedged the memory FSM silently. -/
def gateActValid : Expr 1 :=
  .and gateDescValid
    (.and (.eq (.slice gate_ent_q 0 3) (.lit (BitVec.ofNat 3 0)))
      (.not (.eq gate_ent_q (L64 0))))

/-- **§17: the activation commits when the WALK completes, not at S_EX.**
The descriptor is not known until both words are back, so every funnel that
records the activation (`in_gate`, `tdom`, `tcont`, `tcdom`) fires here --
in `S_GC1`, on `m_done` -- rather than in the execute cycle. Committing
early would install a domain read from a bank that no longer exists.
`pc8` is still the right saved continuation: `pc` has not advanced, because
the gate arm never ran `stepPc`. -/
def gateCall : Expr 1 :=
  .and fsmEn (.and (.eq st (L5 S_GC1)) (.and mDone gateActValid))

/-! ### §9.2 the gate return sentinel (spec aebacd95)

A crossing is a call to BOTH sides. `gate_call` installs a reserved
non-canonical address in `ra` (the mini's `rfTriples` gate-call entry), and
**fetching that address executes `gate_return`** -- so a handler is an
ordinary function ending in an ordinary `ret`, with no veneer and no gate
epilogue in the compiler. Three properties, all inherited from the spec:

* **Trigger, not target.** The return still resolves through the machine's
  own continuation stack (`tcont`/`gdepth` at `gPopIdx`) -- never from `ra`.
  A handler that overwrites `ra` can only run more of its own code or
  trigger the legitimate return; it cannot redirect it.
* **Reserved non-canonical.** `0xFFFF_FFFF_FFFF_FFF8` is outside any legal
  code address and 8-aligned, so it is recognized on the fetch path ahead of
  both the misalignment and the ordinary fetch-fault arms.
* **Fail-closed by composition.** With no frame open it takes the
  empty-continuation-stack fault (`FAULT_GRET_EMPTY`) that landed in
  1235f201 -- guarded by an existing guarantee, not by obscurity.

Recognized in `S_F0` *before* any fetch is issued, after the same
`bus_req`/poison/preempt guards that arm takes, so the funnels below and the
FSM arm agree cycle-for-cycle. It retires no instruction: nothing was
fetched, and the `ret` that jumped here already retired. -/
/-- §13.1 conditions, as the negative 64-bit values a refusal reports in the
status register (`-COND` = two's complement of the catalog number). -/
def COND_MALFORMED : Nat := 0xFFFFFFFFFFFFFFFC   -- -4
def COND_BUSY      : Nat := 0xFFFFFFFFFFFFFFF2   -- -14

/-- §9.2 gate return sentinel -- **architecturally pinned** (ISA d3344899,
Appendix B 25): top-of-64-bit so it is non-canonical on every machine, and
8-aligned so it never first trips the fetch-misalignment fault. An
implementation may not choose its own: an `ra`-inspecting unwinder or crash
dumper hard-codes this value. -/
def GATE_RET_SENTINEL : Nat := 0xFFFFFFFFFFFFFFF8

/-- The sentinel's own FSM state. `S_F0` recognizes the address (one 64-bit
compare) and hands off here; the return work and every funnel that records it
then key on `st = S_GRET` alone.

Historical note, kept because it explains the shape: this started as a
workaround. Folding the `S_F0` guards (`bus_req`/poison/**`preemptFire`**)
into the funnel condition duplicated `preemptFire`'s NT-wide priority tree
into five funnels and made cycle evaluation explode -- the selftests appeared
to hang. Loom's certified shared-DAG evaluation has since made that cost
disappear (this suite went from hours to 39 s), so the state is no longer
*required* for tractability. It stays because it is the clearer design
anyway: the sentinel is a distinct machine event, and a funnel that says
"we are returning through the sentinel" reads better than one that restates
the fetch guards. -/
def S_GRET : Nat := 29

def sentinelPc : Expr 1 := .eq pc (L64 GATE_RET_SENTINEL)

/-- A gate call refused because the continuation stack is FULL. This refuses
at the instruction (it never enters the descriptor walk), so it needs its own
status arm: ISA d3344899 -- "there is no refusal that reports nothing", and
`-BUSY` specifically means genuine exhaustion. -/
def gateFullRefused : Expr 1 := exG (.and (opIs OP_MINI_GATE_CALL) gateFull)

/-- A gate call whose descriptor does not admit the activation (invalid bit,
or the misaligned/zero entry PC `gateActValid` rejects). Fail-closed: the
instruction steps past and the §9.2 status register reports `-MALFORMED`. -/
def gateRefused : Expr 1 :=
  .and fsmEn (.and (.eq st (L5 S_GC1)) (.and mDone (.not gateActValid)))

def sentinelFetch : Expr 1 := .and fsmEn (.eq st (L5 S_GRET))

/-- The gate-return EVENT: the explicit opcode, or a sentinel fetch. -/
def gateRetEvent : Expr 1 := .or (exG (opIs OP_MINI_GATE_RETURN)) sentinelFetch
/-- ...and the committing return: an event with a frame actually open. -/
def gateRet  : Expr 1 := .and gateRetEvent curInGate

/-- Funnel triples. -/

def rfTriples : List (Expr 1 × Expr 10 × Expr 64) :=
  -- 1. zeroing
  [ (zeroing, .zext zctr 10, L64 0)
  -- 2. cmd 52 (wins over zeroing)
  , (.and cmdValid (.and (.eq cmdIdx (L7 52)) (.not (.eq reg_wsel (L5 0)))),
       cat55 cur reg_wsel, .concat cmdData reg_wlo)
  -- 3. FSM writes (mutually exclusive)
  -- §9.2: the activation installs the return sentinel in `ra` (r1). This is
  -- what makes the handler an ordinary function -- its `ret` jumps here and
  -- the fetch path turns that into the crossing return.
  , (gateCall, cat55 cur (L5 1), L64 GATE_RET_SENTINEL)
  -- §9.2 the two-result reply: the VALUE is whatever the handler left in
  -- `call_rd` (psABI pins r2 = the ordinary C return register, so the mini
  -- needs no write for it), and the STATUS is the architecturally fixed r3 --
  -- 0 on a real return, all-ones on a refused activation. Before the
  -- sentinel the reply rode r11 by veneer convention; that mini-lore is gone.
  , (gateRet, cat55 cur (L5 3), L64 0)
  -- ISA d3344899: EVERY pre-activation refusal reports its §13.1 condition in
  -- r3, with the value register left unchanged. A descriptor that does not
  -- admit the call (invalid bit, or an entry PC the machine will not accept)
  -- is `-MALFORMED`; a full continuation stack is genuine exhaustion,
  -- `-BUSY`.
  , (gateRefused, cat55 cur (L5 3), L64 COND_MALFORMED)
  , (gateFullRefused, cat55 cur (L5 3), L64 COND_BUSY)
  -- S_EX is_sel
  , (exG (.and is_sel (.not (.eq rdf (L5 0)))), cat55 cur rdf, .mux sel_cond sel_t sel_f)
  -- EXT-6 (§17): CAP_SEND result, judged in S_CS0 on the walked flags word
  -- -- 0 when the entry is valid and free (the writes that follow cannot
  -- refuse), all-ones otherwise. Fail-closed: a zeroed entry refuses.
  , (.and fsmEn (.and (.eq st (L5 S_CS0)) (.and mDone (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, .mux capSendOk (L64 0) (L64 0xFFFFFFFFFFFFFFFF))
  -- EXT-6 (§17): CAP_RECV refusal, judged in S_CR0 -- all-ones when this
  -- domain's entry is invalid or empty. The entry is `domCur`'s, not an
  -- operand's, so no encoding reaches another domain's inbox.
  , (.and fsmEn (.and (.eq st (L5 S_CR0))
       (.and mDone (.and (.not capRecvOk) (.not (.eq rdf (L5 0)))))),
       cat55 cur rdf, L64 0xFFFFFFFFFFFFFFFF)
  -- EXT-6 (§17): CAP_RECV success -- the handle word the bus returned this
  -- cycle in S_CR1 (`mRdata` directly; the latch would be a cycle late).
  , (.and fsmEn (.and (.eq st (L5 S_CR1)) (.and mDone (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, mRdata)
  -- S_EX GET_PCR Tid (op 0x54, rs1f==2)
  , (exG (.and (opIs OP_GET_PCR) (.and (.eq rs1f (L5 2)) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, .add (.zext cur 64) (L64 1))
  -- S_EX is_alu
  , (exG (.and is_alu (.not (.eq rdf (L5 0)))), cat55 cur rdf, aluE)
  -- §4.1 divide-by-zero, pinned: `div`/`udiv` -> -1 (the same 64-bit pattern
  -- for both), `srem`/`urem` -> the dividend. Written here in S_EX rather
  -- than run through the 64-cycle restoring divider, because with a zero
  -- divisor there is nothing to iterate.
  , (exG (.and is_div (.and (.eq b (L64 0)) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf,
       .mux (.or (opIs OP_SREM) (opIs OP_UREM)) a (L64 0xFFFFFFFFFFFFFFFF))
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
       .or (.zext (rxBank.rd (.slice rx_rptr 0 8)) 64)
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

/-! ### The commit trace ring (EXT-8)

A 16-deep ring of the last committed instructions: `{op[7:0], pc[31:0]}` packed
into one word, and the writeback value in a second. Readable over BSCAN after a
trap or a panic.

This exists because the renumbering's panic arrived 41 550 instructions into a
rump boot, and the only evidence was the panic string. A trace turns that into
"instruction N was `X` at PC `P` and wrote `V`", which a diff against the
emulator's trace localises in one run.

**The CAPTURE is folded into `retireInc` rather than added at the ~20 sites
that retire.** Those sites are exactly the definition of "an instruction committed",
so putting the ring write anywhere else would mean maintaining a second list of
them -- which is the defect class this whole arc has been about. A new
instruction that retires gets traced because it calls `retireInc`, not because
someone remembered.

D38 forbids the obvious implementation. `retireInc` is inlined at every commit
site, so writing the memory there gives `trace_pc` ~35 syntactic write sites all
on port 0 -- and a bank with more than one write port does not fit block RAM
(CapWalk CE10 measured 14x the LUTs for exactly that). The emitter refuses it,
and it is right to: two writes to one port in one cycle are not what the
hardware does.

So `retireInc` only CAPTURES, into ordinary scalar registers where D9's
last-write-wins is well defined, and one rule (`traceRule`) drains them into the
memory at a SINGLE write site. The entry lands one cycle after the retire, which
changes nothing about its contents -- the payload was latched at the right
moment.

D9 gives the read-before-write semantics that make this correct: `pc` here reads
the PRE-cycle value, so the entry records the PC of the instruction that just
retired, not the one about to be fetched, even though `stepPc` writes `pc` in
the same `.seq`. -/
def TRACE_AW : Nat := 4

def traceWpReg   : Reg 4  := ⟨"trace_wp"⟩
def traceSelReg  : Reg 4  := ⟨"trace_sel"⟩
def traceHitReg  : Reg 1  := ⟨"trace_hit"⟩
def traceInPcReg : Reg 64 := ⟨"trace_in_pc"⟩
def traceInWbReg : Reg 64 := ⟨"trace_in_wb"⟩
def trace_wp : Expr 4 := traceWpReg.rd
def trace_sel : Expr 4 := traceSelReg.rd
def trace_hit : Expr 1 := traceHitReg.rd
def trace_in_pc : Expr 64 := traceInPcReg.rd
def trace_in_wb : Expr 64 := traceInWbReg.rd
def L4 (n : Nat) : Expr 4 := .lit (BitVec.ofNat 4 n)

/-- `{op[7:0], 24'b0, pc[31:0]}` -- one word, so the ring costs two memories
rather than three and the reader gets the opcode and the PC together. -/
def traceWord : Expr 64 :=
  .or (.shl (.zext op 64) (L64 56)) (.zext (.slice pc 0 32) 64)

def retireInc : Act :=
  .seq (retireReg.set (.add retire (.lit (BitVec.ofNat 32 1)))) <|
  .seq (traceHitReg.set (L1 1)) <|
  .seq (traceInPcReg.set traceWord)
       (traceInWbReg.set (.mux rfWeE rfWdE (L64 0)))

/-! ## Rules -/

/-- (1) registered priority encoders (separate always block). -/
def encRule : Rule :=
  -- **Coupling 2.** `cur + 1 + nr_off` is an index into the rotated window and
  -- must come back mod `NT`. At `NT = 32` the 5-bit add did that for free.
  ⟨"enc", .seq (nextReadyReg.set (.mux nr_any (tidWrap (.add (.add cur (L5 1)) nr_off)) cur))
    (.seq (freeSlotReg.set fs_off) (hasFreeReg.set hf_c))⟩

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
     .seq (sleepScanReg.set (.add sleep_scan (L5 1)))
      (.seq
        ((List.finRange NT).foldr (fun i acc =>
          .seq (.ite (.and (.eq sleep_scan (L5 i.val)) (.eq (tstate i) (L2 2)))
            (.ite (.not (.ult (L64 1) tsl_s))       -- tsleep[sleep_scan] <= 1
              (tstateRegs.set i (L2 1)) .skip)
            .skip) acc) .skip)
        (.ite (.and scanHit (.ult (L64 1) tsl_s))
          (tsleepBank.write 0 sleep_scan (.sub tsl_s (L64 1))) .skip)))
    .skip⟩

/-- (3) latches: dmem_rd/reg_rd/uart_byte from pre-cycle state, plus the
dmem sync-write block `if (dmem_we) dmem[dmem_a]<=dmem_wd` (pre-cycle regs). -/
def latchRule : Rule :=
  ⟨"latches", [hwstmt| {
    if dmem_we then dmemBank[port 0, dmem_a] <- dmem_wd,
    dmemRdReg <- dmemBank[dmem_a],
    regRdReg <- rfBank[$(cat55 cur reg_sel)],
    uartByteReg <- uartBank[uart_ridx],
    -- EXT-8: registered read sites keep host-visible trace words stable.
    traceRdPcReg <- tracePcBank[trace_sel],
    traceRdWbReg <- traceWbBank[trace_sel]
  }]⟩

/-- EXT-8: the commit-trace ring's single write site.

Reads `trace_hit`/`trace_in_*` PRE-cycle (D9), so it is independent of where
this rule sits in the chain relative to the commit sites that set them. One
`memWrite` per memory, which is what D38 requires and what fits block RAM. -/
def traceRule : Rule :=
  ⟨"trace_ring", [hwstmt|
    if trace_hit then {
      tracePcBank[port 0, trace_wp] <- trace_in_pc,
      traceWbBank[port 0, trace_wp] <- trace_in_wb,
      traceWpReg <- trace_wp + 1
    }]⟩

/-- (4) pulse defaults. -/
def pulseDefaultsRule : Rule :=
  ⟨"pulse_defaults", [hwstmt| {
    dmemWeReg <- 0, coreRdReg <- 0, coreWrReg <- 0,
    jtagWrReg <- 0, jtagRdReg <- 0,
    gpRdReg <- 0, gpWrReg <- 0,
    lrReqReg <- 0, scReqReg <- 0,
    -- `trace_hit` is a pulse; otherwise the ring advances forever.
    traceHitReg <- 0,
    -- `actSeq` historically retained this structural trailing skip.
    skip
  }]⟩

/-- (5) zeroing engine (rf write is in the funnel; here dmem + counters). -/
def zeroingRule : Rule :=
  ⟨"zeroing", .ite zeroing
    (.seq (.ite (.ult zctr (.lit (BitVec.ofNat 10 512)))
            (.seq (dmemWeReg.set (L1 1))
              (.seq (dmemAReg.set (.slice zctr 0 9)) (dmemWdReg.set (L64 0)))) .skip)
      (.ite (.eq zctr (.lit (BitVec.ofNat 10 (32*NT-1))))
        (zeroingReg.set (L1 0))
        (zctrReg.set (.add zctr (.lit (BitVec.ofNat 10 1))))))
    .skip⟩

/-- (6) cmd (wr_pulse) surface — rf write (idx 52) is in the funnel. -/
def cmdRule : Rule :=
  ⟨"cmd", .ite cmdValid cmdBody .skip⟩
where
  ci (n : Nat) : Expr 1 := .eq cmdIdx (L7 n)
  L9 (n : Nat) : Expr 9 := .lit (BitVec.ofNat 9 n)
  L32 (n : Nat) : Expr 32 := .lit (BitVec.ofNat 32 n)
  cmd13reset : Act :=
    .seq (pcReg.set (L64 TEXT_BASE)) <|
    .seq (retireReg.set (L32 0)) <|
    .seq (haltedReg.set (L1 0)) <|
    .seq (runningReg.set (L1 0)) <|
    .seq (stReg.set (L5 S_IDLE)) <|
    .seq (uartWptrReg.set (L9 0)) <|
    .seq (rxRptrReg.set (L9 0)) <|
    .seq (rxWptrReg.set (L9 0)) <|
    .seq (trapActiveReg.set (L1 0)) <|
    .seq (curReg.set (L5 0)) <|
    .seq (lrValidReg.set (L1 0)) <|
    .seq (zeroingReg.set (L1 1)) <|
    -- D20: `tpc` is a memory, so its 32-entry reset is *swept* by the
    -- zeroing engine (`tpcTriples` entry 1) over the first 32 of the 1024
    -- zeroing cycles instead of being written all at once here. Nothing
    -- reads `tpc` while `zeroing` is high (every read sits under `fsmEn`,
    -- which contains `¬zeroing`), so the transient is unobservable and the
    -- post-sweep contents are identical.
    .seq (zctrReg.set (.lit (BitVec.ofNat 10 0)))
      ((List.finRange NT).foldr (fun i acc =>
        .seq (tstateRegs.set i (if i.val = 0 then L2 1 else L2 0)) acc) .skip)
  cmdBody : Act :=
    .seq (.ite (ci 14) (regSelReg.set (.slice cmdData 0 5)) .skip) <|
    .seq (.ite (ci 15) (dmemAddrJReg.set cmdData) .skip) <|
    .seq (.ite (ci 16) (dmemLoJReg.set cmdData) .skip) <|
    .seq (.ite (ci 17)
      (.seq (dmemWeReg.set (L1 1))
        (.seq (dmemAReg.set (.slice dmem_addr_j 0 9))
              (dmemWdReg.set (.concat cmdData dmem_lo_j)))) .skip) <|
    .seq (.ite (ci 18) (uartRidxReg.set (.slice cmdData 0 8)) .skip) <|
    .seq (.ite (ci 19)
      (.seq (rxBank.write 0 (.slice rx_wptr 0 8) (.slice cmdData 0 8))
            (rxWptrReg.set (.add rx_wptr (L9 1)))) .skip) <|
    .seq (.ite (ci 40) (ddrAddrJReg.set cmdData) .skip) <|
    .seq (.ite (ci 41) (ddrLoJReg.set cmdData) .skip) <|
    .seq (.ite (ci 42)
      (.seq (jtagWrReg.set (L1 1))
        (.seq (jtagWdataReg.set (.concat cmdData ddr_lo_j))
              (ddrAddrJReg.set (.add ddr_addr_j (L32 8))))) .skip) <|
    .seq (.ite (ci 43) (jtagRdReg.set (L1 1)) .skip) <|
    -- EXT-8: select a commit-trace ring entry to read back. The ring itself
    -- is host-readable only; nothing in the core reads it, so a wrong select
    -- cannot perturb execution -- which is what makes it safe to leave armed
    -- during a real boot.
    .seq (.ite (ci CMD_TRACE_SEL) (traceSelReg.set (.slice cmdData 0 4)) .skip) <|
    .seq (.ite (ci 50) (regWselReg.set (.slice cmdData 0 5)) .skip) <|
    .seq (.ite (ci 51) (regWloReg.set cmdData) .skip) <|
    .seq (.ite (ci 53) (pcReg.set (.zext cmdData 64)) .skip) <|
    .seq (.ite (.and (ci 54) (.eq (.slice cmdData 0 1) (L1 1)))
      (.seq (trapActiveReg.set (L1 0))
        -- EXT-8: `retireInc`, not a bare retire bump. A host-serviced trap
        -- IS a committed instruction, and routing it here keeps the invariant
        -- "retire incremented <-> a trace entry was pushed" true.
        (.seq retireInc
              (stReg.set (L5 S_F0)))) .skip) <|
    .seq (.ite (ci 55) (busReqReg.set (.slice cmdData 0 1)) .skip) <|
    -- EXT-1: the quantum reload value (0 = preemption disabled). `qctr` is
    -- armed from the same word in `quantumRule`, which owns that register.
    .seq (.ite (ci CMD_QUANTUM) (quantumReg.set cmdData) .skip) <|
    -- EXT-3: the poison bitmap, whole-word (see `CMD_POISON`).
    .seq (.ite (ci CMD_POISON) (poisonReg.set cmdData) .skip) <|
    -- EXT-7: MMU enable and the TLB entry selector.
    .seq (.ite (ci CMD_MMU_EN) (mmuEnReg.set (.slice cmdData 0 1)) .skip) <|
    .seq (.ite (ci CMD_GATE_TBL) (gateTblBaseReg.set cmdData) .skip) <|
    .seq (.ite (ci CMD_CAP_TBL) (capTblBaseReg.set cmdData) .skip) <|
    .seq (.ite (ci CMD_TLB_SEL) (tlbSelReg.set (.slice cmdData 0 3)) .skip) <|
    -- EXT-7 stage B: per-entry VMA fill. `cmd 65` = base + domain,
    -- `cmd 66` = limit (and VALIDATES, so a half-written VMA is never live),
    -- `cmd 68` = physical base + the VMA's epoch cell.
    .seq (actSeq ((List.finRange TLBN).map (fun i =>
          let sel := .eq tlb_sel (.lit (BitVec.ofNat 3 i.val))
          actSeq
          [ .ite (.and (ci CMD_TLB_VPN) sel)
              -- base is cmd_data[23:0]; [31:24] carries the domain, so the
              -- stored base must be MASKED or the range compare sees the
              -- domain byte in the high bits.
              (.seq (tlbBaseRegs.set i (.zext (.slice cmdData 0 24) 32))
                    (tlbDomRegs.set i (.slice cmdData 24 8))) .skip
          , .ite (.and (ci CMD_TLB_PPN) sel)
              (tlbLimitRegs.set i cmdData) .skip
          , .ite (.and (ci CMD_TLB_PHYS) sel)
              -- cmd_data[23:0] is the DELTA (phys - base), computed by the
              -- host; [31:24] carries the VMA's epoch cell.
              (.seq (tlbPhysRegs.set i (.zext (.slice cmdData 0 24) 32))
                    (tlbCellRegs.set i (.slice cmdData 24 8))) .skip ]))) <|
    -- EXT-5: `cmd 62` selects the gate whose entry `cmd 61` then loads.
      (.ite (ci 13)
        (.seq (.ite (.eq (.slice cmdData 0 1) (L1 1)) cmd13reset .skip)
              (.ite (.eq (.slice cmdData 1 1) (L1 1))
                (.seq (runningReg.set (L1 1)) (stReg.set (L5 S_F0))) .skip)) .skip)

/-- (7) ddr_rd_l latch. -/
def ddrRdLRule : Rule :=
  ⟨"ddr_rd_l", .ite (.and mDone (.not hp_core_owns)) (ddrRdLReg.set mRdata) .skip⟩

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
/-- Low 32 bits of the effective address; VMA bounds are 32-bit because the
DDR aperture is. -/
def eaLo (ea : Expr 64) : Expr 32 := .slice ea 0 32

/-- Entry `i` matches: valid, this domain, and `base ≤ ea < limit`. A
**range**, per §15 — the unit the document translates is the VMA. -/
def tlbMatch (i : Fin TLBN) (ea : Expr 64) : Expr 1 :=
  .and (tlbVldBit i)
    (.and (.eq (tlbDom i) domCur)
      (.and (.not (.ult (eaLo ea) (tlbBase i)))
            (.ult (eaLo ea) (tlbLimit i))))

def tlbHit (ea : Expr 64) : Expr 1 :=
  orTree ((List.finRange TLBN).map (fun i => tlbMatch i ea))

/-- Untranslated (bypass) DDR effective address — DATA_BASE + word-aligned
ea, the pre-EXT-7 computation unchanged. -/
def ddrEaRaw (ea : Expr 64) : Expr 32 :=
  .add (.lit (BitVec.ofNat 32 DATA_BASE)) (.shl (.slice ea 3 29 |> fun w => .zext w 32) (.lit (BitVec.ofNat 32 3)))

/-- Translated address. The obvious form is `phys + (ea - base)`, which
costs an adder **and** a subtractor per entry — 8 of each, and it measured
60 528 LUTs (56 %), past this part's practical routing ceiling.

Instead the entry stores the **delta** `phys - base`, computed once by the
host at fill time, and translation is `ea + delta`: one adder per entry, no
subtractors, and the select happens on the delta rather than on a sum. Same
function, and the arithmetic that used to be per-access is now per-map.

`priTree` picks the first match — W3.1 (`Loom/Hw/Trees.lean`) proves that
equals the linear priority chain, so "first match wins" is a theorem. -/
def ddrEaXlat (ea : Expr 64) : Expr 32 :=
  .add (.lit (BitVec.ofNat 32 DATA_BASE))
    (.add (eaLo ea)
      (priTree ((List.finRange TLBN).map (fun i => (tlbMatch i ea, tlbPhys i)))
        (.lit (BitVec.ofNat 32 0))))

def ddrEa (ea : Expr 64) : Expr 32 :=
  .mux mmu_en
    (.mux (tlbHit ea) (ddrEaXlat ea) (.lit (BitVec.ofNat 32 DATA_BASE)))
    (ddrEaRaw ea)
def ddrPc : Expr 32 := .add (.lit (BitVec.ofNat 32 DATA_BASE)) (.slice pc 0 32)

/-! ### EXT-9 cache address decode

`ddrPc` is the physical fetch address (still untranslated in stage 1 — the
whole point of putting the TLB on the miss arm later is that `S_IC`'s hit
path must not grow a translation). -/
def ic_idx : Expr 12 := .slice ddrPc 3 12
def ic_tag : Expr 17 := .slice ddrPc 15 17
/-- A hit is valid ∧ domain match ∧ tag match, read out of the latched word.

**The domain is in the tag** because EXT-9b translates the miss arm: a line
now means "this virtual address, *under this domain's map*". Two domains can
map the same virtual address to different physical text, and the fetch path
cannot re-check that without putting a TLB lookup back on the hit path --
which is the one thing this whole structure exists to avoid. Tagging by
domain makes the aliasing structurally impossible instead of a rule someone
has to remember on every domain switch. -/
def ic_hit : Expr 1 :=
  .and (.eq (.slice ic_tag_q 41 1) (L1 1))
    (.and (.eq (.slice ic_tag_q 25 16) ic_gen)
      (.and (.eq (.slice ic_tag_q 17 8) domCur)
            (.eq (.slice ic_tag_q 0 17) ic_tag)))
/-- The cache-fill tag word: valid, generation, domain, and physical tag. -/
def ic_tag_fill : Expr 42 :=
  .or (.shl (.lit (BitVec.ofNat 42 1)) (.lit (BitVec.ofNat 42 41)))
    (.or (.shl (.zext ic_gen 42) (.lit (BitVec.ofNat 42 25)))
      (.or (.shl (.zext domCur 42) (.lit (BitVec.ofNat 42 17)))
           (.zext ic_tag 42)))


/-! ### EXT-10 — the data cache

Same geometry and same tag word as the I-cache, for the same reasons: the
domain is in the tag because a line means "this address *under this domain's
map*", and the generation field lets a translation change invalidate the
whole bank in O(1) rather than a sweep.

What is different is that data is written. The rungs, in order, are: read
hits (here), write-through with invalidate-on-store (here), and cross-core
invalidation (see the cache contract in `EXTEND_SPEC.md`; the
bank is correct only because a store invalidates the storing core's own copy
and every other core still reads DDR).

The index is computed from the TRANSLATED address, unlike the I-cache's,
whose stage-1 index was physical-by-accident. `S_EX` already translates the
load address once (`sexEa`/`ddrEa`), so this adds no second cone. -/
def dc_ea : Expr 32 := ddrEa mem_ea_l
def dc_idx : Expr 12 := .slice dc_ea 3 12
def dc_tag : Expr 17 := .slice dc_ea 15 17
/-- Index and tag of the address a STORE is about to write, for the
invalidate. Separate from `dc_idx` because the store arm's effective address
is `mem_ea_s`, not `mem_ea_l`. -/
def dc_sidx : Expr 12 := .slice (ddrEa mem_ea_s) 3 12

def dc_hit : Expr 1 :=
  .and (.eq (.slice dc_tag_q 41 1) (L1 1))
    (.and (.eq (.slice dc_tag_q 25 16) ic_gen)
      (.and (.eq (.slice dc_tag_q 17 8) domCur)
            (.eq (.slice dc_tag_q 0 17) dc_tag)))

/-- The tag word written on a fill. The fill happens in `S_DL`, by which time
`mem_ea_l` no longer holds the address, so the fields come from the latched
`dc_tag_q`'s index-mates: `dc_fill_tag` is recomputed from `core_addr`, which
`S_EX` wrote and nothing since has touched. -/
def dc_fill_idx : Expr 12 := .slice core_addr 3 12
def dc_fill_tag : Expr 42 :=
  .or (.shl (.lit (BitVec.ofNat 42 1)) (.lit (BitVec.ofNat 42 41)))
    (.or (.shl (.zext ic_gen 42) (.lit (BitVec.ofNat 42 25)))
      (.or (.shl (.zext domCur 42) (.lit (BitVec.ofNat 42 17)))
           (.zext (.slice core_addr 15 17) 42)))

/-- The ONE effective address S_EX ever translates. LR and SC translate `a`;
FUTEX_WAIT translates its aligned futex word (`rdval & ~7`). Muxing the input
instead of instantiating ddrEa per site keeps S_EX at a single translation
cone: the first futex fix cloned a second one (+1.1k LUTs) and routed Fmax
fell from 27.36 to 23.98 MHz -- under the 25 MHz board clock. The ops are
mutually exclusive in S_EX, so per-site behaviour is unchanged, and yosys
merges the now-identical cones. -/
def sexEa : Expr 64 :=
  .mux (opIs OP_FUTEX_WAIT)
    (.shl (.zext (.slice rdval 3 61) 64) (.lit (BitVec.ofNat 64 3)))
    a

def goF0 : Act := stReg.set (L5 S_F0)

/-- The §9.2 empty-continuation-stack fault, shared by the explicit opcode
and the sentinel fetch: poison the slot (EXT-3 fail-stop), record what/where/
who, retire nothing, leave `pc` at the faulting point. -/
def gretEmptyFault : Act :=
  actSeq [faultCauseReg.set (L8 FAULT_GRET_EMPTY),
          faultPcReg.set pc, faultCurReg.set cur,
          poisonReg.set (.or poison (.shl (L32 1) (.zext cur 32))),
          goF0]
def stepPc : Act := pcReg.set pc8

/-- Cons for an if/else-if chain kept as *data*, so `actPriTree` can
re-associate it into a balanced dispatch instead of a linear one. -/
def gcons (g : Expr 1) (a : Act) (rest : List (Expr 1 × Act)) : List (Expr 1 × Act) :=
  (g, a) :: rest

/-! ### S_EX helpers (dynamic per-thread writes; scheduler switches) -/

/-- `pc <= tpc[idx]`. **D20**: one async memory read instead of a balanced
32-way select over 32 registers. Same function of the same pre-cycle state
(D9: `memRead` evaluates against `σ`). -/
def setPcFromTpc (idx : Expr 5) : Act := pcReg.set (tpcRd idx)
def tstateDynWrite (v : Expr 2) (idx : Expr 5) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (tstateRegs.set i v) .skip) acc) .skip
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

/-- EXT-4 reverted to fit NT=32: the wake is now UNKEYED.

`tfutex` (the per-slot 64-bit wait key) and the NT-parallel comparator bank it
fed were the design's one 64-bit-wide NT-scaling structure — deleting them is
what brings 32 thread slots under the xc7z020 routing ceiling (NT=16 fit at
44% but could not boot NetBSD; keyed NT=32 did not route). A futex wake may be
*spurious* but never *missed*: every waiter re-checks its condition after
waking and re-parks if unsatisfied, so waking EVERY parked (FUTEX) thread on
any wake is spec-legal. The cost is a thundering herd on each wake — a
performance trade, not a correctness one — which the boot (not
wake-frequency-bound) absorbs. So the wake is one combinational, tstate-only
promote: on `wakeEn` (local `FUTEX_WAKE` retiring OR the cross-core doorbell),
every slot with `tstate==FUTEX(3)` goes READY(1). The count limit `a` and the
key are ignored (waking ≥a threads, or threads on a ≠key address, is a
spurious wake = legal). The path into `tstate` is a 2-bit test, so unlike the
old 64-bit-eq→popcount bank it needs no registering. See PLATONIC "the NT=32
fit" and EXTEND_SPEC EXT-4. -/
def wakeAllApply : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.and wakeEn (.eq (tstate i) (L2 3)))
           (tstateRegs.set i (L2 1)) .skip) acc) .skip

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
  (.ite bus_req (stReg.set (L5 S_PAUSE))
    -- EXT-3: fail-stop, checked BEFORE the preemption point and before the
    -- fetch. Nothing has been fetched at `S_F0` and `bus_req` is already
    -- excluded above, so the core stops with no transaction outstanding
    -- and `pc` still addressing the un-executed instruction.
    (.ite curPoisoned (runningReg.set (L1 0))
    (.ite preemptFire
      (.seq (curReg.set next_ready) (setPcFromTpc next_ready))
      -- EXT-9: look the line up instead of issuing a fetch. The two writes
      -- below are the D19 sync-read sites for `ic_tag`/`ic_data`; `S_IC`
      -- consumes them next cycle. A miss from there issues exactly the
      -- transaction this arm used to issue, one cycle later.
      -- §9.2 sentinel: `ra` has been fetched. No memory fetch is issued;
      -- `S_GRET` does the return next cycle (see `S_GRET`).
      (.ite sentinelPc (stReg.set (L5 S_GRET))
      (.seq (icTagQReg.set (icTagBank.rd ic_idx))
        (.seq (icDataQReg.set (icDataBank.rd ic_idx))
          (stReg.set (L5 S_IC))))))))

/-- `S_GRET`: the sentinel was fetched -- execute the §9.2 gate return. The
caller frame comes from the continuation stack (`tcont`/`tcdom` at
`gPopIdx`), never from `ra`: the sentinel is a trigger, not a target. With no
frame open it is the empty-stack fault. Retires nothing -- no instruction was
fetched, and the `ret` that jumped here already retired. -/
def s_gret : Expr 1 × Act := stArm S_GRET
  (.ite curInGate (.seq (pcReg.set (tcontRd gPopIdx)) goF0) gretEmptyFault)

/-- `S_GC0`: the entry PC has arrived; latch it and ask for the domain word
at +8. -/
def s_gc0 : Expr 1 × Act := stArm S_GC0
  (.ite mDone
    (.seq (gateEntQReg.set mRdata)
      (.seq (coreAddrReg.set (.add core_addr (.lit (BitVec.ofNat 32 8))))
        (.seq (coreRdReg.set (L1 1)) (stReg.set (L5 S_GC1)))))
    .skip)

/-- `S_GC1`: the domain word has arrived. Latch it and commit the
activation -- `pc` to the descriptor's entry, and the funnels (`tdom`,
`tcont`, `tcdom`, `in_gate`) fire on `gateCommit` this cycle. -/
def s_gc1 : Expr 1 × Act := stArm S_GC1
  (.ite mDone
    (.seq (gateDomQReg.set (.slice mRdata 0 8))
      (.seq (.ite gateActValid (pcReg.set gate_ent_q) stepPc)
        (.seq retireInc goF0)))
    .skip)

/-- **§17 `S_CS0`**: the target entry's flags word has arrived. A valid,
free entry commits the send -- latch the flags and issue the handle write
at `+0` (the address walked here is `+8`). Anything else refuses: the rd
funnel wrote all-ones this cycle, and the instruction just steps past. -/
def s_cs0 : Expr 1 × Act := stArm S_CS0
  (.ite mDone
    (.ite capSendOk
      (actSeq [capFlQReg.set mRdata,
               coreAddrReg.set (.sub core_addr (.lit (BitVec.ofNat 32 8))),
               coreWdataReg.set a,
               coreWrReg.set (L1 1), stReg.set (L5 S_CS1)])
      (actSeq [stepPc, retireInc, goF0]))
    .skip)

/-- **§17 `S_CS1`**: the handle write completed; issue the flags write with
`occupied` set. The store completes through `S_DSW` (which owns the final
step/retire); `sc_pending` is cleared the way the ordinary DDR-store arm
clears it, so the SC-verdict funnel cannot misread this store. -/
def s_cs1 : Expr 1 × Act := stArm S_CS1
  (.ite mDone
    (actSeq [coreAddrReg.set (.add core_addr (.lit (BitVec.ofNat 32 8))),
             coreWdataReg.set (.or cap_fl_q (L64 1)),
             coreWrReg.set (L1 1), scPendingReg.set (L1 0),
             stReg.set (L5 S_DSW)])
    .skip)

/-- **§17 `S_CR0`**: this domain's flags word has arrived. Valid and
occupied commits the receive -- latch the flags and issue the handle read
at `+0`. Anything else refuses (rd funnel wrote all-ones) and steps past. -/
def s_cr0 : Expr 1 × Act := stArm S_CR0
  (.ite mDone
    (.ite capRecvOk
      (actSeq [capFlQReg.set mRdata,
               coreAddrReg.set (.sub core_addr (.lit (BitVec.ofNat 32 8))),
               coreRdReg.set (L1 1), stReg.set (L5 S_CR1)])
      (actSeq [stepPc, retireInc, goF0]))
    .skip)

/-- **§17 `S_CR1`**: the handle word arrived (`rd` written from `mRdata` in
the funnel this cycle); issue the flags write with `occupied` cleared and
complete through `S_DSW`. -/
def s_cr1 : Expr 1 × Act := stArm S_CR1
  (.ite mDone
    (actSeq [coreAddrReg.set (.add core_addr (.lit (BitVec.ofNat 32 8))),
             coreWdataReg.set (.and cap_fl_q (.not (L64 1))),
             coreWrReg.set (L1 1), scPendingReg.set (L1 0),
             stReg.set (L5 S_DSW)])
    .skip)

def s_pause : Expr 1 × Act := stArm S_PAUSE  (.ite (.not bus_req) goF0 .skip)

def s_fw : Expr 1 × Act := stArm S_FW
  (.ite mDone (.seq (irReg.set mRdata) (stReg.set (L5 S_RD))) .skip)

/-- **EXT-9 `S_IC`**: the tag check, one cycle after `S_F0` latched the
banks. Hit -> `ir` from the latched data word, straight to `S_RD` (a
3-cycle fetch with no bus transaction at all). Miss -> the exact fetch
`S_F0` used to issue; the fill happens in `S_FW` through the funnel. -/
def s_ic : Expr 1 × Act := stArm S_IC
  (.ite ic_hit
    (.seq (irReg.set ic_data_q) (stReg.set (L5 S_RD)))
    -- **EXT-9b: translated fetch.** The miss arm asks the TLB, exactly as
    -- the data path does; the HIT arm above touches no translation at all,
    -- which is the entire reason the cache had to come first. EXTEND_SPEC
    -- recorded the old constraint honestly -- "fetch is untranslated, so
    -- text must stay put" -- and this removes it: with `mmu_en` the whole
    -- address space, text included, is under the VMA.
    --
    -- With `mmu_en = 0`, `ddrEa pc` reduces to `ddrEaRaw pc`, which is
    -- `ddrPc` word-aligned -- so an unmapped machine fetches exactly what it
    -- fetched before.
    (.seq (coreAddrReg.set (ddrEa pc))
      (.seq (coreRdReg.set (L1 1)) (stReg.set (L5 S_FW)))))

/-- `S_RD`: latch the three source operands. **D19 sync-read sites** —
each written value is a bare `memRead` of `rf` (no zero-mux, no shared
address net), so `Design.syncReadOkB "rf"` holds and the compiled
`a <= n_k` / `wire n_k = rf[n_a];` pair is block-RAM shaped.

The `(rsNf == 0) ? 0 : ...` zero-muxes the Verilog original carried are
deleted, not moved: by invariant Z (`Loom/Hw/D19_SPEC.md` — every triple
of `rfTriples` either writes a low-index that is guarded nonzero, or is
the zeroing sweep writing 0) `rf[{t,0}]` is 0 in every reachable state,
so the mux was the identity. Every register keeps its exact cycle-by-cycle
value. -/
def s_rd : Expr 1 × Act := stArm S_RD
  (.seq (aReg.set (rfBank.rd (cat55 cur rs1f)))
    (.seq (bReg.set (rfBank.rd (cat55 cur rs2f)))
      (.seq (rdvalReg.set (rfBank.rd (cat55 cur rdf)))
            (stReg.set (.mux is_sel (L5 S_RD2) (L5 S_EX))))))

/-- `S_RD2`: the two extra operands of a SELECT. Same D19 shape; the
addresses name `rs3f`/`rs4f` directly (they are what `r1a`/`r2a` reduced
to in this state). -/
def s_rd2 : Expr 1 × Act := stArm S_RD2
  (.seq (selTReg.set (rfBank.rd (cat55 cur rs3f)))
    (.seq (selFReg.set (rfBank.rd (cat55 cur rs4f)))
          (stReg.set (L5 S_EX))))

-- S_EX: if-else priority tree mirroring the Verilog (rf writes in the
-- funnel; here: pc/retire/st/scheduler-array/master-handshake side effects).

/-- The S_EX opcode dispatch, kept as an explicit (guard, action) list in
the Verilog's textual if/else-if order. `actPriTree` re-associates it into
a balanced else-if tree: identical first-match-wins behaviour (see
`actPriPair`), but the mux cone every register sees shrinks from ~29
levels to ~5. -/
def s_ex_branches : List (Expr 1 × Act) :=
  -- 0x3a EXIT
  gcons (opIs OP_EXIT) (.seq (haltedReg.set (L1 1)) (.seq (runningReg.set (L1 0)) retireInc)) <|
  -- 0x3b THREAD_EXIT
  gcons (opIs OP_THREAD_EXIT)
    (.seq (tstateDynWrite (L2 0) cur)
      (.seq (.ite (.not (.eq next_ready cur))
              (.seq (curReg.set next_ready) (.seq (setPcFromTpc next_ready) goF0))
              (stReg.set (L5 S_WAIT)))
            retireInc)) <|
  -- 0x00 NOP
  gcons (opIs OP_NOP) (.seq stepPc (.seq retireInc goF0)) <|
  -- fence
  gcons is_fence (.seq stepPc (.seq retireInc goF0)) <|
  -- High-half multiplies retain the area-oriented shift-add implementation;
  -- ordinary MUL is a direct `Expr.mul` ALU operation above.
  gcons is_mulh
    (.seq (mulAccReg.set (.lit (BitVec.ofNat 128 0)))
      (.seq (mulAwReg.set (.zext a 128))
        (.seq (mulBReg.set b)
          (.seq (mulKindReg.set (.mux (opIs OP_MULH) (L2 1) (L2 2))) (stReg.set (L5 S_MUL)))))) <|
  -- div
  gcons is_div
    -- §4.1 makes division and remainder total and non-trapping. SIGFPE is a
    -- personality-level event, not part of these decoded ISA semantics.
    (.ite (.eq b (L64 0))
      (.seq stepPc (.seq retireInc goF0))
      (.seq (divRemReg.set (L64 0))
        (.seq (divQuoReg.set div_a_abs)
          (.seq (divDReg.set div_b_abs)
            (.seq (divCntReg.set (.lit (BitVec.ofNat 7 0)))
              (.seq (divIsremReg.set (.or (opIs OP_SREM) (opIs OP_UREM)))
                (.seq (divNegqReg.set (.and div_sgn (.xor (.slice a 63 1) (.slice b 63 1))))
                  (.seq (divNegrReg.set (.and div_sgn (.slice a 63 1))) (stReg.set (L5 S_DIV)))))))))) <|
  -- sel
  gcons is_sel (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x54 GET_PCR
  gcons (opIs OP_GET_PCR)
    (.ite (.eq rs1f (L5 2)) (.seq stepPc (.seq retireInc goF0))
      (.seq (trapActiveReg.set (L1 1)) (.seq (trappedOpReg.set op) (stReg.set (L5 S_TRAP))))) <|
  -- alu
  gcons is_alu (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x20 J
  gcons (opIs OP_JMP) (.seq (pcReg.set (.add pc (.shl imm_j (L64 3)))) (.seq retireInc goF0)) <|
  -- 0x27 JAL
  gcons (opIs OP_JAL) (.seq (pcReg.set (.add pc (.shl imm_j (L64 3)))) (.seq retireInc goF0)) <|
  -- 0x28 JALR
  gcons (opIs OP_JALR) (.seq (pcReg.set (.add a imm_i)) (.seq retireInc goF0)) <|
  -- branch
  gcons is_branch (.seq (pcReg.set (.mux br_take (.add pc (.shl imm_s (L64 3))) pc8)) (.seq retireInc goF0)) <|
  -- 0x06 YIELD
  gcons (opIs OP_YIELD)
    (.seq (.ite (.eq next_ready cur) stepPc
            (.seq (curReg.set next_ready) (setPcFromTpc next_ready)))
          (.seq retireInc goF0)) <|
  -- 0x07 SLEEP
  gcons (opIs OP_SLEEP)
    (.seq (tstateDynWrite (L2 2) cur)
      (.seq (.ite (.not (.eq next_ready cur))
              (.seq (curReg.set next_ready) (.seq (setPcFromTpc next_ready) goF0))
              (stReg.set (L5 S_WAIT)))
            retireInc)) <|
  -- 0xcb FUTEX_WAIT
  gcons (opIs OP_FUTEX_WAIT)
    -- The futex comparison is an ordinary data access and must pass through
    -- the same translation path as loads and stores.
    (.seq (coreAddrReg.set (ddrEa sexEa))
      (.seq (coreRdReg.set (L1 1))
        (.seq (futexAddrQReg.set rdval) (.seq (futexExpReg.set a) (stReg.set (L5 S_FTX1)))))) <|
  -- 0xcc FUTEX_WAKE (per-element wake; count via matches-before-i < a)
  -- EXT-4: the wake bank moved to `smpRule` (one shared bank); S_EX keeps
  -- only the sequencing half of FUTEX_WAKE.
  gcons (opIs OP_FUTEX_WAKE) (.seq stepPc (.seq retireInc goF0)) <|
  -- EXT-6 (§17): CAP_SEND (a = handle, b = target domain) and CAP_RECV.
  -- Both walk the in-memory entry: issue the flags-word read here, decide
  -- in S_CS0/S_CR0 once the word is back. `rd` is written in the funnels;
  -- pc advances at the end of the walk (S_DSW or the refusal arm), never
  -- here.
  gcons (opIs CAP_SEND_OP)
    (.seq (coreAddrReg.set
            (.add (capEntryAddr capSendSlot) (.lit (BitVec.ofNat 32 8))))
      (.seq (coreRdReg.set (L1 1)) (stReg.set (L5 S_CS0)))) <|
  gcons (opIs CAP_RECV_OP)
    (.seq (coreAddrReg.set
            (.add (capEntryAddr capRecvSlot) (.lit (BitVec.ofNat 32 8))))
      (.seq (coreRdReg.set (L1 1)) (stReg.set (L5 S_CR0)))) <|
  -- EXT-5: 0x60 GATE_CALL. `a` is the gate id. Refused (rd = -1, no state
  -- change) if this thread is already inside a gate -- the continuation is
  -- depth 1. Otherwise: save the return point, mark in-gate, and jump to
  -- the gate's entry in the gate's domain. `tdom`/`tcont`/`tcdom`/`in_gate`
  -- are written in their funnels; this arm owns pc and rd.
  gcons (opIs OP_MINI_GATE_CALL)
    (.ite gateFull
      (.seq (.ite (.not (.eq rdf (L5 0))) .skip .skip)
        (.seq stepPc (.seq retireInc goF0)))
      -- §17: walk the descriptor instead of reading a host-loaded bank.
      -- The address is the table base plus a 16-byte-strided index; the
      -- activation commits in S_GC1, once both words are in.
      (.seq (coreAddrReg.set
              (.add (.add (.lit (BitVec.ofNat 32 DATA_BASE)) gate_tbl_base)
                    (.shl (.zext (.slice a 0 4) 32) (.lit (BitVec.ofNat 32 4)))))
        (.seq (coreRdReg.set (L1 1)) (stReg.set (L5 S_GC0))))) <|
  -- EXT-5: 0x61 GATE_RETURN. Restores the saved pc; the domain and the
  -- in-gate bit are restored in their funnels. A return with NO gate open is
  -- a synchronous FAULT (spec §9.2 step 4, landed 1235f201): the slot is
  -- poisoned in-core (EXT-3 fail-stop -- the runner halts at this boundary),
  -- the cause/pc/slot are recorded, the instruction does NOT retire and `pc`
  -- stays at it. The silent-no-op reading this replaces cost three debugging
  -- campaigns (fpga_dev.md §73): the machine must be loud, at the faulting
  -- instruction, never silent-then-weird-later.
  gcons (opIs OP_MINI_GATE_RETURN)
    (.ite curInGate
      (.seq (pcReg.set (tcontRd gPopIdx)) (.seq retireInc goF0))
      gretEmptyFault) <|
  -- 0x59 CLONE
  gcons (opIs OP_CLONE_SPAWN)
    (.ite has_free
      (.seq (tstateDynWrite (L2 1) free_slot)
        (.seq (cloneDstReg.set rdf) (.seq (cloneTidReg.set free_slot) (stReg.set (L5 S_CLONE2)))))
      (.seq stepPc (.seq retireInc goF0))) <|
  -- LR
  gcons is_lr
    (actSeq [lrAddrReg.set a, lrValidReg.set (L1 1),
      ldBoffQReg.set (.lit (BitVec.ofNat 3 0)), ldOpQReg.set (L8 OP_LD),
      ldRdQReg.set rdf, memIsStoreReg.set (L1 0),
      .ite (.ult a (L64 0x1000))
        (actSeq [dmemAReg.set (.slice a 3 9), stReg.set (L5 S_L0)])
        (actSeq [coreAddrReg.set (ddrEa sexEa), coreRdReg.set (L1 1),
                 lrReqReg.set (L1 1),                 -- tag: this read takes a reservation
                 stReg.set (L5 S_DL)])]) <|
  -- SC
  gcons is_sc
    (.seq (.ite (.and lr_valid (.eq lr_addr a))
            (.ite (.ult a (L64 0x1000))
              (.seq (dmemWeReg.set (L1 1)) (.seq (dmemAReg.set (.slice a 3 9)) (.seq (dmemWdReg.set b) (.seq stepPc (.seq retireInc goF0)))))
              (actSeq [coreAddrReg.set (ddrEa sexEa), coreWdataReg.set b,
                       coreWrReg.set (L1 1),
                       scReqReg.set (L1 1),            -- tag: conditional store
                       scPendingReg.set (L1 1),        -- the verdict is due at S_DSW
                       stReg.set (L5 S_DSW)]))
            (.seq stepPc (.seq retireInc goF0)))
          (lrValidReg.set (L1 0))) <|
  -- UART_RX load
  gcons (.and is_load (.eq mem_ea_l (L64 UART_RX_ADDR)))
    (.seq (.ite (.not (.eq rx_rptr rx_wptr)) (rxRptrReg.set (.add rx_rptr (.lit (BitVec.ofNat 9 1)))) .skip)
          (.seq stepPc (.seq retireInc goF0))) <|
  -- GP load
  gcons (.and is_load l_is_gp)
    (.ite (opIs OP_LD_31)
      (.seq (gpAddrRReg.set (.and (.slice mem_ea_l 0 32) (.lit (BitVec.ofNat 32 0xFFFFFFFC))))
        (.seq (gpRdReg.set (L1 1)) (.seq (ldRdQReg.set rdf) (stReg.set (L5 S_GPL)))))
      (.seq (trapActiveReg.set (L1 1)) (.seq (trappedOpReg.set op) (stReg.set (L5 S_TRAP))))) <|
  -- zp load
  gcons (.and is_load l_is_zp)
    (.seq (dmemAReg.set ld_widx) (.seq (ldBoffQReg.set ld_boff)
      (.seq (ldOpQReg.set op) (.seq (ldRdQReg.set rdf) (.seq (memIsStoreReg.set (L1 0)) (stReg.set (L5 S_L0))))))) <|
  -- DDR load. EXT-10: `core_addr` is written but `core_rd` is NOT asserted --
  -- the D-cache banks are latched here (D19 sync read) and `S_DC` decides
  -- next cycle whether the bus transaction is needed at all. The address is
  -- translated exactly once, here, so the hit path costs no translation.
  gcons is_load
    (.seq (coreAddrReg.set dc_ea)
      (.seq (dcTagQReg.set (dcTagBank.rd dc_idx))
        (.seq (dcDataQReg.set (dcDataBank.rd dc_idx))
          (.seq (ldBoffQReg.set ld_boff) (.seq (ldOpQReg.set op) (.seq (ldRdQReg.set rdf) (.seq (memIsStoreReg.set (L1 0)) (stReg.set (L5 S_DC))))))))) <|
  -- UART store
  gcons (.and is_store (.eq mem_ea_s (L64 UART_ADDR)))
    (.seq (uartBank.write 0 (.slice uart_wptr 0 8) (.slice b 0 8))
      (.seq (uartWptrReg.set (.add uart_wptr (.lit (BitVec.ofNat 9 1)))) (.seq stepPc (.seq retireInc goF0)))) <|
  -- GP store
  gcons (.and is_store s_is_gp)
    (.ite (opIs OP_ST_34)
      (.seq (gpAddrRReg.set (.and (.slice mem_ea_s 0 32) (.lit (BitVec.ofNat 32 0xFFFFFFFC))))
        (.seq (gpWdataRReg.set (.slice b 0 32)) (.seq (gpWrReg.set (L1 1)) (stReg.set (L5 S_GPS)))))
      (.seq (trapActiveReg.set (L1 1)) (.seq (trappedOpReg.set op) (stReg.set (L5 S_TRAP))))) <|
  -- zp store
  gcons (.and is_store s_is_zp)
    (.seq (dmemAReg.set st_widx) (.seq (memIsStoreReg.set (L1 1)) (stReg.set (L5 S_L0)))) <|
  -- DDR store
  gcons is_store
    (actSeq [coreAddrReg.set (ddrEa mem_ea_s), coreRdReg.set (L1 1),
             memIsStoreReg.set (L1 1), scPendingReg.set (L1 0),
             stReg.set (L5 S_DL)]) <|
  []

/-- Opcode 0 is illegal-instruction FOREVER (the spec: zeroed memory faults
in every implementation, for all time). Previously the mini routed it to the
committed-exec host trap like any unknown op -- non-conformant, and it made a
fall-through into padding a host-dependent behavior. Same fault mechanism as
the empty-stack return: poison + record, no retire, pc precise. -/
def opZeroFault : Act :=
  actSeq [faultCauseReg.set (L8 FAULT_ILLEGAL_OP0),
          faultPcReg.set pc, faultCurReg.set cur,
          poisonReg.set (.or poison (.shl (L32 1) (.zext cur 32))),
          goF0]

/-- default: trap on an unknown opcode. -/
def s_ex_trap : Act :=
  .seq (trapActiveReg.set (L1 1)) (.seq (trappedOpReg.set op) (stReg.set (L5 S_TRAP)))

/-- Opcode 0 outranks the host trap: it is an architectural fault, not a
serviceable unknown (see `opZeroFault`). -/
def s_ex_body : Act :=
  .ite (opIs 0) opZeroFault (actPriTree s_ex_branches s_ex_trap)

def s_ex : Expr 1 × Act := stArm S_EX  s_ex_body

def s_l0 : Expr 1 × Act := stArm S_L0  (stReg.set (L5 S_L1))

/-- S_L1: load-wb (rf in funnel) or store commit; then advance. -/
def s_l1 : Expr 1 × Act := stArm S_L1
  (actSeq [.ite (.not mem_is_store) .skip
            (actSeq [dmemWeReg.set (L1 1), dmemAReg.set st_widx, dmemWdReg.set st_merge]),
           stepPc, retireInc, goF0])

/-- **EXT-10 `S_DC`**: the tag check. A hit feeds `ddr_q` from the latched
data word and joins `S_DST`, so the whole sub-word/sign-extend writeback path
is reused unchanged -- a hit is a load that never touched the bus. A miss
asserts `core_rd` on the address `S_EX` already wrote and joins `S_DL`,
setting `dc_alloc` so the fill funnel knows this miss is allocatable. -/
def s_dc : Expr 1 × Act := stArm S_DC
  (.ite dc_hit
    (.seq (ddrQReg.set dc_data_q) (stReg.set (L5 S_DST)))
    (.seq (coreRdReg.set (L1 1))
      (.seq (dcAllocReg.set (L1 1)) (stReg.set (L5 S_DL)))))

def s_dl : Expr 1 × Act := stArm S_DL
  (.ite mDone
    (.seq (ddrQReg.set mRdata)
      (.seq (dcAllocReg.set (L1 0)) (stReg.set (L5 S_DST))))
    .skip)

/-- S_DST: load-wb (rf in funnel) + advance, or issue the DDR store. -/
def s_dst : Expr 1 × Act := stArm S_DST
  (.ite (.not mem_is_store)
    (actSeq [stepPc, retireInc, goF0])
    (actSeq [coreAddrReg.set (ddrEa mem_ea_s), coreWdataReg.set st_merge,
             coreWrReg.set (L1 1), stReg.set (L5 S_DSW)]))

def s_dsw : Expr 1 × Act := stArm S_DSW
  (.ite mDone (actSeq [stepPc, retireInc, goF0]) .skip)

/-- S_CLONE2: child sp (rf in funnel) + fresh tp/sigmask (both in
`tarrFunnelRule`, D20) + advance. -/
def s_clone2 : Expr 1 × Act := stArm S_CLONE2 (stReg.set (L5 S_CLONE3))

def s_clone3 : Expr 1 × Act := stArm S_CLONE3  (actSeq [stepPc, retireInc, goF0])

/-- S_FTX1: FUTEX_WAIT DDR-compare. -/
def s_ftx1 : Expr 1 × Act := stArm S_FTX1
  (.ite mDone
    (actSeq [.ite (.eq mRdata futex_exp)
              (actSeq [tstateDynWrite (L2 3) cur,
                       .ite (.not (.eq next_ready cur))
                         (actSeq [curReg.set next_ready, setPcFromTpc next_ready, goF0])
                         (stReg.set (L5 S_WAIT))])
              (actSeq [stepPc, goF0]),
             retireInc])
    .skip)

/-- S_WAIT: pick next ready or halt if all free. -/
def s_wait : Expr 1 × Act := stArm S_WAIT
  (.ite (tstateEq next_ready (L2 1))
    (actSeq [curReg.set next_ready, setPcFromTpc next_ready, goF0])
    (.ite (.not anyLive) (.seq (haltedReg.set (L1 1)) (runningReg.set (L1 0))) .skip))

/-- S_MUL: shift-add step or done (rf in funnel). -/
def s_mul : Expr 1 × Act := stArm S_MUL
  (.ite (.eq mul_b (L64 0))
    (actSeq [stepPc, retireInc, goF0])
    (actSeq [.ite (.eq (.slice mul_b 0 1) (L1 1)) (mulAccReg.set (.add mul_acc mul_aw)) .skip,
             mulAwReg.set (.shl mul_aw (.lit (BitVec.ofNat 128 1))),
             mulBReg.set (.shr mul_b (L64 1))]))

/-- S_DIV: restoring divide step or done (rf in funnel). 65-bit partial. -/
def s_div : Expr 1 × Act := stArm S_DIV
  (.ite (.eq div_cnt (.lit (BitVec.ofNat 7 64)))
    (actSeq [stepPc, retireInc, goF0])
    (let prem : Expr 65 := .concat div_rem (.slice div_quo 63 1)
     let divd65 : Expr 65 := .zext div_d 65
     actSeq [
       .ite (.not (.ult prem divd65))
         (actSeq [divRemReg.set (.slice (.sub prem divd65) 0 64),
                  divQuoReg.set (.or (.shl div_quo (L64 1)) (L64 1))])
         (actSeq [divRemReg.set (.slice prem 0 64),
                  divQuoReg.set (.shl div_quo (L64 1))]),
       divCntReg.set (.add div_cnt (.lit (BitVec.ofNat 7 1)))]))

def s_gpl : Expr 1 × Act := stArm S_GPL
  (.ite gpDone (actSeq [stepPc, retireInc, goF0]) .skip)
def s_gps : Expr 1 × Act := stArm S_GPS
  (.ite gpDone (actSeq [stepPc, retireInc, goF0]) .skip)

/-- S_TRAP: hold. default state: go F0.

The bound tracks the HIGHEST implemented state, not `S_GPS` -- when EXT-9
added `S_IC` (21) above `S_GPS` (20), leaving this at `S_GPS` would have made
the default arm fire *on the new state* and silently reset the fetch to
`S_F0`, i.e. an I-cache that never hits and a core that still works. A state
added above the bound is invisible exactly the way the renumbering's dead
opcodes were. -/
def s_default : Expr 1 × Act := (.ult (L5 S_DC) st, goF0)

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
       s_cs0, s_cs1, s_cr0, s_cr1,
       s_clone2, s_clone3, s_ftx1, s_wait, s_mul, s_div, s_gpl, s_gps,
       s_ic, s_gret, s_gc0, s_gc1, s_dc, s_default]
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
    [ wakeOutReg.set wakeLocal
      -- publish the key we woke on (hold otherwise). Kept for the dual SoC
      -- output port + the other core's `doorbell_key`; the wake is unkeyed
      -- now, so the key is informational only.
    , .ite wakeLocal (wakeKeyReg.set rdval) .skip
      -- The wake, unkeyed: promote every parked (FUTEX) slot to READY on a
      -- local FUTEX_WAKE or the cross-core doorbell. tstate-only, one cycle.
    , wakeAllApply
    , .ite resKill (lrValidReg.set (L1 0)) .skip ]⟩

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
  -- D9: reads are pre-cycle, so the descriptor word must come from the bus
  -- this cycle (`mRdata`), not from `gate_dom_q`, which does not hold it
  -- until the next one.
  , (gateCall, cur, .slice mRdata 0 8)
  , (gateRet, cur, tcdomRd gPopIdx) ]

def tdomWeE : Expr 1 := orTree (tdomTriples.map (fun t => t.1))
def tdomWaE : Expr 5 := priTree (tdomTriples.map (fun t => (t.1, t.2.1))) (L5 0)
def tdomWdE : Expr 8 := priTree (tdomTriples.map (fun t => (t.1, t.2.2))) (L8 0)

/-! ### EXT-5 — the gate write funnels

`gateCall`/`gateRet` are the two guards; each memory gets ONE syntactic
`memWrite`, the `tpc` discipline. `in_gate` is a bitmap register (like
EXT-3's `poison`) because nothing reads it at a dynamic index -- only at
`cur` -- but it must be *set and cleared* per slot, and a 32-bit
set/clear on a register is one mux where a memory would be a port. -/
/-- The return that EMPTIES the stack (depth 1 → 0): only then does `in_gate`'s
`cur` bit clear. A return from a nested frame (depth ≥ 2) keeps the thread in a
gate. -/
def gateRetLast : Expr 1 :=
  .and gateRet (.eq (gdepthRd cur) (.lit (BitVec.ofNat 3 1)))

/-- `in_gate` after this cycle: bit `cur` = `gdepth[cur] > 0` (inside ≥1 gate).
Set on any gate call, cleared when the LAST frame returns; a CLONE clears the
CHILD's bit and a THREAD_EXIT clears the exiting thread's bit (so a reused slot
carries no stale "in a gate" flag), plus the `cmd 13` reset. -/
def inGateNext : Expr 32 :=
  let cloneG := exG (.and (opIs OP_CLONE_SPAWN) has_free)
  let exitG  := exG (opIs OP_THREAD_EXIT)
  .mux (.and zeroing (.eq zctr (.lit (BitVec.ofNat 10 0)))) (L32 0)
    (.mux gateCall (.or in_gate (.shl (L32 1) (.zext cur 32)))
      (.mux cloneG (.and in_gate (.not (.shl (L32 1) (.zext free_slot 32))))
        (.mux (.or gateRetLast exitG)
          (.and in_gate (.not (.shl (L32 1) (.zext cur 32)))) in_gate)))

/-- EXT-7: the valid bitmap after this cycle. `cmd 65` validates the selected
slot; `cmd 67` clears every slot whose `tlb_cell` equals the bumped cell;
`cmd 13`'s reset clears all. -/
def tlbVldNext : Expr 8 :=
  let clearMask : Expr 8 :=
    orTreeW ((List.finRange TLBN).map (fun i =>
      .mux (.and (.and cmdValid (.eq cmdIdx (L7 CMD_MAP_PROTECT)))
                 (.eq (tlbCell i) (.slice cmdData 0 8)))
        (.shl (.lit (BitVec.ofNat 8 1)) (.lit (BitVec.ofNat 8 i.val)))
        (.lit (BitVec.ofNat 8 0))))
  .mux (.and zeroing (.eq zctr (.lit (BitVec.ofNat 10 0)))) (.lit (BitVec.ofNat 8 0))
    (.mux (.and cmdValid (.eq cmdIdx (L7 CMD_TLB_PPN)))
      (.or tlb_vld (.shl (.lit (BitVec.ofNat 8 1)) (.zext tlb_sel 8)))
      (.and tlb_vld (.not clearMask)))

/-- §9: the gate-depth funnel. `cmd 13` sweeps every slot to 0 (`zctr < NT`);
a gate call increments `gdepth[cur]`, a gate return decrements it; `zeroing`
and the S_EX/S_GC1 ops are mutually exclusive (`fsmEn` excludes `zeroing`), so
the muxed single write port is unambiguous.
A CLONE gives the child a CLEAN gate state (depth 0, not in a gate): a
fresh thread has no open gates, regardless of what the reused slot held. A
THREAD_EXIT clears the exiting thread's depth so its freed slot carries no stale
gate state to the next CLONE. This keeps `gdepth` and `in_gate` synchronized
when a memory-backed slot is reused. -/
def gdepthClone : Expr 1 := exG (.and (opIs OP_CLONE_SPAWN) has_free)
def gdepthExit  : Expr 1 := exG (opIs OP_THREAD_EXIT)
def gdepthWeE : Expr 1 :=
  .or (.and zeroing (.ult zctr (.lit (BitVec.ofNat 10 NT))))
    (.or gdepthClone (.or gdepthExit (.or gateCall gateRet)))
def gdepthWaE : Expr 5 := .mux zeroing (.slice zctr 0 5) (.mux gdepthClone free_slot cur)
def gdepthWdE : Expr 3 :=
  .mux (.or zeroing (.or gdepthClone gdepthExit)) (.lit (BitVec.ofNat 3 0))
    (.mux gateCall (.add (gdepthRd cur) (.lit (BitVec.ofNat 3 1)))
                   (.sub (gdepthRd cur) (.lit (BitVec.ofNat 3 1))))

def tarrFunnelRule : Rule :=
  ⟨"tarr_funnel",
    .seq (.ite tdomWeE (tdomBank.write 0 tdomWaE tdomWdE) .skip) <|
    -- EXT-5 (§9): the continuation STACK. A gate call PUSHES the return point
    -- and caller domain at slot `cur*MAXD + gdepth[cur]`; a return reads the
    -- slot below (`gPopIdx`, in the gate-return arm / tdom funnel). One write
    -- port each, at the push slot, on a gate call.
    .seq (.ite gateCall (tcontBank.write 0 gPushIdx pc8) .skip) <|
    .seq (.ite gateCall (tcdomBank.write 0 gPushIdx domCur) .skip) <|
    -- §9: the per-thread depth. Push on a gate call (++), pop on a gate return
    -- (--); `cmd 13`'s sweep zeroes it, like the other per-thread arrays (D37).
    .seq (.ite gdepthWeE (gdepthBank.write 0 gdepthWaE gdepthWdE) .skip) <|
    .seq (inGateReg.set inGateNext) <|
    -- The fault record clears on the cmd-13 sweep head, like the other
    -- host-visible diagnostics; pc/cur are meaningful only while cause != 0.
    .seq (.ite (.and zeroing (.eq zctr (.lit (BitVec.ofNat 10 0))))
            (faultCauseReg.set (L8 0)) .skip) <|
    -- EXT-6 (§17): the inbox is guest memory now -- its writes ride the
    -- ordinary bus path from S_CS1/S_CR1, and there is no core-resident
    -- occupancy state left to update here.
    -- EXT-7: TLB fill (cmd 65 sets vpn+domain for the selected entry and
    -- validates it; cmd 66 sets its ppn+cell). The shootdown (cmd 67)
    -- invalidates every entry naming the bumped cell -- the §15 line 876
    -- rule that the cached translation's cell IS the VMA's cell.
    -- (stage B: the page-shaped memory funnel is gone -- entries are
    -- per-element registers now, written in the cmd rule.)
    -- EXT-7: the valid bitmap. Fill sets the selected slot; the §15
    -- shootdown clears every slot whose recorded cell was bumped -- several
    -- at once, which is why this is a register and not a memory.
    .seq (tlbVldReg.set tlbVldNext) <|
    -- EXT-5: the host-loaded gate table.
    .seq (.ite tpcWeE (tpcBank.write 0 tpcWaE tpcWdE) .skip)
      (.seq (.ite (exG (opIs OP_SLEEP))
              (tsleepBank.write 1 cur (.mux (.eq a (L64 0)) (L64 1) a)) .skip)
        (.seq (.ite cloneFresh (tpBank.write 0 clone_tid (L64 0)) .skip)
              (.ite cloneFresh (sigmaskBank.write 0 clone_tid (L64 0)) .skip)))⟩

/-- (9) the single regfile write port. -/
def rfFunnelRule : Rule :=
  ⟨"rf_funnel", .ite rfWeE (rfBank.write 0 rfWaE rfWdE) .skip⟩

/-! ### EXT-9 — the I-cache fill funnel

Both banks get exactly ONE syntactic `memWrite` each, here. That is not
tidiness: the qualified board profile permits one macro write site, and a second write site
drops the bank out of block RAM into flops plus a 4096:1 read mux -- the
CE9/CE10 measurement, 9 523 vs 671 LUT for identical logic. The fill fires
on the miss completion in `S_FW`, which is the only moment a line changes
in stage 1 (invalidate arrives with the sweep, below, through the same
site). -/
def icFill : Expr 1 := .and (.eq st (L5 S_FW)) mDone

def icFillRule : Rule :=
  ⟨"ic_data_funnel", .ite icFill (icDataBank.write 0 ic_idx mRdata) .skip⟩

def icTagRule : Rule :=
  -- ONE syntactic write site, address and data muxed. Two sites on port 0
  -- is what `Compile.MemWriteWF` refuses and what CE10 measured at 14x the
  -- LUTs; the emit gate caught exactly that here before any RTL existed.
  -- Sweep wins over fill: during a wrap the bank is being retired, and a
  -- fill landing in the middle of it would survive the sweep.
  ⟨"ic_tag_funnel",
    .ite (.or ic_inv icFill)
      (icTagBank.write 0
        (.mux ic_inv ic_ctr ic_idx)
        (.mux ic_inv (.lit (BitVec.ofNat 42 0)) ic_tag_fill))
      .skip⟩

/-- Any command that changes the mapping a cached line was filled under.
Bumping `ic_gen` retires every line at once, in one cycle. `cmd 13`'s soft
reset is included so a re-armed core cannot inherit lines from the previous
run. -/
def icGenBump : Expr 1 :=
  .and cmdValid
    (orTree ([CMD_MMU_EN, CMD_TLB_SEL, CMD_TLB_VPN, CMD_TLB_PPN,
              67, CMD_TLB_PHYS, 13].map (fun n => .eq cmdIdx (L7 n))))

/-! ### EXT-10 funnels

Two writers per bank, muxed into one syntactic site each (D38): the **fill**
on an allocatable miss returning in `S_DL`, and the **invalidate** a store
performs on its own line. Invalidate wins the mux, for the same reason the
I-cache's sweep wins over its fill: a store's job is to make the old line
unreachable, and a fill that landed on top of it would resurrect it.

The generation tag is shared with the I-cache (`ic_gen`), so a translation
change retires both caches in one cycle rather than needing a second sweep.

**Not yet cross-core.** `dcStoreInv` invalidates the *storing* core's copy.
The other core's copy is stale until rung 5 broadcasts the address; until
then this is a single-core cache, and `EXTEND_SPEC.md` says so rather than
the code implying otherwise. -/
def dcFill : Expr 1 := .and (.eq st (L5 S_DL)) (.and mDone dc_alloc)

/-- A store that must invalidate: a DDR store, in `S_EX`, on the cacheable
path. The zp/UART/GP store arms never reach DDR and cannot alias a line. -/
def dcStoreInv : Expr 1 :=
  .and (exG is_store) (.and (.not s_is_zp) (.and (.not s_is_gp)
    (.not (.eq mem_ea_s (L64 UART_ADDR)))))

/-- **§17: the cap walk's stores invalidate too.** The walk writes the
handle word (issued from `S_CS0`) and the flags word (issued from
`S_CS1`/`S_CR1`) straight onto the bus, bypassing the store arm's
`dcStoreInv` -- so a previously cached inbox line would serve the
pre-transfer value forever, the exact defect `dcacheselftest`'s `r10`
caught for ordinary stores. The invalidated index is the line of the
address each state is writing THIS cycle: `core_addr - 8` from `S_CS0`
(the handle word), `core_addr + 8` from the flags writers. -/
def dcCapInvS0 : Expr 1 :=
  .and fsmEn (.and (.eq st (L5 S_CS0)) (.and mDone capSendOk))
def dcCapInvFl : Expr 1 :=
  .and fsmEn (.and (.or (.eq st (L5 S_CS1)) (.eq st (L5 S_CR1))) mDone)
def dcCapInv : Expr 1 := .or dcCapInvS0 dcCapInvFl
def dc_cap_idx : Expr 12 :=
  .slice (.shr (.mux dcCapInvS0
                 (.sub core_addr (.lit (BitVec.ofNat 32 8)))
                 (.add core_addr (.lit (BitVec.ofNat 32 8))))
               (.lit (BitVec.ofNat 32 3))) 0 12

def dcDataRule : Rule :=
  ⟨"dc_data_funnel", .ite dcFill (dcDataBank.write 0 dc_fill_idx mRdata) .skip⟩

def dcTagRule : Rule :=
  ⟨"dc_tag_funnel",
    .ite (.or dcStoreInv (.or dcCapInv dcFill))
      (dcTagBank.write 0
        (.mux dcStoreInv dc_sidx (.mux dcCapInv dc_cap_idx dc_fill_idx))
        (.mux (.or dcStoreInv dcCapInv) (.lit (BitVec.ofNat 42 0)) dc_fill_tag))
      .skip⟩

/-- The generation register, and the wrap fallback.

The bump is O(1). The sweep exists only for the wrap: when `ic_gen` is about
to return to a value a surviving line might still carry, the tag bank is
walked once. That keeps the design *correct* rather than merely improbable,
at an amortized cost of 4096 cycles per 65 536 invalidations -- about 0.06
cycles each. -/
def icGenRule : Rule :=
  ⟨"ic_gen", .ite icGenBump
    (.ite (.eq ic_gen (.lit (BitVec.ofNat 16 65535)))
      (.seq (icGenReg.set (.lit (BitVec.ofNat 16 0)))
        (.seq (icInvReg.set (L1 1)) (icCtrReg.set (.lit (BitVec.ofNat 12 0)))))
      (icGenReg.set (.add ic_gen (.lit (BitVec.ofNat 16 1))))) .skip⟩

/-- The wrap sweep: a `zeroing` clone over the tag bank, through the same
single write site. Ends by clearing `ic_inv`, which releases `fsmEn`. -/
def icInvRule : Rule :=
  ⟨"ic_inv", .ite ic_inv
    (.ite (.eq ic_ctr (.lit (BitVec.ofNat 12 4095)))
      (.seq (icInvReg.set (L1 0)) (icCtrReg.set (.lit (BitVec.ofNat 12 0))))
      (icCtrReg.set (.add ic_ctr (.lit (BitVec.ofNat 12 1))))) .skip⟩

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
  ⟨"quantum", [hwstmt|
    if cmdValid & (cmdIdx == $(L7 CMD_QUANTUM)) then qctrReg <- cmdData else
    if cmdValid & (cmdIdx == 13) & (cmdData[0] == 1) then qctrReg <- quantum else
    if preemptAtF0 then qctrReg <- quantum else
    if qTick then qctrReg <- qctr - 1]⟩

/-! ## Register / memory / input declarations -/

def scalarRegs : List RegDecl :=
  [curReg.decl, pcReg.decl (BitVec.ofNat 64 TEXT_BASE), retireReg.decl,
     -- EXT-8: the commit-trace ring write pointer (wraps at 16).
     traceWpReg.decl, traceSelReg.decl,
     traceRdPcReg.decl, traceRdWbReg.decl,
     traceHitReg.decl, traceInPcReg.decl, traceInWbReg.decl,
   runningReg.decl, haltedReg.decl, stReg.decl, irReg.decl,
   aReg.decl, bReg.decl, rdvalReg.decl, selTReg.decl, selFReg.decl,
   -- EXT-9: the I-cache sync-read latches (D19). Both reset to 0, which is
   -- an invalid tag, so the cache comes up empty on every technology.
   icTagQReg.decl, icDataQReg.decl, icGenReg.decl, gateTblBaseReg.decl,
   -- §17: the cap-inbox root pointer and the walked-flags latch
   capTblBaseReg.decl, capFlQReg.decl,
   -- EXT-10 latches. `dc_alloc` records that the miss now in flight came from
   -- the cacheable path, so the fill funnel cannot allocate for an atomic or
   -- an out-of-window read that merely happened to pass through S_DL.
   dcTagQReg.decl, dcDataQReg.decl, dcAllocReg.decl,
   gateEntQReg.decl, gateDomQReg.decl,
   icInvReg.decl, icCtrReg.decl,
   memIsStoreReg.decl, trapActiveReg.decl, trappedOpReg.decl,
   coreRdReg.decl, coreWrReg.decl, coreAddrReg.decl, coreWdataReg.decl,
   jtagRdReg.decl, jtagWrReg.decl, jtagWdataReg.decl, ddrAddrJReg.decl,
   ddrLoJReg.decl, ddrRdLReg.decl, ddrQReg.decl, busReqReg.decl,
   gpRdReg.decl, gpWrReg.decl, gpAddrRReg.decl, gpWdataRReg.decl,
   dmemWeReg.decl, dmemAReg.decl, dmemWdReg.decl, dmemRdReg.decl,
   uartWptrReg.decl, uartRidxReg.decl, uartByteReg.decl,
   rxWptrReg.decl, rxRptrReg.decl,
   ldBoffQReg.decl, ldOpQReg.decl, ldRdQReg.decl,
   lrAddrReg.decl, lrValidReg.decl, futexExpReg.decl, futexAddrQReg.decl,
   sleepScanReg.decl, nextReadyReg.decl, freeSlotReg.decl, hasFreeReg.decl,
   cloneDstReg.decl, cloneTidReg.decl,
   mulAccReg.decl, mulAwReg.decl, mulBReg.decl, mulKindReg.decl,
   divRemReg.decl, divQuoReg.decl, divDReg.decl, divCntReg.decl,
   divIsremReg.decl, divNegqReg.decl, divNegrReg.decl,
   zeroingReg.decl, zctrReg.decl,
   regSelReg.decl, regWselReg.decl, regWloReg.decl,
   dmemAddrJReg.decl, dmemLoJReg.decl, regRdReg.decl,
   wakeOutReg.decl, wakeKeyReg.decl, lrReqReg.decl, scReqReg.decl, scPendingReg.decl,
   -- EXT-1: both reset to 0 = preemption disabled = the cooperative machine
   quantumReg.decl, qctrReg.decl,
   -- EXT-2: observation mirror of `tdom[cur]` (the datapath uses `domCur`)
   curDomReg.decl,
   -- EXT-3: fail-stop bitmap; 0 = nothing poisoned = the pre-EXT-3 machine
   poisonReg.decl,
   -- EXT-5: gates. `in_gate` = per-slot "inside ≥1 gate" bitmap.
   inGateReg.decl,
   -- §9 diagnostic (the loud GATE_RETURN): first no-op return's pc + slot +
   -- count. Zero unless a GATE_RETURN ran with no gate open on its slot.
   faultCauseReg.decl, faultPcReg.decl, faultCurReg.decl,
  -- EXT-7: mmu_en = 0 at reset = bypass = the pre-EXT-7 machine
   mmuEnReg.decl, tlbSelReg.decl, tlbVldReg.decl]
  ++ (List.finRange TLBN).flatMap (fun i =>
       [(tlbBaseRegs.reg i).decl, (tlbLimitRegs.reg i).decl,
        (tlbPhysRegs.reg i).decl, (tlbDomRegs.reg i).decl,
        (tlbCellRegs.reg i).decl])

/-- The thread-table array that stays per-element registers (D20): `tstate`
(2-bit, multi-writer, read at every index by the ready/free priority encoders
and the unkeyed wake). `tfutex` and its 64-bit-wide NT comparator bank were
deleted to fit NT=32 (the wake is unkeyed now — see `wakeAllApply`). -/
def arrRegs : List RegDecl :=
  tstateRegs.decls (fun i => if i.val = 0 then 1 else 0)

/-- (12) EXT-2 — the observation mirror. Unconditional: `cur_dom` is
`tdom[cur]` as of the previous cycle. It is the *only* writer of `cur_dom`
and `cur_dom` has no readers inside the design, so it cannot influence
behaviour — which is what makes it safe to let it lag. -/
def domainRule : Rule := ⟨"domain", [hwstmt| curDomReg <- domCur]⟩

def declarations : Declarations :=
  { Declarations.empty with
      regs := scalarRegs ++ arrRegs
      outputs := (scalarRegs ++ arrRegs).map (fun r : RegDecl => r.name) }
    |>.addMem rfBank (syncRead := true)
    |>.addMem dmemBank (syncRead := true)
    -- The trace ring and RX FIFO are intentionally distributed memories.
    |>.addMem tracePcBank
    |>.addMem traceWbBank
    |>.addMem uartBank (syncRead := true)
    |>.addMem rxBank
    -- Cache tags are 42 bits: valid, generation, and address tag.
    |>.addMem icDataBank (syncRead := true)
    |>.addMem icTagBank (syncRead := true)
    |>.addMem dcDataBank (syncRead := true)
    |>.addMem dcTagBank (syncRead := true)
    -- Thread-table memories have all-zero physical reset images; the reset
    -- sweep establishes live architectural contents before `fsmEn` opens.
    |>.addMem tpcBank
    |>.addMem tsleepBank
    |>.addMem tpBank
    |>.addMem sigmaskBank
    |>.addMem tdomBank
    |>.addMem tcontBank
    |>.addMem tcdomBank
    |>.addMem gdepthBank
    |>.addInput mDonePort
    |>.addInput mRdataPort
    |>.addInput mBusyPort
    |>.addInput gpDonePort
    |>.addInput gpRdataPort
    |>.addInput gpBusyPort
    |>.addInput cmdValidPort
    |>.addInput cmdIdxPort
    |>.addInput cmdDataPort
    |>.addInput resKillPort
    |>.addInput doorbellPort
    |>.addInput doorbellKeyPort
    |>.addInput holdPort
    |>.addInput scFailPort

def coreRules : List Rule :=
  [encRule, sleepScanRule, latchRule, traceRule, pulseDefaultsRule, zeroingRule, cmdRule, ddrRdLRule,
   fsmRule, smpRule, tarrFunnelRule, rfFunnelRule, quantumRule, domainRule,
   icFillRule, icTagRule, icGenRule, icInvRule,
   dcDataRule, dcTagRule]

def design : Design := Design.ofDecls "lnp64mini" declarations coreRules

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
