-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
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

/-! ## Per-element register arrays (Fin 32 builders) -/

def tpc     (i : Fin NT) : Expr 64 := .reg 64 s!"tpc{i.val}"
def tstate  (i : Fin NT) : Expr 2  := .reg 2  s!"tstate{i.val}"
def tsleep  (i : Fin NT) : Expr 64 := .reg 64 s!"tsleep{i.val}"
def tfutex  (i : Fin NT) : Expr 64 := .reg 64 s!"tfutex{i.val}"
def tp_arr  (i : Fin NT) : Expr 64 := .reg 64 s!"tp_arr{i.val}"
def sigmask_arr (i : Fin NT) : Expr 64 := .reg 64 s!"sigmask_arr{i.val}"

/-! ## Literal helpers -/

def L1  (n : Nat) : Expr 1  := .lit (BitVec.ofNat 1 n)
def L2  (n : Nat) : Expr 2  := .lit (BitVec.ofNat 2 n)
def L5  (n : Nat) : Expr 5  := .lit (BitVec.ofNat 5 n)
def L7  (n : Nat) : Expr 7  := .lit (BitVec.ofNat 7 n)
def L8  (n : Nat) : Expr 8  := .lit (BitVec.ofNat 8 n)
def L64 (n : Nat) : Expr 64 := .lit (BitVec.ofNat 64 n)

/-! ## Balanced-tree builders (timing; semantics-preserving)

The Verilog emitter turns a `foldr`/`foldl` over a list of guarded values
into a *linear* mux chain, so a 64-entry fold becomes a 64-level
combinational cone. The builders below produce the SAME function of the
same inputs with `O(log n)` depth. None of them needs the guards to be
mutually exclusive — see `priTree`. -/

/-- One balanced-reduction pass: fuse adjacent elements with `f`. -/
def pairFold {w : Nat} (f : Expr w → Expr w → Expr w) : List (Expr w) → List (Expr w)
  | a :: b :: t => f a b :: pairFold f t
  | l => l

def reduceTreeAux {w : Nat} (f : Expr w → Expr w → Expr w) (d : Expr w) :
    Nat → List (Expr w) → Expr w
  | _,   []  => d
  | _,   [x] => x
  | 0,   xs  => xs.foldr f d          -- fuel guard; never taken (fuel = length)
  | n+1, xs  => reduceTreeAux f d n (pairFold f xs)

/-- Balanced `f`-reduction of `xs` (`d` when empty). Equal to the linear
fold whenever `f` is associative and `d` is a right unit — used here only
with `.or` (associative, unit `0`) and `.add` on disjoint/bounded lanes. -/
def reduceTree {w : Nat} (f : Expr w → Expr w → Expr w) (d : Expr w)
    (xs : List (Expr w)) : Expr w :=
  reduceTreeAux f d xs.length xs

/-- Balanced OR-reduction (replaces linear `.or` chains). -/
def orTree (xs : List (Expr 1)) : Expr 1 := reduceTree .or (L1 0) xs

/-- Balanced OR-reduction at width `w` (for disjoint-lane merges). -/
def orTreeW {w : Nat} (xs : List (Expr w)) : Expr w :=
  reduceTree .or (.lit (BitVec.ofNat w 0)) xs

/-- Balanced ADD-reduction (for popcount-style sums). -/
def addTree {w : Nat} (xs : List (Expr w)) : Expr w :=
  reduceTree .add (.lit (BitVec.ofNat w 0)) xs

/-- Fuse two guarded groups into one, keeping *earliest-guard-wins*:
`(gl,vl) ⊕ (gr,vr) = (gl ∨ gr, if gl then vl else vr)`.
If `gl` the pair yields `vl`; if `¬gl ∧ gr` it yields `vr`; if neither, the
pair's guard is false so the parent never selects its value. Hence the
fusion is associative *as a priority chain* and needs **no** mutual
exclusivity between the guards. -/
def priPair {w : Nat} : (Expr 1 × Expr w) → (Expr 1 × Expr w) → (Expr 1 × Expr w)
  | (gl, vl), (gr, vr) => (.or gl gr, .mux gl vl vr)

def priPairFold {w : Nat} : List (Expr 1 × Expr w) → List (Expr 1 × Expr w)
  | a :: b :: t => priPair a b :: priPairFold t
  | l => l

def priTreeAux {w : Nat} : Nat → List (Expr 1 × Expr w) → Expr w → Expr w
  | _,   [],      d => d
  | _,   [(g,v)], d => .mux g v d
  | 0,   xs,      d => xs.foldr (fun gv acc => .mux gv.1 gv.2 acc) d
  | n+1, xs,      d => priTreeAux n (priPairFold xs) d

/-- Balanced priority select: exactly
`xs.foldr (fun (g,v) acc => .mux g v acc) d` (first matching guard wins),
at `O(log n)` depth. -/
def priTree {w : Nat} (xs : List (Expr 1 × Expr w)) (d : Expr w) : Expr w :=
  priTreeAux xs.length xs d

/-- Last-match-wins variant (mirrors a `foldl` funnel). -/
def priTreeLast {w : Nat} (xs : List (Expr 1 × Expr w)) (d : Expr w) : Expr w :=
  priTree xs.reverse d

/-! ### The same trick for `Act` if/else-if chains

`.ite (gl ∨ gr) (.ite gl al ar) rest` runs `al` if `gl`, else `ar` if `gr`,
else `rest` — bit-for-bit the linear `if gl … else if gr … else rest`.
Since all reads are pre-cycle (D9) and only one branch of an `.ite` ever
runs, fusing branches pairwise is a pure re-association of the priority
chain: no mutual exclusivity needed, no write order changed. -/
def actPriPair : (Expr 1 × Act) → (Expr 1 × Act) → (Expr 1 × Act)
  | (gl, al), (gr, ar) => (.or gl gr, .ite gl al ar)

def actPriPairFold : List (Expr 1 × Act) → List (Expr 1 × Act)
  | a :: b :: t => actPriPair a b :: actPriPairFold t
  | l => l

def actPriTreeAux : Nat → List (Expr 1 × Act) → Act → Act
  | _,   [],      d => d
  | _,   [(g,a)], d => .ite g a d
  | 0,   xs,      d => xs.foldr (fun ga acc => .ite ga.1 ga.2 acc) d
  | n+1, xs,      d => actPriTreeAux n (actPriPairFold xs) d

/-- Balanced else-if chain: exactly
`xs.foldr (fun (g,a) acc => .ite g a acc) d`, at `O(log n)` depth. -/
def actPriTree (xs : List (Expr 1 × Act)) (d : Act) : Act :=
  actPriTreeAux xs.length xs d

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
  opAny [0x04,0x02,0x10,0x11,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,
   0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0x1d,0x1e,0xd0,
   0xad,0xae,0xaf,0xb0,0xb1,0xb2,0xb8,0xb9,0xba,0xb6,0xb7,0xb4]

def is_load : Expr 1 := opAny [0x30,0x31,0x05,0x36,0x09,0x32,0x08]
def is_store : Expr 1 := opAny [0x33,0x34,0x37,0x35]
/-- is_branch: op in [0x21,0x26]. -/
def is_branch : Expr 1 := opAny [0x21,0x22,0x23,0x24,0x25,0x26]
def is_lr : Expr 1 := opAny [0xc5,0xc7,0xc9]
def is_sc : Expr 1 := opAny [0xc6,0xc8,0xca]
/-- is_fence: op==0xcd || (0xd1<=op<=0xd4). -/
def is_fence : Expr 1 := opAny [0xcd,0xd1,0xd2,0xd3,0xd4]
/-- is_sel: 0x40<=op<=0x45. -/
def is_sel : Expr 1 := opAny [0x40,0x41,0x42,0x43,0x44,0x45]
def is_div : Expr 1 := opAny [0x13,0xa7,0xa8,0xa9]
def is_mulh : Expr 1 := .or (opIs 0xaa) (opIs 0xab)
def div_sgn : Expr 1 := .or (opIs 0x13) (opIs 0xa8)

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
  [ (opIs 0x02, a)
  , (opIs 0x10, .add a b)
  , (opIs 0x11, .sub a b)
  , (opIs 0x04, .or (.zext (.slice a 0 32) 64) (.shl (.zext (.slice imm_i 0 32) 64) (L64 32)))
  , (opIs 0x14, .and a b)
  , (opIs 0x15, .or a b)
  , (opIs 0x16, .xor a b)
  , (opIs 0x17, .not a)
  , (opIs 0x18, .shl a (.zext shamt_r 64))
  , (opIs 0x19, .shr a (.zext shamt_r 64))
  , (opIs 0x1a, asr a shamt_r)
  , (opIs 0x1b, .mux (.slt a b) (L64 1) (L64 0))
  , (opIs 0x1c, .mux (.ult a b) (L64 1) (L64 0))
  , (opIs 0xa0, .add a imm_i)
  , (opIs 0xa1, .and a imm_i)
  , (opIs 0xa2, .or a imm_i)
  , (opIs 0xa3, .xor a imm_i)
  , (opIs 0xa4, .shl a (.zext shamt_i 64))
  , (opIs 0xa5, .shr a (.zext shamt_i 64))
  , (opIs 0xa6, asr a shamt_i)
  , (opIs 0x1d, .mux (.slt a imm_i) (L64 1) (L64 0))
  , (opIs 0x1e, .mux (.ult a imm_i) (L64 1) (L64 0))
  , (opIs 0xd0, .add pc imm_j)
  , (opIs 0xad, .sext (.slice a 0 8) 64)
  , (opIs 0xae, .sext (.slice a 0 16) 64)
  , (opIs 0xaf, .sext (.slice a 0 32) 64)
  , (opIs 0xb0, .zext (.slice a 0 8) 64)
  , (opIs 0xb1, .zext (.slice a 0 16) 64)
  , (opIs 0xb2, .zext (.slice a 0 32) 64)
  , (opIs 0xb8, bswap16)
  , (opIs 0xb9, bswap32)
  , (opIs 0xba, bswap64)
  , (opIs 0xb4, ctzE)
  , (opIs 0xb6, .or (.shl a (.zext shamt_r 64)) (.shr a (.zext (negShamt shamt_r) 64)))
  , (opIs 0xb7, .or (.shr a (.zext shamt_r 64)) (.shl a (.zext (negShamt shamt_r) 64)))
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
  [ (opIs 0x21, .eq a b)
  , (opIs 0x22, .not (.eq a b))
  , (opIs 0x23, .slt a b)
  , (opIs 0x24, .not (.slt a b))
  , (opIs 0x25, .ult a b)
  , (opIs 0x26, .not (.ult a b)) ] (L1 0)

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

def ld_wb : Expr 64 :=
  priTree
  [ (.eq ld_op_q (L8 0x30), mem_src)
  , (.eq ld_op_q (L8 0x31), .zext (.slice lw_shift 0 32) 64)
  , (.eq ld_op_q (L8 0x05), .sext (.slice lw_shift 0 32) 64)
  , (.eq ld_op_q (L8 0x36), .zext (.slice lw_shift 0 16) 64)
  , (.eq ld_op_q (L8 0x09), .sext (.slice lw_shift 0 16) 64)
  , (.eq ld_op_q (L8 0x32), .zext (.slice lw_shift 0 8) 64)
  , (.eq ld_op_q (L8 0x08), .sext (.slice lw_shift 0 8) 64) ] mem_src

def st_width : Expr 4 :=
  priTree
  [ (opIs 0x35, .lit (BitVec.ofNat 4 1))
  , (opIs 0x37, .lit (BitVec.ofNat 4 2))
  , (opIs 0x34, .lit (BitVec.ofNat 4 4)) ] (.lit (BitVec.ofNat 4 8))

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
  orTreeW ((List.finRange NT).map
    (fun i => .shl (.zext (.eq (tstate i) (L2 1)) 32) (.lit (BitVec.ofNat 32 i.val))))
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
  -- S_EX GET_PCR Tid (op 0x54, rs1f==2)
  , (exG (.and (opIs 0x54) (.and (.eq rs1f (L5 2)) (.not (.eq rdf (L5 0))))),
       cat55 cur rdf, .add (.zext cur 64) (L64 1))
  -- S_EX is_alu
  , (exG (.and is_alu (.not (.eq rdf (L5 0)))), cat55 cur rdf, aluE)
  -- S_EX JAL (0x27)
  , (exG (.and (opIs 0x27) (.not (.eq rdf (L5 0)))), cat55 cur rdf, pc8)
  -- S_EX JALR (0x28)
  , (exG (.and (opIs 0x28) (.not (.eq rdf (L5 0)))), cat55 cur rdf, pc8)
  -- S_EX CLONE has_free: child r2 = b
  , (exG (.and (opIs 0x59) has_free), cat55 free_slot (L5 2), b)
  -- S_EX CLONE no-free: rd = -1
  , (exG (.and (opIs 0x59) (.and (.not has_free) (.not (.eq rdf (L5 0))))),
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

/-- (2) serialized sleep scan (per-element). -/
def sleepScanRule : Rule :=
  ⟨"sleepdec", .ite (.and (.not holdEn) (.and running (.not halted)))
    (.seq (.write 5 "sleep_scan" (.add sleep_scan (L5 1)))
      ((List.finRange NT).foldr (fun i acc =>
        .seq (.ite (.and (.eq sleep_scan (L5 i.val)) (.eq (tstate i) (L2 2)))
          (.ite (.not (.ult (L64 1) (tsleep i)))   -- tsleep <= 1
            (.write 2 s!"tstate{i.val}" (L2 1))
            (.write 64 s!"tsleep{i.val}" (.sub (tsleep i) (L64 1))))
          .skip) acc) .skip))
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
    .seq (.write 10 "zctr" (.lit (BitVec.ofNat 10 0)))
      ((List.finRange NT).foldr (fun i acc =>
        .seq (.write 2 s!"tstate{i.val}" (if i.val = 0 then L2 1 else L2 0))
          (.seq (.write 64 s!"tpc{i.val}" (L64 TEXT_BASE)) acc)) .skip)
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

/-- DATA_BASE + (word-aligned) ea, as a 32-bit core_addr. -/
def ddrEa (ea : Expr 64) : Expr 32 :=
  .add (.lit (BitVec.ofNat 32 DATA_BASE)) (.shl (.slice ea 3 29 |> fun w => .zext w 32) (.lit (BitVec.ofNat 32 3)))
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

/-- `pc <= tpc[idx]`. Was a 32-deep `.ite` chain (⇒ a 32-deep 64-bit mux
cone on `pc`); `idx : Expr 5` ranges over exactly the 32 cases, so the
chain always writes and the `.skip` tail is unreachable — an unconditional
write of the balanced 32-way select is the same function. -/
def setPcFromTpc (idx : Expr 5) : Act :=
  .write 64 "pc"
    (priTree ((List.finRange NT).map (fun i => (.eq idx (L5 i.val), tpc i))) (L64 0))
def tpcDynWrite (idx : Expr 5) (v : Expr 64) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (.write 64 s!"tpc{i.val}" v) .skip) acc) .skip
def tstateDynWrite (v : Expr 2) (idx : Expr 5) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (.write 2 s!"tstate{i.val}" v) .skip) acc) .skip
def tsleepDynWrite (idx : Expr 5) (v : Expr 64) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (.write 64 s!"tsleep{i.val}" v) .skip) acc) .skip
def tfutexDynWrite (idx : Expr 5) (v : Expr 64) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (.write 64 s!"tfutex{i.val}" v) .skip) acc) .skip
def tp_arrDynWrite (idx : Expr 5) (v : Expr 64) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (.write 64 s!"tp_arr{i.val}" v) .skip) acc) .skip
def sigmaskDynWrite (idx : Expr 5) (v : Expr 64) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.eq idx (L5 i.val)) (.write 64 s!"sigmask_arr{i.val}" v) .skip) acc) .skip
/-- dynamic tstate[idx]==v test as a (balanced) mux chain. -/
def tstateEq (idx : Expr 5) (v : Expr 2) : Expr 1 :=
  priTree ((List.finRange NT).map (fun i => (.eq idx (L5 i.val), .eq (tstate i) v))) (L1 0)
/-- any thread not FREE. -/
def anyLive : Expr 1 :=
  orTree ((List.finRange NT).map (fun i => .not (.eq (tstate i) (L2 0))))

/-- FUTEX_WAKE: wake lowest-indexed matching FUTEX threads, up to count a.
per-element guard: tstate_i==3 ∧ tfutex_i==rdval ∧ (matches-before-i < a). -/
def futexWakeBody : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .seq (.ite (.and (.eq (tstate i) (L2 3))
                 (.and (.eq (tfutex i) rdval) (.ult (matchesBefore i.val) a)))
            (.write 2 s!"tstate{i.val}" (L2 1)) .skip) acc) .skip
where
  /-- `tstate_j == FUTEX ∧ tfutex_j == rdval`. -/
  fmatch (j : Nat) : Expr 1 :=
    .and (.eq (.reg 2 s!"tstate{j}") (L2 3)) (.eq (.reg 64 s!"tfutex{j}") rdval)
  /-- popcount of `fmatch j` for `j < i`, zero-extended to 64 for the
  `< a` test. Was a linear chain of up to 31 **64-bit** adds; the count is
  bounded by NT = 32, so a 6-bit balanced adder tree carries the exact same
  value (no truncation) at depth ~log₂32 with 6-bit — not 64-bit — carry
  chains. -/
  matchesBefore (i : Nat) : Expr 64 :=
    .zext (addTree ((List.range i).map (fun j => (.zext (fmatch j) 6 : Expr 6)))) 64

def s_f0 : Expr 1 × Act := stArm S_F0
  (.ite bus_req (.write 5 "st" (L5 S_PAUSE))
    (.seq (.write 32 "core_addr" ddrPc) (.seq (.write 1 "core_rd" (L1 1)) (.write 5 "st" (L5 S_FW)))))

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
  gcons (opIs 0x3a) (.seq (.write 1 "halted" (L1 1)) (.seq (.write 1 "running" (L1 0)) retireInc)) <|
  -- 0x3b THREAD_EXIT
  gcons (opIs 0x3b)
    (.seq (tstateDynWrite (L2 0) cur)
      (.seq (.ite (.not (.eq next_ready cur))
              (.seq (.write 5 "cur" next_ready) (.seq (setPcFromTpc next_ready) goF0))
              (.write 5 "st" (L5 S_WAIT)))
            retireInc)) <|
  -- 0x00 NOP
  gcons (opIs 0x00) (.seq stepPc (.seq retireInc goF0)) <|
  -- fence
  gcons is_fence (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x12 MUL
  gcons (opIs 0x12)
    (.seq (.write 128 "mul_acc" (.lit (BitVec.ofNat 128 0)))
      (.seq (.write 128 "mul_aw" (.zext a 128))
        (.seq (.write 64 "mul_b" b) (.seq (.write 2 "mul_kind" (L2 0)) (.write 5 "st" (L5 S_MUL)))))) <|
  -- mulh
  gcons is_mulh
    (.seq (.write 128 "mul_acc" (.lit (BitVec.ofNat 128 0)))
      (.seq (.write 128 "mul_aw" (.zext a 128))
        (.seq (.write 64 "mul_b" b)
          (.seq (.write 2 "mul_kind" (.mux (opIs 0xaa) (L2 1) (L2 2))) (.write 5 "st" (L5 S_MUL)))))) <|
  -- div
  gcons is_div
    (.ite (.eq b (L64 0))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))
      (.seq (.write 64 "div_rem" (L64 0))
        (.seq (.write 64 "div_quo" div_a_abs)
          (.seq (.write 64 "div_d" div_b_abs)
            (.seq (.write 7 "div_cnt" (.lit (BitVec.ofNat 7 0)))
              (.seq (.write 1 "div_isrem" (.or (opIs 0xa8) (opIs 0xa9)))
                (.seq (.write 1 "div_negq" (.and div_sgn (.xor (.slice a 63 1) (.slice b 63 1))))
                  (.seq (.write 1 "div_negr" (.and div_sgn (.slice a 63 1))) (.write 5 "st" (L5 S_DIV)))))))))) <|
  -- sel
  gcons is_sel (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x54 GET_PCR
  gcons (opIs 0x54)
    (.ite (.eq rs1f (L5 2)) (.seq stepPc (.seq retireInc goF0))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))) <|
  -- alu
  gcons is_alu (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x20 J
  gcons (opIs 0x20) (.seq (.write 64 "pc" (.add pc (.shl imm_j (L64 3)))) (.seq retireInc goF0)) <|
  -- 0x27 JAL
  gcons (opIs 0x27) (.seq (.write 64 "pc" (.add pc (.shl imm_j (L64 3)))) (.seq retireInc goF0)) <|
  -- 0x28 JALR
  gcons (opIs 0x28) (.seq (.write 64 "pc" (.add a imm_i)) (.seq retireInc goF0)) <|
  -- branch
  gcons is_branch (.seq (.write 64 "pc" (.mux br_take (.add pc (.shl imm_s (L64 3))) pc8)) (.seq retireInc goF0)) <|
  -- 0x06 YIELD
  gcons (opIs 0x06)
    (.seq (.ite (.eq next_ready cur) stepPc
            (.seq (tpcDynWrite cur pc8) (.seq (.write 5 "cur" next_ready) (setPcFromTpc next_ready))))
          (.seq retireInc goF0)) <|
  -- 0x07 SLEEP
  gcons (opIs 0x07)
    (.seq (tpcDynWrite cur pc8)
      (.seq (tstateDynWrite (L2 2) cur)
        (.seq (tsleepDynWrite cur (.mux (.eq a (L64 0)) (L64 1) a))
          (.seq (.ite (.not (.eq next_ready cur))
                  (.seq (.write 5 "cur" next_ready) (.seq (setPcFromTpc next_ready) goF0))
                  (.write 5 "st" (L5 S_WAIT)))
                retireInc)))) <|
  -- 0xcb FUTEX_WAIT
  gcons (opIs 0xcb)
    (.seq (.write 32 "core_addr" (.add (.lit (BitVec.ofNat 32 DATA_BASE)) (.shl (.zext (.slice rdval 3 29) 32) (.lit (BitVec.ofNat 32 3)))))
      (.seq (.write 1 "core_rd" (L1 1))
        (.seq (.write 64 "futex_addr_q" rdval) (.seq (.write 64 "futex_exp" a) (.write 5 "st" (L5 S_FTX1)))))) <|
  -- 0xcc FUTEX_WAKE (per-element wake; count via matches-before-i < a)
  gcons (opIs 0xcc) (.seq futexWakeBody (.seq stepPc (.seq retireInc goF0))) <|
  -- 0x59 CLONE
  gcons (opIs 0x59)
    (.ite has_free
      (.seq (tpcDynWrite free_slot a)
        (.seq (tstateDynWrite (L2 1) free_slot)
          (.seq (.write 5 "clone_dst" rdf) (.seq (.write 5 "clone_tid" free_slot) (.write 5 "st" (L5 S_CLONE2))))))
      (.seq stepPc (.seq retireInc goF0))) <|
  -- LR
  gcons is_lr
    (actSeq [.write 64 "lr_addr" a, .write 1 "lr_valid" (L1 1),
      .write 3 "ld_boff_q" (.lit (BitVec.ofNat 3 0)), .write 8 "ld_op_q" (L8 0x30),
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
    (.ite (opIs 0x31)
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
    (.ite (opIs 0x34)
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

/-- S_CLONE2: child sp (rf in funnel) + fresh tp/sigmask + advance. -/
def s_clone2 : Expr 1 × Act := stArm S_CLONE2
  (actSeq [tp_arrDynWrite clone_tid (L64 0), sigmaskDynWrite clone_tid (L64 0),
           .write 5 "st" (L5 S_CLONE3)])

def s_clone3 : Expr 1 × Act := stArm S_CLONE3  (actSeq [stepPc, retireInc, goF0])

/-- S_FTX1: FUTEX_WAIT DDR-compare. -/
def s_ftx1 : Expr 1 × Act := stArm S_FTX1
  (.ite mDone
    (actSeq [.ite (.eq mRdata futex_exp)
              (actSeq [tpcDynWrite cur pc8, tstateDynWrite (L2 3) cur, tfutexDynWrite cur futex_addr_q,
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
  ⟨"smp",
    .seq (.write 1 "wake_out" (.and fsmEn (.and (.eq st (L5 S_EX)) (opIs 0xcc))))
      (.seq
        (.ite doorbell
          ((List.finRange NT).foldr (fun i acc =>
            .seq (.ite (.eq (tstate i) (L2 3)) (.write 2 s!"tstate{i.val}" (L2 1)) .skip) acc)
            .skip)
          .skip)
        (.ite resKill (.write 1 "lr_valid" (L1 0)) .skip))⟩

/-- (9) the single regfile write port. -/
def rfFunnelRule : Rule :=
  ⟨"rf_funnel", .ite rfWeE (.memWrite 10 64 "rf" 0 rfWaE rfWdE) .skip⟩

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
   ⟨"wake_out",1,0⟩, ⟨"lr_req",1,0⟩, ⟨"sc_req",1,0⟩, ⟨"sc_pending",1,0⟩]

def arrRegs : List RegDecl :=
  (List.finRange NT).map (fun i => ⟨s!"tpc{i.val}", 64, BitVec.ofNat 64 TEXT_BASE⟩)
  ++ (List.finRange NT).map (fun i => ⟨s!"tstate{i.val}", 2, if i.val = 0 then 1 else 0⟩)
  ++ (List.finRange NT).map (fun i => ⟨s!"tsleep{i.val}", 64, 0⟩)
  ++ (List.finRange NT).map (fun i => ⟨s!"tfutex{i.val}", 64, 0⟩)
  ++ (List.finRange NT).map (fun i => ⟨s!"tp_arr{i.val}", 64, 0⟩)
  ++ (List.finRange NT).map (fun i => ⟨s!"sigmask_arr{i.val}", 64, 0⟩)

def design : Design where
  name := "lnp64mini"
  regs := scalarRegs ++ arrRegs
  mems :=
    [⟨"rf", 10, 64, fun _ => 0⟩, ⟨"dmem", 9, 64, fun _ => 0⟩,
     ⟨"uart_mem", 8, 8, fun _ => 0⟩, ⟨"rx_mem", 8, 8, fun _ => 0⟩]
  rules :=
    [encRule, sleepScanRule, latchRule, pulseDefaultsRule, zeroingRule, cmdRule, ddrRdLRule,
     fsmRule, smpRule, rfFunnelRule]
  inputs :=
    [⟨"m_done",1⟩, ⟨"m_rdata",64⟩, ⟨"m_busy",1⟩,
     ⟨"gp_done",1⟩, ⟨"gp_rdata",32⟩, ⟨"gp_busy",1⟩,
     ⟨"cmd_valid",1⟩, ⟨"cmd_idx",7⟩, ⟨"cmd_data",32⟩,
     ⟨"res_kill",1⟩, ⟨"doorbell",1⟩, ⟨"hold",1⟩, ⟨"sc_fail",1⟩]

/-! ## D19 — the sync-read (block RAM) obligation

`rf`, `dmem` and `uart_mem` must be read *only* through a register-latch
site, or `yosys` demotes them to distributed LUTRAM and the dual core does
not fit an XC7Z020 (`Loom/Hw/D19_SPEC.md`). The obligation is one
kernel-reducible Boolean per memory, discharged here and re-checked by
every emit path in `Emit.lean` (the D12/D13/D14 pattern).

`rx_mem` is deliberately *not* in the list: the UART_RX load reads it
combinationally inside the `rf` write data, so it stays LUTRAM — 256x8,
which is the right implementation for it anyway. -/
def syncReadMems : List String := ["rf", "dmem", "uart_mem"]

/-- The D19 check over `syncReadMems`. -/
def syncReadOk : Bool := syncReadMems.all (fun m => design.syncReadOkB m)

/-- Human-readable D19 report (one line per declared memory). -/
def syncReadReport : String :=
  String.intercalate "\n" (design.mems.map (fun md => design.syncReadReport md.name))

end Machines.Lnp64mini
