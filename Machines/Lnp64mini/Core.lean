-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

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

/-- Shared read-port addresses: S_RD2 → rs3/rs4, else rs1/rs2. -/
def r1a : Expr 5 := .mux (.eq st (L5 S_RD2)) rs3f rs1f
def r2a : Expr 5 := .mux (.eq st (L5 S_RD2)) rs4f rs2f

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

def is_alu : Expr 1 :=
  [0x04,0x02,0x10,0x11,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,
   0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0x1d,0x1e,0xd0,
   0xad,0xae,0xaf,0xb0,0xb1,0xb2,0xb8,0xb9,0xba,0xb6,0xb7,0xb4].foldr
    (fun n acc => .or (opIs n) acc) (L1 0)

def is_load : Expr 1 :=
  [0x30,0x31,0x05,0x36,0x09,0x32,0x08].foldr
    (fun n acc => .or (opIs n) acc) (L1 0)
def is_store : Expr 1 :=
  [0x33,0x34,0x37,0x35].foldr (fun n acc => .or (opIs n) acc) (L1 0)
/-- is_branch: op in [0x21,0x26]. -/
def is_branch : Expr 1 :=
  [0x21,0x22,0x23,0x24,0x25,0x26].foldr
    (fun n acc => .or (opIs n) acc) (L1 0)
def is_lr : Expr 1 :=
  .or (opIs 0xc5) (.or (opIs 0xc7) (opIs 0xc9))
def is_sc : Expr 1 :=
  .or (opIs 0xc6) (.or (opIs 0xc8) (opIs 0xca))
/-- is_fence: op==0xcd || (0xd1<=op<=0xd4). -/
def is_fence : Expr 1 :=
  .or (opIs 0xcd) ([0xd1,0xd2,0xd3,0xd4].foldr
    (fun n acc => .or (opIs n) acc) (L1 0))
/-- is_sel: 0x40<=op<=0x45. -/
def is_sel : Expr 1 :=
  [0x40,0x41,0x42,0x43,0x44,0x45].foldr
    (fun n acc => .or (opIs n) acc) (L1 0)
def is_div : Expr 1 :=
  .or (opIs 0x13) (.or (opIs 0xa7) (.or (opIs 0xa8) (opIs 0xa9)))
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

/-- CTZ: lowest set bit index (64 if a==0). Downward scan, index 0 outermost. -/
def ctzE : Expr 64 :=
  (List.range 64).foldr
    (fun i acc => .mux (.eq (.slice a i 1) (L1 1)) (L64 i) acc)
    (L64 64)

def aluE : Expr 64 :=
  .mux (opIs 0x02) a <|
  .mux (opIs 0x10) (.add a b) <|
  .mux (opIs 0x11) (.sub a b) <|
  .mux (opIs 0x04) (.or (.zext (.slice a 0 32) 64) (.shl (.zext (.slice imm_i 0 32) 64) (L64 32))) <|
  .mux (opIs 0x14) (.and a b) <|
  .mux (opIs 0x15) (.or a b) <|
  .mux (opIs 0x16) (.xor a b) <|
  .mux (opIs 0x17) (.not a) <|
  .mux (opIs 0x18) (.shl a (.zext shamt_r 64)) <|
  .mux (opIs 0x19) (.shr a (.zext shamt_r 64)) <|
  .mux (opIs 0x1a) (asr a shamt_r) <|
  .mux (opIs 0x1b) (.mux (.slt a b) (L64 1) (L64 0)) <|
  .mux (opIs 0x1c) (.mux (.ult a b) (L64 1) (L64 0)) <|
  .mux (opIs 0xa0) (.add a imm_i) <|
  .mux (opIs 0xa1) (.and a imm_i) <|
  .mux (opIs 0xa2) (.or a imm_i) <|
  .mux (opIs 0xa3) (.xor a imm_i) <|
  .mux (opIs 0xa4) (.shl a (.zext shamt_i 64)) <|
  .mux (opIs 0xa5) (.shr a (.zext shamt_i 64)) <|
  .mux (opIs 0xa6) (asr a shamt_i) <|
  .mux (opIs 0x1d) (.mux (.slt a imm_i) (L64 1) (L64 0)) <|
  .mux (opIs 0x1e) (.mux (.ult a imm_i) (L64 1) (L64 0)) <|
  .mux (opIs 0xd0) (.add pc imm_j) <|
  .mux (opIs 0xad) (.sext (.slice a 0 8) 64) <|
  .mux (opIs 0xae) (.sext (.slice a 0 16) 64) <|
  .mux (opIs 0xaf) (.sext (.slice a 0 32) 64) <|
  .mux (opIs 0xb0) (.zext (.slice a 0 8) 64) <|
  .mux (opIs 0xb1) (.zext (.slice a 0 16) 64) <|
  .mux (opIs 0xb2) (.zext (.slice a 0 32) 64) <|
  .mux (opIs 0xb8) bswap16 <|
  .mux (opIs 0xb9) bswap32 <|
  .mux (opIs 0xba) bswap64 <|
  .mux (opIs 0xb4) ctzE <|
  .mux (opIs 0xb6) (.or (.shl a (.zext shamt_r 64)) (.shr a (.zext (negShamt shamt_r) 64))) <|
  .mux (opIs 0xb7) (.or (.shr a (.zext shamt_r 64)) (.shl a (.zext (negShamt shamt_r) 64)))
  (L64 0)
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
  byteRev8 (x : Expr 64) : Expr 64 :=
    (List.range 8).foldl
      (fun acc i => .or acc (.shl (.zext (.slice x (i*8) 8) 64) (L64 ((7-i)*8))))
      (L64 0)

/-! ### branch / sel conditions -/

def br_take : Expr 1 :=
  .mux (opIs 0x21) (.eq a b) <|
  .mux (opIs 0x22) (.not (.eq a b)) <|
  .mux (opIs 0x23) (.slt a b) <|
  .mux (opIs 0x24) (.not (.slt a b)) <|
  .mux (opIs 0x25) (.ult a b) <|
  .mux (opIs 0x26) (.not (.ult a b)) (L1 0)

/-- sel_cond keys on op[2:0] (0x40-0x45). -/
def sel_cond : Expr 1 :=
  let o3 := (.slice op 0 3 : Expr 3)
  .mux (.eq o3 (.lit (BitVec.ofNat 3 0))) (.eq a b) <|
  .mux (.eq o3 (.lit (BitVec.ofNat 3 1))) (.not (.eq a b)) <|
  .mux (.eq o3 (.lit (BitVec.ofNat 3 2))) (.slt a b) <|
  .mux (.eq o3 (.lit (BitVec.ofNat 3 3))) (.not (.slt a b)) <|
  .mux (.eq o3 (.lit (BitVec.ofNat 3 4))) (.ult a b) (.not (.ult a b))

/-! ### load writeback / store merge -/

def mem_src : Expr 64 := .mux (.eq st (L5 S_L1)) dmem_rd ddr_q
def lw_shift : Expr 64 := .shr mem_src (.shl (.zext ld_boff_q 64) (L64 3))

def ld_wb : Expr 64 :=
  .mux (.eq ld_op_q (L8 0x30)) mem_src <|
  .mux (.eq ld_op_q (L8 0x31)) (.zext (.slice lw_shift 0 32) 64) <|
  .mux (.eq ld_op_q (L8 0x05)) (.sext (.slice lw_shift 0 32) 64) <|
  .mux (.eq ld_op_q (L8 0x36)) (.zext (.slice lw_shift 0 16) 64) <|
  .mux (.eq ld_op_q (L8 0x09)) (.sext (.slice lw_shift 0 16) 64) <|
  .mux (.eq ld_op_q (L8 0x32)) (.zext (.slice lw_shift 0 8) 64) <|
  .mux (.eq ld_op_q (L8 0x08)) (.sext (.slice lw_shift 0 8) 64) mem_src

def st_width : Expr 4 :=
  .mux (opIs 0x35) (.lit (BitVec.ofNat 4 1)) <|
  .mux (opIs 0x37) (.lit (BitVec.ofNat 4 2)) <|
  .mux (opIs 0x34) (.lit (BitVec.ofNat 4 4)) (.lit (BitVec.ofNat 4 8))

/-- st_merge: overlay b bytes into mem_src by byte lane. Build byte-by-byte:
lane bi takes b[(bi-st_boff)] if st_boff <= bi < st_boff+st_width. -/
def st_merge : Expr 64 :=
  (List.range 8).foldl (fun acc bi =>
    let boffN := (.zext st_boff 32 : Expr 32)
    let inRange : Expr 1 :=
      .and (.not (.ult (.lit (BitVec.ofNat 32 bi)) boffN))
           (.ult (.lit (BitVec.ofNat 32 bi)) (.add boffN (.zext st_width 32)))
    -- source byte index (bi - st_boff), as shift amount into b
    let srcByte : Expr 64 := .shr b (.shl (.sub (.lit (BitVec.ofNat 64 bi)) (.zext st_boff 64)) (L64 3))
    let laneVal : Expr 64 := .shl (.zext (.slice srcByte 0 8) 64) (L64 (bi*8))
    let laneMask : Expr 64 := .lit (BitVec.ofNat 64 (0xFF <<< (bi*8)))
    .mux inRange (.or (.and acc (.not laneMask)) laneVal) acc)
    mem_src

/-! ### div abs helpers -/

def div_a_abs : Expr 64 :=
  .mux (.and div_sgn (.eq (.slice a 63 1) (L1 1))) (.add (.not a) (L64 1)) a
def div_b_abs : Expr 64 :=
  .mux (.and div_sgn (.eq (.slice b 63 1) (L1 1))) (.add (.not b) (L64 1)) b

/-! ### scheduler bitmaps / priority encoders -/

/-- ready bitmap as a 32-bit Expr (bit i = tstate_i == 1). -/
def readyBm : Expr 32 :=
  (List.finRange NT).foldl
    (fun acc i => .or acc (.shl (.zext (.eq (tstate i) (L2 1)) 32) (.lit (BitVec.ofNat 32 i.val))))
    (.lit 0)
def freeBm : Expr 32 :=
  (List.finRange NT).foldl
    (fun acc i => .or acc (.shl (.zext (.eq (tstate i) (L2 0)) 32) (.lit (BitVec.ofNat 32 i.val))))
    (.lit 0)

/-- rbm2 = ({ready,ready} >> (cur+1))[63:0]. -/
def rbm2 : Expr 64 :=
  .shr (.or (.zext readyBm 64) (.shl (.zext readyBm 64) (L64 32)))
       (.zext (.add cur (L5 1)) 64)

/-- Downward scan over rbm2[31:0]: lowest set bit index wins (0 outermost). -/
def nr_off : Expr 5 :=
  (List.range NT).foldr
    (fun i acc => .mux (.eq (.slice rbm2 i 1) (L1 1)) (L5 i) acc) (L5 0)
def nr_any : Expr 1 :=
  (List.range NT).foldr
    (fun i acc => .or (.slice rbm2 i 1) acc) (L1 0)
def fs_off : Expr 5 :=
  (List.range NT).foldr
    (fun i acc => .mux (.eq (.slice freeBm i 1) (L1 1)) (L5 i) acc) (L5 0)
def hf_c : Expr 1 :=
  (List.range NT).foldr
    (fun i acc => .or (.slice freeBm i 1) acc) (L1 0)

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

/-- running ∧ ¬halted ∧ ¬zeroing — the FSM enable. -/
def fsmEn : Expr 1 := .and running (.and (.not halted) (.not zeroing))

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
  ]
where
  mulDoneWd : Expr 64 :=
    .mux (.eq mul_kind (L2 0)) (.slice mul_acc 0 64) <|
    .mux (.eq mul_kind (L2 1))
      (.sub (.sub (.slice mul_acc 64 64) (.mux (.eq (.slice a 63 1) (L1 1)) b (L64 0)))
            (.mux (.eq (.slice b 63 1) (L1 1)) a (L64 0)))
      (.slice mul_acc 64 64)
  divDoneWd : Expr 64 :=
    .mux div_isrem (.mux div_negr (.add (.not div_rem) (L64 1)) div_rem)
                   (.mux div_negq (.add (.not div_quo) (L64 1)) div_quo)

/-- Fold the triples: last matching guard wins. -/
def rfWeE : Expr 1 := rfTriples.foldl (fun acc (g,_,_) => .or acc g) (L1 0)
def rfWaE : Expr 10 := rfTriples.foldl (fun acc (g,wa,_) => .mux g wa acc) (.lit 0)
def rfWdE : Expr 64 := rfTriples.foldl (fun acc (g,_,wd) => .mux g wd acc) (L64 0)

/-! ## Rules -/

/-- (1) registered priority encoders (separate always block). -/
def encRule : Rule :=
  ⟨"enc", .seq (.write 5 "next_ready" (.mux nr_any (.add (.add cur (L5 1)) nr_off) cur))
    (.seq (.write 5 "free_slot" fs_off) (.write 1 "has_free" hf_c))⟩

/-- (2) serialized sleep scan (per-element). -/
def sleepScanRule : Rule :=
  ⟨"sleepdec", .ite (.and running (.not halted))
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
    [("dmem_we",1),("core_rd",1),("core_wr",1),("jtag_wr",1),("jtag_rd",1),("gp_rd",1),("gp_wr",1)].foldr
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

/-- guard: fsmEn ∧ st==X. -/
def stG (x : Nat) (a : Act) : Act := .ite (.and fsmEn (.eq st (L5 x))) a .skip

/-- DATA_BASE + (word-aligned) ea, as a 32-bit core_addr. -/
def ddrEa (ea : Expr 64) : Expr 32 :=
  .add (.lit (BitVec.ofNat 32 DATA_BASE)) (.shl (.slice ea 3 29 |> fun w => .zext w 32) (.lit (BitVec.ofNat 32 3)))
def ddrPc : Expr 32 := .add (.lit (BitVec.ofNat 32 DATA_BASE)) (.slice pc 0 32)

def retireInc : Act := .write 32 "retire" (.add retire (.lit (BitVec.ofNat 32 1)))
def goF0 : Act := .write 5 "st" (L5 S_F0)
def stepPc : Act := .write 64 "pc" pc8

/-- if/else-if chain link: `gchain g a rest` = if g then a else rest. -/
def gchain (g : Expr 1) (a rest : Act) : Act := .ite g a rest

/-- Right-nested sequence of a list of actions. -/
def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

/-! ### S_EX helpers (dynamic per-thread writes; scheduler switches) -/

def setPcFromTpc (idx : Expr 5) : Act :=
  (List.finRange NT).foldr (fun i acc =>
    .ite (.eq idx (L5 i.val)) (.write 64 "pc" (tpc i)) acc) .skip
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
/-- dynamic tstate[idx]==v test as a mux chain. -/
def tstateEq (idx : Expr 5) (v : Expr 2) : Expr 1 :=
  (List.finRange NT).foldr (fun i acc =>
    .mux (.eq idx (L5 i.val)) (.eq (tstate i) v) acc) (L1 0)
/-- any thread not FREE. -/
def anyLive : Expr 1 :=
  (List.finRange NT).foldr (fun i acc => .or (.not (.eq (tstate i) (L2 0))) acc) (L1 0)

/-- FUTEX_WAKE: wake lowest-indexed matching FUTEX threads, up to count a.
per-element guard: tstate_i==3 ∧ tfutex_i==rdval ∧ (matches-before-i < a). -/
def futexWakeBody : Act :=
  (List.finRange NT).foldr (fun i acc =>
    let matchesBefore : Expr 64 :=
      (List.range i.val).foldl (fun s j =>
        .add s (.zext (.and (.eq (.reg 2 s!"tstate{j}") (L2 3))
                            (.eq (.reg 64 s!"tfutex{j}") rdval)) 64)) (L64 0)
    .seq (.ite (.and (.eq (tstate i) (L2 3))
                 (.and (.eq (tfutex i) rdval) (.ult matchesBefore a)))
            (.write 2 s!"tstate{i.val}" (L2 1)) .skip) acc) .skip

def s_f0 : Rule := ⟨"S_F0", stG S_F0
  (.ite bus_req (.write 5 "st" (L5 S_PAUSE))
    (.seq (.write 32 "core_addr" ddrPc) (.seq (.write 1 "core_rd" (L1 1)) (.write 5 "st" (L5 S_FW)))))⟩

def s_pause : Rule := ⟨"S_PAUSE", stG S_PAUSE (.ite (.not bus_req) goF0 .skip)⟩

def s_fw : Rule := ⟨"S_FW", stG S_FW
  (.ite mDone (.seq (.write 64 "ir" mRdata) (.write 5 "st" (L5 S_RD))) .skip)⟩

def s_rd : Rule := ⟨"S_RD", stG S_RD
  (.seq (.write 64 "a" (.mux (.eq rs1f (L5 0)) (L64 0) (.memRead 64 "rf" (cat55 cur r1a))))
    (.seq (.write 64 "b" (.mux (.eq rs2f (L5 0)) (L64 0) (.memRead 64 "rf" (cat55 cur r2a))))
      (.seq (.write 64 "rdval" (.mux (.eq rdf (L5 0)) (L64 0) (.memRead 64 "rf" (cat55 cur rdf))))
            (.write 5 "st" (.mux is_sel (L5 S_RD2) (L5 S_EX))))))⟩

def s_rd2 : Rule := ⟨"S_RD2", stG S_RD2
  (.seq (.write 64 "sel_t" (.mux (.eq rs3f (L5 0)) (L64 0) (.memRead 64 "rf" (cat55 cur r1a))))
    (.seq (.write 64 "sel_f" (.mux (.eq rs4f (L5 0)) (L64 0) (.memRead 64 "rf" (cat55 cur r2a))))
          (.write 5 "st" (L5 S_EX))))⟩

/-- S_EX: nested if-else priority tree mirroring the Verilog (rf writes in
funnel; here: pc/retire/st/scheduler-array/master-handshake side effects). -/
def s_ex_body : Act :=
  -- 0x3a EXIT
  gchain (opIs 0x3a) (.seq (.write 1 "halted" (L1 1)) (.seq (.write 1 "running" (L1 0)) retireInc)) <|
  -- 0x3b THREAD_EXIT
  gchain (opIs 0x3b)
    (.seq (tstateDynWrite (L2 0) cur)
      (.seq (.ite (.not (.eq next_ready cur))
              (.seq (.write 5 "cur" next_ready) (.seq (setPcFromTpc next_ready) goF0))
              (.write 5 "st" (L5 S_WAIT)))
            retireInc)) <|
  -- 0x00 NOP
  gchain (opIs 0x00) (.seq stepPc (.seq retireInc goF0)) <|
  -- fence
  gchain is_fence (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x12 MUL
  gchain (opIs 0x12)
    (.seq (.write 128 "mul_acc" (.lit (BitVec.ofNat 128 0)))
      (.seq (.write 128 "mul_aw" (.zext a 128))
        (.seq (.write 64 "mul_b" b) (.seq (.write 2 "mul_kind" (L2 0)) (.write 5 "st" (L5 S_MUL)))))) <|
  -- mulh
  gchain is_mulh
    (.seq (.write 128 "mul_acc" (.lit (BitVec.ofNat 128 0)))
      (.seq (.write 128 "mul_aw" (.zext a 128))
        (.seq (.write 64 "mul_b" b)
          (.seq (.write 2 "mul_kind" (.mux (opIs 0xaa) (L2 1) (L2 2))) (.write 5 "st" (L5 S_MUL)))))) <|
  -- div
  gchain is_div
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
  gchain is_sel (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x54 GET_PCR
  gchain (opIs 0x54)
    (.ite (.eq rs1f (L5 2)) (.seq stepPc (.seq retireInc goF0))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))) <|
  -- alu
  gchain is_alu (.seq stepPc (.seq retireInc goF0)) <|
  -- 0x20 J
  gchain (opIs 0x20) (.seq (.write 64 "pc" (.add pc (.shl imm_j (L64 3)))) (.seq retireInc goF0)) <|
  -- 0x27 JAL
  gchain (opIs 0x27) (.seq (.write 64 "pc" (.add pc (.shl imm_j (L64 3)))) (.seq retireInc goF0)) <|
  -- 0x28 JALR
  gchain (opIs 0x28) (.seq (.write 64 "pc" (.add a imm_i)) (.seq retireInc goF0)) <|
  -- branch
  gchain is_branch (.seq (.write 64 "pc" (.mux br_take (.add pc (.shl imm_s (L64 3))) pc8)) (.seq retireInc goF0)) <|
  -- 0x06 YIELD
  gchain (opIs 0x06)
    (.seq (.ite (.eq next_ready cur) stepPc
            (.seq (tpcDynWrite cur pc8) (.seq (.write 5 "cur" next_ready) (setPcFromTpc next_ready))))
          (.seq retireInc goF0)) <|
  -- 0x07 SLEEP
  gchain (opIs 0x07)
    (.seq (tpcDynWrite cur pc8)
      (.seq (tstateDynWrite (L2 2) cur)
        (.seq (tsleepDynWrite cur (.mux (.eq a (L64 0)) (L64 1) a))
          (.seq (.ite (.not (.eq next_ready cur))
                  (.seq (.write 5 "cur" next_ready) (.seq (setPcFromTpc next_ready) goF0))
                  (.write 5 "st" (L5 S_WAIT)))
                retireInc)))) <|
  -- 0xcb FUTEX_WAIT
  gchain (opIs 0xcb)
    (.seq (.write 32 "core_addr" (.add (.lit (BitVec.ofNat 32 DATA_BASE)) (.shl (.zext (.slice rdval 3 29) 32) (.lit (BitVec.ofNat 32 3)))))
      (.seq (.write 1 "core_rd" (L1 1))
        (.seq (.write 64 "futex_addr_q" rdval) (.seq (.write 64 "futex_exp" a) (.write 5 "st" (L5 S_FTX1)))))) <|
  -- 0xcc FUTEX_WAKE (per-element wake; count via matches-before-i < a)
  gchain (opIs 0xcc) (.seq futexWakeBody (.seq stepPc (.seq retireInc goF0))) <|
  -- 0x59 CLONE
  gchain (opIs 0x59)
    (.ite has_free
      (.seq (tpcDynWrite free_slot a)
        (.seq (tstateDynWrite (L2 1) free_slot)
          (.seq (.write 5 "clone_dst" rdf) (.seq (.write 5 "clone_tid" free_slot) (.write 5 "st" (L5 S_CLONE2))))))
      (.seq stepPc (.seq retireInc goF0))) <|
  -- LR
  gchain is_lr
    (actSeq [.write 64 "lr_addr" a, .write 1 "lr_valid" (L1 1),
      .write 3 "ld_boff_q" (.lit (BitVec.ofNat 3 0)), .write 8 "ld_op_q" (L8 0x30),
      .write 5 "ld_rd_q" rdf, .write 1 "mem_is_store" (L1 0),
      .ite (.ult a (L64 0x1000))
        (actSeq [.write 9 "dmem_a" (.slice a 3 9), .write 5 "st" (L5 S_L0)])
        (actSeq [.write 32 "core_addr" (ddrEa a), .write 1 "core_rd" (L1 1), .write 5 "st" (L5 S_DL)])]) <|
  -- SC
  gchain is_sc
    (.seq (.ite (.and lr_valid (.eq lr_addr a))
            (.ite (.ult a (L64 0x1000))
              (.seq (.write 1 "dmem_we" (L1 1)) (.seq (.write 9 "dmem_a" (.slice a 3 9)) (.seq (.write 64 "dmem_wd" b) (.seq stepPc (.seq retireInc goF0)))))
              (.seq (.write 32 "core_addr" (ddrEa a)) (.seq (.write 64 "core_wdata" b) (.seq (.write 1 "core_wr" (L1 1)) (.write 5 "st" (L5 S_DSW))))))
            (.seq stepPc (.seq retireInc goF0)))
          (.write 1 "lr_valid" (L1 0))) <|
  -- UART_RX load
  gchain (.and is_load (.eq mem_ea_l (L64 UART_RX_ADDR)))
    (.seq (.ite (.not (.eq rx_rptr rx_wptr)) (.write 9 "rx_rptr" (.add rx_rptr (.lit (BitVec.ofNat 9 1)))) .skip)
          (.seq stepPc (.seq retireInc goF0))) <|
  -- GP load
  gchain (.and is_load l_is_gp)
    (.ite (opIs 0x31)
      (.seq (.write 32 "gp_addr_r" (.and (.slice mem_ea_l 0 32) (.lit (BitVec.ofNat 32 0xFFFFFFFC))))
        (.seq (.write 1 "gp_rd" (L1 1)) (.seq (.write 5 "ld_rd_q" rdf) (.write 5 "st" (L5 S_GPL)))))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))) <|
  -- zp load
  gchain (.and is_load l_is_zp)
    (.seq (.write 9 "dmem_a" ld_widx) (.seq (.write 3 "ld_boff_q" ld_boff)
      (.seq (.write 8 "ld_op_q" op) (.seq (.write 5 "ld_rd_q" rdf) (.seq (.write 1 "mem_is_store" (L1 0)) (.write 5 "st" (L5 S_L0))))))) <|
  -- DDR load
  gchain is_load
    (.seq (.write 32 "core_addr" (ddrEa mem_ea_l)) (.seq (.write 1 "core_rd" (L1 1))
      (.seq (.write 3 "ld_boff_q" ld_boff) (.seq (.write 8 "ld_op_q" op) (.seq (.write 5 "ld_rd_q" rdf) (.seq (.write 1 "mem_is_store" (L1 0)) (.write 5 "st" (L5 S_DL)))))))) <|
  -- UART store
  gchain (.and is_store (.eq mem_ea_s (L64 UART_ADDR)))
    (.seq (.memWrite 8 8 "uart_mem" 0 (.slice uart_wptr 0 8) (.slice b 0 8))
      (.seq (.write 9 "uart_wptr" (.add uart_wptr (.lit (BitVec.ofNat 9 1)))) (.seq stepPc (.seq retireInc goF0)))) <|
  -- GP store
  gchain (.and is_store s_is_gp)
    (.ite (opIs 0x34)
      (.seq (.write 32 "gp_addr_r" (.and (.slice mem_ea_s 0 32) (.lit (BitVec.ofNat 32 0xFFFFFFFC))))
        (.seq (.write 32 "gp_wdata_r" (.slice b 0 32)) (.seq (.write 1 "gp_wr" (L1 1)) (.write 5 "st" (L5 S_GPS)))))
      (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))) <|
  -- zp store
  gchain (.and is_store s_is_zp)
    (.seq (.write 9 "dmem_a" st_widx) (.seq (.write 1 "mem_is_store" (L1 1)) (.write 5 "st" (L5 S_L0)))) <|
  -- DDR store
  gchain is_store
    (.seq (.write 32 "core_addr" (ddrEa mem_ea_s)) (.seq (.write 1 "core_rd" (L1 1)) (.seq (.write 1 "mem_is_store" (L1 1)) (.write 5 "st" (L5 S_DL))))) <|
  -- default trap
  (.seq (.write 1 "trap_active" (L1 1)) (.seq (.write 8 "trapped_op" op) (.write 5 "st" (L5 S_TRAP))))

def s_ex : Rule := ⟨"S_EX", stG S_EX s_ex_body⟩

def s_l0 : Rule := ⟨"S_L0", stG S_L0 (.write 5 "st" (L5 S_L1))⟩

/-- S_L1: load-wb (rf in funnel) or store commit; then advance. -/
def s_l1 : Rule := ⟨"S_L1", stG S_L1
  (actSeq [.ite (.not mem_is_store) .skip
            (actSeq [.write 1 "dmem_we" (L1 1), .write 9 "dmem_a" st_widx, .write 64 "dmem_wd" st_merge]),
           stepPc, retireInc, goF0])⟩

def s_dl : Rule := ⟨"S_DL", stG S_DL
  (.ite mDone (.seq (.write 64 "ddr_q" mRdata) (.write 5 "st" (L5 S_DST))) .skip)⟩

/-- S_DST: load-wb (rf in funnel) + advance, or issue the DDR store. -/
def s_dst : Rule := ⟨"S_DST", stG S_DST
  (.ite (.not mem_is_store)
    (actSeq [stepPc, retireInc, goF0])
    (actSeq [.write 32 "core_addr" (ddrEa mem_ea_s), .write 64 "core_wdata" st_merge,
             .write 1 "core_wr" (L1 1), .write 5 "st" (L5 S_DSW)]))⟩

def s_dsw : Rule := ⟨"S_DSW", stG S_DSW
  (.ite mDone (actSeq [stepPc, retireInc, goF0]) .skip)⟩

/-- S_CLONE2: child sp (rf in funnel) + fresh tp/sigmask + advance. -/
def s_clone2 : Rule := ⟨"S_CLONE2", stG S_CLONE2
  (actSeq [tp_arrDynWrite clone_tid (L64 0), sigmaskDynWrite clone_tid (L64 0),
           .write 5 "st" (L5 S_CLONE3)])⟩

def s_clone3 : Rule := ⟨"S_CLONE3", stG S_CLONE3 (actSeq [stepPc, retireInc, goF0])⟩

/-- S_FTX1: FUTEX_WAIT DDR-compare. -/
def s_ftx1 : Rule := ⟨"S_FTX1", stG S_FTX1
  (.ite mDone
    (actSeq [.ite (.eq mRdata futex_exp)
              (actSeq [tpcDynWrite cur pc8, tstateDynWrite (L2 3) cur, tfutexDynWrite cur futex_addr_q,
                       .ite (.not (.eq next_ready cur))
                         (actSeq [.write 5 "cur" next_ready, setPcFromTpc next_ready, goF0])
                         (.write 5 "st" (L5 S_WAIT))])
              (actSeq [stepPc, goF0]),
             retireInc])
    .skip)⟩

/-- S_WAIT: pick next ready or halt if all free. -/
def s_wait : Rule := ⟨"S_WAIT", stG S_WAIT
  (.ite (tstateEq next_ready (L2 1))
    (actSeq [.write 5 "cur" next_ready, setPcFromTpc next_ready, goF0])
    (.ite (.not anyLive) (.seq (.write 1 "halted" (L1 1)) (.write 1 "running" (L1 0))) .skip))⟩

/-- S_MUL: shift-add step or done (rf in funnel). -/
def s_mul : Rule := ⟨"S_MUL", stG S_MUL
  (.ite (.eq mul_b (L64 0))
    (actSeq [stepPc, retireInc, goF0])
    (actSeq [.ite (.eq (.slice mul_b 0 1) (L1 1)) (.write 128 "mul_acc" (.add mul_acc mul_aw)) .skip,
             .write 128 "mul_aw" (.shl mul_aw (.lit (BitVec.ofNat 128 1))),
             .write 64 "mul_b" (.shr mul_b (L64 1))]))⟩

/-- S_DIV: restoring divide step or done (rf in funnel). 65-bit partial. -/
def s_div : Rule := ⟨"S_DIV", stG S_DIV
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
       .write 7 "div_cnt" (.add div_cnt (.lit (BitVec.ofNat 7 1)))]))⟩

def s_gpl : Rule := ⟨"S_GPL", stG S_GPL
  (.ite gpDone (actSeq [stepPc, retireInc, goF0]) .skip)⟩
def s_gps : Rule := ⟨"S_GPS", stG S_GPS
  (.ite gpDone (actSeq [stepPc, retireInc, goF0]) .skip)⟩

/-- S_TRAP: hold. default state: go F0. -/
def s_default : Rule := ⟨"S_default", .ite (.and fsmEn (.ult (L5 S_GPS) st)) goF0 .skip⟩

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
   ⟨"dmem_addr_j",32,0⟩, ⟨"dmem_lo_j",32,0⟩, ⟨"reg_rd",64,0⟩]

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
     s_f0, s_pause, s_fw, s_rd, s_rd2, s_ex, s_l0, s_l1, s_dl, s_dst, s_dsw,
     s_clone2, s_clone3, s_ftx1, s_wait, s_mul, s_div, s_gpl, s_gps, s_default,
     rfFunnelRule]
  inputs :=
    [⟨"m_done",1⟩, ⟨"m_rdata",64⟩, ⟨"m_busy",1⟩,
     ⟨"gp_done",1⟩, ⟨"gp_rdata",32⟩, ⟨"gp_busy",1⟩,
     ⟨"cmd_valid",1⟩, ⟨"cmd_idx",7⟩, ⟨"cmd_data",32⟩]

end Machines.Lnp64mini
