-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Core

/-!
# Lnp64mini ISS — the cycle-accurate fast mirror

`MiniSt` holds every register of the Verilog core; `step : MiniSt → MiniIn
→ MiniSt` mirrors the single `always @(posedge sysclk)` block top-to-bottom
with the pre-state discipline (all reads from `s`, writes build `s'`; the
blocking regfile temps `rf_we/rf_wa/rf_wd` become locals exactly as in the
Verilog). This is the oracle the EDSL Design is lockstepped against.
-/

namespace Machines.Lnp64mini

open Loom.Hw

/-! ## Inputs -/

structure MiniIn where
  mDone    : Bool := false
  mRdata   : BitVec 64 := 0
  mBusy    : Bool := false
  gpDone   : Bool := false
  gpRdata  : BitVec 32 := 0
  gpBusy   : Bool := false
  cmdValid : Bool := false
  cmdIdx   : Nat  := 0
  cmdData  : BitVec 32 := 0
  -- SMP extensions (DUAL_SPEC.md): all inert at `false`.
  resKill  : Bool := false
  doorbell : Bool := false
  -- EXT-4: the key the doorbell wakes on (park/wake directory).
  doorbellKey : BitVec 64 := 0
  hold     : Bool := false
  scFail   : Bool := false
  deriving Repr

/-! ## State -/

structure MiniSt where
  cur       : BitVec 5  := 0
  pc        : BitVec 64 := BitVec.ofNat 64 TEXT_BASE
  retire    : BitVec 32 := 0
  -- EXT-8: the commit-trace ring (see Core.lean). 16 entries of
  -- {op[7:0], 24'b0, pc[31:0]} and the writeback value.
  trace_wp  : BitVec 4  := 0
  trace_sel : BitVec 4  := 0
  trace_hit : Bool := false
  trace_in_pc : BitVec 64 := 0
  trace_in_wb : BitVec 64 := 0
  trace_rd_pc : BitVec 64 := 0
  trace_rd_wb : BitVec 64 := 0
  trace_pc  : Array (BitVec 64) := Array.replicate 16 0
  trace_wb  : Array (BitVec 64) := Array.replicate 16 0
  running   : Bool := false
  halted    : Bool := false
  st        : BitVec 5  := 0
  ir        : BitVec 64 := 0
  a         : BitVec 64 := 0
  b         : BitVec 64 := 0
  rdval     : BitVec 64 := 0
  sel_t     : BitVec 64 := 0
  sel_f     : BitVec 64 := 0
  mem_is_store : Bool := false
  trap_active  : Bool := false
  trapped_op   : BitVec 8 := 0
  core_rd   : Bool := false
  core_wr   : Bool := false
  core_addr : BitVec 32 := 0
  -- EXT-9: the I-cache (CACHE_PLAN.md). 4096 x 64 data + 4096 x 18 tag,
  -- mirrored cycle-exactly because the lockstep compares every declared
  -- coordinate: an ISS that "abstracted" the cache would simply disagree.
  ic_data   : Array (BitVec 64) := Array.replicate 4096 0
  ic_tag    : Array (BitVec 42) := Array.replicate 4096 0
  ic_tag_q  : BitVec 42 := 0
  ic_data_q : BitVec 64 := 0
  -- EXT-9b: O(1) invalidation. A line is live only in the current
  -- generation; a map change bumps the generation instead of walking the
  -- bank. `ic_inv`/`ic_ctr` are the wrap fallback only.
  ic_gen    : BitVec 16 := 0
  ic_inv    : Bool := false
  ic_ctr    : BitVec 12 := 0
  core_wdata: BitVec 64 := 0
  jtag_rd   : Bool := false
  jtag_wr   : Bool := false
  jtag_wdata: BitVec 64 := 0
  ddr_addr_j: BitVec 32 := 0
  ddr_lo_j  : BitVec 32 := 0
  ddr_rd_l  : BitVec 64 := 0
  ddr_q     : BitVec 64 := 0
  bus_req   : Bool := false
  gp_rd     : Bool := false
  gp_wr     : Bool := false
  gp_addr_r : BitVec 32 := 0
  gp_wdata_r: BitVec 32 := 0
  dmem_we   : Bool := false
  dmem_a    : BitVec 9  := 0
  dmem_wd   : BitVec 64 := 0
  dmem_rd   : BitVec 64 := 0
  uart_wptr : BitVec 9  := 0
  uart_ridx : BitVec 8  := 0
  uart_byte : BitVec 8  := 0
  rx_wptr   : BitVec 9  := 0
  rx_rptr   : BitVec 9  := 0
  ld_boff_q : BitVec 3  := 0
  ld_op_q   : BitVec 8  := 0
  ld_rd_q   : BitVec 5  := 0
  lr_addr   : BitVec 64 := 0
  lr_valid  : Bool := false
  futex_exp : BitVec 64 := 0
  futex_addr_q : BitVec 64 := 0
  sleep_scan: BitVec 5  := 0
  next_ready: BitVec 5  := 0
  free_slot : BitVec 5  := 0
  has_free  : Bool := false
  clone_dst : BitVec 5  := 0
  clone_tid : BitVec 5  := 0
  mul_acc   : BitVec 128:= 0
  mul_aw    : BitVec 128:= 0
  mul_b     : BitVec 64 := 0
  mul_kind  : BitVec 2  := 0
  div_rem   : BitVec 64 := 0
  div_quo   : BitVec 64 := 0
  div_d     : BitVec 64 := 0
  div_cnt   : BitVec 7  := 0
  div_isrem : Bool := false
  div_negq  : Bool := false
  div_negr  : Bool := false
  zeroing   : Bool := false
  zctr      : BitVec 10 := 0
  reg_sel   : BitVec 5  := 0
  reg_wsel  : BitVec 5  := 0
  reg_wlo   : BitVec 32 := 0
  dmem_addr_j : BitVec 32 := 0
  dmem_lo_j   : BitVec 32 := 0
  reg_rd    : BitVec 64 := 0
  -- EXT-1 (the preemption tick): reload value and running counter, both 0
  -- (= preemption disabled = the cooperative machine) at power-on.
  quantum   : BitVec 32 := 0
  qctr      : BitVec 32 := 0
  -- EXT-2 (protection domains): the per-thread tag and its observation
  -- mirror. All-zero at power-on = every thread in domain 0.
  tdom      : Array (BitVec 8) := Array.replicate NT 0
  cur_dom   : BitVec 8 := 0
  -- EXT-3 (fail-stop): one bit per thread slot; 0 = nothing poisoned.
  poison    : BitVec 32 := 0
  -- EXT-5 (gates): the host-loaded gate table, the depth-1 per-thread
  -- continuation, and the in-gate bitmap.
  gate_ent  : Array (BitVec 64) := Array.replicate 16 0
  gate_dom  : Array (BitVec 8)  := Array.replicate 16 0
  tcont     : Array (BitVec 64) := Array.replicate NT 0
  tcdom     : Array (BitVec 8)  := Array.replicate NT 0
  in_gate   : BitVec 32 := 0
  gate_sel  : BitVec 4  := 0
  -- EXT-6 (cross-domain transfer): one capability handle addressed to each
  -- domain, plus per-domain occupancy.
  cap_ibox  : Array (BitVec 64) := Array.replicate 16 0
  cap_ival  : BitVec 16 := 0
  -- EXT-7 (§15): the domain-tagged TLB. mmu_en = 0 is bypass.
  mmu_en    : Bool := false
  tlb_sel   : BitVec 3 := 0
  tlb_base  : Array (BitVec 32) := Array.replicate 8 0
  tlb_limit : Array (BitVec 32) := Array.replicate 8 0
  tlb_phys  : Array (BitVec 32) := Array.replicate 8 0
  tlb_dom   : Array (BitVec 8)  := Array.replicate 8 0
  -- EXT-7: valid bits are a bitmap (the shootdown clears several at once).
  tlb_vld   : BitVec 8 := 0
  tlb_cell  : Array (BitVec 8)  := Array.replicate 8 0
  wake_out  : Bool := false
  -- EXT-4: the key this core last woke on (captured on the pulse).
  wake_key  : BitVec 64 := 0
  -- EXT-4: the per-slot wake decision, applied one cycle later so the
  -- comparator bank stays off the critical path (see `wake_bm` in Core).
  wake_bm   : BitVec 32 := 0
  lr_req    : Bool := false
  sc_req    : Bool := false
  sc_pending: Bool := false
  -- arrays
  rf     : Array (BitVec 64) := Array.replicate 1024 0
  dmem   : Array (BitVec 64) := Array.replicate 512 0
  uartMem: Array (BitVec 8)  := Array.replicate 256 0
  rxMem  : Array (BitVec 8)  := Array.replicate 256 0
  -- D37: all-zero at power-on, mirroring the design's `tpc` reset image
  -- (Core.lean). `cmd 13`'s sweep writes TEXT_BASE into every entry before
  -- any read, so this is the same machine; it is now also the machine the
  -- fabric builds (D30 dropped a non-zero distributed-RAM image silently).
  tpc    : Array (BitVec 64) := Array.replicate NT 0
  tstate : Array (BitVec 2)  := (Array.replicate NT 0).set! 0 1
  tsleep : Array (BitVec 64) := Array.replicate NT 0
  tfutex : Array (BitVec 64) := Array.replicate NT 0
  tp_arr : Array (BitVec 64) := Array.replicate NT 0
  sigmask_arr : Array (BitVec 64) := Array.replicate NT 0
  deriving Repr

/-! ## Combinational helpers over the pre-state -/

namespace MiniIss

/-- EXT-7 (§15): the same translation `Core.ddrEa` computes. A hit needs the
entry valid, the VPN equal AND **the domain equal to `tdom[cur]`** -- the
tag is what makes a domain-3 translation unusable by domain 5. A miss under
`mmu_en` fails closed to `DATA_BASE`; with `mmu_en = 0` this is the identity
computation of every earlier increment. -/
def ddrEaOf (s : MiniSt) (ea : BitVec 64) : BitVec 32 :=
  let raw := (BitVec.ofNat 32 DATA_BASE) + ((ea.extractLsb' 3 29).setWidth 32 <<< 3)
  if ¬ s.mmu_en then raw
  else
    -- fully-associative VMA lookup, first match wins (mirrors `priTree`).
    let lo := ea.setWidth 32
    match (List.range 8).find? (fun i =>
            s.tlb_vld.getLsbD i && s.tlb_dom[i]! == s.tdom[s.cur.toNat]! &&
            !(lo < s.tlb_base[i]!) && lo < s.tlb_limit[i]!) with
    -- entries store the DELTA (phys - base), so translation is one add
    | some i => (BitVec.ofNat 32 DATA_BASE) + (lo + s.tlb_phys[i]!)
    | none   => BitVec.ofNat 32 DATA_BASE

def bit {n : Nat} (x : BitVec n) (i : Nat) : Bool := x.getLsbD i

def rfIdx (curV : BitVec 5) (r : BitVec 5) : Nat := (curV.toNat) * 32 + r.toNat

def op   (s : MiniSt) : BitVec 8 := s.ir.extractLsb' 56 8
def rdf  (s : MiniSt) : BitVec 5 := s.ir.extractLsb' 51 5
def rs1f (s : MiniSt) : BitVec 5 := s.ir.extractLsb' 46 5
def rs2f (s : MiniSt) : BitVec 5 := s.ir.extractLsb' 41 5
def rs3f (s : MiniSt) : BitVec 5 := s.ir.extractLsb' 36 5
def rs4f (s : MiniSt) : BitVec 5 := s.ir.extractLsb' 31 5

def imm_i (s : MiniSt) : BitVec 64 := (s.ir.extractLsb' 14 32).signExtend 64
def imm_s (s : MiniSt) : BitVec 64 := (s.ir.extractLsb' 9 32).signExtend 64
def imm_j (s : MiniSt) : BitVec 64 := (s.ir.extractLsb' 19 32).signExtend 64

def shamt_r (s : MiniSt) : Nat := (s.b.extractLsb' 0 6).toNat
def shamt_i (s : MiniSt) : Nat := ((imm_i s).extractLsb' 0 6).toNat
def pc8 (s : MiniSt) : BitVec 64 := s.pc + 8

def opN (s : MiniSt) : Nat := (op s).toNat

-- Mirrors Core.lean's `is_alu` exactly. It did not, and the differences were
-- invisible because no test program executed the affected opcodes:
--   * OP_NOT was MISSING, so `not` wrote no destination register;
--   * raw literals 0x1c, 0xa5, 0xa6, 0x1e survived the renumbering. They were
--     SLTU, LSRI, ASRI and SLTIU under the OLD map; after the move to the ISA
--     numbering those four ops live at 0x26/0x4d/0x4e/0x51 and were no longer
--     recognised as ALU at all, while the stale bytes matched other things.
-- Found by the emulator/ISS differential (`minitest stepop` vs
-- `lnp64 step-op`) on its first run. Keep this list and Core.lean's in step.
def is_alu (s : MiniSt) : Bool :=
  [OP_LIU, OP_MOV, OP_ADD, OP_SUB, OP_AND, OP_OR, OP_XOR, OP_NOT, OP_LSL, OP_LSR, OP_ASR, OP_SLT, OP_SLTU,
   OP_ADDI, OP_ANDI, OP_ORI, OP_XORI, OP_LSLI, OP_LSRI, OP_ASRI, OP_SLTI, OP_SLTIU, OP_AUIPC,
   OP_SEXT_B, OP_SEXT_H, OP_SEXT_W, OP_ZEXT_B, OP_ZEXT_H, OP_ZEXT_W, OP_BSWAP16, OP_BSWAP32, OP_BSWAP64,
   OP_ROL, OP_ROR, OP_CTZ].contains (opN s)
def is_load (s : MiniSt) : Bool :=
  [OP_LD,OP_LD_31,OP_LD_S_70,OP_LD_36,OP_LD_S,OP_LD_32,OP_LD_S_72].contains (opN s)
def is_store (s : MiniSt) : Bool := [OP_ST,OP_ST_34,OP_ST_37,OP_ST_35].contains (opN s)
-- W1.5d: membership, not a RANGE. An opcode's number must not carry
-- semantic grouping, or the numbering cannot be changed.
-- The sixth member was OP_SLTU, not OP_BGEU. This list replaced the range
-- `0x21 <= o <= 0x26`, where 0x26 was BGEU; renumbering moved SLTU onto 0x26
-- and BGEU to 0x68, so the conversion silently captured the wrong opcode --
-- SLTU branched and BGEU did not. Exactly the failure W1.5d's comment below
-- warns about, committed in the same edit that wrote the warning.
def is_branch (s : MiniSt) : Bool := [OP_BEQ, OP_BNE, OP_BLT, OP_BGE, OP_BLTU, OP_BGEU].contains (opN s)
def is_lr (s : MiniSt) : Bool := [OP_LR_D,OP_LR_D_ACQ,OP_LR_D_ACQ_REL].contains (opN s)
def is_sc (s : MiniSt) : Bool := [OP_SC_D,OP_SC_D_REL,OP_SC_D_ACQ_REL].contains (opN s)
def is_fence (s : MiniSt) : Bool := [OP_FENCE, OP_FENCE_D1, OP_FENCE_D2, OP_FENCE_D3, OP_FENCE_D4].contains (opN s)
def is_sel (s : MiniSt) : Bool := [OP_SEL, OP_SEL_41, OP_SEL_42, OP_SEL_43, OP_SEL_44, OP_SEL_45].contains (opN s)
def is_div (s : MiniSt) : Bool := [OP_DIV,OP_UDIV,OP_SREM,OP_UREM].contains (opN s)
def is_mulh (s : MiniSt) : Bool := [OP_MULH,OP_MULHU].contains (opN s)
def div_sgn (s : MiniSt) : Bool := [OP_DIV,OP_SREM].contains (opN s)

/-- arithmetic shift right of a 64-bit value by `sh`. -/
def asr (x : BitVec 64) (sh : Nat) : BitVec 64 := x.sshiftRight sh

def aluV (s : MiniSt) : BitVec 64 :=
  let av := s.a; let bv := s.b
  -- W1.5c: an if-chain rather than `match opN s with`. Lean reads
  -- `| OP_ADD =>` as a BINDER, not the constant, so it matches everything
  -- and shadows every later arm -- which is what blocked the ISA
  -- renumbering from moving these opcodes with the rest.
  if opN s = OP_MOV then av
  else if opN s = OP_ADD then av + bv
  else if opN s = OP_SUB then av - bv
  else if opN s = OP_LIU then (av.extractLsb' 0 32).setWidth 64 ||| (((imm_i s).extractLsb' 0 32).setWidth 64 <<< 32)
  else if opN s = OP_AND then av &&& bv
  else if opN s = OP_OR then av ||| bv
  else if opN s = OP_XOR then av ^^^ bv
  else if opN s = OP_NOT then ~~~ av
  else if opN s = OP_LSL then av <<< shamt_r s
  else if opN s = OP_LSR then av >>> shamt_r s
  else if opN s = OP_ASR then asr av (shamt_r s)
  else if opN s = OP_SLT then if av.slt bv then 1 else 0
  else if opN s = OP_SLTU then if av.ult bv then 1 else 0
  else if opN s = OP_ADDI then av + imm_i s
  else if opN s = OP_ANDI then av &&& imm_i s
  else if opN s = OP_ORI then av ||| imm_i s
  else if opN s = OP_XORI then av ^^^ imm_i s
  else if opN s = OP_LSLI then av <<< shamt_i s
  else if opN s = OP_LSRI then av >>> shamt_i s
  else if opN s = OP_ASRI then asr av (shamt_i s)
  else if opN s = OP_SLTI then if av.slt (imm_i s) then 1 else 0
  else if opN s = OP_SLTIU then if av.ult (imm_i s) then 1 else 0
  else if opN s = OP_AUIPC then s.pc + imm_j s
  else if opN s = OP_SEXT_B then (av.extractLsb' 0 8).signExtend 64
  else if opN s = OP_SEXT_H then (av.extractLsb' 0 16).signExtend 64
  else if opN s = OP_SEXT_W then (av.extractLsb' 0 32).signExtend 64
  else if opN s = OP_ZEXT_B then (av.extractLsb' 0 8).setWidth 64
  else if opN s = OP_ZEXT_H then (av.extractLsb' 0 16).setWidth 64
  else if opN s = OP_ZEXT_W then (av.extractLsb' 0 32).setWidth 64
  else if opN s = OP_BSWAP16 then ((av.extractLsb' 0 8).setWidth 64 <<< 8) ||| (av.extractLsb' 8 8).setWidth 64
  else if opN s = OP_BSWAP32 then
      (List.range 4).foldl (fun acc i =>
        acc ||| ((av.extractLsb' (i*8) 8).setWidth 64 <<< ((3-i)*8))) 0
  else if opN s = OP_BSWAP64 then
      (List.range 8).foldl (fun acc i =>
        acc ||| ((av.extractLsb' (i*8) 8).setWidth 64 <<< ((7-i)*8))) 0
  else if opN s = OP_CTZ then
      -- CTZ: lowest set bit; 64 if a==0. downward scan, lowest wins.
      (List.range 64).foldr (fun i acc => if bit av i then BitVec.ofNat 64 i else acc)
        (BitVec.ofNat 64 64)
  else if opN s = OP_ROL then (av <<< shamt_r s) ||| (av >>> ((0 - (s.b.extractLsb' 0 6)).toNat))
  else if opN s = OP_ROR then (av >>> shamt_r s) ||| (av <<< ((0 - (s.b.extractLsb' 0 6)).toNat))
  else 0

def br_take (s : MiniSt) : Bool :=
  let av := s.a; let bv := s.b
  if opN s = OP_BEQ then av = bv
  else if opN s = OP_BNE then av ≠ bv
  else if opN s = OP_BLT then av.slt bv
  else if opN s = OP_BGE then ¬ av.slt bv
  else if opN s = OP_BLTU then av.ult bv
  else if opN s = OP_BGEU then ¬ av.ult bv
  else false

def sel_cond (s : MiniSt) : Bool :=
  -- Keyed on the OP_ constants, mirroring Core.sel_cond. The old `% 8` keying
  -- was the ISS half of the sel_cond defect: both models wrong TOGETHER under
  -- the scattered spec bytes, so every same-repo differential stayed green.
  let av := s.a; let bv := s.b
  if opN s = OP_SEL then av = bv
  else if opN s = OP_SEL_41 then av ≠ bv
  else if opN s = OP_SEL_42 then av.slt bv
  else if opN s = OP_SEL_43 then ¬ av.slt bv
  else if opN s = OP_SEL_44 then av.ult bv
  else ¬ av.ult bv

def mem_src (s : MiniSt) : BitVec 64 := if s.st = BitVec.ofNat 5 S_L1 then s.dmem_rd else s.ddr_q
def lw_shift (s : MiniSt) : BitVec 64 := mem_src s >>> (s.ld_boff_q.toNat * 8)

def ld_wb (s : MiniSt) : BitVec 64 :=
  let ms := mem_src s; let sh := lw_shift s
  -- W1.5c: if-chain (named opcodes cannot be Lean patterns).
  if s.ld_op_q.toNat = OP_LD then ms
  else if s.ld_op_q.toNat = OP_LD_31 then (sh.extractLsb' 0 32).setWidth 64
  else if s.ld_op_q.toNat = OP_LD_S_70 then (sh.extractLsb' 0 32).signExtend 64
  else if s.ld_op_q.toNat = OP_LD_36 then (sh.extractLsb' 0 16).setWidth 64
  else if s.ld_op_q.toNat = OP_LD_S then (sh.extractLsb' 0 16).signExtend 64
  else if s.ld_op_q.toNat = OP_LD_32 then (sh.extractLsb' 0 8).setWidth 64
  else if s.ld_op_q.toNat = OP_LD_S_72 then (sh.extractLsb' 0 8).signExtend 64
  else ms

def st_width (s : MiniSt) : Nat :=
  if opN s = OP_ST_35 then 1 else if opN s = OP_ST_37 then 2 else if opN s = OP_ST_34 then 4 else 8

def st_boff (s : MiniSt) : Nat := (mem_ea_s s).extractLsb' 0 3 |>.toNat
  where mem_ea_s (s : MiniSt) : BitVec 64 := s.a + imm_s s

def mem_ea_l (s : MiniSt) : BitVec 64 := s.a + imm_i s
def mem_ea_s (s : MiniSt) : BitVec 64 := s.a + imm_s s
def ld_widx (s : MiniSt) : BitVec 9 := (mem_ea_l s).extractLsb' 3 9
def st_widx (s : MiniSt) : BitVec 9 := (mem_ea_s s).extractLsb' 3 9
def ld_boff (s : MiniSt) : BitVec 3 := (mem_ea_l s).extractLsb' 0 3
def l_is_zp (s : MiniSt) : Bool := (mem_ea_l s).ult (BitVec.ofNat 64 0x1000)
def s_is_zp (s : MiniSt) : Bool := (mem_ea_s s).ult (BitVec.ofNat 64 0x1000)
def l_is_gp (s : MiniSt) : Bool :=
  (mem_ea_l s).extractLsb' 16 16 = BitVec.ofNat 16 0xE000 ||
  (mem_ea_l s).extractLsb' 20 12 = BitVec.ofNat 12 0x0A0
def s_is_gp (s : MiniSt) : Bool :=
  (mem_ea_s s).extractLsb' 16 16 = BitVec.ofNat 16 0xE000 ||
  (mem_ea_s s).extractLsb' 20 12 = BitVec.ofNat 12 0x0A0

def st_merge (s : MiniSt) : BitVec 64 :=
  let bo := st_boff s; let w := st_width s
  (List.range 8).foldl (fun acc bi =>
    if bo ≤ bi ∧ bi < bo + w then
      let srcByte := (s.b >>> ((bi - bo)*8)).extractLsb' 0 8
      let mask : BitVec 64 := BitVec.ofNat 64 (0xFF <<< (bi*8))
      (acc &&& ~~~mask) ||| (srcByte.setWidth 64 <<< (bi*8))
    else acc)
    (mem_src s)

def div_a_abs (s : MiniSt) : BitVec 64 :=
  if div_sgn s ∧ bit s.a 63 then (~~~ s.a) + 1 else s.a
def div_b_abs (s : MiniSt) : BitVec 64 :=
  if div_sgn s ∧ bit s.b 63 then (~~~ s.b) + 1 else s.b

/-- next_ready priority encoder (registered value for next cycle). -/
def compute_next_ready (s : MiniSt) : BitVec 5 :=
  -- EXT-3: fail-stop -- a poisoned slot is not READY, so it is never
  -- picked. Same single masking point as `readyBm` in the EDSL.
  let readyBm : BitVec 32 :=
    (~~~ s.poison) &&&
      ((List.range NT).foldl (fun acc i =>
        acc ||| (if s.tstate[i]! = (1 : BitVec 2) then (1#32 <<< i) else 0)) 0)
  let rbm2 : BitVec 64 :=
    (((readyBm.setWidth 64) ||| (readyBm.setWidth 64 <<< 32)) >>> (s.cur + 1).toNat)
  let nr_off : BitVec 5 :=
    (List.range NT).foldr (fun i acc => if rbm2.getLsbD i then BitVec.ofNat 5 i else acc) 0
  let nr_any : Bool := (List.range NT).any (fun i => rbm2.getLsbD i)
  if nr_any then s.cur + 1 + nr_off else s.cur
def compute_free_slot (s : MiniSt) : BitVec 5 :=
  (List.range NT).foldr (fun i acc => if s.tstate[i]! = 0 then BitVec.ofNat 5 i else acc) 0
def compute_has_free (s : MiniSt) : Bool := (List.range NT).any (fun i => s.tstate[i]! = 0)

def hp_core_owns (s : MiniSt) : Bool :=
  s.running && s.st ≠ BitVec.ofNat 5 S_TRAP && s.st ≠ BitVec.ofNat 5 S_WAIT && s.st ≠ BitVec.ofNat 5 S_PAUSE

/-! ## The cycle step -/

/-- rf write helper: set rf at the raw 10-bit index. -/
def rfSetIdx (s' : MiniSt) (idx : BitVec 10) (v : BitVec 64) : MiniSt :=
  { s' with rf := s'.rf.set! idx.toNat v }

/-- One cycle. Mirrors always@(posedge sysclk) top-to-bottom. Blocking rf
temps become `rfWe/rfWa/rfWd` locals; the single funnel write at the end. -/
def step (s : MiniSt) (inp : MiniIn) : MiniSt := Id.run do
  let mut s' := s
  -- blocking single-port regfile temps (default: no write)
  let mut rfWe : Bool := false
  let mut rfWa : BitVec 10 := 0
  let mut rfWd : BitVec 64 := 0
  -- pulse defaults (nonblocking): dmem_we/core_rd/core_wr/jtag_wr/jtag_rd/gp_rd/gp_wr <= 0
  s' := { s' with dmem_we := false, core_rd := false, core_wr := false,
                  jtag_wr := false, jtag_rd := false, gp_rd := false, gp_wr := false,
                  lr_req := false, sc_req := false }
  let localRstn := true   -- wrapper POR handled by reset values; always run.

  -- (1) registered priority encoders (separate always block; pre-state)
  s' := { s' with next_ready := compute_next_ready s, free_slot := compute_free_slot s,
                  has_free := compute_has_free s }

  -- zeroing engine
  if s.zeroing then
    rfWe := true; rfWa := s.zctr.setWidth 10; rfWd := 0
    -- D20: `tpc` is a memory now, so `cmd 13`'s 32-entry reset rides the
    -- zeroing counter (one slot per cycle, done long before the 1024-cycle
    -- sweep ends). Nothing reads `tpc` while `zeroing` is high.
    if s.zctr.toNat < NT then
      s' := { s' with tpc := s'.tpc.set! s.zctr.toNat (BitVec.ofNat 64 TEXT_BASE) }
      -- EXT-2: the same sweep puts every thread in domain 0 (`tdomTriples`
      -- entry 1), which is what makes "the guest is domain 0" hold by
      -- construction rather than by a reset image the flow may not deliver.
      s' := { s' with tdom := s'.tdom.set! s.zctr.toNat 0 }
    -- EXT-5: the reset also clears every open gate.
    if s.zctr.toNat = 0 then s' := { s' with in_gate := 0, cap_ival := 0, tlb_vld := 0 }
    if s.zctr.toNat < 512 then
      s' := { s' with dmem_we := true, dmem_a := s.zctr.setWidth 9, dmem_wd := 0 }
    if s.zctr.toNat = 32*NT - 1 then s' := { s' with zeroing := false }
    else s' := { s' with zctr := s.zctr + 1 }

  -- EXT-9b: the I$ generation bump (O(1) invalidate) and its wrap fallback.
  -- Mirrors icGenRule/icInvRule. The bump fires on any command that changes
  -- the mapping a cached line was filled under, plus the soft reset.
  if inp.cmdValid ∧ (inp.cmdIdx = 63 ∨ inp.cmdIdx = 64 ∨ inp.cmdIdx = 65
                     ∨ inp.cmdIdx = 66 ∨ inp.cmdIdx = 67 ∨ inp.cmdIdx = 68
                     ∨ inp.cmdIdx = 13) then
    if s.ic_gen = 65535 then
      s' := { s' with ic_gen := 0, ic_inv := true, ic_ctr := 0 }
    else
      s' := { s' with ic_gen := s.ic_gen + 1 }
  if s.ic_inv then
    s' := { s' with ic_tag := s'.ic_tag.set! s.ic_ctr.toNat 0 }
    if s.ic_ctr = 4095 then s' := { s' with ic_inv := false, ic_ctr := 0 }
    else s' := { s' with ic_ctr := s.ic_ctr + 1 }

  -- cmd (wr_pulse) surface
  if inp.cmdValid then
    let d := inp.cmdData
    match inp.cmdIdx with
    | 14 => s' := { s' with reg_sel := d.setWidth 5 }
    | 15 => s' := { s' with dmem_addr_j := d }
    | 16 => s' := { s' with dmem_lo_j := d }
    | 17 => s' := { s' with dmem_we := true, dmem_a := s.dmem_addr_j.setWidth 9,
                            dmem_wd := (d.setWidth 64 <<< 32) ||| s.dmem_lo_j.setWidth 64 }
    | 18 => s' := { s' with uart_ridx := d.setWidth 8 }
    | 19 => s' := { s' with rxMem := s'.rxMem.set! (s.rx_wptr.setWidth 8).toNat (d.setWidth 8),
                            rx_wptr := s.rx_wptr + 1 }
    | 40 => s' := { s' with ddr_addr_j := d }
    | 41 => s' := { s' with ddr_lo_j := d }
    | 42 => s' := { s' with jtag_wr := true,
                            jtag_wdata := (d.setWidth 64 <<< 32) ||| s.ddr_lo_j.setWidth 64,
                            ddr_addr_j := s.ddr_addr_j + 8 }
    | 43 => s' := { s' with jtag_rd := true }
    | 50 => s' := { s' with reg_wsel := d.setWidth 5 }
    | 51 => s' := { s' with reg_wlo := d }
    | 52 => if s.reg_wsel ≠ 0 then
              rfWe := true; rfWa := (s.cur ++ s.reg_wsel);
              rfWd := (d.setWidth 64 <<< 32) ||| s.reg_wlo.setWidth 64
    | 53 => s' := { s' with pc := d.setWidth 64 }
    | 54 => if bit d 0 then s' := { s' with trap_active := false, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
    | 55 => s' := { s' with bus_req := bit d 0 }
    -- EXT-1: `CMD_QUANTUM` = 57 (56 is the dual wrapper's CORE1_HOLD, which
    -- never reaches a core). `qctr` is armed from the same word in the
    -- quantum block below, the only writer of that register.
    | 57 => s' := { s' with quantum := d }
    -- EXT-3: `CMD_POISON` = 60, whole-word (the raise is atomic across slots)
    | 60 => s' := { s' with poison := d }
    -- EXT-2: `CMD_SETDOM` = 58. data[4:0] = thread slot, data[15:8] = domain.
    -- EXT-5: cmd 62 selects a gate and sets its domain; cmd 61 loads its entry.
    -- EXT-7: MMU enable, TLB select/fill, and the §15 shootdown.
    | 63 => s' := { s' with mmu_en := bit d 0 }
    | 64 => s' := { s' with tlb_sel := BitVec.ofNat 3 (d.toNat % 8) }
    | 65 => s' := { s' with tlb_base := s'.tlb_base.set! s.tlb_sel.toNat
                              (BitVec.ofNat 32 (d.toNat % 0x1000000)),
                            tlb_dom := s'.tlb_dom.set! s.tlb_sel.toNat
                                         (BitVec.ofNat 8 ((d.toNat >>> 24) % 256)) }
    | 66 => s' := { s' with tlb_limit := s'.tlb_limit.set! s.tlb_sel.toNat d,
                            tlb_vld := s.tlb_vld ||| (1#8 <<< s.tlb_sel.toNat) }
    | 68 => s' := { s' with tlb_phys := s'.tlb_phys.set! s.tlb_sel.toNat
                              (BitVec.ofNat 32 (d.toNat % 0x1000000)),
                            tlb_cell := s'.tlb_cell.set! s.tlb_sel.toNat
                                          (BitVec.ofNat 8 ((d.toNat >>> 24) % 256)) }
    | 67 =>
        -- map.protect / munmap: the cached translation's cell IS the VMA's
        -- cell (§15 line 876), so bumping it kills every entry naming it.
        let cell := BitVec.ofNat 8 (d.toNat % 256)
        for i in List.range 8 do
          if s.tlb_cell[i]! = cell then
            s' := { s' with tlb_vld := s'.tlb_vld &&& ~~~(1#8 <<< i) }
    | 62 => s' := { s' with gate_sel := BitVec.ofNat 4 (d.toNat % 16),
                            gate_dom := s'.gate_dom.set! (d.toNat % 16)
                                          (BitVec.ofNat 8 ((d.toNat >>> 8) % 256)) }
    | 61 => s' := { s' with gate_ent := s'.gate_ent.set! s.gate_sel.toNat (d.setWidth 64) }
    | 58 => s' := { s' with tdom := s'.tdom.set! (d.toNat % NT)
                              (BitVec.ofNat 8 ((d.toNat >>> 8) % 256)) }
    | 13 =>
        if bit d 0 then
          s' := { s' with pc := BitVec.ofNat 64 TEXT_BASE, retire := 0, halted := false,
                          running := false, st := BitVec.ofNat 5 S_IDLE, uart_wptr := 0,
                          rx_rptr := 0, rx_wptr := 0, trap_active := false, cur := 0,
                          lr_valid := false, zeroing := true, zctr := 0,
                          tstate := (Array.replicate NT 0).set! 0 1 }
        if bit d 1 then s' := { s' with running := true, st := BitVec.ofNat 5 S_F0 }
    | _ => pure ()

  -- registered rdata latch for JTAG DDR reads
  if inp.mDone ∧ ¬ hp_core_owns s then s' := { s' with ddr_rd_l := inp.mRdata }

  -- effective hold: only bites at the instruction boundary S_F0
  let holdEff := inp.hold ∧ s.st = BitVec.ofNat 5 S_F0
  -- EXT-1 (the preemption tick): the three predicates of `Core.lean`, over
  -- the pre-state. `preemptAtF0` is true only at the instruction boundary
  -- (never mid-instruction, never while zeroing/held/trapped/paused, and
  -- S_WAIT/S_PAUSE/S_TRAP are excluded because they are not S_F0).
  let fsmEnB := s.running ∧ ¬ s.halted ∧ ¬ s.zeroing ∧ ¬ s.ic_inv ∧ ¬ holdEff
  let qOn := s.quantum ≠ 0
  let qExpired := qOn ∧ s.qctr = 0
  let preemptAtF0 :=
    fsmEnB ∧ s.st = BitVec.ofNat 5 S_F0 ∧ ¬ s.bus_req ∧ ¬ s.trap_active ∧ qExpired
  let preemptFire := preemptAtF0 ∧ s.next_ready ≠ s.cur
  -- serialized sleep scan (paused while the core is held)
  if s.running ∧ ¬ s.halted ∧ ¬ holdEff then
    s' := { s' with sleep_scan := s.sleep_scan + 1 }
    let ssi := s.sleep_scan.toNat
    if s.tstate[ssi]! = 2 then
      if (s.tsleep[ssi]!).ule 1 then
        s' := { s' with tstate := s'.tstate.set! ssi 1 }
      else
        s' := { s' with tsleep := s'.tsleep.set! ssi ((s.tsleep[ssi]!) - 1) }

  -- FSM (frozen while the core is held)
  if s.running ∧ ¬ s.halted ∧ ¬ s.zeroing ∧ ¬ holdEff then
    let curV := s.cur
    let stN := s.st.toNat
    if stN = S_F0 then
      if s.bus_req then s' := { s' with st := BitVec.ofNat 5 S_PAUSE }
      -- EXT-3: fail-stop, before the preemption point and before the fetch.
      else if s.poison.getLsbD curV.toNat then s' := { s' with running := false }
      -- EXT-1: the preemption. Exactly `YIELD`'s switch, but the saved pc is
      -- `pc` (nothing consumed yet at S_F0), not `pc8`; `st` stays S_F0, so
      -- the new thread's fetch is issued on the next cycle.
      else if preemptFire then
        s' := { s' with tpc := s'.tpc.set! curV.toNat s.pc, cur := s.next_ready,
                        pc := s.tpc[s.next_ready.toNat]! }
      else
        -- EXT-9: latch both banks (the D19 sync-read sites) and check next
        -- cycle in S_IC. The fetch this arm used to issue now lives on the
        -- miss path.
        let ddrPcV := (BitVec.ofNat 32 DATA_BASE) + s.pc.setWidth 32
        let idx := (ddrPcV >>> 3).setWidth 12
        s' := { s' with ic_tag_q := s.ic_tag[idx.toNat]!,
                        ic_data_q := s.ic_data[idx.toNat]!,
                        st := BitVec.ofNat 5 S_IC }
    else if stN = S_IC then
      -- hit: valid bit (17) set and tag match; miss: exactly the old fetch.
      let ddrPcV := (BitVec.ofNat 32 DATA_BASE) + s.pc.setWidth 32
      let tagV := (ddrPcV >>> 15).setWidth 17
      let hit := s.ic_tag_q.getLsbD 41
                 ∧ ((s.ic_tag_q >>> 25).setWidth 16) = s.ic_gen
                 ∧ ((s.ic_tag_q >>> 17).setWidth 8) = s.tdom[s.cur.toNat]!
                 ∧ s.ic_tag_q.setWidth 17 = tagV
      if hit then
        s' := { s' with ir := s.ic_data_q, st := BitVec.ofNat 5 S_RD }
      else
        -- EXT-9b: the miss arm translates; the hit arm above does not.
        s' := { s' with core_addr := ddrEaOf s s.pc, core_rd := true,
                        st := BitVec.ofNat 5 S_FW }
    else if stN = S_PAUSE then
      if ¬ s.bus_req then s' := { s' with st := BitVec.ofNat 5 S_F0 }
    else if stN = S_FW then
      if inp.mDone then
        -- EXT-9 fill, the single write site (mirrors icFillRule/icTagRule).
        let ddrPcV := (BitVec.ofNat 32 DATA_BASE) + s.pc.setWidth 32
        let idx := (ddrPcV >>> 3).setWidth 12
        let tagV := (ddrPcV >>> 15).setWidth 17
        s' := { s' with ir := inp.mRdata, st := BitVec.ofNat 5 S_RD,
                        ic_data := s.ic_data.set! idx.toNat inp.mRdata,
                        ic_tag := s.ic_tag.set! idx.toNat
                                    (((1 : BitVec 42) <<< 41)
                                     ||| ((s.ic_gen.setWidth 42) <<< 25)
                                     ||| ((s.tdom[s.cur.toNat]!).setWidth 42 <<< 17)
                                     ||| tagV.setWidth 42) }
    else if stN = S_RD then
      let r1 := if s.st = BitVec.ofNat 5 S_RD2 then rs3f s else rs1f s
      let r2 := if s.st = BitVec.ofNat 5 S_RD2 then rs4f s else rs2f s
      s' := { s' with
        a := if rs1f s = 0 then 0 else s.rf[rfIdx curV r1]!,
        b := if rs2f s = 0 then 0 else s.rf[rfIdx curV r2]!,
        rdval := if rdf s = 0 then 0 else s.rf[rfIdx curV (rdf s)]!,
        st := if is_sel s then BitVec.ofNat 5 S_RD2 else BitVec.ofNat 5 S_EX }
    else if stN = S_RD2 then
      let r1 := if s.st = BitVec.ofNat 5 S_RD2 then rs3f s else rs1f s
      let r2 := if s.st = BitVec.ofNat 5 S_RD2 then rs4f s else rs2f s
      s' := { s' with
        sel_t := if rs3f s = 0 then 0 else s.rf[rfIdx curV r1]!,
        sel_f := if rs4f s = 0 then 0 else s.rf[rfIdx curV r2]!,
        st := BitVec.ofNat 5 S_EX }
    else if stN = S_EX then
      let o := opN s
      if o = OP_EXIT then
        s' := { s' with halted := true, running := false, retire := s.retire + 1 }
      else if o = OP_THREAD_EXIT then
        s' := { s' with tstate := s'.tstate.set! curV.toNat 0, retire := s.retire + 1 }
        if s.next_ready ≠ curV then
          s' := { s' with cur := s.next_ready, pc := s.tpc[s.next_ready.toNat]!, st := BitVec.ofNat 5 S_F0 }
        else s' := { s' with st := BitVec.ofNat 5 S_WAIT }
      else if o = OP_NOP then
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if is_fence s then
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_MUL then
        s' := { s' with mul_acc := 0, mul_aw := s.a.setWidth 128, mul_b := s.b, mul_kind := 0, st := BitVec.ofNat 5 S_MUL }
      else if is_mulh s then
        s' := { s' with mul_acc := 0, mul_aw := s.a.setWidth 128, mul_b := s.b,
                        mul_kind := if o = OP_MULH then 1 else 2, st := BitVec.ofNat 5 S_MUL }
      else if is_div s then
        if s.b = 0 then
          -- §4.1 pinned: div/udiv -> -1, srem/urem -> the dividend. Was a
          -- trap; see the note in Core.lean's matching arm.
          if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := if o = OP_SREM ∨ o = OP_UREM then s.a else 0xFFFFFFFFFFFFFFFF
          s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
        else
          s' := { s' with div_rem := 0, div_quo := div_a_abs s, div_d := div_b_abs s, div_cnt := 0,
                          div_isrem := (o = OP_SREM ∨ o = OP_UREM),
                          div_negq := div_sgn s ∧ (bit s.a 63 ≠ bit s.b 63),
                          div_negr := div_sgn s ∧ bit s.a 63,
                          st := BitVec.ofNat 5 S_DIV }
      else if is_sel s then
        if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := if sel_cond s then s.sel_t else s.sel_f
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_GET_PCR then
        if rs1f s = 2 then
          if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := curV.setWidth 64 + 1
          s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
        else s' := { s' with trap_active := true, trapped_op := op s, st := BitVec.ofNat 5 S_TRAP }
      else if is_alu s then
        if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := aluV s
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_JMP then
        s' := { s' with pc := s.pc + (imm_j s <<< 3), retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_JAL then
        if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := pc8 s
        s' := { s' with pc := s.pc + (imm_j s <<< 3), retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_JALR then
        if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := pc8 s
        s' := { s' with pc := s.a + imm_i s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if is_branch s then
        s' := { s' with pc := if br_take s then s.pc + (imm_s s <<< 3) else pc8 s,
                        retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_YIELD then
        if s.next_ready = curV then s' := { s' with pc := pc8 s }
        else s' := { s' with tpc := s'.tpc.set! curV.toNat (pc8 s), cur := s.next_ready, pc := s.tpc[s.next_ready.toNat]! }
        s' := { s' with retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_SLEEP then
        s' := { s' with tpc := s'.tpc.set! curV.toNat (pc8 s), tstate := s'.tstate.set! curV.toNat 2,
                        tsleep := s'.tsleep.set! curV.toNat (if s.a = 0 then 1 else s.a) }
        if s.next_ready ≠ curV then
          s' := { s' with cur := s.next_ready, pc := s.tpc[s.next_ready.toNat]!, st := BitVec.ofNat 5 S_F0 }
        else s' := { s' with st := BitVec.ofNat 5 S_WAIT }
        s' := { s' with retire := s.retire + 1 }
      else if o = OP_FUTEX_WAIT then
        -- Mirrors the design: the futex word address is ALIGNED (&~7) and then
        -- TRANSLATED through ddrEa. The two models used to disagree here --
        -- the design was raw+aligned, this was translated+unaligned -- and no
        -- test executed FUTEX_WAIT under a nonzero delta to see it. The
        -- design's raw half of that split is the bug that spun stage B.
        s' := { s' with core_addr := ddrEaOf s (s.rdval &&& (~~~(7 : BitVec 64))),
                        core_rd := true, futex_addr_q := s.rdval, futex_exp := s.a, st := BitVec.ofNat 5 S_FTX1 }
      else if o = OP_FUTEX_WAKE then
        -- EXT-4: the wake bank moved to the SMP block (one shared bank, see
        -- `smpRule`); S_EX keeps only FUTEX_WAKE's sequencing half.
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      -- EXT-6: 0x3e CAP_SEND (a = handle, b = target domain), 0x3f CAP_RECV.
      -- RECV indexes the receiver's OWN domain -- not an operand -- so no
      -- encoding reaches another domain's inbox.
      else if o = OP_MINI_CAP_SEND then
        let tgt := (s.b.toNat) % 16
        let occ := s.cap_ival.getLsbD tgt
        if ¬ occ then
          s' := { s' with cap_ibox := s'.cap_ibox.set! tgt s.a,
                          cap_ival := s.cap_ival ||| (1#16 <<< tgt) }
        if rdf s ≠ 0 then
          rfWe := true; rfWa := (curV ++ rdf s)
          rfWd := if occ then BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF else 0
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_MINI_CAP_RECV then
        let me := (s.tdom[curV.toNat]!).toNat % 16
        let occ := s.cap_ival.getLsbD me
        if occ then
          s' := { s' with cap_ival := s.cap_ival &&& ~~~(1#16 <<< me) }
        if rdf s ≠ 0 then
          rfWe := true; rfWa := (curV ++ rdf s)
          rfWd := if occ then s.cap_ibox[me]! else BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      -- EXT-5: 0x3c GATE_CALL / 0x3d GATE_RETURN. A gate is the only way a
      -- thread changes domain, and only to a domain the host installed.
      else if o = OP_MINI_GATE_CALL then
        let inG := s.in_gate.getLsbD curV.toNat
        if inG then
          -- depth 1: a nested call is refused, no state change
          s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
        else
          let g := (s.a.toNat) % 16
          s' := { s' with tcont := s'.tcont.set! curV.toNat (pc8 s),
                          tcdom := s'.tcdom.set! curV.toNat s.tdom[curV.toNat]!,
                          in_gate := s.in_gate ||| (1#32 <<< curV.toNat),
                          tdom := s'.tdom.set! curV.toNat s.gate_dom[g]!,
                          pc := s.gate_ent[g]!,
                          retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_MINI_GATE_RETURN then
        if s.in_gate.getLsbD curV.toNat then
          s' := { s' with pc := s.tcont[curV.toNat]!,
                          tdom := s'.tdom.set! curV.toNat s.tcdom[curV.toNat]!,
                          in_gate := s.in_gate &&& ~~~(1#32 <<< curV.toNat),
                          retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
        else
          s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if o = OP_CLONE_SPAWN then
        if s.has_free then
          s' := { s' with tpc := s'.tpc.set! s.free_slot.toNat s.a, tstate := s'.tstate.set! s.free_slot.toNat 1 }
          -- EXT-2: the child inherits the parent's domain. A thread cannot
          -- leave its domain by spawning (`tdomTriples` entry 2).
          s' := { s' with tdom := s'.tdom.set! s.free_slot.toNat s.tdom[curV.toNat]! }
          rfWe := true; rfWa := (s.free_slot ++ (2 : BitVec 5)); rfWd := s.b
          s' := { s' with clone_dst := rdf s, clone_tid := s.free_slot, st := BitVec.ofNat 5 S_CLONE2 }
        else
          if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF
          s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if is_lr s then
        s' := { s' with lr_addr := s.a, lr_valid := true, ld_boff_q := 0, ld_op_q := BitVec.ofNat 8 OP_LD, ld_rd_q := rdf s, mem_is_store := false }
        if s.a.ult (BitVec.ofNat 64 0x1000) then
          s' := { s' with dmem_a := s.a.extractLsb' 3 9, st := BitVec.ofNat 5 S_L0 }
        else
          s' := { s' with core_addr := ddrEaOf s s.a, core_rd := true, lr_req := true, st := BitVec.ofNat 5 S_DL }
      else if is_sc s then
        if s.lr_valid ∧ s.lr_addr = s.a then
          if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := 0
          if s.a.ult (BitVec.ofNat 64 0x1000) then
            s' := { s' with dmem_we := true, dmem_a := s.a.extractLsb' 3 9, dmem_wd := s.b, pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
          else
            s' := { s' with core_addr := ddrEaOf s s.a, core_wdata := s.b, core_wr := true, sc_req := true, sc_pending := true, st := BitVec.ofNat 5 S_DSW }
        else
          if rdf s ≠ 0 then rfWe := true; rfWa := (curV ++ rdf s); rfWd := 1
          s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
        s' := { s' with lr_valid := false }
      else if is_load s ∧ mem_ea_l s = BitVec.ofNat 64 UART_RX_ADDR then
        if rdf s ≠ 0 then
          rfWe := true; rfWa := (curV ++ rdf s)
          rfWd := ((s.rxMem[(s.rx_rptr.setWidth 8).toNat]!).setWidth 64)
                  ||| (if s.rx_rptr ≠ s.rx_wptr then (1#64 <<< 8) else 0)
        if s.rx_rptr ≠ s.rx_wptr then s' := { s' with rx_rptr := s.rx_rptr + 1 }
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if is_load s ∧ l_is_gp s then
        if o = OP_LD_31 then
          s' := { s' with gp_addr_r := (mem_ea_l s).extractLsb' 0 32 &&& BitVec.ofNat 32 0xFFFFFFFC, gp_rd := true, ld_rd_q := rdf s, st := BitVec.ofNat 5 S_GPL }
        else s' := { s' with trap_active := true, trapped_op := op s, st := BitVec.ofNat 5 S_TRAP }
      else if is_load s ∧ l_is_zp s then
        s' := { s' with dmem_a := ld_widx s, ld_boff_q := ld_boff s, ld_op_q := op s, ld_rd_q := rdf s, mem_is_store := false, st := BitVec.ofNat 5 S_L0 }
      else if is_load s then
        s' := { s' with core_addr := ddrEaOf s (mem_ea_l s), core_rd := true,
                        ld_boff_q := ld_boff s, ld_op_q := op s, ld_rd_q := rdf s, mem_is_store := false, st := BitVec.ofNat 5 S_DL }
      else if is_store s ∧ mem_ea_s s = BitVec.ofNat 64 UART_ADDR then
        s' := { s' with uartMem := s'.uartMem.set! (s.uart_wptr.setWidth 8).toNat (s.b.setWidth 8), uart_wptr := s.uart_wptr + 1, pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else if is_store s ∧ s_is_gp s then
        if o = OP_ST_34 then
          s' := { s' with gp_addr_r := (mem_ea_s s).extractLsb' 0 32 &&& BitVec.ofNat 32 0xFFFFFFFC, gp_wdata_r := s.b.setWidth 32, gp_wr := true, st := BitVec.ofNat 5 S_GPS }
        else s' := { s' with trap_active := true, trapped_op := op s, st := BitVec.ofNat 5 S_TRAP }
      else if is_store s ∧ s_is_zp s then
        s' := { s' with dmem_a := st_widx s, mem_is_store := true, st := BitVec.ofNat 5 S_L0 }
      else if is_store s then
        s' := { s' with core_addr := ddrEaOf s (mem_ea_s s), core_rd := true, mem_is_store := true, sc_pending := false, st := BitVec.ofNat 5 S_DL }
      else
        s' := { s' with trap_active := true, trapped_op := op s, st := BitVec.ofNat 5 S_TRAP }
    else if stN = S_L0 then
      s' := { s' with st := BitVec.ofNat 5 S_L1 }
    else if stN = S_L1 then
      if ¬ s.mem_is_store then
        if s.ld_rd_q ≠ 0 then rfWe := true; rfWa := (curV ++ s.ld_rd_q); rfWd := ld_wb s
      else
        s' := { s' with dmem_we := true, dmem_a := st_widx s, dmem_wd := st_merge s }
      s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
    else if stN = S_DL then
      if inp.mDone then s' := { s' with ddr_q := inp.mRdata, st := BitVec.ofNat 5 S_DST }
    else if stN = S_DST then
      if ¬ s.mem_is_store then
        if s.ld_rd_q ≠ 0 then rfWe := true; rfWa := (curV ++ s.ld_rd_q); rfWd := ld_wb s
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else
        s' := { s' with core_addr := ddrEaOf s (mem_ea_s s), core_wdata := st_merge s, core_wr := true, st := BitVec.ofNat 5 S_DSW }
    else if stN = S_DSW then
      if inp.mDone then
        -- a GLOBAL SC the arbiter refused: overwrite the optimistic rd=0
        if s.sc_pending ∧ inp.scFail ∧ rdf s ≠ 0 then
          rfWe := true; rfWa := (curV ++ rdf s); rfWd := 1
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
    else if stN = S_CLONE2 then
      rfWe := true; rfWa := (s.clone_tid ++ (31 : BitVec 5))
      rfWd := (BitVec.ofNat 64 0x1800000) + ((s.clone_tid.setWidth 64 + 1) <<< 18)
      s' := { s' with tp_arr := s'.tp_arr.set! s.clone_tid.toNat 0, sigmask_arr := s'.sigmask_arr.set! s.clone_tid.toNat 0, st := BitVec.ofNat 5 S_CLONE3 }
    else if stN = S_CLONE3 then
      if s.clone_dst ≠ 0 then rfWe := true; rfWa := (curV ++ s.clone_dst); rfWd := s.clone_tid.setWidth 64 + 1
      s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
    else if stN = S_FTX1 then
      if inp.mDone then
        if inp.mRdata = s.futex_exp then
          s' := { s' with tpc := s'.tpc.set! curV.toNat (pc8 s), tstate := s'.tstate.set! curV.toNat 3, tfutex := s'.tfutex.set! curV.toNat s.futex_addr_q }
          if s.next_ready ≠ curV then
            s' := { s' with cur := s.next_ready, pc := s.tpc[s.next_ready.toNat]!, st := BitVec.ofNat 5 S_F0 }
          else s' := { s' with st := BitVec.ofNat 5 S_WAIT }
        else s' := { s' with pc := pc8 s, st := BitVec.ofNat 5 S_F0 }
        s' := { s' with retire := s.retire + 1 }
    else if stN = S_WAIT then
      if s.tstate[s.next_ready.toNat]! = 1 then
        s' := { s' with cur := s.next_ready, pc := s.tpc[s.next_ready.toNat]!, st := BitVec.ofNat 5 S_F0 }
      else
        let anyLive := (List.range NT).any (fun ti => s.tstate[ti]! ≠ 0)
        if ¬ anyLive then s' := { s' with halted := true, running := false }
    else if stN = S_MUL then
      if s.mul_b = 0 then
        if rdf s ≠ 0 then
          rfWe := true; rfWa := (curV ++ rdf s)
          rfWd := match s.mul_kind.toNat with
            | 0 => s.mul_acc.extractLsb' 0 64
            | 1 => (s.mul_acc.extractLsb' 64 64) - (if bit s.a 63 then s.b else 0) - (if bit s.b 63 then s.a else 0)
            | _ => s.mul_acc.extractLsb' 64 64
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else
        if bit s.mul_b 0 then s' := { s' with mul_acc := s.mul_acc + s.mul_aw }
        s' := { s' with mul_aw := s.mul_aw <<< 1, mul_b := s.mul_b >>> 1 }
    else if stN = S_DIV then
      if s.div_cnt = 64 then
        if rdf s ≠ 0 then
          rfWe := true; rfWa := (curV ++ rdf s)
          rfWd := if s.div_isrem then (if s.div_negr then (~~~ s.div_rem) + 1 else s.div_rem)
                  else (if s.div_negq then (~~~ s.div_quo) + 1 else s.div_quo)
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
      else
        -- 65-bit partial remainder: {div_rem, div_quo[63]} vs {1'b0, div_d}
        let prem : BitVec 65 := (s.div_rem ++ (s.div_quo.extractLsb' 63 1))
        let divd65 : BitVec 65 := s.div_d.setWidth 65
        if ¬ prem.ult divd65 then
          s' := { s' with div_rem := (prem - divd65).setWidth 64, div_quo := (s.div_quo <<< 1) ||| 1 }
        else
          s' := { s' with div_rem := (prem.setWidth 64), div_quo := s.div_quo <<< 1 }
        s' := { s' with div_cnt := s.div_cnt + 1 }
    else if stN = S_GPL then
      if inp.gpDone then
        if s.ld_rd_q ≠ 0 then rfWe := true; rfWa := (curV ++ s.ld_rd_q); rfWd := inp.gpRdata.setWidth 64
        s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
    else if stN = S_GPS then
      if inp.gpDone then s' := { s' with pc := pc8 s, retire := s.retire + 1, st := BitVec.ofNat 5 S_F0 }
    else if stN = S_TRAP then pure ()
    else s' := { s' with st := BitVec.ofNat 5 S_F0 }

  -- SMP cross-core block (mirrors `smpRule`, which runs AFTER the FSM)
  let wakeLocal := s.running ∧ ¬ s.halted ∧ ¬ s.zeroing ∧ ¬ holdEff
                   ∧ s.st = BitVec.ofNat 5 S_EX ∧ opN s = OP_FUTEX_WAKE
  s' := { s' with wake_out := wakeLocal }
  -- EXT-4: publish the key we woke on; hold otherwise.
  if wakeLocal then s' := { s' with wake_key := s.rdval }
  -- EXT-4: THE one wake comparator bank, shared by the local FUTEX_WAKE and
  -- the remote doorbell via wakeKey/wakeEn. The count limit is the local
  -- wake's; a doorbell wakes everything parked on the key. Local wins a tie.
  let wakeEn  := wakeLocal ∨ inp.doorbell
  let wakeKey := if wakeLocal then s.rdval else inp.doorbellKey
  -- EXT-4: compute the match bitmap this cycle...
  let mut bm : BitVec 32 := 0
  if wakeEn then
    let mut wk := s.a
    for ti in List.range NT do
      if s.tstate[ti]! = 3 ∧ s.tfutex[ti]! = wakeKey ∧ (¬ wakeLocal ∨ wk > 0) then
        bm := bm ||| (1#32 <<< ti)
        if wakeLocal then wk := wk - 1
  s' := { s' with wake_bm := bm }
  -- ...and promote on the PRE-cycle bitmap, i.e. the one computed last
  -- cycle. Guarded on still being parked, mirroring `wakeApply`.
  for ti in List.range NT do
    if s.wake_bm.getLsbD ti ∧ s.tstate[ti]! = 3 then
      s' := { s' with tstate := s'.tstate.set! ti 1 }
  if inp.resKill then s' := { s' with lr_valid := false }

  -- EXT-1: the quantum counter (mirrors `quantumRule`, the sole writer of
  -- `qctr`, in the same priority order: cmd load, cmd-13 re-arm, boundary
  -- reload, countdown). Every input is pre-state, so the position of this
  -- block relative to the FSM is immaterial.
  let cmdQ   := inp.cmdValid ∧ inp.cmdIdx = CMD_QUANTUM
  let cmdR13 := inp.cmdValid ∧ inp.cmdIdx = 13 ∧ bit inp.cmdData 0
  let qTick  := fsmEnB ∧ hp_core_owns s ∧ ¬ s.trap_active ∧ qOn ∧ s.qctr ≠ 0
  s' := { s' with qctr :=
            if cmdQ then inp.cmdData
            else if cmdR13 then s.quantum
            else if preemptAtF0 then s.quantum
            else if qTick then s.qctr - 1
            else s.qctr }

  -- EXT-2: `cur_dom` mirrors `tdom[cur]` one cycle late (`domainRule`).
  -- Both operands are PRE-cycle, so this is order-independent like the
  -- quantum block above. Nothing reads it; it exists for the BSCAN path.
  s' := { s' with cur_dom := s.tdom[s.cur.toNat]! }

  -- dmem sync block: `if (dmem_we) dmem[dmem_a]<=dmem_wd; dmem_rd<=dmem[dmem_a]`
  -- both use the PRE-cycle (registered) dmem_we/dmem_a/dmem_wd.
  if s.dmem_we then s' := { s' with dmem := s'.dmem.set! s.dmem_a.toNat s.dmem_wd }
  -- latches (registered readbacks; occur every cycle, from pre-state)
  s' := { s' with trace_rd_pc := s.trace_pc[s.trace_sel.toNat]!,
                  trace_rd_wb := s.trace_wb[s.trace_sel.toNat]!,
                  dmem_rd := s.dmem[s.dmem_a.toNat]!,
                  reg_rd := s.rf[rfIdx s.cur s.reg_sel]!,
                  uart_byte := s.uartMem[s.uart_ridx.toNat]! }
  -- NOTE: dmem_rd uses PRE-cycle dmem_a per Verilog (dmem_rd<=dmem[dmem_a]).

  -- the one regfile write port
  if rfWe then s' := rfSetIdx s' rfWa rfWd

  -- EXT-8: the commit-trace ring.
  --
  -- The design pushes an entry inside `retireInc`, which is ONE definition
  -- covering every commit site. The ISS counts retires at ~25 separate places,
  -- so mirroring it there would mean maintaining a second list of commit sites
  -- -- the exact defect class this arc has been about, and the one that put a
  -- stale `lw`/`lb` decode into a bitstream.
  --
  -- Instead the mirror is driven by the OBSERVABLE: retire went up by one, so
  -- an instruction committed, so an entry is pushed. It cannot miss a case
  -- because it does not enumerate the cases. This is exact only because
  -- `cmd 54` (host-serviced trap resume) was routed through `retireInc` on the
  -- design side, so "retire incremented" and "an entry was pushed" are the same
  -- event with no exception.
  --
  -- All three operands are PRE-cycle, matching D9: the entry records the
  -- instruction that just retired, not the one about to be fetched.
  -- capture (mirrors `retireInc`): the payload is latched at the retire, into
  -- scalar registers. `trace_wb` takes the value the regfile funnel writes THIS
  -- cycle, not the `rdval` register, which is pre-cycle at the retire point and
  -- so still holds the PREVIOUS instruction's result (see Core.lean).
  if s'.retire = s.retire + 1 then
    s' := { s' with
      trace_hit := true,
      trace_in_pc := ((BitVec.zeroExtend 64 (op s)) <<< 56)
                       ||| (BitVec.zeroExtend 64 (s.pc.truncate 32)),
      trace_in_wb := if rfWe then rfWd else 0 }
  else
    s' := { s' with trace_hit := false }

  -- drain (mirrors `traceRule`): reads the PRE-cycle capture, one write site.
  if s.trace_hit then
    s' := { s' with
      trace_pc := s'.trace_pc.set! s.trace_wp.toNat s.trace_in_pc,
      trace_wb := s'.trace_wb.set! s.trace_wp.toNat s.trace_in_wb,
      trace_wp := s.trace_wp + 1 }

  return s'

end MiniIss

end Machines.Lnp64mini
