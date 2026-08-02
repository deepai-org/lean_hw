-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Iss
import Std.Data.HashMap

/-!
# Lnp64mini Harness — DDR model, EDSL≡ISS selftest, and progtest

A behavioral DDR model (word-addressed `Std.HashMap` with a configurable
read latency) plays the two AXI masters. The system stepper advances the
core (ISS or EDSL) and the DDR model together; `selftest` locksteps the
EDSL open-design cycle against the ISS on every register and touched
memory entry over a directed script; `progtest` runs hand-encoded programs
on the ISS to a clean EXIT and prints the architectural state.
-/

namespace Machines.Lnp64mini

open Loom.Hw

/-! ## DDR model (the AXI HP master, behavioral)

The core drives `core_rd/core_wr/core_addr/core_wdata` (or the JTAG path
`jtag_rd/jtag_wr/ddr_addr_j/jtag_wdata`), muxed by `hp_core_owns`. A start
pulse begins a transaction; after `latency` cycles the model pulses
`m_done` for one cycle with the read data (writes commit to the map and
also pulse `m_done`). `m_busy` is high while a transaction is in flight. -/

structure DdrModel where
  mem     : Std.HashMap Nat (BitVec 64) := {}
  latency : Nat := 2
  -- countdown: none = idle; some (k, isRead, wdata addr) = k cycles left
  pending : Option (Nat × Bool × Nat × BitVec 64) := none
  deriving Inhabited

/-- Word address of a byte address into the DDR data window. -/
def ddrWord (a : Nat) : Nat := a / 8

namespace DdrModel

/-- The masters' inputs to the core THIS cycle, from the model's pre-state. -/
def outputs (d : DdrModel) : Bool × BitVec 64 :=
  match d.pending with
  | some (0, _isRead, addr, _) => (true, d.mem.getD (ddrWord addr) 0)
  | _ => (false, 0)

def busy (d : DdrModel) : Bool := d.pending.isSome

/-- Advance the model given the core's registered request lines this cycle.
`startRd/startWr` are the muxed HP start pulses; `addr`/`wdata` the muxed
request payload. -/
def step (d : DdrModel) (startRd startWr : Bool) (addr : Nat) (wdata : BitVec 64) : DdrModel :=
  match d.pending with
  | some (k, isRead, paddr, pw) =>
      if k = 0 then
        -- completing this cycle: commit a write, then go idle
        let mem' := if isRead then d.mem else d.mem.insert (ddrWord paddr) pw
        { d with mem := mem', pending := none }
      else { d with pending := some (k-1, isRead, paddr, pw) }
  | none =>
      if startRd then { d with pending := some (d.latency, true, addr, 0) }
      else if startWr then { d with pending := some (d.latency, false, addr, wdata) }
      else d

end DdrModel

/-! ## System stepper (ISS core + DDR model) -/

/-- The muxed HP request lines the model sees, from the core pre-state. -/
def hpReq (s : MiniSt) : Bool × Bool × Nat × BitVec 64 :=
  if MiniIss.hp_core_owns s then (s.core_rd, s.core_wr, s.core_addr.toNat, s.core_wdata)
  else (s.jtag_rd, s.jtag_wr, s.ddr_addr_j.toNat, s.jtag_wdata)

/-- Build the core inputs for this cycle from the DDR model + a cmd. -/
def sysIn (d : DdrModel) (c : MiniIn) : MiniIn :=
  let (mdone, mrd) := d.outputs
  { c with mDone := mdone, mRdata := mrd, mBusy := d.busy,
           gpDone := c.gpDone, gpRdata := c.gpRdata, gpBusy := c.gpBusy }

/-- One system cycle on the ISS: model outputs → core inputs → step both.
Both sides read the SAME pre-cycle model, so ordering is deterministic. -/
def sysStepIss (s : MiniSt) (d : DdrModel) (c : MiniIn) : MiniSt × DdrModel :=
  let inp := sysIn d c
  let s' := MiniIss.step s inp
  let (rd, wr, addr, wdata) := hpReq s
  let d' := d.step rd wr addr wdata
  (s', d')

/-! ## GP model (single-cycle, for the MMIO selftest) -/

/-- A trivial GP master: completes in one cycle. Returns (gpDone, gpRdata)
for the cycle AFTER a start pulse, tracked by a one-bit pending flag. -/
structure GpModel where
  pending : Bool := false
  rdata   : BitVec 32 := 0
  deriving Inhabited

def GpModel.outputs (g : GpModel) : Bool × BitVec 32 := (g.pending, g.rdata)
def GpModel.step (g : GpModel) (startRd startWr : Bool) (rval : BitVec 32) : GpModel :=
  if g.pending then { g with pending := false }
  else if startRd ∨ startWr then { pending := true, rdata := rval }
  else g

/-! ## Full system step (ISS + DDR + GP), producing the canonical MiniIn -/

/-- One system cycle: compute the core inputs from both models (pre-state),
step the ISS, then step the models from the core's request lines. Returns
the new core/model state AND the `MiniIn` that was applied (the canonical
input stream for the EDSL lockstep). `gpRval` is the value the GP peripheral
returns on a read this cycle. -/
def sysStep (s : MiniSt) (d : DdrModel) (g : GpModel) (cmd : MiniIn) (gpRval : BitVec 32) :
    MiniSt × DdrModel × GpModel × MiniIn := Id.run do
  let (mdone, mrd) := d.outputs
  let (gdone, grd) := g.outputs
  let inp : MiniIn := { cmd with mDone := mdone, mRdata := mrd, mBusy := d.busy,
                                 gpDone := gdone, gpRdata := grd, gpBusy := g.pending }
  let s' := MiniIss.step s inp
  let (rd, wr, addr, wdata) := hpReq s
  let d' := d.step rd wr addr wdata
  let g' := g.step s.gp_rd s.gp_wr gpRval
  (s', d', g', inp)

/-! ## EDSL InEnv from a MiniIn -/

def MiniIn.toEnv (c : MiniIn) : InEnv := fun n w =>
  match n with
  | "m_done"    => (BitVec.ofBool c.mDone).setWidth w
  | "m_rdata"   => c.mRdata.setWidth w
  | "m_busy"    => (BitVec.ofBool c.mBusy).setWidth w
  | "gp_done"   => (BitVec.ofBool c.gpDone).setWidth w
  | "gp_rdata"  => c.gpRdata.setWidth w
  | "gp_busy"   => (BitVec.ofBool c.gpBusy).setWidth w
  | "cmd_valid" => (BitVec.ofBool c.cmdValid).setWidth w
  | "cmd_idx"   => (BitVec.ofNat 7 c.cmdIdx).setWidth w
  | "cmd_data"  => c.cmdData.setWidth w
  | "res_kill"  => (BitVec.ofBool c.resKill).setWidth w
  | "doorbell"  => (BitVec.ofBool c.doorbell).setWidth w
  | "hold"      => (BitVec.ofBool c.hold).setWidth w
  | "sc_fail"   => (BitVec.ofBool c.scFail).setWidth w
  | _ => 0#w

/-! ## Reading the ISS state as (name, value) pairs (for lockstep vs EDSL) -/

def issRegs (s : MiniSt) : List (String × Nat × Nat) :=
  -- (name, width, value)
  [("cur",5,s.cur.toNat), ("pc",64,s.pc.toNat), ("retire",32,s.retire.toNat),
   ("running",1,if s.running then 1 else 0), ("halted",1,if s.halted then 1 else 0),
   ("st",5,s.st.toNat), ("ir",64,s.ir.toNat), ("a",64,s.a.toNat), ("b",64,s.b.toNat),
   ("rdval",64,s.rdval.toNat), ("sel_t",64,s.sel_t.toNat), ("sel_f",64,s.sel_f.toNat),
   ("mem_is_store",1,if s.mem_is_store then 1 else 0),
   ("trap_active",1,if s.trap_active then 1 else 0), ("trapped_op",8,s.trapped_op.toNat),
   ("core_rd",1,if s.core_rd then 1 else 0), ("core_wr",1,if s.core_wr then 1 else 0),
   ("core_addr",32,s.core_addr.toNat), ("core_wdata",64,s.core_wdata.toNat),
   ("jtag_rd",1,if s.jtag_rd then 1 else 0), ("jtag_wr",1,if s.jtag_wr then 1 else 0),
   ("jtag_wdata",64,s.jtag_wdata.toNat), ("ddr_addr_j",32,s.ddr_addr_j.toNat),
   ("ddr_lo_j",32,s.ddr_lo_j.toNat), ("ddr_rd_l",64,s.ddr_rd_l.toNat), ("ddr_q",64,s.ddr_q.toNat),
   ("bus_req",1,if s.bus_req then 1 else 0),
   ("gp_rd",1,if s.gp_rd then 1 else 0), ("gp_wr",1,if s.gp_wr then 1 else 0),
   ("gp_addr_r",32,s.gp_addr_r.toNat), ("gp_wdata_r",32,s.gp_wdata_r.toNat),
   ("dmem_we",1,if s.dmem_we then 1 else 0), ("dmem_a",9,s.dmem_a.toNat),
   ("dmem_wd",64,s.dmem_wd.toNat), ("dmem_rd",64,s.dmem_rd.toNat),
   ("uart_wptr",9,s.uart_wptr.toNat), ("uart_ridx",8,s.uart_ridx.toNat),
   ("uart_byte",8,s.uart_byte.toNat), ("rx_wptr",9,s.rx_wptr.toNat), ("rx_rptr",9,s.rx_rptr.toNat),
   ("ld_boff_q",3,s.ld_boff_q.toNat), ("ld_op_q",8,s.ld_op_q.toNat), ("ld_rd_q",5,s.ld_rd_q.toNat),
   ("lr_addr",64,s.lr_addr.toNat), ("lr_valid",1,if s.lr_valid then 1 else 0),
   ("futex_exp",64,s.futex_exp.toNat), ("futex_addr_q",64,s.futex_addr_q.toNat),
   ("sleep_scan",5,s.sleep_scan.toNat), ("next_ready",5,s.next_ready.toNat),
   ("free_slot",5,s.free_slot.toNat), ("has_free",1,if s.has_free then 1 else 0),
   ("clone_dst",5,s.clone_dst.toNat), ("clone_tid",5,s.clone_tid.toNat),
   ("mul_acc",128,s.mul_acc.toNat), ("mul_aw",128,s.mul_aw.toNat), ("mul_b",64,s.mul_b.toNat),
   ("mul_kind",2,s.mul_kind.toNat), ("div_rem",64,s.div_rem.toNat), ("div_quo",64,s.div_quo.toNat),
   ("div_d",64,s.div_d.toNat), ("div_cnt",7,s.div_cnt.toNat),
   ("div_isrem",1,if s.div_isrem then 1 else 0), ("div_negq",1,if s.div_negq then 1 else 0),
   ("div_negr",1,if s.div_negr then 1 else 0),
   ("zeroing",1,if s.zeroing then 1 else 0), ("zctr",10,s.zctr.toNat),
   ("reg_sel",5,s.reg_sel.toNat), ("reg_wsel",5,s.reg_wsel.toNat), ("reg_wlo",32,s.reg_wlo.toNat),
   ("dmem_addr_j",32,s.dmem_addr_j.toNat), ("dmem_lo_j",32,s.dmem_lo_j.toNat),
   ("reg_rd",64,s.reg_rd.toNat),
   ("quantum",32,s.quantum.toNat), ("qctr",32,s.qctr.toNat),
   -- EXT-2: the domain observation mirror
   ("cur_dom",8,s.cur_dom.toNat),
   -- EXT-3: the fail-stop bitmap
   ("poison",32,s.poison.toNat),
   ("wake_out",1,if s.wake_out then 1 else 0),
   ("lr_req",1,if s.lr_req then 1 else 0), ("sc_req",1,if s.sc_req then 1 else 0),
   ("sc_pending",1,if s.sc_pending then 1 else 0)]
  ++ (List.range NT).map (fun i => (s!"tstate{i}",2,s.tstate[i]!.toNat))
  ++ (List.range NT).map (fun i => (s!"tfutex{i}",64,s.tfutex[i]!.toNat))

/-- D20: the four thread-table arrays that became Loom **memories**
(`tpc`, `tsleep`, `tp_arr`, `sigmask_arr`). The lockstep compares them
entry by entry the way it already compares `rf`/`dmem`, so the EDSL≡ISS
gate still covers every bit of the thread table. -/
def issTArrays (s : MiniSt) : List (String × Array (BitVec 64)) :=
  [("tpc", s.tpc), ("tsleep", s.tsleep), ("tp_arr", s.tp_arr),
   ("sigmask_arr", s.sigmask_arr)]

/-! ## EDSL ≡ ISS lockstep -/

/-- Compare the EDSL open-design state `σ` to the ISS `s`: all registers +
the touched rf/dmem words listed in `mrf`/`mdmem`. Returns the mismatch
count and prints the first few. -/
def cmpStates (σ : St) (s : MiniSt) (mrf mdmem : List Nat) (step : Nat) : IO Nat := do
  let mut bad := 0
  for (n, w, v) in issRegs s do
    if (σ.regs n w).toNat ≠ v then
      if bad < 12 then IO.println s!"  MISMATCH step {step} reg {n}: edsl={(σ.regs n w).toNat} iss={v}"
      bad := bad + 1
  for a in mrf do
    if (σ.mems "rf" a 64).toNat ≠ (s.rf[a]!).toNat then
      if bad < 12 then IO.println s!"  MISMATCH step {step} rf[{a}]: edsl={(σ.mems "rf" a 64).toNat} iss={(s.rf[a]!).toNat}"
      bad := bad + 1
  for a in mdmem do
    if (σ.mems "dmem" a 64).toNat ≠ (s.dmem[a]!).toNat then
      if bad < 12 then IO.println s!"  MISMATCH step {step} dmem[{a}]: edsl={(σ.mems "dmem" a 64).toNat} iss={(s.dmem[a]!).toNat}"
      bad := bad + 1
  -- EXT-2: the per-thread domain tag (8-bit, so not in `issTArrays`,
  -- which is the 64-bit thread-table family). Compared at every slot --
  -- the inheritance rule is a claim about slots the program never reads,
  -- so a spot check at `cur` would not see a violation.
  for i in List.range NT do
    if (σ.mems "tdom" i 8).toNat ≠ (s.tdom[i]!).toNat then
      if bad < 12 then
        IO.println s!"  MISMATCH step {step} tdom[{i}]: edsl={(σ.mems "tdom" i 8).toNat} iss={(s.tdom[i]!).toNat}"
      bad := bad + 1
  -- D20: the thread-table memories, all 32 entries of each
  for (mn, arr) in issTArrays s do
    for i in List.range NT do
      if (σ.mems mn i 64).toNat ≠ (arr[i]!).toNat then
        if bad < 12 then
          IO.println s!"  MISMATCH step {step} {mn}[{i}]: edsl={(σ.mems mn i 64).toNat} iss={(arr[i]!).toNat}"
        bad := bad + 1
  return bad

/-- Run the ISS+DDR system for `nCyc` cycles under a cmd script (indexed by
cycle) and a gp-read-value function, lockstepping the EDSL design against
the ISS on every cycle. Touched-memory address sets are the full rf window
[0,64) and dmem [0,32) — small enough for the directed script. -/
def lockstep (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32) (nCyc : Nat) : IO Nat := do
  let d0 : DdrModel := { mem := Std.HashMap.ofList image, latency := latency }
  let mut s : MiniSt := {}
  let mut d : DdrModel := d0
  let mut g : GpModel := {}
  let mut σ : St := design.reset
  -- preload the EDSL rf/dmem? Both start zeroed (RAM). DDR image only in the model.
  let mrf := (List.range 64)
  let mdmem := (List.range 64)
  let mut bad := 0
  for k in List.range nCyc do
    let (s', d', g', inp) := sysStep s d g (cmds k) (gpVal k)
    σ := design.cycleOpen inp.toEnv σ
    s := s'; d := d'; g := g'
    bad := bad + (← cmpStates σ s mrf mdmem k)
  return bad

/-! ## Directed selftest script

Builds a program image in DDR and a cmd stream that resets, loads a few
words via the JTAG DDR path is unnecessary — the program is preloaded in
the model. The cmd stream: reset (13.b0), wait for zeroing, start (13.b1),
then idle while the FSM runs the program. The program exercises the FSM
groups; the ISS+EDSL are compared every cycle. -/

/-- Instruction encoder: op[63:56] rd[55:51] rs1[50:46] rs2[45:41] rs3[40:36] rs4[35:31]. -/
def enc (op rd rs1 rs2 : Nat) (rs3 : Nat := 0) (rs4 : Nat := 0) : BitVec 64 :=
  BitVec.ofNat 64 ((op <<< 56) ||| (rd <<< 51) ||| (rs1 <<< 46) ||| (rs2 <<< 41)
                   ||| (rs3 <<< 36) ||| (rs4 <<< 31))

/-- Encode with a signed 32-bit imm_i field at ir[45:14]. -/
def encImmI (op rd rs1 : Nat) (imm : Int) : BitVec 64 :=
  let immBits := (BitVec.ofInt 32 imm).toNat
  BitVec.ofNat 64 ((op <<< 56) ||| (rd <<< 51) ||| (rs1 <<< 46) ||| (immBits <<< 14))

/-- Encode with a signed 32-bit imm_j at ir[50:19] (for J/JAL). -/
def encImmJ (op rd : Nat) (imm : Int) : BitVec 64 :=
  let immBits := (BitVec.ofInt 32 imm).toNat
  BitVec.ofNat 64 ((op <<< 56) ||| (rd <<< 51) ||| (immBits <<< 19))

/-- Encode with a signed 32-bit imm_s at ir[40:9] (branches use imm_s;
stores use imm_s for the address offset and rs2 for the data reg). -/
def encImmS (op rs1 rs2 : Nat) (imm : Int) : BitVec 64 :=
  let immBits := (BitVec.ofInt 32 imm).toNat
  BitVec.ofNat 64 ((op <<< 56) ||| (rs1 <<< 46) ||| (rs2 <<< 41) ||| (immBits <<< 9))

/-- Program image words placed at DDR[DATA_BASE + pc], pc starting at
TEXT_BASE. `image` maps word-address → data. -/
def imageFrom (base : Nat) (words : List (BitVec 64)) : List (Nat × BitVec 64) :=
  (words.zipIdx).map (fun (w, i) => (ddrWord (DATA_BASE + base + i*8), w))

/-- Full program (ISS progtest): reaches EXIT with mul/div/store/load. -/
def prog1 : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 7,        -- 0x1000 ADDI r1 = 7
    encImmI 0xa0 2 0 5,        -- ADDI r2 = 5
    enc 0x10 3 1 2,            -- ADD  r3 = 12
    enc 0x11 4 1 2,            -- SUB  r4 = 2
    enc 0x12 5 1 2,            -- MUL  r5 = 35
    enc 0x13 6 5 2,            -- DIV  r6 = 35/5 = 7
    encImmS 0x33 0 3 0,        -- SD [r0+0] = r3 (zp store, 8-byte)  (rs1=0,rs2=3,imm_s=0)
    encImmI 0x30 8 0 0,        -- LD r8 = [r0+0] = 12 (zp load)
    enc 0x3a 0 0 0 ]           -- EXIT

/-- Fast lockstep program (no long mul/div; reaches EXIT quickly so the
EDSL≡ISS lockstep stays within the closure-RegEnv budget). Covers fetch,
ALU-reg, ALU-imm, small MUL, small DIV, SEL, GET_PCR(Tid), zp store
(1-cycle dmem pipeline), zp load, DDR-data store (RMW) + DDR-data load,
LR/SC, UART TX, branch-taken, JAL, JALR, and EXIT. -/
def progLS : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 7,        -- 0x1000 w0  ADDI r1 = 7
    encImmI 0xa0 2 0 5,        --       w1  ADDI r2 = 5
    encImmI 0xa0 3 0 1,        --       w2  ADDI r3 = 1
    enc 0x10 4 1 2,            --       w3  ADD  r4 = 12
    enc 0x12 5 1 3,            --       w4  MUL  r5 = 7*1 = 7 (fast: mul_b=1)
    enc 0x40 7 1 1 2,          --       w5  SEL(EQ) r7: r1==r1 -> sel_t=rf[rs3=2]=5
    encImmI 0x54 10 2 0,       --       w6  GET_PCR r10 = Tid = cur+1 = 1
    encImmS 0x33 0 4 0,        --       w7  SD [0] = r4 (zp store)
    encImmI 0x30 11 0 0,       --       w8  LD r11 = [0] = 12 (zp load)
    encImmS 0x21 1 1 2,        --       w9  BEQ r1,r1 taken (skip next)
    encImmI 0xa0 9 0 99,       --       w10 (skipped) ADDI r9 = 99
    enc 0x3a 0 0 0 ]           --       w11 EXIT

/-- DDR-data path: store r3 to a DDR address (ea ≥ 0x1000) then load it
back. ea = 0x2000. Covers S_DL/S_DST/S_DSW (RMW store) + DDR load. -/
def progDDR : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 0x2000,   -- r1 = 0x2000 (DDR ea)
    encImmI 0xa0 3 0 42,       -- r3 = 42
    encImmS 0x33 1 3 0,        -- SD [r1+0] = r3 (DDR store, RMW)
    encImmI 0x30 8 1 0,        -- LD r8 = [r1+0] = 42 (DDR load)
    enc 0x3a 0 0 0 ]

/-- LR/SC: LR.D reserve, SC.D store (should succeed, rd=0). ea=0 (zp). -/
def progLRSC : List (BitVec 64) :=
  [ encImmI 0xa0 3 0 77,       -- r3 = 77
    enc 0xc5 5 0 0,            -- LR.D r5 = [r0] (=0), reserve addr 0
    enc 0xc6 6 0 3,            -- SC.D [r0] = r3 ; rd=r6 = 0 (ok)
    encImmI 0x30 8 0 0,        -- LD r8 = [0] = 77
    enc 0x3a 0 0 0 ]

/-- UART TX store then UART RX load (RX empty → returns 0, no valid bit). -/
def progUART : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 UART_ADDR,     -- r1 = 0x8000
    encImmI 0xa0 3 0 0x41,          -- r3 = 'A'
    encImmS 0x33 1 3 0,             -- SD [UART_ADDR] = r3 (UART TX)
    encImmI 0xa0 2 0 UART_RX_ADDR,  -- r2 = 0x8008
    enc 0x30 8 2 0,                 -- LD r8 = [UART_RX] (RX empty -> 0)
    enc 0x3a 0 0 0 ]

/-- Scheduler: CLONE spawns thread 1 (entry=r1), YIELD switches to it, the
child THREAD_EXITs, back to parent which EXITs. -/
def progSched : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 0x1018,   -- r1 = child entry (word 3 = 0x1000+3*8=0x1018)
    enc 0x59 4 1 2,            -- CLONE_SPAWN r4=childtid, entry=r1, arg=r2
    enc 0x06 0 0 0,            -- YIELD -> switch to child
    -- child entry (0x1018, word 3):
    enc 0x3b 0 0 0,           -- THREAD_EXIT (child) -> back to parent
    enc 0x3a 0 0 0 ]          -- EXIT (parent, word 4)

/-- SLEEP then wake: thread 0 sleeps 1 tick; with only 1 thread it goes to
S_WAIT, the sleep scan wakes it, then it EXITs. -/
def progSleep : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 1,        -- r1 = 1 (sleep ticks)
    enc 0x07 0 1 0,           -- SLEEP(rs1=r1=1)
    enc 0x3a 0 0 0 ]          -- EXIT (after wake)

/-- Trap + RESUME: an unknown opcode traps (S_TRAP); the host services it
via cmd 54 (RESUME), and the program continues to EXIT. -/
def progTrap : List (BitVec 64) :=
  [ enc 0x7f 0 0 0,           -- unknown op -> trap
    enc 0x3a 0 0 0 ]          -- EXIT (after RESUME advances to here? no:
                              -- RESUME sets st=S_F0 WITHOUT advancing pc, so
                              -- it re-fetches the SAME trapping instr. Host
                              -- must also SET_PC past it. See cmdTrap below.)

/-- GP MMIO: LWU (op 0x31) from 0xE000_0000 returns the GP model's value;
SW (op 0x34) writes. Covers S_GPL/S_GPS. ea low32 = 0xE0000000 built via
ADDI r0 + (-0x20000000) (low 32 bits = 0xE0000000; aperture check is
ea[31:16]==0xE000). -/
def progGP : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 (-0x20000000),  -- r1 low32 = 0xE0000000
    encImmI 0xa0 3 0 0x99,           -- r3 = 0x99 (SW data)
    encImmS 0x34 1 3 0,              -- SW [r1] = r3 (GP store)
    enc 0x31 8 1 0,                  -- LWU r8 = [r1] (GP load -> model value)
    enc 0x3a 0 0 0 ]

/-- Directed cmd stream for a program: reset at cycle 0, start after the
zeroing sweep (32*NT=1024 cycles), then idle. -/
def cmdStream (resetCyc startCyc : Nat) : Nat → MiniIn := fun k =>
  if k = resetCyc then { cmdValid := true, cmdIdx := 13, cmdData := 1 }       -- reset (b0)
  else if k = startCyc then { cmdValid := true, cmdIdx := 13, cmdData := 2 }  -- start (b1)
  else {}

/-- selftest: lockstep a battery of directed scripts. To keep the zeroing
sweep short in the harness we START before zeroing completes is NOT valid
(mini3 gates the FSM on ¬zeroing), so we let the full 1024-cycle sweep run
but only compare a compact touched set. This is expensive; we cap prog1 to
a short run and rely on progtest + iverilog for the deep programs. -/
def selftest : IO Unit := do
  -- Start immediately (cmd 13 bit1 only) from the reset state; the rf/dmem
  -- are already zero (RAM reset), tstate0=READY, pc=TEXT_BASE — so we skip
  -- the 1024-cycle zeroing sweep and exercise the FSM directly.
  let start : Nat → MiniIn := fun k => if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
  let scripts : List (String × List (BitVec 64) × Nat × BitVec 32) :=
    [("LS   (ALU/MUL/SEL/GET_PCR/zp-st/zp-ld/branch/JAL)", progLS, 54, 0),
     ("DDR  (S_DL/S_DST/S_DSW RMW store + DDR load)",      progDDR, 30, 0),
     ("LRSC (LR.D reserve + SC.D success)",                progLRSC, 22, 0),
     ("UART (UART TX store + UART RX load)",               progUART, 24, 0),
     ("SCH  (CLONE + YIELD + THREAD_EXIT switch)",         progSched, 34, 0),
     ("SLP  (SLEEP + sleep-scan wake + S_WAIT)",           progSleep, 20, 0),
     ("GP   (S_GPL/S_GPS MMIO load/store handshake)",      progGP, 24, 0xABCD)]
  -- NOTE: LS(54) is the slow outlier (closure-RegEnv cost is ~cubic in the
  -- window). Each script starts fresh from reset, so per-script cost is
  -- bounded by its own window; the whole battery completes in a few min.
  let mut total := 0
  for (nm, p, nc, gp) in scripts do
    let img := imageFrom TEXT_BASE p
    let bad ← lockstep img 1 start (fun _ => gp) nc
    if bad = 0 then IO.println s!"  OK  {nm}  ({nc} cyc)"
    else IO.println s!"  FAIL {nm} ({bad} mismatches)"
    total := total + bad
  if total = 0 then
    IO.println s!"LNP64MINI SELFTEST OK — EDSL≡ISS bit-exact on {scripts.length} scripts (all regs + rf[0..64) + dmem[0..64) + tpc/tsleep/tp_arr/sigmask_arr[0..32))"
  else
    IO.println s!"LNP64MINI SELFTEST FAILED ({total} total mismatches)"

/-! ## ISS-only system run (fast; no EDSL) -/

/-- Run the ISS+DDR+GP system to `halted` or `maxCyc`, under a cmd stream. -/
def runIss (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32) (maxCyc : Nat) :
    MiniSt × DdrModel × Nat := Id.run do
  let mut s : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := latency }
  let mut g : GpModel := {}
  let mut k := 0
  for i in List.range maxCyc do
    if s.halted then return (s, d, k)
    let (s', d', g', _) := sysStep s d g (cmds i) (gpVal i)
    s := s'; d := d'; g := g'
    k := i + 1
  return (s, d, k)

/-! ## progtest — hand-encoded program to a clean EXIT on the ISS -/

/-- Program with a trap at word 0 (unknown op 0x7f) then real work: after
the trap raises, the host SET_PCs past it (cmd 53) and RESUMEs (cmd 54). -/
def progTrapReal : List (BitVec 64) :=
  [ enc 0x7f 0 0 0,           -- w0 unknown op -> trap
    encImmI 0xa0 1 0 55,      -- w1 ADDI r1 = 55 (after resume)
    enc 0x3a 0 0 0 ]          -- w2 EXIT

def hexStr (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def progtest : IO Unit := do
  -- (a) prog1 to a clean EXIT.
  let img := imageFrom TEXT_BASE prog1
  let (s, _, k) := runIss img 1 (fun i => if i = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}) (fun _ => 0) 400
  IO.println s!"PROGTEST prog1: halted={s.halted} cycles={k} pc={hexStr s.pc.toNat} retire={s.retire.toNat}"
  IO.print "  rf[1..8] ="
  for i in List.range 8 do
    IO.print s!" r{i+1}={(s.rf[i+1]!).toNat}"
  IO.println ""
  IO.println s!"  dmem[0]={(s.dmem[0]!).toNat}"
  let ok1 := s.halted ∧ (s.rf[1]!).toNat = 7 ∧ (s.rf[3]!).toNat = 12 ∧ (s.rf[5]!).toNat = 35
            ∧ (s.rf[6]!).toNat = 7 ∧ (s.rf[8]!).toNat = 12 ∧ (s.dmem[0]!).toNat = 12

  -- (b) trap + RESUME: run to the trap, then at a later cycle SET_PC=0x1008
  -- (word 1) and RESUME (cmd 54).
  let imgT := imageFrom TEXT_BASE progTrapReal
  let cmdsT : Nat → MiniIn := fun i =>
    if i = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
    else if i = 10 then { cmdValid := true, cmdIdx := 53, cmdData := BitVec.ofNat 32 0x1008 }  -- SET_PC
    else if i = 11 then { cmdValid := true, cmdIdx := 54, cmdData := 1 }                        -- RESUME
    else {}
  let (st, _, kt) := runIss imgT 1 cmdsT (fun _ => 0) 200
  IO.println s!"PROGTEST trap+resume: halted={st.halted} cycles={kt} r1={(st.rf[1]!).toNat} trap_active={st.trap_active}"
  let ok2 := st.halted ∧ (st.rf[1]!).toNat = 55 ∧ st.trap_active = false

  IO.println (if ok1 ∧ ok2 then "PROGTEST OK" else "PROGTEST FAILED")

/-! ## SMP-extension programs + selftest (DUAL_SPEC ladder step 1)

Six directed scripts for the `res_kill` / `sc_fail` / `doorbell` / `hold`
D15 inputs and the `wake_out` register. Each is lockstepped EDSL≡ISS on
every register (including `wake_out`/`lr_req`/`sc_req`/`sc_pending`) and
additionally checked for the *architectural* outcome on the ISS. -/

/-- FUTEX_WAIT on the DDR word at 0x2000 (image value 0 = the expected
value, so the thread blocks), then — after an external `doorbell` — r9=5
and EXIT. With one thread the core parks in S_WAIT until the doorbell. -/
def progDoorbell : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 0x2000,   -- r1 = futex word address (DDR)
    encImmI 0xa0 2 0 0,        -- r2 = expected value (0)
    enc 0xcb 1 2 0,            -- FUTEX_WAIT(addr=r1, expected=r2) -> blocks
    encImmI 0xa0 9 0 5,        -- r9 = 5 (only reached after the doorbell)
    enc 0x3a 0 0 0 ]           -- EXIT

/-- A GLOBAL (DDR) LR/SC pair: `S_DSW` consumes the arbiter's `sc_fail`
verdict and rewrites `rd`. r6 = 0 when the arbiter accepts, 1 when it
refuses. -/
def progScDDR : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 0x2000,   -- r1 = DDR address
    encImmI 0xa0 3 0 77,       -- r3 = 77
    enc 0xc5 5 1 0,            -- LR.D  r5 = [r1]  (global reservation)
    enc 0xc6 6 1 3,            -- SC.D  [r1] = r3 ; r6 = verdict
    enc 0x3a 0 0 0 ]           -- EXIT

/-- FUTEX_WAKE: the `wake_out` pulse source (no local waiter matches). -/
def progWake : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 0x2000,   -- r1 = futex word address
    encImmI 0xa0 7 0 1,        -- r7 = wake count
    enc 0xcc 1 7 0,            -- FUTEX_WAKE(addr=r1, count=r7)
    encImmI 0xa0 9 0 9,        -- r9 = 9
    enc 0x3a 0 0 0 ]           -- EXIT

/-- Count the `wake_out` pulses over an ISS run (must be exactly one for
`progWake`). -/
def countWake (image : List (Nat × BitVec 64)) (maxCyc : Nat) : Nat × Bool := Id.run do
  let mut s : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := 1 }
  let mut g : GpModel := {}
  let mut n := 0
  for i in List.range maxCyc do
    if s.halted then return (n, true)
    let cmd : MiniIn := if i = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
    let (s', d', g', _) := sysStep s d g cmd 0
    s := s'; d := d'; g := g'
    if s.wake_out then n := n + 1
  return (n, s.halted)

/-- The SMP-extension selftest: EDSL≡ISS lockstep on the six scripts, plus
the architectural assertions. -/
def smpSelftest : IO Unit := do
  let start : Nat → MiniIn := fun k =>
    if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
  -- (1) res_kill held high: every LR's reservation dies the same cycle, so
  --     the SC must FAIL (rd=1) and leave dmem[0] untouched.
  let rk : Nat → MiniIn := fun k => { start k with resKill := true }
  -- (2) doorbell at cycle 30: the FUTEX-blocked thread wakes and finishes.
  let db : Nat → MiniIn := fun k => { start k with doorbell := k = 26 }
  -- (3) hold over cycles 10..30: the FSM freezes at the next S_F0, then resumes.
  let hd : Nat → MiniIn := fun k => { start k with hold := 10 ≤ k ∧ k ≤ 30 }
  -- (4) sc_fail: the arbiter refuses the global SC at the serialization point.
  let sf : Nat → MiniIn := fun k => { start k with scFail := true }
  let scripts : List (String × List (BitVec 64) × (Nat → MiniIn) × Nat) :=
    [("RESKILL (res_kill clears lr_valid -> SC fails)", progLRSC, rk, 24),
     ("SCFAIL  (global SC refused -> rd=1 at S_DSW)",   progScDDR, sf, 40),
     ("SCOK    (global SC accepted -> rd=0)",           progScDDR, start, 40),
     ("DOORBELL(FUTEX_WAIT parks; doorbell wakes it)",  progDoorbell, db, 34),
     ("WAKEOUT (FUTEX_WAKE pulses wake_out)",           progWake, start, 26),
     ("HOLD    (FSM frozen at S_F0, then resumes)",     progLRSC, hd, 38)]
  let mut total := 0
  for (nm, p, c, nc) in scripts do
    let img := imageFrom TEXT_BASE p
    let bad ← lockstep img 1 c (fun _ => 0) nc
    if bad = 0 then IO.println s!"  OK  {nm}  ({nc} cyc)"
    else IO.println s!"  FAIL {nm} ({bad} mismatches)"
    total := total + bad
  -- architectural outcomes on the ISS
  let (sfs, _, _) := runIss (imageFrom TEXT_BASE progScDDR) 1 sf (fun _ => 0) 200
  let (sos, _, _) := runIss (imageFrom TEXT_BASE progScDDR) 1 start (fun _ => 0) 200
  let okSc := sfs.halted && sos.halted && (sfs.rf[6]!).toNat == 1 && (sos.rf[6]!).toNat == 0
  IO.println s!"  sc_fail: refused r6={(sfs.rf[6]!).toNat} (want 1)  accepted r6={(sos.rf[6]!).toNat} (want 0)"
  let (sk, _, _) := runIss (imageFrom TEXT_BASE progLRSC) 1 rk (fun _ => 0) 200
  let okRk := sk.halted && (sk.rf[6]!).toNat == 1 && (sk.dmem[0]!).toNat == 0
                        && (sk.rf[8]!).toNat == 0
  IO.println s!"  res_kill: halted={sk.halted} r6(SC result)={(sk.rf[6]!).toNat} (want 1=fail) dmem[0]={(sk.dmem[0]!).toNat} (want 0)"
  let (sd, _, kd) := runIss (imageFrom TEXT_BASE progDoorbell) 1 db (fun _ => 0) 300
  let okDb := sd.halted && (sd.rf[9]!).toNat == 5
  IO.println s!"  doorbell: halted={sd.halted} cycles={kd} r9={(sd.rf[9]!).toNat} (want 5) tstate0={(sd.tstate[0]!).toNat}"
  -- doorbell-less control: the thread must STAY parked (no spurious wake)
  let (sn, _, _) := runIss (imageFrom TEXT_BASE progDoorbell) 1 start (fun _ => 0) 300
  let okNo := (!sn.halted) && (sn.tstate[0]!).toNat == 3 && (sn.rf[9]!).toNat == 0
  IO.println s!"  no-doorbell control: halted={sn.halted} (want false) tstate0={(sn.tstate[0]!).toNat} (want 3)"
  let (nw, hw) := countWake (imageFrom TEXT_BASE progWake) 300
  IO.println s!"  wake_out pulses={nw} (want 1) halted={hw}"
  let okWk := nw == 1 && hw
  -- hold: the held run must reach the SAME architectural state as the free run
  let (sh, _, kh) := runIss (imageFrom TEXT_BASE progLRSC) 1 hd (fun _ => 0) 300
  let (sf, _, kf) := runIss (imageFrom TEXT_BASE progLRSC) 1 start (fun _ => 0) 300
  let rfEq := sh.rf == sf.rf
  let okHd := sh.halted && sf.halted && rfEq && sh.retire == sf.retire && kf < kh
  IO.println s!"  hold: cycles held={kh} free={kf} (want held>free) rf equal={rfEq} retire={(sh.retire).toNat}"
  if total == 0 && okRk && okSc && okDb && okNo && okWk && okHd then
    IO.println "LNP64MINI SMP SELFTEST OK — EDSL≡ISS on res_kill/sc_fail/doorbell/wake_out/hold + outcomes"
  else
    IO.println s!"LNP64MINI SMP SELFTEST FAILED ({total} mismatches; rk={okRk} sc={okSc} db={okDb} no={okNo} wk={okWk} hd={okHd})"


/-! ## EXT-1 — the preemption tick (selftest)

Four claims, each with a control:

1. **Expiry switches threads.** With two runnable threads and a quantum,
   `cur` changes at `S_F0` although neither thread ever yields.
2. **Expiry with nobody else READY continues.** A single-threaded program
   with a quantum runs in exactly the same number of cycles as without one
   — preempting to yourself is a no-op, not a stall.
3. **`quantum = 0` is cooperative.** Bit-identical to a run that never
   touches `CMD_QUANTUM`: same `rf`, same `retire`, same cycle count, and
   the child of the preemption program never runs at all.
4. **A preempted thread resumes correctly.** `preemptAudit` checks, at
   every fire, that `tpc[cur]` received the pc that was *about to be
   fetched* (not `pc+8`), that the switch landed on `next_ready` with
   `pc = tpc[next_ready]`, and that the core stayed at `S_F0`. The program
   also carries a poison opcode one word past the child's loop, so a
   one-instruction resume slip traps instead of passing silently. -/

/-- Two threads that never yield. Parent (thread 0): CLONE a child, then
`r9 += 1` twice, then EXIT. Child (thread 1): `r10 += 1` in a
two-instruction loop, forever. Word 7 is unreachable in a correct machine
and traps in a broken one. -/
def progPreempt : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 0x1028,   -- w0  r1 = child entry (word 5)
    enc 0x59 4 1 2,            -- w1  CLONE r4 = tid, entry = r1, arg = r2
    encImmI 0xa0 9 9 1,        -- w2  r9 += 1                 (parent)
    encImmI 0xa0 9 9 1,        -- w3  r9 += 1
    enc 0x3a 0 0 0,            -- w4  EXIT (halts the core)
    encImmI 0xa0 10 10 1,      -- w5  r10 += 1  (child entry, 0x1028)
    encImmJ 0x20 0 (-1),       -- w6  J -1 -> back to w5
    enc 0x7f 0 0 0 ]           -- w7  poison: only a bad resume gets here

/-- cmd stream: load the quantum (cycle 0), then start (cycle 1). -/
def cmdQuantum (q : Nat) : Nat → MiniIn := fun k =>
  if k = 0 then { cmdValid := true, cmdIdx := CMD_QUANTUM, cmdData := BitVec.ofNat 32 q }
  else if k = 1 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else {}

/-- The same start with no `CMD_QUANTUM` write at all (the control for the
`quantum = 0` byte-identity claim). -/
def cmdNoQuantum : Nat → MiniIn := fun k =>
  if k = 1 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}

/-- Run the ISS and audit **every** preemption. Returns
`(fires, allChecksPassed, finalState, cycles)`. -/
def preemptAudit (image : List (Nat × BitVec 64)) (q : Nat) (maxCyc : Nat) :
    Nat × Bool × MiniSt × Nat := Id.run do
  let cmds := cmdQuantum q
  let mut s : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := 1 }
  let mut g : GpModel := {}
  let mut fires := 0
  let mut ok := true
  let mut k := 0
  for i in List.range maxCyc do
    if s.halted then return (fires, ok, s, k)
    -- the fire predicate, read off the pre-state exactly as the design does
    let fire := s.running ∧ ¬ s.halted ∧ ¬ s.zeroing ∧ s.st = BitVec.ofNat 5 S_F0
                ∧ ¬ s.bus_req ∧ ¬ s.trap_active ∧ s.quantum ≠ 0 ∧ s.qctr = 0
                ∧ s.next_ready ≠ s.cur
    let savedPc := s.pc
    let outgoing := s.cur.toNat
    let incoming := s.next_ready.toNat
    let target := s.tpc[incoming]!
    let (s', d', g', _) := sysStep s d g (cmds i) 0
    if fire then
      fires := fires + 1
      if s'.tpc[outgoing]! ≠ savedPc then ok := false   -- saved pc, NOT pc+8
      if s'.cur.toNat ≠ incoming then ok := false
      if s'.pc ≠ target then ok := false
      if s'.st ≠ BitVec.ofNat 5 S_F0 then ok := false   -- costs one cycle, no fetch
    s := s'; d := d'; g := g'
    k := i + 1
  return (fires, ok, s, k)

/-! ### The Law-5 program: a spinner that cannot be dislodged cooperatively

Nine words. Thread 0 CLONEs a child and then spins on a zero-page flag it
never sets itself; the child sets the flag and exits; thread 0 then stores
42 and EXITs. **Cooperatively the spinner owns the core forever** — which
is the failure `PORTING_SPEC.md` records from silicon, where a spinning
core-1 thread starved core 0's GEM pump to 100 % packet loss. With a
quantum the child gets the CPU and the program terminates.

Every architectural field of the final state is timing-INDEPENDENT (the
number of spin iterations is not, so `retire` and the cycle count are not
compared), which is what lets the iverilog leg be diffed byte-for-byte
against this ISS. -/
def progSpin : List (BitVec 64) :=
  [ encImmI 0xa0 1 0 0x1030,   -- w0  r1 = child entry (word 6)
    enc 0x59 4 1 2,            -- w1  CLONE r4 = tid, entry = r1
    encImmI 0x30 5 0 0,        -- w2  spin head (0x1010): r5 = [0]
    encImmS 0x21 5 0 (-1),     -- w3  BEQ r5, r0 -> back to w2
    encImmI 0xa0 9 0 42,       -- w4  r9 = 42   (only after the flag is set)
    enc 0x3a 0 0 0,            -- w5  EXIT
    encImmI 0xa0 6 0 1,        -- w6  child entry (0x1030): r6 = 1
    encImmS 0x33 0 6 0,        -- w7  SD [0] = r6   (sets the flag)
    enc 0x3b 0 0 0 ]           -- w8  THREAD_EXIT

/-- 16 lowercase hex digits, `$readmemh` shaped. -/
def hex16 (v : BitVec 64) : String :=
  String.ofList ((List.range 16).map (fun i =>
    (Nat.toDigits 16 ((v.toNat >>> ((15 - i) * 4)) % 16)).head!))

/-- Write `progSpin` as a `$readmemh` image (the RTL leg's program). -/
def writePreemptHex (path : String) : IO Unit := do
  IO.FS.writeFile path (String.intercalate "\n" (progSpin.map hex16) ++ "\n")
  IO.println s!"{path} written ({progSpin.length} words)"

/-- The oracle line for `fpga/zc702/tb_lnp64mini_preempt.v`, printed from
the ISS. Format and field order are identical to the tb's `$display`. -/
def preemptPredict (q : Nat) (maxCyc : Nat := 20000) : IO Unit := do
  let (fires, _, s, _) := preemptAudit (imageFrom TEXT_BASE progSpin) q maxCyc
  IO.println s!"PREEMPT halted={if s.halted then 1 else 0} \
trap={if s.trap_active then 1 else 0} pc={if s.halted then s.pc.toNat else 0} \
r5={(s.rf[5]!).toNat} r9={(s.rf[9]!).toNat} dmem0={(s.dmem[0]!).toNat} \
t1state={(s.tstate[1]!).toNat} preempted={if fires ≠ 0 then 1 else 0}"

/-! ## EXT-2 — the domain selftest

Two claims, and the second is the one that matters:

1. **EDSL ≡ ISS on the domain state**, via the ordinary `lockstep` — which
   now compares `cur_dom` and all 32 `tdom` slots on every cycle. Slot-wise
   comparison is deliberate: inheritance is a claim about a slot the running
   program never reads, so a spot check at `cur` could not observe a
   violation.
2. **A thread cannot leave its domain by spawning.** Put the parent in a
   non-zero domain with `cmd 58`, let it `CLONE`, and the child's tag must
   equal the parent's. The domain is non-zero on purpose: with everything at
   0 the test passes even if inheritance is deleted outright, which is
   exactly the vacuous test EXT-2 is most at risk of shipping.

`cmd 13` with `data = 2` sets the *start* bit without the *reset* bit, so
it does not launch the 1024-cycle zeroing sweep — the tags come from the
(all-zero) reset image instead, and `cmd 58` can be issued at cycle 0 and
stick. That is what keeps this test 60 cycles rather than 1400; the sweep
path is covered by the same `tdomTriples` entry the `cmd 13` reset uses. -/
def DOM_TEST : Nat := 7

/-- cmd stream: quantum, start, then (past the zeroing sweep) put thread 0
in domain `DOM_TEST`. -/
def cmdDomain : Nat → MiniIn := fun k =>
  if k = 0 then
    { cmdValid := true, cmdIdx := CMD_SETDOM, cmdData := BitVec.ofNat 32 (DOM_TEST <<< 8) }
  else if k = 1 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else {}

def domSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progPreempt
  -- (1) EDSL ≡ ISS, including `cur_dom` and every `tdom` slot, every cycle.
  let bad ← lockstep img 1 cmdDomain (fun _ => 0) 60
  if bad = 0 then IO.println "  OK  DOMAIN (EDSL≡ISS on cur_dom + all 32 tdom slots, 60 cyc)"
  else IO.println s!"  FAIL DOMAIN ({bad} mismatches)"
  -- (2) the architectural claim: CLONE inherits, and the tag is non-zero.
  let (sd, _, _) := runIss img 1 cmdDomain (fun _ => 0) 200
  let parent := (sd.tdom[0]!).toNat
  let child  := (sd.tdom[1]!).toNat
  let others := (List.range NT).drop 2 |>.filter (fun i => (sd.tdom[i]!).toNat ≠ 0)
  IO.println s!"  domain: parent tdom[0]={parent} (want {DOM_TEST}) child tdom[1]={child} (want {DOM_TEST}) other non-zero slots={others.length} (want 0) cur_dom={sd.cur_dom.toNat}"
  let okInherit := parent = DOM_TEST && child = DOM_TEST && others.isEmpty
  if bad = 0 && okInherit then
    IO.println "LNP64MINI DOMAIN SELFTEST OK — EDSL≡ISS on the tag + CLONE cannot leave its domain"
  else
    IO.println s!"LNP64MINI DOMAIN SELFTEST FAILED ({bad} mismatches; inherit={okInherit})"
    throw <| IO.userError "domain selftest failed"

/-! ## EXT-3 — the fail-stop selftest

Poison has two enforcement points and they fail differently, so both are
claimed separately:

1. **The running thread.** Poisoning `cur` must stop the core at the next
   instruction boundary — `running` goes false and `retire` freezes. Masking
   the scheduler alone would NOT do this: the running thread is not re-picked,
   so it would keep executing until it happened to yield. This claim is what
   distinguishes fail-stop from "descheduled".
2. **A ready-but-not-running thread.** The child is poisoned at cycle 2 —
   *before* `CLONE` has admitted it — so when it is admitted READY it can
   never be picked, and the parent runs to `EXIT` alone. This is the
   `readyBm` mask, and the parent's progress is the control: a bug that
   stopped *everything* would pass claim 1 alone.

   Poisoning it mid-run instead tests nothing, and finding that out was the
   useful part of writing this. At cycle 24 the *child* is the thread on the
   core, so poisoning it takes the claim-1 path and stops the machine — the
   parent then never runs again and the test fails for a reason that has
   nothing to do with descheduling. "Deschedule" and "fail-stop" are only
   distinguishable when the poisoned slot is provably not `cur`. -/
def cmdPoison (q : Nat) (at_ : Nat) (bm : Nat) : Nat → MiniIn := fun k =>
  if k = 0 then { cmdValid := true, cmdIdx := CMD_QUANTUM, cmdData := BitVec.ofNat 32 q }
  else if k = 1 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else if k = at_ then
    { cmdValid := true, cmdIdx := CMD_POISON, cmdData := BitVec.ofNat 32 bm }
  else {}

def failstopSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progPreempt
  -- (0) EDSL ≡ ISS with poison live, every register + all thread arrays.
  let bad ← lockstep img 1 (cmdPoison 8 24 0xFFFFFFFF) (fun _ => 0) 60
  if bad = 0 then IO.println "  OK  FAILSTOP (EDSL≡ISS with poison live, 60 cyc)"
  else IO.println s!"  FAIL FAILSTOP ({bad} mismatches)"
  -- (1) poisoning the running thread stops the core, and it stays stopped.
  let (sp, _, _) := runIss img 1 (cmdPoison 8 24 0xFFFFFFFF) (fun _ => 0) 4000
  let (sc, _, _) := runIss img 1 (cmdQuantum 8) (fun _ => 0) 4000
  IO.println s!"  running-thread: poisoned running={sp.running} (want false) retire={sp.retire.toNat} vs unpoisoned retire={sc.retire.toNat} halted={sc.halted} (want strictly less, control halts)"
  let ok1 := (¬ sp.running) && sp.retire.toNat < sc.retire.toNat && sc.halted
  -- (2) poisoning ONLY the child (slot 1) descheduules it; the parent runs on.
  --     The parent reaches EXIT, so `halted` is the evidence it was undisturbed.
  let (sk, _, _) := runIss img 1 (cmdPoison 8 2 0x2) (fun _ => 0) 4000
  let childPc := (sk.tpc[1]!).toNat
  IO.println s!"  ready-thread:   parent halted={sk.halted} (want true) r9={(sk.rf[9]!).toNat} (want 2) child tstate={(sk.tstate[1]!).toNat} child tpc=0x{String.ofList (Nat.toDigits 16 childPc)}"
  let ok2 := sk.halted && (sk.rf[9]!).toNat == 2
  if bad = 0 && ok1 && ok2 then
    IO.println "LNP64MINI FAILSTOP SELFTEST OK — poison stops the runner AND deschedules the ready"
  else
    IO.println s!"LNP64MINI FAILSTOP SELFTEST FAILED ({bad} mismatches; runner={ok1} ready={ok2})"
    throw <| IO.userError "failstop selftest failed"

def preemptSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progPreempt
  let imgLS := imageFrom TEXT_BASE progLS
  -- ---- EDSL ≡ ISS lockstep, every register (incl. quantum/qctr) ----
  let scripts : List (String × List (BitVec 64) × (Nat → MiniIn) × Nat) :=
    [("PREEMPT (quantum=8, two runnable threads interleave)", progPreempt, cmdQuantum 8, 46),
     ("QZERO   (quantum=0, the cooperative machine)",         progPreempt, cmdQuantum 0, 46),
     ("SOLO    (quantum=4, one thread: expiry is a no-op)",   progLS,      cmdQuantum 4, 46)]
  let mut total := 0
  for (nm, p, c, nc) in scripts do
    let bad ← lockstep (imageFrom TEXT_BASE p) 1 c (fun _ => 0) nc
    if bad = 0 then IO.println s!"  OK  {nm}  ({nc} cyc)"
    else IO.println s!"  FAIL {nm} ({bad} mismatches)"
    total := total + bad
  -- ---- (1)+(4) expiry switches threads; every switch resumes correctly ----
  let (fires, resumeOk, sp, kp) := preemptAudit img 8 4000
  let childR10 := (sp.rf[32 + 10]!).toNat
  IO.println s!"  preempt: fires={fires} resume-audit={resumeOk} cycles={kp} halted={sp.halted} \
parent r9={(sp.rf[9]!).toNat} (want 2) child r10={childR10} (want >0) trap={sp.trap_active}"
  let ok1 := fires > 0 && resumeOk && sp.halted && !sp.trap_active
             && (sp.rf[9]!).toNat == 2 && childR10 > 0
  -- ---- (3) quantum = 0 is the cooperative machine, bit for bit ----
  let (f0, _, s0, k0) := preemptAudit img 0 4000
  let (sn, _, kn) := runIss img 1 cmdNoQuantum (fun _ => 0) 4000
  let coopIdentical := s0.rf == sn.rf && s0.retire == sn.retire && k0 == kn
                       && s0.tpc == sn.tpc && s0.tstate == sn.tstate
  IO.println s!"  quantum=0: fires={f0} (want 0) cycles={k0} vs no-cmd control {kn} \
child r10={(s0.rf[32+10]!).toNat} (want 0) state-identical={coopIdentical}"
  let ok3 := f0 == 0 && s0.halted && (s0.rf[9]!).toNat == 2
             && (s0.rf[32 + 10]!).toNat == 0 && coopIdentical
  -- ---- (2) expiry with nobody else READY: same result, SAME cycle count ----
  let (sq, _, kq) := runIss imgLS 1 (cmdQuantum 4) (fun _ => 0) 4000
  let (sz, _, kz) := runIss imgLS 1 cmdNoQuantum (fun _ => 0) 4000
  let ok2 := sq.halted && sz.halted && sq.rf == sz.rf && sq.retire == sz.retire && kq == kz
  IO.println s!"  solo: quantum=4 cycles={kq} vs quantum=0 cycles={kz} (want equal) \
rf equal={sq.rf == sz.rf} retire={(sq.retire).toNat}"
  -- ---- Law 5: the spinner. Cooperatively it owns the core forever ----
  let imgSpin := imageFrom TEXT_BASE progSpin
  let (fq, _, sq2, kq2) := preemptAudit imgSpin 64 20000
  let (_fc, _, sc2, _) := preemptAudit imgSpin 0 20000
  IO.println s!"  spinner: quantum=64 halted={sq2.halted} cycles={kq2} r9={(sq2.rf[9]!).toNat} \
(want 42) flag={(sq2.dmem[0]!).toNat} fires={fq} | cooperative halted={sc2.halted} (want false) \
r9={(sc2.rf[9]!).toNat} (want 0) child tstate={(sc2.tstate[1]!).toNat} (want 1 = READY, never run)"
  let ok4 := sq2.halted && (sq2.rf[9]!).toNat == 42 && (sq2.dmem[0]!).toNat == 1
             && fq > 0 && !sc2.halted && (sc2.rf[9]!).toNat == 0
             && (sc2.dmem[0]!).toNat == 0 && (sc2.tstate[1]!).toNat == 1
  if total == 0 && ok1 && ok2 && ok3 && ok4 then
    IO.println "LNP64MINI PREEMPT SELFTEST OK — EDSL≡ISS on 3 scripts + switch/no-stall/cooperative/resume/Law-5 spinner"
  else
    IO.println s!"LNP64MINI PREEMPT SELFTEST FAILED ({total} mismatches; switch={ok1} nostall={ok2} coop={ok3} spin={ok4})"

end Machines.Lnp64mini
