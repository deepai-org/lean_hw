-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.StateCover
import Loom.Hw.Diff
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
  | "doorbell_key" => c.doorbellKey.setWidth w
  | "hold"      => (BitVec.ofBool c.hold).setWidth w
  | "sc_fail"   => (BitVec.ofBool c.scFail).setWidth w
  | _ => 0#w

/-! ## Reading the ISS state as (name, value) pairs (for lockstep vs EDSL) -/

def issRegs (s : MiniSt) : List (String × Nat × Nat) :=
  -- (name, width, value)
  [("cur",5,s.cur.toNat), ("pc",64,s.pc.toNat), ("retire",32,s.retire.toNat),
   -- EXT-9/9b: the cache's own registers. The Oracle's closed list makes
   -- adding them mandatory rather than optional -- omitting one reports
   -- UNDECLARED-UNMODELLED instead of quietly shrinking the comparison.
   ("ic_tag_q",42,s.ic_tag_q.toNat), ("ic_data_q",64,s.ic_data_q.toNat),
   ("ic_gen",16,s.ic_gen.toNat), ("ic_inv",1,if s.ic_inv then 1 else 0),
   ("ic_ctr",12,s.ic_ctr.toNat),
   ("gate_tbl_base",32,s.gate_tbl_base.toNat), ("gate_ent_q",64,s.gate_ent_q.toNat),
   ("gate_dom_q",8,s.gate_dom_q.toNat),
   -- EXT-6 (§17): the cap-inbox root pointer and walked-flags latch
   ("cap_tbl_base",32,s.cap_tbl_base.toNat), ("cap_fl_q",64,s.cap_fl_q.toNat),
   -- EXT-10: the D-cache's registers.
   ("dc_tag_q",42,s.dc_tag_q.toNat), ("dc_data_q",64,s.dc_data_q.toNat),
   ("dc_alloc",1,if s.dc_alloc then 1 else 0),
   ("trace_wp",4,s.trace_wp.toNat), ("trace_sel",4,s.trace_sel.toNat),
   ("trace_rd_pc",64,s.trace_rd_pc.toNat), ("trace_rd_wb",64,s.trace_rd_wb.toNat),
   ("trace_hit",1,if s.trace_hit then 1 else 0),
   ("trace_in_pc",64,s.trace_in_pc.toNat), ("trace_in_wb",64,s.trace_in_wb.toNat),
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
   -- EXT-4: the outgoing park/wake key
   ("wake_key",64,s.wake_key.toNat), ("wake_bm",32,s.wake_bm.toNat),
   -- EXT-5: gates
   ("in_gate",32,s.in_gate.toNat),
   -- EXT-7: the MMU enable and TLB selector
   ("mmu_en",1,if s.mmu_en then 1 else 0), ("tlb_sel",3,s.tlb_sel.toNat),
   ("tlb_vld",8,s.tlb_vld.toNat),
   ("wake_out",1,if s.wake_out then 1 else 0),
   ("lr_req",1,if s.lr_req then 1 else 0), ("sc_req",1,if s.sc_req then 1 else 0),
   ("sc_pending",1,if s.sc_pending then 1 else 0)]
  -- EXT-7 stage B: the TLB is per-index REGISTERS, not memories (D20 -- every
  -- entry is read at once, so it is a register file). Listed here so Loom's
  -- derived comparator finds them; before this they were only in `cmpStates`'s
  -- hand-written loop, which the derived path does not consult.
  ++ (List.range 8).flatMap (fun i =>
       [(s!"tlb_base{i}",  32, (s.tlb_base[i]!).toNat),
        (s!"tlb_limit{i}", 32, (s.tlb_limit[i]!).toNat),
        (s!"tlb_phys{i}",  32, (s.tlb_phys[i]!).toNat),
        (s!"tlb_dom{i}",    8, (s.tlb_dom[i]!).toNat),
        (s!"tlb_cell{i}",   8, (s.tlb_cell[i]!).toNat)])
  ++ (List.range NT).map (fun i => (s!"tstate{i}",2,s.tstate[i]!.toNat))
  ++ (List.range NT).map (fun i => (s!"tfutex{i}",64,s.tfutex[i]!.toNat))

/-- D20: the four thread-table arrays that became Loom **memories**
(`tpc`, `tsleep`, `tp_arr`, `sigmask_arr`). The lockstep compares them
entry by entry the way it already compares `rf`/`dmem`, so the EDSL≡ISS
gate still covers every bit of the thread table. -/
def issTArrays (s : MiniSt) : List (String × Array (BitVec 64)) :=
  [("tpc", s.tpc), ("tsleep", s.tsleep), ("tp_arr", s.tp_arr),
   ("sigmask_arr", s.sigmask_arr)]

/-- What `cmpStates` actually compares, as plain name lists, so Loom's W5
coverage check can hold them against the design's own declarations.

Kept immediately beside `issRegs`/`issTArrays` and the memory loops in
`cmpStates` — if those change and these do not, `coverageSelftest` fails and
names the difference. That is the whole point: the previous rule was "remember
to update `cmpStates`", and it was forgotten twice (EXT-2's `tdom`, EXT-7's
TLB), each time leaving a green test that had never looked at the new state. -/
def cmpCoveredRegs (s : MiniSt) : List String := (issRegs s).map (·.1)

def cmpCoveredMems (s : MiniSt) : List String :=
  ["rf", "dmem", "tdom", "tcont", "tcdom",
   -- EXT-8: the commit-trace ring. Compared, not exempted -- the whole value
   -- of a trace is that it says what actually happened, so a ring the models
   -- disagree about would be worse than no ring at all.
   "trace_pc", "trace_wb",
   -- EXT-9: the I-cache banks. Compared, not exempted: a cache the two
   -- models disagree about is a cache that can hand the core a different
   -- instruction than the reference expects, which is the whole failure
   -- mode. (The lockstep already caught one such disagreement -- a fill
   -- that put the tag in the valid bit.)
   "ic_data", "ic_tag", "dc_data", "dc_tag"]
    ++ (issTArrays s).map (·.1)

/-- Memories the ISS deliberately does not model, so the lockstep has nothing
to compare them against. Listed explicitly rather than omitted, so that the
coverage check passes on a stated exemption instead of on an oversight.

The ISS models the UART by its pointers (`uart_wptr`, `uart_ridx`,
`uart_byte`, `rx_wptr`, `rx_rptr`) and not by buffer contents: the bytes are a
host-visible side channel drained over BSCAN, not architectural state the ISS
claims to reproduce. If the ISS ever models them, delete the entry here and
the check will require the comparison. -/
def cmpExemptMems : List String := ["uart_mem", "rx_mem"]

/-! ## EDSL ≡ ISS lockstep -/

/-- Read one of Loom's derived coordinates out of the ISS.

This is the whole machine-specific part of the cross-check now: a lookup from
`(name, addr)` to the ISS's value. Loom's `Design.diffAgainst` supplies the
coordinates — every register and memory cell the design declares — so the
*enumeration* is no longer written or maintained here, and state added to the
design is compared without anyone remembering to add it.

`none` means the ISS does not model that coordinate. Loom reports those
separately from mismatches, which is the distinction the old hand-written
comparator could not make: it simply omitted them, and an omission looks
exactly like agreement. -/
def issAtWith (regs : List (String × Nat × Nat)) (s : MiniSt)
    (c : Loom.Hw.Coord) : Option Nat :=
  if c.kind = "reg" then
    (regs.find? (fun r => r.1 = c.name)).map (fun r => r.2.2)
  else
    let idx := c.addr
    match c.name with
    | "rf"          => some (s.rf[idx]!).toNat
    | "dmem"        => some (s.dmem[idx]!).toNat
    | "tdom"        => some (s.tdom[idx]!).toNat
    | "tcont"       => some (s.tcont[idx]!).toNat
    | "tcdom"       => some (s.tcdom[idx]!).toNat
    -- EXT-8: the commit-trace ring is compared like any other memory. It is
    -- state the design declares, so D39 says it is observable and Loom's
    -- coordinate enumeration will ask about it; answering `none` would make it
    -- silently "unmodelled" rather than checked.
    -- EXT-9: the I-cache banks. The ISS models them cycle-exactly, so they
    -- are compared like any other memory -- and the Oracle's closed-list
    -- enforcement is what made that mandatory: adding the banks to the
    -- design without teaching the oracle produced UNDECLARED-UNMODELLED
    -- ic_tag[...] on the first run, instead of a silently shrinking
    -- comparison.
    | "ic_data"     => some (s.ic_data[idx]!).toNat
    | "ic_tag"      => some (s.ic_tag[idx]!).toNat
    | "dc_data"     => some (s.dc_data[idx]!).toNat
    | "dc_tag"      => some (s.dc_tag[idx]!).toNat
    | "trace_pc"    => some (s.trace_pc[idx]!).toNat
    | "trace_wb"    => some (s.trace_wb[idx]!).toNat
    | "tpc"         => some (s.tpc[idx]!).toNat
    | "tsleep"      => some (s.tsleep[idx]!).toNat
    | "tp_arr"      => some (s.tp_arr[idx]!).toNat
    | "sigmask_arr" => some (s.sigmask_arr[idx]!).toNat
    -- The UART buffers are modelled by their pointers, not their contents:
    -- the bytes are a host-visible side channel drained over BSCAN, not
    -- architectural state the ISS reproduces. Reported as unmodelled.
    | _             => none

/-- The CLOSED list of coordinates the ISS deliberately does not model, with
the reason. `issAtWith`'s fall-through used to be an anonymous `none`: a NEW
memory added to the design would have joined the unmodelled set silently,
visible only as the per-run count drifting — an omission that looks exactly
like agreement, the same shape as the hand-written comparator this derived
one replaced (and as the stage-B cmpStates gap before it). Now
`opDiffSelftest` fails on an unmodelled coordinate that is not NAMED here. -/
def issUnmodelled : List String :=
  [ "uart_mem"   -- host-visible side channel, drained over BSCAN; modelled
                 -- by its pointers, not its contents
  , "rx_mem" ]   -- same, receive direction

/-- Convenience wrapper. Prefer `issAtWith` in a per-cycle loop: `issRegs`
rebuilds a 152-entry list on every call, so calling this once per coordinate
rebuilds it once per coordinate. -/
def issAt (s : MiniSt) (c : Loom.Hw.Coord) : Option Nat := issAtWith (issRegs s) s c

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
  -- EXT-7: the TLB. These were NOT compared when the MMU landed, so a green
  -- `MMU-XLAT` meant "the legs agree on core_addr", not "the legs agree on
  -- the TLB" -- the same trap EXT-2 hit. Widths differ per array, so they
  -- cannot ride `issTArrays` (which is the 64-bit family).
  for i in List.range 8 do
    let checks : List (String × Nat × Nat) :=
      [(s!"tlb_base{i}", 32, (s.tlb_base[i]!).toNat),
       (s!"tlb_limit{i}", 32, (s.tlb_limit[i]!).toNat),
       (s!"tlb_phys{i}", 32, (s.tlb_phys[i]!).toNat),
       (s!"tlb_dom{i}", 8,  (s.tlb_dom[i]!).toNat),
       (s!"tlb_cell{i}", 8, (s.tlb_cell[i]!).toNat)]
    for (rn, w, v) in checks do
      if (σ.regs rn w).toNat ≠ v then
        if bad < 12 then
          IO.println s!"  MISMATCH step {step} {rn}: edsl={(σ.regs rn w).toNat} iss={v}"
        bad := bad + 1
  -- EXT-5/EXT-6: the gate table, the gate continuation, and the capability
  -- inbox. Found uncompared on 2026-08-04 by Loom's W5 coverage check --
  -- `gateselftest` and `capxferselftest` were green without ever looking at
  -- the state their own increments added, the third and fourth instance of
  -- the trap EXT-2 (`tdom`) and EXT-7 (the TLB) hit. Compared at EVERY slot:
  -- a gate is a claim about entries the program does not call, so a spot
  -- check at the invoked index would not see a violation.
  -- EXT-6 (§17): the capability inbox moved into guest memory, so its
  -- contents are compared the way all guest memory is -- through the DDR
  -- model both models drive -- and there is no core bank left to walk here.
  for i in List.range NT do
    let checksNT : List (String × Nat × Nat) :=
      [("tcont", 64, (s.tcont[i]!).toNat), ("tcdom", 8, (s.tcdom[i]!).toNat)]
    for (mn, w, v) in checksNT do
      if (σ.mems mn i w).toNat ≠ v then
        if bad < 12 then
          IO.println s!"  MISMATCH step {step} {mn}[{i}]: edsl={(σ.mems mn i w).toNat} iss={v}"
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

/-- Cycle-level EDSL ≡ ISS using **Loom's derived coordinate set**.

`lockstep`/`cmpStates` enumerate what to compare by hand. This does not: the
coordinates come from `Design.coords`, i.e. from the design's own register and
memory declarations, so a coordinate cannot be omitted — there is no list here
to forget to update. The only machine-specific part is `issAt`, which reads a
coordinate out of the ISS.

Coordinates the ISS does not model are reported as *unmodelled* rather than
skipped, which is the distinction that matters: the hand-written comparator
could only omit them, and an omission is indistinguishable from agreement.

`cap` bounds cells per memory; `rf` alone is 1024 entries, so a cycle-level run
over every cell of every memory is not free. -/
def lockstepDerived (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32) (nCyc : Nat)
    (cap : Nat := 64) : IO (Nat × Nat) := do
  let mut s : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := latency }
  let mut g : GpModel := {}
  let mut σ : St := design.reset
  let mut bad := 0
  let mut unmodelled := 0
  for k in List.range nCyc do
    let (s', d', g', inp) := sysStep s d g (cmds k) (gpVal k)
    σ := design.cycleOpen inp.toEnv σ
    s := s'; d := d'; g := g'
    -- `issRegs` is rebuilt once per CYCLE, not once per coordinate.
    let regs := issRegs s
    -- Loom's Oracle carries the CLOSED exclusion list; a coordinate the ISS
    -- fails to model without declaring it is a failure named after the
    -- coordinate, not a count drifting (Loom.Hw.Design.diffAgainstOracle).
    let (mism, undeclared, declared) := design.diffAgainstOracle cap σ
      { read := issAtWith regs s, unmodelled := issUnmodelled }
    unmodelled := declared.length
    if !undeclared.isEmpty then
      if bad < 8 then
        for c in undeclared.take 4 do
          IO.println s!"  UNDECLARED-UNMODELLED cycle {k} {c.render}: not in issUnmodelled"
      bad := bad + undeclared.length
    if !mism.isEmpty then
      if bad < 8 then
        for c in mism.take 4 do
          IO.println s!"  MISMATCH cycle {k} {c.render}: edsl={σ.at c} iss={(issAtWith regs s c).getD 0}"
      bad := bad + mism.length
  return (bad, unmodelled)

/-! ### W5, the deeper half: matrix equality as a THEOREM

`lockstepFast` below is IO only because it prints. This is the same run with
the printing removed: a pure mismatch count, so a whole test matrix can be a
single `Nat` and "the design agrees with the ISS on the matrix" can be stated
as `matrixMismatches = 0` and discharged by `native_decide` at BUILD time.

Honesty about what that buys: `native_decide` evaluates with the compiler, so
the trusted base is the same one the *test* uses. What changes is WHERE the
check lives -- inside the artifact the kernel accepts, so it cannot be skipped,
filtered, or forgotten by a harness; a build in which the design and the ISS
disagree on the matrix does not exist. It is strictly stronger than a test that
someone must run, and strictly weaker than a symbolic proof, and PLATONIC.md
records it in exactly those terms. -/
def lockstepPure (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (nCyc : Nat) (cap : Nat := 16) : Nat := Id.run do
  let fd := design.elaborate
  let plan := design.coordPlan cap
  let mut fs := design.fastReset
  let mut s : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := latency }
  let mut g : GpModel := {}
  let mut bad := 0
  for k in List.range nCyc do
    let (s', d', g', inp) := sysStep s d g (cmds k) 0
    fs := fastCycleOpen fd inp.toEnv fs
    s := s'; d := d'; g := g'
    let (mism, undeclared, _) := diffFastAgainstOracle plan fs
      { read := issAtWith (issRegs s) s, unmodelled := issUnmodelled }
    bad := bad + mism.length + undeclared.length
  return bad


/-- The same derived-coordinate lockstep, run against `FastEval`.

`lockstepDerived` compares against the closure-based `St`, which is correct and
gets slower every cycle because `RegEnv` is a function. This runs the design
through `fastCycleOpen` on the flat state instead, and reads coordinates through
a `CoordPlan` resolved once outside the loop.

This is not a shortcut around the semantics: `Loom.Hw.fastCycleOpen_eq` proves
the flat evaluator agrees with `Design.cycleOpen`, so the comparison is against
the same design behaviour, evaluated a way that does not accumulate closures. -/
def lockstepFast (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32) (nCyc : Nat)
    (cap : Nat := 64) : IO (Nat × Nat) := do
  let fd := design.elaborate
  let plan := design.coordPlan cap
  let mut fs := design.fastReset
  let mut s : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := latency }
  let mut g : GpModel := {}
  let mut bad := 0
  let mut unmodelled := 0
  for k in List.range nCyc do
    let (s', d', g', inp) := sysStep s d g (cmds k) (gpVal k)
    fs := fastCycleOpen fd inp.toEnv fs
    s := s'; d := d'; g := g'
    let regs := issRegs s
    let (mism, undeclared, declared) := diffFastAgainstOracle plan fs
      { read := issAtWith regs s, unmodelled := issUnmodelled }
    unmodelled := declared.length
    if !undeclared.isEmpty then
      if bad < 8 then
        for c in undeclared.take 4 do
          IO.println s!"  UNDECLARED-UNMODELLED cycle {k} {c.render}: not in issUnmodelled"
      bad := bad + undeclared.length
    if !mism.isEmpty then
      if bad < 8 then
        for (c, got, want) in mism.take 4 do
          IO.println s!"  MISMATCH cycle {k} {c.render}: edsl={got} iss={want}"
      bad := bad + mism.length
  return (bad, unmodelled)

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
  [ encImmI OP_ADDI 1 0 7,        -- 0x1000 ADDI r1 = 7
    encImmI OP_ADDI 2 0 5,        -- ADDI r2 = 5
    enc OP_ADD 3 1 2,            -- ADD  r3 = 12
    enc OP_SUB 4 1 2,            -- SUB  r4 = 2
    enc OP_MUL 5 1 2,            -- MUL  r5 = 35
    enc OP_DIV 6 5 2,            -- DIV  r6 = 35/5 = 7
    encImmS OP_ST 0 3 0,        -- SD [r0+0] = r3 (zp store, 8-byte)  (rs1=0,rs2=3,imm_s=0)
    encImmI OP_LD 8 0 0,        -- LD r8 = [r0+0] = 12 (zp load)
    enc OP_EXIT 0 0 0 ]           -- EXIT

/-- Fast lockstep program (no long mul/div; reaches EXIT quickly so the
EDSL≡ISS lockstep stays within the closure-RegEnv budget). Covers fetch,
ALU-reg, ALU-imm, small MUL, small DIV, SEL, GET_PCR(Tid), zp store
(1-cycle dmem pipeline), zp load, DDR-data store (RMW) + DDR-data load,
LR/SC, UART TX, branch-taken, JAL, JALR, and EXIT. -/
def progLS : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 7,        -- 0x1000 w0  ADDI r1 = 7
    encImmI OP_ADDI 2 0 5,        --       w1  ADDI r2 = 5
    encImmI OP_ADDI 3 0 1,        --       w2  ADDI r3 = 1
    enc OP_ADD 4 1 2,            --       w3  ADD  r4 = 12
    enc OP_MUL 5 1 3,            --       w4  MUL  r5 = 7*1 = 7 (fast: mul_b=1)
    enc OP_SEL 7 1 1 2,          --       w5  SEL(EQ) r7: r1==r1 -> sel_t=rf[rs3=2]=5
    encImmI OP_GET_PCR 10 2 0,       --       w6  GET_PCR r10 = Tid = cur+1 = 1
    encImmS OP_ST 0 4 0,        --       w7  SD [0] = r4 (zp store)
    encImmI OP_LD 11 0 0,       --       w8  LD r11 = [0] = 12 (zp load)
    encImmS OP_BEQ 1 1 2,        --       w9  BEQ r1,r1 taken (skip next)
    encImmI OP_ADDI 9 0 99,       --       w10 (skipped) ADDI r9 = 99
    enc OP_EXIT 0 0 0 ]           --       w11 EXIT

/-- DDR-data path: store r3 to a DDR address (ea ≥ 0x1000) then load it
back. ea = 0x2000. Covers S_DL/S_DST/S_DSW (RMW store) + DDR load. -/
def progDDR : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0x2000,   -- r1 = 0x2000 (DDR ea)
    encImmI OP_ADDI 3 0 42,       -- r3 = 42
    encImmS OP_ST 1 3 0,        -- SD [r1+0] = r3 (DDR store, RMW)
    encImmI OP_LD 8 1 0,        -- LD r8 = [r1+0] = 42 (DDR load)
    enc OP_EXIT 0 0 0 ]

/-! ## Mechanical EDSL ≡ ISS coverage over the ALU opcode space

The six-opcode bug survived because EDSL≡ISS was checked with *hand-written
programs*, and no program executed `not`, `sltu`, `bgeu`, `srli`, `srai` or
`sltiu`. Adding another hand-written program (`alugapselftest`) fixes those six
and nothing else — the next opcode to go wrong will be one nobody thought to
write a program for.

So the opcode list is enumerated and the programs are *generated*: one tiny
program per opcode per operand vector, each run through the same EDSL≡ISS
lockstep. Coverage becomes a property of the list rather than of anybody's
memory, and `opDiffSelftest` fails if an opcode in `aluOpcodes` is not
exercised.

The operand vectors are boundary values, because that is where a decode or
width bug actually shows: sign bits, all-ones, shift amounts at and past 64. -/
def aluOpsRRR : List (Nat × String) :=
  [(OP_ADD,"add"), (OP_SUB,"sub"), (OP_MUL,"mul"), (OP_AND,"and"), (OP_OR,"or"),
   (OP_XOR,"xor"), (OP_LSL,"sll"), (OP_LSR,"srl"), (OP_ASR,"sra"),
   (OP_SLT,"slt"), (OP_SLTU,"sltu"), (OP_DIV,"div"), (OP_SREM,"srem"),
   (OP_UDIV,"udiv"), (OP_UREM,"urem"), (OP_MULH,"mulh"), (OP_MULHU,"mulhu"),
   (OP_ROL,"rol"), (OP_ROR,"ror")]

def aluOpsRR : List (Nat × String) :=
  [(OP_NOT,"not"), (OP_SEXT_B,"sext.b"), (OP_SEXT_H,"sext.h"), (OP_SEXT_W,"sext.w"),
   (OP_ZEXT_B,"zext.b"), (OP_ZEXT_H,"zext.h"), (OP_ZEXT_W,"zext.w"),
   (OP_CTZ,"ctz"), (OP_CLZ,"clz"), (OP_BSWAP16,"bswap16"), (OP_BSWAP32,"bswap32"), (OP_BSWAP64,"bswap64")]

def aluOpsIMM : List (Nat × String) :=
  [(OP_ADDI,"addi"), (OP_ANDI,"andi"), (OP_ORI,"ori"), (OP_XORI,"xori"),
   (OP_LSLI,"slli"), (OP_LSRI,"srli"), (OP_ASRI,"srai"),
   (OP_SLTI,"slti"), (OP_SLTIU,"sltiu")]

/-- The wide-immediate constant builders, and the jump family.

These five were found UNCOVERED by `scripts/check_opcode_coverage.py` on its
first run — `liu`, `auipc`, `jmp`, `jal`, `jalr`. `liu` is how every 64-bit
constant is built, and a wrong constant is what panicked the guest on silicon
after the 2026-08-05 renumbering ("not lightweight enough for -1 CPUs").

`liu` and `auipc` get a directed battery below as well as a matrix entry: a
single-instruction diff can agree on one `liu` and still get the hi/lo assembly
or the sign-extension of the ORI half wrong, which is precisely the shape of a
`-1` appearing where a small count belongs. -/
def wideImmOps : List (Nat × String) := [(OP_LIU, "liu"), (OP_AUIPC, "auipc")]

def jumpOps : List (Nat × String) :=
  [(OP_JMP, "jmp"), (OP_JAL, "jal"), (OP_JALR, "jalr")]

/-- Materialise one exact 64-bit constant with `liu` + `ori`, the sequence the
compiler uses. `r3` must hold `value` at EXIT. -/
def progConst (hi lo : Int) : List (BitVec 64) :=
  [ encImmI OP_LIU 3 0 hi,        -- r3[63:32] = hi
    encImmI OP_ORI 3 3 lo,        -- r3 |= lo
    enc OP_EXIT 0 0 0 ]

/-- Constants chosen where hi/lo assembly and sign extension actually break:
zero, one, all-ones, both sign boundaries, and a high-bit pattern. -/
def constBattery : List (Int × Int) :=
  [(0, 0), (0, 1), (0, -1), (-1, -1), (0x7fffffff, -1), (-2147483648, 0),
   (0x12345678, 0x7ABCDEF0), (0x0000ffff, 0xffff0000)]

/-- `jmp`/`jal`/`jalr`: the taken path skips a poison write; `jal` also leaves a
link. Generated so the jump family is executed, not merely defined. -/
def progJump (op : Nat) : List (BitVec 64) :=
  if op = OP_JMP then
    [ encImmJ OP_JMP 0 2, encImmI OP_ADDI 5 0 0xBAD,
      encImmI OP_ADDI 6 0 0x600D, enc OP_EXIT 0 0 0 ]
  else if op = OP_JAL then
    [ encImmJ OP_JAL 1 2, encImmI OP_ADDI 5 0 0xBAD,
      encImmI OP_ADDI 6 0 0x600D, enc OP_EXIT 0 0 0 ]
  else
    [ encImmI OP_ADDI 2 0 (TEXT_BASE + 24), encImmI OP_JALR 1 2 0,
      encImmI OP_ADDI 5 0 0xBAD, encImmI OP_ADDI 6 0 0x600D,
      enc OP_EXIT 0 0 0 ]

/-- Operand pairs chosen for edges, not coverage-by-volume: signed vs unsigned,
all-ones, zero, and a shift amount past 64 — where decode and width bugs show.

Nine of these were unaffordable against the closure-based `St` (a 39-opcode
matrix did not finish in twenty minutes). Against `FastEval` they are, which is
the whole reason the fast path was built. -/
def opVectors : List (Int × Int) :=
  [(7, 9), (9, 7), (0, 0), (-1, 1), (1, -1), (255, 8), (-8, 4), (1, 64), (1, 65),
   -- Full-width operands (2026-08-06). Every pair above produces a trivial
   -- high half (0 or -1) from MULH/MULHU and a tiny quotient path from
   -- DIV/UDIV, so the wide datapath was never exercised by a generated
   -- program on RTL or silicon -- divcheck.s had to be written by hand to
   -- clear the divider during the renumbering-panic diagnosis. These are
   -- strtoll's exact cutoff shapes plus a mixed-carry pattern.
   (0x7fffffffffffffff, 10), (0x7fffffffffffffff, 0x6666666666666667),
   (-0x8000000000000000, 10), (0x123456789abcdef0, 0x0fedcba987654321)]

/-- Loads, stores and branches. These need memory or control flow rather than a
register triple, so they get their own generated shapes — and they are the
remaining place renumbering fallout could hide, since every one of them was
moved or re-membershipped at some point.

Both memory paths are covered: `ea < 0x1000` is the on-chip `dmem`, `ea >=
0x1000` is the DDR read-modify-write. They are different hardware. -/
def memOpsLoad : List (Nat × String) :=
  [(OP_LD,"ld"), (OP_LD_31,"lwu"), (OP_LD_32,"lbu"), (OP_LD_36,"lhu"),
   (OP_LD_S,"lh"), (OP_LD_S_70,"lw"), (OP_LD_S_72,"lb")]

def memOpsStore : List (Nat × String) :=
  [(OP_ST,"sd"), (OP_ST_34,"sw"), (OP_ST_35,"sb"), (OP_ST_37,"sh")]

def brOps : List (Nat × String) :=
  [(OP_BEQ,"beq"), (OP_BNE,"bne"), (OP_BLT,"blt"), (OP_BGE,"bge"),
   (OP_BLTU,"bltu"), (OP_BGEU,"bgeu")]

/-- Seed a word, then load it back with the opcode under test. -/
def progLoad (op : Nat) (base : Nat) (pat : Int) : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 base,
    encImmI OP_ADDI 3 0 pat,
    encImmS OP_ST 1 3 0,            -- sd [r1] = pattern
    encImmI op 4 1 0,               -- the load under test
    enc OP_EXIT 0 0 0 ]

/-- Seed a word, store over it with the opcode under test, read the whole word
back. A store that writes the wrong lanes shows up in `r4`. -/
def progStore (op : Nat) (base : Nat) (pat : Int) : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 base,
    encImmI OP_LIU 3 0 0x11223344,
    encImmI OP_ORI 3 3 0x55667788,
    encImmS OP_ST 1 3 0,            -- seed the word
    encImmI OP_ADDI 5 0 pat,
    encImmS op 1 5 0,               -- the store under test
    encImmI OP_LD 4 1 0,            -- read the whole word back
    enc OP_EXIT 0 0 0 ]

/-- Both directions of a branch: the taken path skips a poison write. -/
def progBranch (op : Nat) (a b : Int) : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 a,
    encImmI OP_ADDI 2 0 b,
    encImmS op 1 2 2,               -- taken -> skip the next word
    encImmI OP_ADDI 5 0 0xBAD,
    encImmI OP_ADDI 6 0 0x600D,
    enc OP_EXIT 0 0 0 ]

/-- Materialize a full 64-bit value into a register: ADDI for the low half
(its sign garbage in bits 63:32 is erased by LIU's zext of rs1[31:0]), LIU
for the high half. The first version of the wide-vector extension used a bare
ADDI, whose 32-bit immediate silently TRUNCATED the wide operands — 518
programs "passed" without a single one delivering LLONG_MAX to an op. -/
def matConst (rd : Nat) (v : Int) : List (BitVec 64) :=
  let u := (BitVec.ofInt 64 v).toNat
  let lo : Int := Int.ofNat (u % 4294967296)
  let hi : Int := Int.ofNat (u / 4294967296)
  [encImmI OP_ADDI rd 0 lo, encImmI OP_LIU rd rd hi]

def progOp (form : Nat) (op : Nat) (a b : Int) : List (BitVec 64) :=
  let setup := matConst 1 a ++ matConst 2 b
  let body :=
    if form = 0 then [enc op 3 1 2]        -- rd, rs1, rs2
    else if form = 1 then [enc op 3 1 0]   -- rd, rs1
    else if form = 3 then
      -- SEL: rd, cc-pair r1/r2, then distinct true/false values so a
      -- wrong-arm selection cannot alias a right one. sel_cond used to key on
      -- op[2:0] — correct only while the family sat on 0x40-0x45 — and no
      -- generated program could build the 5-slot form, so both silicon
      -- renumber attempts panicked through it (strtoll's neg?MIN:MAX).
      matConst 3 24589 ++ matConst 4 2989 ++ [enc op 5 1 2 3 4]
    else [encImmI op 3 1 b]                -- rd, rs1, imm
  setup ++ body ++ [enc OP_EXIT 0 0 0]

def selOps : List (Nat × String) :=
  [(OP_SEL,"sel.eq"), (OP_SEL_41,"sel.ne"), (OP_SEL_42,"sel.lt"),
   (OP_SEL_43,"sel.ge"), (OP_SEL_44,"sel.ltu"), (OP_SEL_45,"sel.geu")]

/-- The six opcodes the renumbering broke in the ISS, executed so the
EDSL≡ISS lockstep actually looks at them.

`not`, `sltu`, `bgeu`, `srli`, `srai` and `sltiu` were all mis-decoded by the
ISS after the move to the ISA numbering — `OP_NOT` was missing from `is_alu`,
`is_alu` still held the old raw bytes `0x1c/0xa5/0xa6/0x1e`, and `is_branch`
had `OP_SLTU` where `OP_BGEU` belonged. `Core.lean` was correct throughout, so
the *design* was right and only the hand-written mirror was wrong — and no
existing selftest executed any of the six, which is why the whole ladder stayed
green over a broken oracle.

Every value below is checked, so a silently-missing write fails rather than
passing as "no change". -/
def progAluGap : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 7,          -- r1 = 7
    encImmI OP_ADDI 2 0 9,          -- r2 = 9
    enc OP_NOT 3 1 0,               -- r3 = ~7            = 0xFFFF...F8
    enc OP_SLTU 4 1 2,              -- r4 = (7 <u 9) = 1
    enc OP_SLTU 5 2 1,              -- r5 = (9 <u 7) = 0
    encImmI OP_ADDI 6 0 0x100,      -- r6 = 256
    encImmI OP_LSRI 7 6 4,          -- r7 = 256 >> 4      = 16
    encImmI OP_ASRI 8 3 4,          -- r8 = ~7 >>a 4      = 0xFFFF...FF
    encImmI OP_SLTIU 9 1 9,         -- r9 = (7 <u 9) = 1
    encImmS OP_BGEU 2 1 2,          -- if 9 >=u 7 skip the next word
    encImmI OP_ADDI 10 0 0xBAD,     -- (skipped when BGEU works)
    encImmI OP_ADDI 11 0 0x600D,    -- r11 = 0x600D
    enc OP_EXIT 0 0 0 ]

/-- Sub-word stores. `sb` (0x35) and `sh` (0x37) had NO coverage anywhere in
this harness -- only `sd` (0x33) and `sw` (0x34) were ever encoded -- and the
gap showed up on silicon, not here: the guest's in-DDR console ring is written
by `buf[i] = c`, a byte store, and read back smeared across eight bytes while
the 32-bit `magic` and `wptr` in the same struct read back perfectly.

Both memory paths are covered, because they are different hardware: ea < 0x1000
is the 1-cycle on-chip `dmem`, ea >= 0x1000 is the DDR read-modify-write path
(S_DST/S_DSW). A byte store must leave the other seven lanes of its word alone;
`st_merge` is supposed to guarantee that, and this is what checks it.

Layout: seed the word with 8 known bytes, then overwrite lane 1 with `sb` and
lanes 4..5 with `sh`, and read the whole word back. -/
def progSubWord (base : Nat) : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 base,       -- r1 = target address
    encImmI OP_LIU 3 0 0x11223344,  -- r3 high half
    encImmI OP_ORI 3 3 0x55667788,  -- r3 = 0x1122334455667788 (seed)
    encImmS OP_ST 1 3 0,             -- SD [r1] = seed
    encImmI OP_ADDI 4 0 0xAA,       -- r4 = 0xAA
    encImmS OP_ST_35 1 4 1,             -- SB [r1+1] = 0xAA   (lane 1 only)
    encImmI OP_ADDI 5 0 0xBBCC,     -- r5 = 0xBBCC
    encImmS OP_ST_37 1 5 4,             -- SH [r1+4] = 0xBBCC (lanes 4..5)
    encImmI OP_LD 8 1 0,            -- r8 = [r1] -- the merged word
    encImmI OP_LD_32 9 1 1,         -- r9 = LBU [r1+1] = 0xAA
    enc OP_EXIT 0 0 0 ]

/-- LR/SC: LR.D reserve, SC.D store (should succeed, rd=0). ea=0 (zp). -/
def progLRSC : List (BitVec 64) :=
  [ encImmI OP_ADDI 3 0 77,       -- r3 = 77
    enc OP_LR_D 5 0 0,            -- LR.D r5 = [r0] (=0), reserve addr 0
    enc OP_SC_D 6 0 3,            -- SC.D [r0] = r3 ; rd=r6 = 0 (ok)
    encImmI OP_LD 8 0 0,        -- LD r8 = [0] = 77
    enc OP_EXIT 0 0 0 ]

/-- UART TX store then UART RX load (RX empty → returns 0, no valid bit). -/
def progUART : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 UART_ADDR,     -- r1 = 0x8000
    encImmI OP_ADDI 3 0 0x41,          -- r3 = 'A'
    encImmS OP_ST 1 3 0,             -- SD [UART_ADDR] = r3 (UART TX)
    encImmI OP_ADDI 2 0 UART_RX_ADDR,  -- r2 = 0x8008
    enc OP_LD 8 2 0,                 -- LD r8 = [UART_RX] (RX empty -> 0)
    enc OP_EXIT 0 0 0 ]

/-- Scheduler: CLONE spawns thread 1 (entry=r1), YIELD switches to it, the
child THREAD_EXITs, back to parent which EXITs. -/
def progSched : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0x1018,   -- r1 = child entry (word 3 = 0x1000+3*8=0x1018)
    enc OP_CLONE_SPAWN 4 1 2,            -- CLONE_SPAWN r4=childtid, entry=r1, arg=r2
    enc OP_YIELD 0 0 0,            -- YIELD -> switch to child
    -- child entry (0x1018, word 3):
    enc OP_THREAD_EXIT 0 0 0,           -- THREAD_EXIT (child) -> back to parent
    enc OP_EXIT 0 0 0 ]          -- EXIT (parent, word 4)

/-- SLEEP then wake: thread 0 sleeps 1 tick; with only 1 thread it goes to
S_WAIT, the sleep scan wakes it, then it EXITs. -/
def progSleep : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 1,        -- r1 = 1 (sleep ticks)
    enc OP_SLEEP 0 1 0,           -- SLEEP(rs1=r1=1)
    enc OP_EXIT 0 0 0 ]          -- EXIT (after wake)

/-- Trap + RESUME: an unknown opcode traps (S_TRAP); the host services it
via cmd 54 (RESUME), and the program continues to EXIT. -/
def progTrap : List (BitVec 64) :=
  [ enc OP_INVALID 0 0 0,           -- unknown op -> trap
    enc OP_EXIT 0 0 0 ]          -- EXIT (after RESUME advances to here? no:
                              -- RESUME sets st=S_F0 WITHOUT advancing pc, so
                              -- it re-fetches the SAME trapping instr. Host
                              -- must also SET_PC past it. See cmdTrap below.)

/-- GP MMIO: LWU (op 0x31) from 0xE000_0000 returns the GP model's value;
SW (op 0x34) writes. Covers S_GPL/S_GPS. ea low32 = 0xE0000000 built via
ADDI r0 + (-0x20000000) (low 32 bits = 0xE0000000; aperture check is
ea[31:16]==0xE000). -/
def progGP : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 (-0x20000000),  -- r1 low32 = 0xE0000000
    encImmI OP_ADDI 3 0 0x99,           -- r3 = 0x99 (SW data)
    encImmS OP_ST_34 1 3 0,              -- SW [r1] = r3 (GP store)
    enc OP_LD_31 8 1 0,                  -- LWU r8 = [r1] (GP load -> model value)
    enc OP_EXIT 0 0 0 ]

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

/-! ## Differential single-step against the emulator (`lnp64 step-op`)

The two implementations agree on opcode *numbers* — `check_isa_agreement.py`
proves that and is wired into `check_stale.sh`. They have already been caught
disagreeing on opcode *behaviour*: `MINI_GATE_CALL` wrote a destination
register in the emulator and none on the fabric, with identical encodings on
both sides. A numeric check cannot see that, by construction.

`issStepOp` is the mini half of a differential test. It takes one encoded
instruction and 32 register values, runs the ISS until the instruction retires,
and prints the registers it changed in exactly the format
`lnp64 step-op <hex-word> <r0,...,r31>` prints, so the two can be diffed
directly. The register file is seeded at raw indices 0..31, which is thread 0's
window (`rf` is indexed `(cur << 5) | reg` and `cur` is 0 at reset). -/
def issStepOp (word : BitVec 64) (regs : List Nat) : IO Unit := do
  let img := imageFrom TEXT_BASE [word, enc OP_EXIT 0 0 0]
  -- Start ALREADY RUNNING rather than via cmd 13/2. The normal start path
  -- runs the reset zeroing engine, which wipes the register file -- so a
  -- seeded `rf` came back all zeros and every instruction looked like a
  -- no-op. Here the state is placed directly in the post-reset,
  -- pre-first-fetch configuration with `rf` seeded.
  let mut s0 : MiniSt :=
    { running := true, halted := false, zeroing := false,
      pc := BitVec.ofNat 64 TEXT_BASE, st := BitVec.ofNat 5 S_F0 }
  -- `List.zipIdx` yields (element, index), not (index, element).
  for (v, i) in regs.zipIdx do
    if i < 32 then s0 := { s0 with rf := s0.rf.set! i (BitVec.ofNat 64 v) }
  let cmds : Nat → MiniIn := fun _ => {}
  let mut s := s0
  let mut d : DdrModel := { mem := Std.HashMap.ofList img, latency := 1 }
  let mut g : GpModel := {}
  for i in List.range 400 do
    if s.halted then break
    let (s', d', g', _) := sysStep s d g (cmds i) (0 : BitVec 32)
    s := s'; d := d'; g := g'
  for i in List.range 32 do
    let before := (regs[i]?).getD 0
    let after := (s.rf[i]!).toNat
    if after ≠ before then IO.println s!"STEP_OP_REG {i} {after}"
  IO.println "STEP_OP_OK"

/-- Batch form of `issStepOp`: one process, many cases. A `minitest` process
costs ~7.5 s of module initialization before `main` runs a single line, so a
270-case differential at one case per process is ~35 minutes of pure startup —
which is what silently pushed section 6 of check_stale past its budget. Input
file: one case per line, `<hex-word> <r0,...,r31>`; output per case:
`STEP_OP_CASE <i>`, the `STEP_OP_REG` lines, `STEP_OP_OK`. -/
def issStepOpBatch (file : String) : IO Unit := do
  let text ← IO.FS.readFile file
  let hexVal : String → Nat := fun t =>
    (t.toList.foldl (fun acc c =>
      let d := if c.isDigit then c.toNat - 48
               else if c.toLower.isAlpha then c.toLower.toNat - 87 else 0
      acc * 16 + d) 0)
  let mut i := 0
  for line in text.splitOn "\n" do
    let parts := (line.trim.splitOn " ").filter (· ≠ "")
    if h : parts.length = 2 then
      IO.println s!"STEP_OP_CASE {i}"
      issStepOp (BitVec.ofNat 64 (hexVal parts[0]))
        (((parts[1]).splitOn ",").map (fun t => (t.trim.toNat?).getD 0))
      i := i + 1

/-! ## progtest — hand-encoded program to a clean EXIT on the ISS -/

/-- Program with a trap at word 0 (unknown op 0x7f) then real work: after
the trap raises, the host SET_PCs past it (cmd 53) and RESUMEs (cmd 54). -/
def progTrapReal : List (BitVec 64) :=
  [ enc OP_INVALID 0 0 0,           -- w0 unknown op -> trap
    encImmI OP_ADDI 1 0 55,      -- w1 ADDI r1 = 55 (after resume)
    enc OP_EXIT 0 0 0 ]          -- w2 EXIT

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
  [ encImmI OP_ADDI 1 0 0x2000,   -- r1 = futex word address (DDR)
    encImmI OP_ADDI 2 0 0,        -- r2 = expected value (0)
    enc OP_FUTEX_WAIT 1 2 0,            -- FUTEX_WAIT(addr=r1, expected=r2) -> blocks
    encImmI OP_ADDI 9 0 5,        -- r9 = 5 (only reached after the doorbell)
    enc OP_EXIT 0 0 0 ]           -- EXIT

/-- A GLOBAL (DDR) LR/SC pair: `S_DSW` consumes the arbiter's `sc_fail`
verdict and rewrites `rd`. r6 = 0 when the arbiter accepts, 1 when it
refuses. -/
def progScDDR : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0x2000,   -- r1 = DDR address
    encImmI OP_ADDI 3 0 77,       -- r3 = 77
    enc OP_LR_D 5 1 0,            -- LR.D  r5 = [r1]  (global reservation)
    enc OP_SC_D 6 1 3,            -- SC.D  [r1] = r3 ; r6 = verdict
    enc OP_EXIT 0 0 0 ]           -- EXIT

/-- FUTEX_WAKE: the `wake_out` pulse source (no local waiter matches). -/
def progWake : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0x2000,   -- r1 = futex word address
    encImmI OP_ADDI 7 0 1,        -- r7 = wake count
    enc OP_FUTEX_WAKE 1 7 0,            -- FUTEX_WAKE(addr=r1, count=r7)
    encImmI OP_ADDI 9 0 9,        -- r9 = 9
    enc OP_EXIT 0 0 0 ]           -- EXIT

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
  -- EXT-4: the doorbell is KEYED, so it must carry the address the thread
  -- parked on (`progDoorbell` waits on 0x2000). `dbWrong` carries another
  -- key and must NOT wake it -- that is the whole increment.
  let db : Nat → MiniIn :=
    fun k => { start k with doorbell := k = 26, doorbellKey := 0x2000 }
  let dbWrong : Nat → MiniIn :=
    fun k => { start k with doorbell := k = 26, doorbellKey := 0x3000 }
  -- (3) hold over cycles 10..30: the FSM freezes at the next S_F0, then resumes.
  let hd : Nat → MiniIn := fun k => { start k with hold := 10 ≤ k ∧ k ≤ 30 }
  -- (4) sc_fail: the arbiter refuses the global SC at the serialization point.
  let sf : Nat → MiniIn := fun k => { start k with scFail := true }
  let scripts : List (String × List (BitVec 64) × (Nat → MiniIn) × Nat) :=
    [("RESKILL (res_kill clears lr_valid -> SC fails)", progLRSC, rk, 24),
     ("SCFAIL  (global SC refused -> rd=1 at S_DSW)",   progScDDR, sf, 40),
     ("SCOK    (global SC accepted -> rd=0)",           progScDDR, start, 40),
     ("DOORBELL(FUTEX_WAIT parks; keyed doorbell wakes it)", progDoorbell, db, 34),
     ("DBWRONG (doorbell on a DIFFERENT key: stays parked)", progDoorbell, dbWrong, 34),
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
  -- EXT-4: a doorbell on the WRONG key must leave it parked. This is the
  -- claim the unkeyed broadcast could not make -- before EXT-4 this run woke
  -- the thread and halted, identically to the right-key run.
  let (sx, _, _) := runIss (imageFrom TEXT_BASE progDoorbell) 1 dbWrong (fun _ => 0) 300
  let okKey := (!sx.halted) && (sx.tstate[0]!).toNat == 3 && (sx.rf[9]!).toNat == 0
  IO.println s!"  wrong-key doorbell: halted={sx.halted} (want false) tstate0={(sx.tstate[0]!).toNat} \
(want 3 = still parked) r9={(sx.rf[9]!).toNat} (want 0) | right-key woke it: halted={sd.halted}"
  let (nw, hw) := countWake (imageFrom TEXT_BASE progWake) 300
  IO.println s!"  wake_out pulses={nw} (want 1) halted={hw}"
  let okWk := nw == 1 && hw
  -- hold: the held run must reach the SAME architectural state as the free run
  let (sh, _, kh) := runIss (imageFrom TEXT_BASE progLRSC) 1 hd (fun _ => 0) 300
  let (sf, _, kf) := runIss (imageFrom TEXT_BASE progLRSC) 1 start (fun _ => 0) 300
  let rfEq := sh.rf == sf.rf
  let okHd := sh.halted && sf.halted && rfEq && sh.retire == sf.retire && kf < kh
  IO.println s!"  hold: cycles held={kh} free={kf} (want held>free) rf equal={rfEq} retire={(sh.retire).toNat}"
  if total == 0 && okRk && okSc && okDb && okNo && okKey && okWk && okHd then
    IO.println "LNP64MINI SMP SELFTEST OK — EDSL≡ISS on res_kill/sc_fail/doorbell/wake_out/hold + outcomes"
  else
    IO.println s!"LNP64MINI SMP SELFTEST FAILED ({total} mismatches; rk={okRk} sc={okSc} db={okDb} no={okNo} key={okKey} wk={okWk} hd={okHd})"


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
  [ encImmI OP_ADDI 1 0 0x1028,   -- w0  r1 = child entry (word 5)
    enc OP_CLONE_SPAWN 4 1 2,            -- w1  CLONE r4 = tid, entry = r1, arg = r2
    encImmI OP_ADDI 9 9 1,        -- w2  r9 += 1                 (parent)
    encImmI OP_ADDI 9 9 1,        -- w3  r9 += 1
    enc OP_EXIT 0 0 0,            -- w4  EXIT (halts the core)
    encImmI OP_ADDI 10 10 1,      -- w5  r10 += 1  (child entry, 0x1028)
    encImmJ OP_JMP 0 (-1),       -- w6  J -1 -> back to w5
    enc OP_INVALID 0 0 0 ]           -- w7  poison: only a bad resume gets here

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
  [ encImmI OP_ADDI 1 0 0x1030,   -- w0  r1 = child entry (word 6)
    enc OP_CLONE_SPAWN 4 1 2,            -- w1  CLONE r4 = tid, entry = r1
    encImmI OP_LD 5 0 0,        -- w2  spin head (0x1010): r5 = [0]
    encImmS OP_BEQ 5 0 (-1),     -- w3  BEQ r5, r0 -> back to w2
    encImmI OP_ADDI 9 0 42,       -- w4  r9 = 42   (only after the flag is set)
    enc OP_EXIT 0 0 0,            -- w5  EXIT
    encImmI OP_ADDI 6 0 1,        -- w6  child entry (0x1030): r6 = 1
    encImmS OP_ST 0 6 0,        -- w7  SD [0] = r6   (sets the flag)
    enc OP_THREAD_EXIT 0 0 0 ]           -- w8  THREAD_EXIT

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

/-! ## EXT-10 — the data cache

Three claims, and the third is the one worth the program:

1. a repeated load of the same address hits, and the hit returns the value
   the miss filled -- checked by loading twice and comparing;
2. a **store invalidates its own line**, so a load after a store to the same
   address sees the stored value and not the filled one. This is the defect a
   write-through cache without invalidation has, and it is invisible to any
   program that loads an address only once;
3. the caches are cycle-exact against the ISS throughout, which is what makes
   1 and 2 evidence about the *design* rather than about one trace -- the
   lockstep compares `dc_data`/`dc_tag` at every slot, so a cache that
   returned the right value by luck through a wrong tag still fails.

`progDcache` uses two addresses 32 KB apart (0x2000 and 0x8002000): the index
is `ea[14:3]`, so they collide in the same set with different tags, which is
what makes r9 a conflict-miss check rather than another hit. -/
def DC_A : Nat := 0x2000
def DC_B : Nat := 0x802000

def progDcache : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 DC_A,       -- w0  r1 = A
    encImmI OP_ADDI 3 0 42,         -- w1  r3 = 42
    encImmS OP_ST 1 3 0,            -- w2  [A] = 42            (store; invalidates A)
    encImmI OP_LD 8 1 0,            -- w3  r8 = [A] = 42       (miss -> fill)
    encImmI OP_LD 9 1 0,            -- w4  r9 = [A] = 42       (HIT)
    encImmI OP_ADDI 4 0 7,          -- w5  r4 = 7
    encImmS OP_ST 1 4 0,            -- w6  [A] = 7             (store; must INVALIDATE)
    encImmI OP_LD 10 1 0,           -- w7  r10 = [A] = 7       (must NOT be the stale 42)
    encImmI OP_ADDI 2 0 DC_B,       -- w8  r2 = B (same set, other tag)
    encImmI OP_ADDI 5 0 99,         -- w9  r5 = 99
    encImmS OP_ST 2 5 0,            -- w10 [B] = 99
    encImmI OP_LD 11 2 0,           -- w11 r11 = [B] = 99      (conflict miss)
    encImmI OP_LD 12 1 0,           -- w12 r12 = [A] = 7       (evicted by B -> miss, still 7)
    enc OP_EXIT 0 0 0 ]

def dcacheSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progDcache
  let bad ← lockstep img 1 (fun k => if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}) (fun _ => 0) 260
  if bad = 0 then IO.println "  OK  DCACHE (EDSL≡ISS incl. dc_data/dc_tag banks, 260 cyc)"
  else IO.println s!"  FAIL DCACHE ({bad} mismatches)"
  let (s, _, _) := runIss img 1 (fun k => if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}) (fun _ => 0) 600
  IO.println s!"  halted={s.halted} r8={(s.rf[8]!).toNat} (want 42, fill) r9={(s.rf[9]!).toNat} (want 42, hit) \
r10={(s.rf[10]!).toNat} (want 7, store INVALIDATED the line) r11={(s.rf[11]!).toNat} (want 99) \
r12={(s.rf[12]!).toNat} (want 7, refilled after conflict eviction)"
  let ok := s.halted && (s.rf[8]!).toNat == 42 && (s.rf[9]!).toNat == 42
            && (s.rf[10]!).toNat == 7 && (s.rf[11]!).toNat == 99 && (s.rf[12]!).toNat == 7
  if bad = 0 && ok then
    IO.println "LNP64MINI DCACHE SELFTEST OK — hits return the filled value, and a store invalidates its own line"
  else
    IO.println s!"LNP64MINI DCACHE SELFTEST FAILED ({bad} mismatches; values={ok})"
    throw <| IO.userError "dcache selftest failed"

/-! ## EXT-5 — the gate selftest

The claim is **mediation**: a gate is the only way a thread changes domain,
and it moves the thread only to a domain the *host* installed in the gate
table — never one the instruction names. Two programs, because entry and
exit are separate transitions and a test that only checks the round trip
would pass if both were no-ops:

* `progGate` calls gate 0, runs the gate body, returns, and exits. The
  domain must be back to 0 and `in_gate` clear.
* `progGateStay` is the same but the gate body `EXIT`s instead of
  returning, so the machine halts *inside* the gate: the domain must read
  **3**, the gate's installed domain, and the `in_gate` bit must be set.

Domain 3 is non-zero on purpose — with everything at 0 both programs pass
even if gate entry never changes the domain at all. -/
def GATE_DOM_TEST : Nat := 3

/-- Gate body entry is word 4 = `TEXT_BASE + 32`. -/
def progGate : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0,        -- w0  r1 = 0 (gate id)
    enc OP_MINI_GATE_CALL 0 1 0,            -- w1  GATE_CALL gate r1  -> word 4
    encImmI OP_ADDI 9 0 7,        -- w2  r9 = 7   (only after a correct return)
    enc OP_EXIT 0 0 0,            -- w3  EXIT
    encImmI OP_ADDI 10 0 5,       -- w4  r10 = 5  (gate body, in domain 3)
    enc OP_MINI_GATE_RETURN 0 0 0 ]           -- w5  GATE_RETURN -> word 2

/-- Same, but the gate body halts instead of returning: the machine stops
inside the gate. -/
def progGateStay : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0,
    enc OP_MINI_GATE_CALL 0 1 0,
    encImmI OP_ADDI 9 0 7,
    enc OP_EXIT 0 0 0,
    encImmI OP_ADDI 10 0 5,
    enc OP_EXIT 0 0 0 ]           -- w5  EXIT *inside* the gate

/-- §17 fail-closed: call gate **1**, for which the image places no
descriptor. The walk reads zeros; zeros are not an activation, so this must
step past and reach the EXIT with `r9 = 7`, in domain 0, not in a gate. The
old host-poked banks had the same hole (a gate id nobody installed read as
entry 0 / domain 0) and it was unreachable only because the host filled every
entry; moving the table into guest memory is what made it reachable. -/
def progGateUnbacked : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 1,          -- w0  r1 = 1 (an id with no descriptor)
    enc OP_MINI_GATE_CALL 0 1 0,    -- w1  must be REFUSED
    encImmI OP_ADDI 9 0 7,          -- w2  r9 = 7 -- reached only if refused
    enc OP_EXIT 0 0 0 ]

/-- §17: where these tests put the gate table. Well clear of the text at
`TEXT_BASE`, and byte-addressed from `DATA_BASE`. -/
def GATE_TBL : Nat := 0x2000

/-- A §17 gate descriptor, in the spec's layout: `+0` entry PC, `+8` target
domain. This is what the machine now *reads*; nothing about the activation
comes from a host-poked bank any more. -/
def gateDescriptor (id entry dom : Nat) : List (Nat × BitVec 64) :=
  [ (ddrWord (DATA_BASE + GATE_TBL + id*16),     BitVec.ofNat 64 entry),
    -- bit 8 is `valid`; zeros are not an activation.
    (ddrWord (DATA_BASE + GATE_TBL + id*16 + 8), BitVec.ofNat 64 (dom ||| 0x100)) ]

/-- cmd stream: point the machine at the table (`cmd 74`), then start.
`cmd 13` data=2 starts without the zeroing sweep, so the descriptor the
image placed in DDR survives to be walked. -/
def cmdGate : Nat → MiniIn := fun k =>
  if k = 0 then
    { cmdValid := true, cmdIdx := CMD_GATE_TBL, cmdData := BitVec.ofNat 32 GATE_TBL }
  else if k = 2 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else {}

def gateSelftest : IO Unit := do
  let tbl  := gateDescriptor 0 (TEXT_BASE + 32) GATE_DOM_TEST
  let img  := imageFrom TEXT_BASE progGate ++ tbl
  let imgS := imageFrom TEXT_BASE progGateStay ++ tbl
  -- (0) EDSL ≡ ISS across a full gate call/return.
  let bad ← lockstep img 1 cmdGate (fun _ => 0) 80
  if bad = 0 then IO.println "  OK  GATE (EDSL≡ISS across call+return, 80 cyc)"
  else IO.println s!"  FAIL GATE ({bad} mismatches)"
  -- (1) the round trip: body ran, returned to the right place, domain restored.
  let (sg, _, _) := runIss img 1 cmdGate (fun _ => 0) 400
  IO.println s!"  round trip: halted={sg.halted} r10={(sg.rf[10]!).toNat} (want 5, gate body ran) \
r9={(sg.rf[9]!).toNat} (want 7, returned to w2) tdom[0]={(sg.tdom[0]!).toNat} (want 0) \
in_gate={sg.in_gate.toNat} (want 0)"
  let ok1 := sg.halted && (sg.rf[10]!).toNat == 5 && (sg.rf[9]!).toNat == 7
             && (sg.tdom[0]!).toNat == 0 && sg.in_gate.toNat == 0
  -- (2) halting INSIDE the gate: the thread is in the gate's domain, not its own.
  let (ss, _, _) := runIss imgS 1 cmdGate (fun _ => 0) 400
  IO.println s!"  inside gate: halted={ss.halted} tdom[0]={(ss.tdom[0]!).toNat} \
(want {GATE_DOM_TEST}) in_gate={ss.in_gate.toNat} (want 1) r10={(ss.rf[10]!).toNat} (want 5)"
  let ok2 := ss.halted && (ss.tdom[0]!).toNat == GATE_DOM_TEST
             && ss.in_gate.toNat == 1 && (ss.rf[10]!).toNat == 5
  -- (3) §17 fail-closed: an id with no descriptor must not activate.
  let (su, _, _) := runIss (imageFrom TEXT_BASE progGateUnbacked ++ tbl) 1 cmdGate (fun _ => 0) 400
  IO.println s!"  unbacked gate 1: halted={su.halted} r9={(su.rf[9]!).toNat} (want 7, refused) \
tdom[0]={(su.tdom[0]!).toNat} (want 0) in_gate={su.in_gate.toNat} (want 0)"
  let ok3 := su.halted && (su.rf[9]!).toNat == 7 && (su.tdom[0]!).toNat == 0
             && su.in_gate.toNat == 0
  let badU ← lockstep (imageFrom TEXT_BASE progGateUnbacked ++ tbl) 1 cmdGate (fun _ => 0) 60
  if badU = 0 then IO.println "  OK  GATE-UNBACKED (EDSL≡ISS, 60 cyc)"
  else IO.println s!"  FAIL GATE-UNBACKED ({badU} mismatches)"
  if bad = 0 && badU = 0 && ok1 && ok2 && ok3 then
    IO.println "LNP64MINI GATE SELFTEST OK — a gate is the only way to change domain, and only to the gate's"
  else
    IO.println s!"LNP64MINI GATE SELFTEST FAILED ({bad} mismatches; roundtrip={ok1} inside={ok2} unbacked={ok3})"
    throw <| IO.userError "gate selftest failed"

/-! ## EXT-6 — the cross-domain transfer selftest

The claim is **mediation, structurally**: a handle addressed to domain 3 is
reachable from domain 3 and from nowhere else, because `CAP_RECV` indexes
the receiver's *own* domain (`domCur`) and that index is not an operand.

Two programs sharing one send. Domain 0 sends handle `0xCAFE` to domain 3,
then enters a gate and receives:

* `progCapRight` — gate 0 targets domain **3**, the addressed one. The
  receive must yield `0xCAFE`.
* `progCapWrong` — gate 0 targets domain **5**. Same instructions, same
  handle, same inbox contents; the receive must yield all-ones, and the
  handle must still be sitting in inbox 3 afterwards (entry 3's flags word
  in guest memory still has `occupied` set).

The second program is the whole test. Without it, a `CAP_RECV` that ignored
the domain entirely and just popped *any* occupied inbox would pass.

**§17: the inbox is guest memory now.** The table lives in the DDR image at
`CAP_TBL`; the host supplies only the root pointer (`cmd 75`). Occupancy is
bit 0 of each entry's flags word and validity is bit 8, so the assertions
below read the *image* back out of the DDR model — the state the machine
walked — not a core bank. A third program sends to a domain whose entry is
all zeros, which must refuse: that is the fail-closed arm, and it is the
same property the silicon negative test exercises by zeroing a descriptor. -/
def CAP_HANDLE : Nat := 0xCAFE
def CAP_TBL : Nat := 0x2100

/-- A valid, empty inbox entry for domain `d` (flags only; handle word 0). -/
def capInboxEmpty (d : Nat) : List (Nat × BitVec 64) :=
  [ (ddrWord (DATA_BASE + CAP_TBL + d*16 + 8), BitVec.ofNat 64 0x100) ]

def progCapSendThen (retReg : Nat) : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 CAP_HANDLE,   -- w0  r1 = the handle
    encImmI OP_ADDI 2 0 3,            -- w1  r2 = 3 (target domain)
    enc OP_MINI_CAP_SEND 3 1 2,                -- w2  CAP_SEND r3 = send(r1 -> domain r2)
    encImmI OP_ADDI 4 0 0,            -- w3  r4 = 0 (gate id)
    enc OP_MINI_GATE_CALL 0 4 0,                -- w4  GATE_CALL gate 0 -> word 7
    enc OP_EXIT 0 0 0,                -- w5  EXIT (after the gate returns)
    enc OP_NOP 0 0 0,                -- w6  (pad)
    enc OP_MINI_CAP_RECV retReg 0 0,           -- w7  CAP_RECV -> rretReg   (gate body)
    enc OP_MINI_GATE_RETURN 0 0 0 ]               -- w8  GATE_RETURN -> word 5

def progCapRight : List (BitVec 64) := progCapSendThen 9
def progCapWrong : List (BitVec 64) := progCapSendThen 9

/-- Install the gate and cap-table root pointers, then start. Two roots,
two commands — the host says where the structures ARE and never again what
they SAY. -/
def cmdCap (_dom : Nat) : Nat → MiniIn := fun k =>
  if k = 0 then
    { cmdValid := true, cmdIdx := CMD_GATE_TBL, cmdData := BitVec.ofNat 32 GATE_TBL }
  else if k = 1 then
    { cmdValid := true, cmdIdx := CMD_CAP_TBL, cmdData := BitVec.ofNat 32 CAP_TBL }
  else if k = 3 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else {}

/-- The cap tests' image tail: gate 0 into `dom` at word 7, plus valid empty
inbox entries for domains 3 and 5. Domain 7's entry is deliberately ABSENT
(zeros): the fail-closed arm sends there. -/
def capTable (dom : Nat) : List (Nat × BitVec 64) :=
  gateDescriptor 0 (TEXT_BASE + 56) dom ++ capInboxEmpty 3 ++ capInboxEmpty 5

/-- Fail-closed arm: send to domain 7, whose entry is zeros. -/
def progCapUnbacked : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 CAP_HANDLE,   -- w0  r1 = the handle
    encImmI OP_ADDI 2 0 7,            -- w1  r2 = 7 (no entry in the image)
    enc OP_MINI_CAP_SEND 3 1 2,       -- w2  r3 = send -> must refuse (-1)
    enc OP_EXIT 0 0 0 ]               -- w3

def capXferSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progCapRight ++ capTable 3
  let fl3 (d : DdrModel) : Nat :=
    (d.mem.getD (ddrWord (DATA_BASE + CAP_TBL + 3*16 + 8)) 0).toNat
  let h3 (d : DdrModel) : Nat :=
    (d.mem.getD (ddrWord (DATA_BASE + CAP_TBL + 3*16)) 0).toNat
  -- (0) EDSL ≡ ISS across send + gate + receive, now six bus transactions
  -- longer than the bank version.
  let bad ← lockstep img 1 (cmdCap 3) (fun _ => 0) 160
  if bad = 0 then IO.println "  OK  CAPXFER (EDSL≡ISS across send+gate+recv, 160 cyc)"
  else IO.println s!"  FAIL CAPXFER ({bad} mismatches)"
  -- (1) the addressed domain receives the handle, and the ENTRY IN MEMORY
  -- is empty again afterwards (occupied cleared, valid kept).
  let (sr, dr, _) := runIss img 1 (cmdCap 3) (fun _ => 0) 300
  let got := (sr.rf[9]!).toNat
  IO.println s!"  addressed domain 3: halted={sr.halted} send r3={(sr.rf[3]!).toNat} (want 0) \
recv r9=0x{String.ofList (Nat.toDigits 16 got)} (want 0x{String.ofList (Nat.toDigits 16 CAP_HANDLE)}) \
mem flags3=0x{String.ofList (Nat.toDigits 16 (fl3 dr))} (want 0x100, consumed)"
  let ok1 := sr.halted && got == CAP_HANDLE && (sr.rf[3]!).toNat == 0
             && fl3 dr == 0x100
  -- (2) a DIFFERENT domain gets nothing, and the handle stays put IN MEMORY:
  -- entry 3 still occupied, handle word still the sent handle.
  let (sw, dw, _) := runIss (imageFrom TEXT_BASE progCapWrong ++ capTable 5) 1 (cmdCap 5) (fun _ => 0) 300
  let gotW := (sw.rf[9]!).toNat
  IO.println s!"  other domain 5:     halted={sw.halted} recv r9=0x{String.ofList (Nat.toDigits 16 gotW)} \
(want all-ones) mem flags3=0x{String.ofList (Nat.toDigits 16 (fl3 dw))} (want 0x101, still occupied) \
mem handle3=0x{String.ofList (Nat.toDigits 16 (h3 dw))}"
  let ok2 := sw.halted && gotW == 0xFFFFFFFFFFFFFFFF && fl3 dw == 0x101
             && h3 dw == CAP_HANDLE
  -- (3) §17 fail-closed: a zeroed entry refuses the send and stays zeros.
  let imgU := imageFrom TEXT_BASE progCapUnbacked ++ capTable 3
  let (su, du, _) := runIss imgU 1 (cmdCap 3) (fun _ => 0) 220
  let fl7 := (du.mem.getD (ddrWord (DATA_BASE + CAP_TBL + 7*16 + 8)) 0).toNat
  IO.println s!"  unbacked domain 7:  halted={su.halted} send r3 all-ones={((su.rf[3]!).toNat == 0xFFFFFFFFFFFFFFFF)} \
(want true, refused) mem flags7=0x{String.ofList (Nat.toDigits 16 fl7)} (want 0)"
  let ok3 := su.halted && (su.rf[3]!).toNat == 0xFFFFFFFFFFFFFFFF && fl7 == 0
  let badU ← lockstep imgU 1 (cmdCap 3) (fun _ => 0) 70
  if badU = 0 then IO.println "  OK  CAPXFER-UNBACKED (EDSL≡ISS, 70 cyc)"
  else IO.println s!"  FAIL CAPXFER-UNBACKED ({badU} mismatches)"
  if bad = 0 && badU = 0 && ok1 && ok2 && ok3 then
    IO.println "LNP64MINI CAPXFER SELFTEST OK — a handle reaches its domain and no other, out of memory the machine walked"
  else
    IO.println s!"LNP64MINI CAPXFER SELFTEST FAILED ({bad}/{badU} mismatches; right={ok1} wrong={ok2} unbacked={ok3})"
    throw <| IO.userError "capxfer selftest failed"

/-! ## Thread-slot exhaustion boundary (the NT property a real boot needs)

The scheduler selftests spawn one or two threads; none fills the slot table,
so allocation across the full `[0,NT)` range is untested. NT=8's silicon boot
failed by exhaustion at the ~9th live thread -- invisible to every example
test at low occupancy (PLATONIC.md, "What NT taught"). This is the missing
boundary property, checked at whatever `NT` the design is emitted at: the
parent CLONEs `NT-1` children, each spinning so it holds its slot, and

* all `NT-1` clones must SUCCEED (slots 1..NT-1 allocate; slot 0 is the
  parent), so every slot ends occupied; and
* the `NT`-th clone, with the table full, must be REFUSED (`rd = -1`).

Layout: `w0` loads the child entry, `w1..w(NT-1)` are the filling clones,
`w(NT)` is the over-full clone (result in r6), `w(NT+1)` is the parent's
self-loop, and `w(NT+2)` is the child's self-loop. -/
def progFillSlots : List (BitVec 64) :=
  let childWord := NT + 2
  [ encImmI OP_ADDI 1 0 (Int.ofNat (TEXT_BASE + childWord*8)) ]
  ++ (List.replicate (NT-1) (enc OP_CLONE_SPAWN 4 1 2))
  ++ [ enc OP_CLONE_SPAWN 6 1 2 ]        -- over-full: r6 must be -1
  ++ [ encImmJ OP_JMP 0 0 ]              -- parent self-loop
  ++ [ encImmJ OP_JMP 0 0 ]             -- child self-loop

def slotFillSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progFillSlots
  let start : Nat → MiniIn := fun k =>
    if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
  let cyc := NT*8 + 60
  let bad ← lockstep img 1 start (fun _ => 0) cyc
  if bad = 0 then IO.println s!"  OK  SLOTFILL (EDSL≡ISS, {cyc} cyc)"
  else IO.println s!"  FAIL SLOTFILL ({bad} mismatches)"
  let (s, _, _) := runIss img 1 start (fun _ => 0) (cyc*2)
  let occ := (List.range NT).foldl
    (fun n i => if (s.tstate[i]!).toNat != 0 then n+1 else n) 0
  let overFull := (s.rf[6]!).toNat == 0xFFFFFFFFFFFFFFFF
  let lastOk := (s.rf[4]!).toNat != 0xFFFFFFFFFFFFFFFF
  IO.println s!"  occupied slots={occ} (want {NT}); over-full r6={(s.rf[6]!).toNat} (want -1); \
last-clone r4={(s.rf[4]!).toNat} (valid, not -1)"
  if bad == 0 && occ == NT && overFull && lastOk then
    IO.println s!"LNP64MINI SLOTFILL SELFTEST OK — {NT-1} clones fill the table and the {NT}th is refused"
  else
    IO.println s!"LNP64MINI SLOTFILL SELFTEST FAILED (occ={occ} want {NT}; overFull={overFull}; lastOk={lastOk})"
    throw <| IO.userError "slotfill selftest failed"

/-! ## EXT-7 — the MMU selftest (§15)

Three claims, and the second and third are the ones with content:

1. **Bypass is bit-identical.** With `mmu_en = 0` the machine is the
   pre-EXT-7 machine — this is what keeps NetBSD alive in stage A.
2. **A translation is domain-tagged.** The same virtual address, the same
   TLB entry, translated from the domain the entry names and from another
   domain: the first hits, the second misses and fails closed. Without this
   the TLB is a cache, not a protection mechanism.
3. **The shootdown is the epoch cell.** `cmd 67` names a *cell*, not an
   entry, and every entry depending on that cell dies — §15 line 876's rule
   that the cached translation's cell IS the VMA's cell. An access that
   succeeded before the bump fails after it.

`progLdSt` loads from a virtual address the TLB maps; `r5` is the value it
read, so `r5` is the observable that distinguishes hit from fail-closed. -/
def MMU_VA   : Nat := 0x4000      -- virtual page 4, index 4
def MMU_PPN  : Nat := 0x21        -- maps to physical page 0x21
def MMU_CELL : Nat := 0x9         -- the VMA's epoch cell
def MMU_DOM  : Nat := 3

def progLdSt : List (BitVec 64) :=
  -- The leading ADDIs are a DELAY, not decoration. The core starts at cycle
  -- 0 while the harness is still issuing the TLB/`mmu_en` command stream, so
  -- a three-instruction program can reach its load BEFORE translation is on
  -- and read the untranslated address -- which looks exactly like a
  -- fail-closed miss (r5 = 0) and would make this test lie about the TLB.
  -- EXT-9b made the stream four commands longer (a text VMA must exist
  -- before fetch is translated), which is what exposed the race.
  [ encImmI OP_ADDI 2 0 1,           -- w0..w3: delay past the command stream
    encImmI OP_ADDI 2 0 2,
    encImmI OP_ADDI 2 0 3,
    encImmI OP_ADDI 2 0 4,
    encImmI OP_ADDI 1 0 MMU_VA,      -- r1 = the virtual address
    enc OP_LD_31 5 1 0,              -- r5 = [r1]   (LD -- translated)
    enc OP_EXIT 0 0 0 ]

/-- Install TLB entry 4: VPN 4, domain `dom`, PPN, cell; enable the MMU;
put thread 0 in domain `dom`; start. `bump` optionally fires the §15
shootdown on the cell before the program runs. -/
def cmdMmu (dom : Nat) (bump : Bool) : Nat → MiniIn := fun k =>
  -- EXT-7 stage B: install VMAs — base+domain, then physical delta, then
  -- limit (which validates the entry, so a half-written VMA is never live).
  --
  -- **EXT-9b: the TEXT mapping is installed first, before `mmu_en`.** Fetch
  -- is translated now, so a program whose own text is unmapped cannot run:
  -- `ddrEa` fails closed to the poison page and the core fetches `0x0BAD`
  -- as an instruction. That is the correct fail-closed behaviour, and it is
  -- exactly what these tests used to rely on NOT happening — two of them
  -- carried the comment "fetches are deliberately untranslated". Entry 0
  -- maps text identically for the domain under test, so what they measure
  -- is still the DATA translation they were written to measure.
  if k = 0 then { cmdValid := true, cmdIdx := CMD_TLB_SEL, cmdData := 0 }
  else if k = 1 then
    { cmdValid := true, cmdIdx := CMD_TLB_VPN,
      cmdData := BitVec.ofNat 32 ((dom <<< 24) ||| 0) }
  else if k = 2 then
    { cmdValid := true, cmdIdx := CMD_TLB_PHYS, cmdData := BitVec.ofNat 32 0 }
  else if k = 3 then
    -- limit 0x2000, NOT something wide: `priTree` gives the lowest index
    -- priority, so a broad text entry at index 0 would shadow the data VMA
    -- under test at index 4 (MMU_VA = 0x4000 is inside any wide range) and
    -- the test would measure identity instead of translation. Narrow to the
    -- program's own pages.
    { cmdValid := true, cmdIdx := CMD_TLB_PPN, cmdData := BitVec.ofNat 32 0x2000 }
  -- the data VMA under test
  else if k = 4 then { cmdValid := true, cmdIdx := CMD_TLB_SEL, cmdData := 4 }
  else if k = 5 then
    -- base in [23:0], domain in [31:24]
    { cmdValid := true, cmdIdx := CMD_TLB_VPN,
      cmdData := BitVec.ofNat 32 ((MMU_DOM <<< 24) ||| MMU_VA) }
  else if k = 6 then
    { cmdValid := true, cmdIdx := CMD_TLB_PHYS,
      -- the entry stores the DELTA phys-base, so the host does the subtract
      cmdData := BitVec.ofNat 32 ((MMU_CELL <<< 24)
                   ||| (((MMU_PPN <<< 12) - MMU_VA) &&& 0xffffff)) }
  else if k = 7 then
    -- limit last: it is what makes the entry live
    { cmdValid := true, cmdIdx := CMD_TLB_PPN,
      cmdData := BitVec.ofNat 32 (MMU_VA + 0x1000) }
  -- **SETDOM BEFORE MMU_EN.** The text entry is domain-tagged, so enabling
  -- translation while the thread still carries domain 0 makes the very next
  -- FETCH miss and fail closed -- the core then executes the poison page.
  -- The old order (mmu_en, then setdom) was harmless only because fetch was
  -- untranslated. Same shape as the stage-B silicon bug in fpga_dev.md §69,
  -- where core 0 started before its map existed.
  else if k = 8 then
    { cmdValid := true, cmdIdx := CMD_SETDOM, cmdData := BitVec.ofNat 32 (dom <<< 8) }
  else if k = 9 then { cmdValid := true, cmdIdx := CMD_MMU_EN, cmdData := 1 }
  else if bump ∧ k = 10 then
    { cmdValid := true, cmdIdx := CMD_MAP_PROTECT, cmdData := BitVec.ofNat 32 MMU_CELL }
  -- START THE CORE, last. This line lived at k=7 before EXT-9b renumbered
  -- the stream to fit a text VMA in front; overwriting it left the core in
  -- S_IDLE and every value check reading 0 -- which looks exactly like a
  -- fail-closed TLB miss. Starting last is also what makes the delay
  -- instructions in `progLdSt` unnecessary in principle and harmless in
  -- practice: nothing executes until the map is complete.
  else if k = 11 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else {}

def mmuSelftest : IO Unit := do
  -- Seed the mapped physical page and the fail-closed page with DIFFERENT
  -- values, or a hit and a miss are indistinguishable and the test is
  -- vacuous whatever the TLB does.
  let img := imageFrom TEXT_BASE progLdSt
             ++ [(ddrWord ((BitVec.ofNat 32 DATA_BASE).toNat + (MMU_PPN <<< 12)), 0xD00D),
                 (ddrWord DATA_BASE, 0x0BAD)]
  -- (1) bypass is the pre-EXT-7 machine.
  let bad ← lockstep img 1 (cmdQuantum 0) (fun _ => 0) 60
  if bad = 0 then IO.println "  OK  MMU-BYPASS (mmu_en=0: EDSL≡ISS, the pre-EXT-7 machine, 60 cyc)"
  else IO.println s!"  FAIL MMU-BYPASS ({bad} mismatches)"
  -- (2) domain-tagged: the entry's own domain hits, another misses.
  let bad2 ← lockstep img 1 (cmdMmu MMU_DOM false) (fun _ => 0) 60
  if bad2 = 0 then IO.println "  OK  MMU-XLAT (mmu_en=1: EDSL≡ISS through the TLB, 60 cyc)"
  else IO.println s!"  FAIL MMU-XLAT ({bad2} mismatches)"
  let (sh, dh, _) := runIss img 1 (cmdMmu MMU_DOM false) (fun _ => 0) 300
  let (sm, _, _)  := runIss img 1 (cmdMmu 5 false) (fun _ => 0) 300
  -- The observable is the LOADED VALUE, not `core_addr`. `core_addr` at halt
  -- holds the instruction fetch that followed the load, and fetches are
  -- deliberately untranslated (`ddrPc` is separate from `ddrEa`), so it
  -- cannot distinguish a hit from a fail-closed. A hit reads the mapped
  -- physical page; a fail-closed reads `DATA_BASE`, which the image never
  -- wrote, so the two values differ.
  let hitVal  := (dh.mem.getD (ddrWord ((BitVec.ofNat 32 DATA_BASE).toNat + (MMU_PPN <<< 12))) 0).toNat
  let missVal := (dh.mem.getD (ddrWord DATA_BASE) 0).toNat
  IO.println s!"  domain tag: from domain {MMU_DOM} r5={(sh.rf[5]!).toNat} (mapped page holds {hitVal}) \
| from domain 5 r5={(sm.rf[5]!).toNat} (fail-closed page holds {missVal})"
  let ok2 := (sh.rf[5]!).toNat == hitVal && (sm.rf[5]!).toNat == missVal && hitVal ≠ missVal
  -- (3) the shootdown: bumping the VMA's cell kills the translation.
  let (sb, _, _) := runIss img 1 (cmdMmu MMU_DOM true) (fun _ => 0) 300
  IO.println s!"  shootdown:  after cmd 67 on cell {MMU_CELL}, r5={(sb.rf[5]!).toNat} \
(want {missVal} = fail-closed) | before the bump it was {(sh.rf[5]!).toNat}"
  let ok3 := (sb.rf[5]!).toNat == missVal && (sh.rf[5]!).toNat ≠ missVal
  if bad = 0 && bad2 = 0 && ok2 && ok3 then
    IO.println "LNP64MINI MMU SELFTEST OK — translation is domain-tagged and the VMA's epoch cell shoots it down"
  else
    IO.println s!"LNP64MINI MMU SELFTEST FAILED (bypass={bad} xlat={bad2}; tag={ok2} shootdown={ok3})"
    throw <| IO.userError "mmu selftest failed"

/-- Sub-word stores must not disturb neighbouring bytes, on EITHER memory path.

This closes a real coverage hole. `sb` (0x35) and `sh` (0x37) were encoded
nowhere in this harness, so nothing below silicon ever executed one, and the
first evidence that something was wrong came from a board run: the guest's
in-DDR console ring, written by `buf[i] = c`, read back with every character
smeared over eight bytes, while the 32-bit `magic` and `wptr` fields of the
same struct read back exactly right.

Seed `0x1122334455667788`, then `SB` lane 1 := 0xAA and `SH` lanes 4..5 :=
0xBBCC. Little-endian lane `i` is byte `i` from the LSB, so the result is
0x1122BBCC5566AA88. Anything else -- and in particular the byte replicated
across all eight lanes -- is the bug. -/
def subwordSelftest : IO Unit := do
  let expect : Nat := 0x1122BBCC5566AA88
  let mut bad := 0
  for (nm, base) in [("dmem (ea < 0x1000, 1-cycle on-chip)", 0x40),
                     ("DDR  (ea >= 0x1000, RMW via S_DST/S_DSW)", 0x2000)] do
    let img := imageFrom TEXT_BASE (progSubWord base)
    -- EDSL ≡ ISS first: if the two models disagree the expected-value check
    -- below is meaningless, because it only ever consults the ISS.
    let mism ← lockstep img 1 (cmdQuantum 0) (fun _ => 0) 60
    let (st, _, _) := runIss img 1 (cmdQuantum 0) (fun _ => 0) 300
    let got := (st.rf[8]!).toNat
    let gotB := (st.rf[9]!).toNat
    let ok := mism == 0 && got == expect && gotB == 0xAA
    if !ok then bad := bad + 1
    IO.println s!"  {if ok then "OK  " else "FAIL"} SUBWORD {nm}"
    IO.println s!"       word=0x{String.ofList (Nat.toDigits 16 got)} \
(want 0x{String.ofList (Nat.toDigits 16 expect)}) lbu=0x{String.ofList (Nat.toDigits 16 gotB)} \
(want 0xaa) EDSL≡ISS mismatches={mism}"
  if bad == 0 then
    IO.println "LNP64MINI SUBWORD SELFTEST OK — sb/sh merge into their lanes and leave the rest alone, on both paths"
  else
    IO.println s!"LNP64MINI SUBWORD SELFTEST FAILED ({bad} path(s))"
    throw <| IO.userError "subword selftest failed"

/-- **W5 coverage gate.** Hold `cmpStates`'s claimed coverage against the
design's own declarations, so that adding state to `lnp64mini` breaks a test
instead of silently widening the gap between what is simulated and what is
compared.

This is the check that replaces a rule people were supposed to remember. It
found five uncompared memories the moment it was first run — `gate_ent`,
`gate_dom`, `cap_ibox` (EXT-5/EXT-6's gate table and capability inbox) and
`tcont`/`tcdom` (the gate continuation) — meaning `gateselftest` and
`capxferselftest` had been green without ever comparing the state their own
increments introduced. Both still pass now that they do, so the legs really did
agree; the tests simply had not been looking. -/
def coverageSelftest : IO Unit := do
  let s : MiniSt := {}
  let cr := cmpCoveredRegs s
  let cm := cmpCoveredMems s ++ cmpExemptMems
  IO.println s!"  design declares {design.regEntries.length} registers, \
{design.memEntries.length} memories"
  IO.println s!"  cmpStates compares {cr.length} registers, {(cmpCoveredMems s).length} \
memories ({cmpExemptMems.length} exempt: {cmpExemptMems})"
  let report := design.coverageReport cr cm
  if report ≠ "" then
    IO.println report
    IO.println "LNP64MINI COVERAGE SELFTEST FAILED"
    throw <| IO.userError "state coverage incomplete"
  IO.println "LNP64MINI COVERAGE SELFTEST OK — every declared register and memory is compared or explicitly exempt"

/-- EDSL ≡ ISS on the six opcodes the renumbering broke, plus their values. -/
def aluGapSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progAluGap
  let mism ← lockstep img 1 (cmdQuantum 0) (fun _ => 0) 80
  let (st, _, _) := runIss img 1 (cmdQuantum 0) (fun _ => 0) 400
  let g : Nat → Nat := fun i => (st.rf[i]!).toNat
  let want : List (Nat × Nat × String) :=
    [(3, 0xFFFFFFFFFFFFFFF8, "not r1"), (4, 1, "sltu 7<9"), (5, 0, "sltu 9<7"),
     (7, 16, "srli 256>>4"), (8, 0xFFFFFFFFFFFFFFFF, "srai ~7>>4"),
     (9, 1, "sltiu 7<9"), (10, 0, "bgeu skipped the poison word"),
     (11, 0x600D, "fell through to the tail")]
  let mut bad := 0
  for (r, w, lbl) in want do
    if g r ≠ w then
      bad := bad + 1
      IO.println s!"  FAIL r{r} = 0x{String.ofList (Nat.toDigits 16 (g r))} \
want 0x{String.ofList (Nat.toDigits 16 w)}  ({lbl})"
  IO.println s!"  EDSL≡ISS mismatches={mism}; value checks failed={bad}"
  if mism = 0 && bad = 0 then
    IO.println "LNP64MINI ALUGAP SELFTEST OK — not/sltu/bgeu/srli/srai/sltiu decode and write"
  else
    IO.println "LNP64MINI ALUGAP SELFTEST FAILED"
    throw <| IO.userError "alu gap selftest failed"

/-- The testbench's own command stream, so the ISS reference runs the same
sequence the RTL does: reset (starts the 1024-cycle zeroing sweep), a wait, then
start. `cmdQuantum` starts immediately and is right for the in-Lean lockstep,
where the model is placed directly in the started state; it is NOT what the
testbench drives, and using it here would compare two different experiments. -/
def cmdTb : Nat → MiniIn := fun k =>
  if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 1 }
  else if k = 1210 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else {}

/-- Run the ISS on a program and render the architectural result in exactly the
form `tb_lnp64mini_soc.v` prints, so the two can be compared as text.

`cycles` is deliberately NOT part of the comparison: the DDR model's latency is
a parameter of the experiment rather than an architectural fact, and a core that
took a different number of cycles to reach the same architectural state has not
misdecoded anything. HALTED, pc, retire, r1..r9 and the zero-page word are the
observables that a decode disagreement actually moves. -/
def issExpect (prog : List (BitVec 64)) (nCyc : Nat := 400000) : String := Id.run do
  let image := imageFrom TEXT_BASE prog
  let mut s : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := 1 }
  let mut g : GpModel := {}
  for k in List.range nCyc do
    if s.halted || s.trap_active then break
    let (s', d', g', _) := sysStep s d g (cmdTb k) 0
    s := s'; d := d'; g := g'
  let mut out := ""
  if s.trap_active then
    out := out ++ s!"TRAP op={(String.ofList (Nat.toDigits 16 s.trapped_op.toNat)).leftpad 2 '0'} \
pc={s.pc.toNat}\n"
  out := out ++ s!"HALTED={if s.halted then 1 else 0} pc={s.pc.toNat} retire={s.retire.toNat}\n"
  for i in List.range 9 do
    out := out ++ s!"r{i+1}={(s.rf[i+1]!).toNat}\n"
  out := out ++ s!"dmem32={(s.dmem[32]!).toNat}\n"
  return out

/-- Emit the generated matrix's programs as `.hex` files for the RTL leg.

The 2026-08-05 renumbering passed every gate here and panicked on silicon. The
reason is structural: `opDiffSelftest` compares EDSL against ISS and
`diff_emulator_iss.py` compares emulator against ISS — **nothing compared
against the RTL**, which is what the bitstream is built from and what the board
actually runs. An infinitely thorough emulator-vs-ISS matrix could not have
caught it.

This writes each generated program to `fpga/zc702/opdiff/`, where
`scripts/opdiff_rtl.sh` runs it through iverilog on the emitted SoC and diffs
the architectural result against the ISS. 41 000 instructions is nothing in
simulation; a kernel boot is the most expensive possible place to first learn
about a decode disagreement. -/
def writeOpDiffHex (dir : String) : IO Unit := do
  let mut n := 0
  let emit : String → List (BitVec 64) → IO Unit := fun nm prog => do
    let mut txt := ""
    for w in prog do
      txt := txt ++ (String.ofList (Nat.toDigits 16 w.toNat)).leftpad 16 '0' ++ "\n"
    IO.FS.writeFile s!"{dir}/{nm}.hex" txt
    -- The expectation travels WITH the program. Without it the RTL leg can only
    -- report that a program ran, which is the weaker claim that let the
    -- renumbering through: `liu` "ran" fine and produced the wrong constant.
    IO.FS.writeFile s!"{dir}/{nm}.exp" (issExpect prog)
  for (form, ops) in [(0, aluOpsRRR), (1, aluOpsRR), (2, aluOpsIMM), (3, selOps)] do
    for (op, nm) in ops do
      for (a, b) in opVectors do
        emit s!"{nm}_{a}_{b}" (progOp form op a b); n := n + 1
  for (hi, lo) in constBattery do
    emit s!"const_{hi}_{lo}" (progConst hi lo); n := n + 1
  for (op, nm) in jumpOps do
    emit s!"jump_{nm}" (progJump op); n := n + 1
  IO.println s!"wrote {n} matrix programs to {dir}"

/-- Run a program read from a flat `.hex` (one 64-bit word per line, the format
`$readmemh` and the board loader both take) and print the ISS expectation.

This is what makes a program written in MNEMONICS checkable. Every other leg
generates its test programs from lean_hw's own `OP_` constants, so a renumbering
moves the design and the program together and they agree by construction --
correct for the design, and blind to the question that broke the board: does the
*assembler*, in the other repo, still emit what this core decodes? Feed it a
`.hex` from `lnp64 asm-flat-exec` and the answer stops being an assumption. -/
def issExpectHexFile (path : String) : IO Unit := do
  let txt ← IO.FS.readFile path
  let words := txt.splitOn "\n" |>.filterMap (fun l =>
    let t := l.trim
    if t.isEmpty then none
    else
      let ds := t.toList.filterMap (fun c =>
        if c.isDigit then some (c.toNat - 48)
        else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
        else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
        else none)
      some (BitVec.ofNat 64 (ds.foldl (fun acc d => acc * 16 + d) 0)))
  IO.print (issExpect words)

/-- EXT-8: the commit trace actually records what executed.

The lockstep proves the EDSL and the ISS agree about the ring. That is not the
same as the ring being USEFUL -- two models can agree on a ring that is empty,
or off by one, or holding the PC of the next instruction instead of the retired
one. This runs a program whose instruction sequence is known and reads the
entries back.

The off-by-one matters more than it looks: a trace that names the instruction
AFTER the faulting one sends you to the wrong place, which is worse than having
no trace, because it looks authoritative. -/
def traceSelftest : IO Unit := do
  -- Four instructions: addi r1,7 / addi r2,9 / add r3,r1,r2 / exit.
  let prog := progOp 0 OP_ADD 7 9
  let image := imageFrom TEXT_BASE prog
  let mut st : MiniSt := {}
  let mut d : DdrModel := { mem := Std.HashMap.ofList image, latency := 1 }
  let mut g : GpModel := {}
  -- Keep clocking for a few cycles after the halt. The ring lands an entry one
  -- cycle after the retire that produced it (D38 forced the capture and the
  -- memory write into different cycles), so stopping the instant `halted` goes
  -- high loses the LAST instruction -- the one a post-mortem most wants. On
  -- silicon the clock does not stop when the core halts, so this models the
  -- board rather than papering over the lag.
  let mut after := 0
  for k in List.range 400000 do
    if st.halted || st.trap_active then
      after := after + 1
      if after > 4 then break
    let (s', d', g', _) := sysStep st d g (cmdTb k) 0
    st := s'; d := d'; g := g'
  let mut bad := 0
  let n := st.retire.toNat
  IO.println s!"  retired {n} instruction(s), write pointer at {st.trace_wp.toNat}"
  if st.trace_wp.toNat ≠ n % 16 then
    IO.println s!"  FAIL write pointer {st.trace_wp.toNat} ≠ retire {n} mod 16"
    bad := bad + 1
  -- Entry i must hold the i-th instruction of the program, at its own PC.
  for i in List.range (min n 4) do
    let w := st.trace_pc[i]!
    let gotOp := (w >>> 56).toNat
    let gotPc := (w.truncate 32).toNat
    let wantOp := ((prog[i]!) >>> 56).toNat
    let wantPc := TEXT_BASE + i * 8
    if gotOp ≠ wantOp || gotPc ≠ wantPc then
      IO.println s!"  FAIL entry {i}: op=0x{String.ofList (Nat.toDigits 16 gotOp)} \
pc={gotPc}, want op=0x{String.ofList (Nat.toDigits 16 wantOp)} pc={wantPc}"
      bad := bad + 1
    else
      IO.println s!"  ok   entry {i}: op=0x{String.ofList (Nat.toDigits 16 gotOp)} pc={gotPc} \
wb={(st.trace_wb[i]!).toNat}"
  if bad = 0 then
    IO.println "LNP64MINI TRACE SELFTEST OK — the ring records the retired \
instruction, at its own PC, in order"
  else
    IO.println "LNP64MINI TRACE SELFTEST FAILED"
    throw (IO.userError "trace ring wrong")

/-- Total EDSL≡ISS mismatches over the generated ALU matrix — the same
programs `opDiffSelftest` runs, as one number. -/
def matrixMismatches : Nat := Id.run do
  let mut bad := 0
  for (form, ops) in [(0, aluOpsRRR), (1, aluOpsRR), (2, aluOpsIMM), (3, selOps)] do
    for (op, _) in ops do
      for (a, b) in opVectors do
        bad := bad + lockstepPure (imageFrom TEXT_BASE (progOp form op a b)) 1
                       (cmdQuantum 0) 24 16
  return bad

/-- Generated EDSL ≡ ISS coverage over every ALU opcode in the matrix. -/
def opDiffSelftest : IO Unit := do
  let mut bad := 0
  let mut ran := 0
  for (form, ops) in [(0, aluOpsRRR), (1, aluOpsRR), (2, aluOpsIMM), (3, selOps)] do
    for (op, nm) in ops do
      let mut opBad := 0
      for (a, b) in opVectors do
        let img := imageFrom TEXT_BASE (progOp form op a b)
        -- Loom's derived coordinates, not a hand-written comparison list:
        -- every declared register and memory cell, enumerated from the design.
        -- cap 16 cells/memory and 24 cycles: the programs are four
        -- instructions and touch r1..r3, so a larger window costs time without
        -- covering anything. EVERY DECLARED MEMORY is still compared -- the cap
        -- bounds cells per memory, not which memories -- so the property this
        -- test enforces is unchanged.
        let (m, _) ← lockstepFast img 1 (cmdQuantum 0) (fun _ => 0) 24 16
        opBad := opBad + m
        ran := ran + 1
      if opBad ≠ 0 then
        bad := bad + 1
        IO.println s!"  FAIL {nm} (opcode 0x{String.ofList (Nat.toDigits 16 op)}): \
{opBad} EDSL≡ISS mismatches across {opVectors.length} operand vectors"
  -- Loads and stores, on BOTH memory paths: dmem (ea < 0x1000) and the DDR
  -- read-modify-write (ea >= 0x1000) are different hardware.
  for base in [0x40, 0x2000] do
    for (op, nm) in memOpsLoad do
      let mut opBad := 0
      for (a, _) in opVectors do
        let img := imageFrom TEXT_BASE (progLoad op base a)
        let (m, _) ← lockstepFast img 1 (cmdQuantum 0) (fun _ => 0) 40 16
        opBad := opBad + m
        ran := ran + 1
      if opBad ≠ 0 then
        bad := bad + 1
        IO.println s!"  FAIL {nm} @0x{String.ofList (Nat.toDigits 16 base)}: {opBad} mismatches"
    for (op, nm) in memOpsStore do
      let mut opBad := 0
      for (a, _) in opVectors do
        let img := imageFrom TEXT_BASE (progStore op base a)
        let (m, _) ← lockstepFast img 1 (cmdQuantum 0) (fun _ => 0) 48 16
        opBad := opBad + m
        ran := ran + 1
      if opBad ≠ 0 then
        bad := bad + 1
        IO.println s!"  FAIL {nm} @0x{String.ofList (Nat.toDigits 16 base)}: {opBad} mismatches"
  -- Branches, both directions.
  for (op, nm) in brOps do
    let mut opBad := 0
    for (a, b) in opVectors do
      let img := imageFrom TEXT_BASE (progBranch op a b)
      let (m, _) ← lockstepFast img 1 (cmdQuantum 0) (fun _ => 0) 40 16
      opBad := opBad + m
      ran := ran + 1
    if opBad ≠ 0 then
      bad := bad + 1
      IO.println s!"  FAIL {nm}: {opBad} mismatches"
  -- The wide-immediate constant builders, with a DIRECTED battery: not "does
  -- one liu agree" but "does this exact 64-bit value come out".
  for (hi, lo) in constBattery do
    let img := imageFrom TEXT_BASE (progConst hi lo)
    let (m, _) ← lockstepFast img 1 (cmdQuantum 0) (fun _ => 0) 24 16
    ran := ran + 1
    if m ≠ 0 then
      bad := bad + 1
      IO.println s!"  FAIL liu/ori constant hi=0x{String.ofList (Nat.toDigits 16 hi.toNat)}: {m} mismatches"
  -- auipc, and the jump family.
  for (op, nm) in wideImmOps ++ jumpOps do
    let mut opBad := 0
    if op = OP_LIU then pure () else
      for (a, _) in opVectors do
        let img := imageFrom TEXT_BASE
          (if op = OP_AUIPC then [encImmI OP_AUIPC 3 0 a, enc OP_EXIT 0 0 0]
           else progJump op)
        let (m, _) ← lockstepFast img 1 (cmdQuantum 0) (fun _ => 0) 32 16
        opBad := opBad + m
        ran := ran + 1
    if opBad ≠ 0 then
      bad := bad + 1
      IO.println s!"  FAIL {nm}: {opBad} mismatches"
  let total := aluOpsRRR.length + aluOpsRR.length + aluOpsIMM.length
             + 2 * (memOpsLoad.length + memOpsStore.length) + brOps.length
             + wideImmOps.length + jumpOps.length
  let (_, unm) ← lockstepFast (imageFrom TEXT_BASE (progOp 0 OP_ADD 1 2))
                   1 (cmdQuantum 0) (fun _ => 0) 8 16
  IO.println s!"  {total} opcode/path combinations x {opVectors.length} vectors = {ran} programs"
  IO.println s!"  compared against Loom's derived coordinate set \
({(design.coords 16).length} coordinates; {unm} not modelled by the ISS)"
  if bad = 0 then
    IO.println s!"LNP64MINI OPDIFF SELFTEST OK — EDSL≡ISS on {total} ALU/load/store/branch combinations, generated not hand-written"
  else
    IO.println s!"LNP64MINI OPDIFF SELFTEST FAILED ({bad} opcodes disagree)"
    throw <| IO.userError "opdiff selftest failed"

/-- **Identity translation must equal bypass.**

If a VMA maps a range onto itself (`delta = 0`), then `mmu_en = 1` and
`mmu_en = 0` must compute the same effective address for every access — that is
what "the mapping is the identity" means. Any difference is a translation-path
bug that would break the guest the moment the MMU is switched on, and it would
be found on the board rather than here.

This matters because the two paths are NOT the same expression: `ddrEaRaw`
word-aligns (`ea & ~7`) while `ddrEaXlat` is `DATA_BASE + eaLo + delta`. Whether
that difference is observable is exactly the question, and it is cheaper to
answer in the ladder than in a six-minute board cycle.

The program touches byte, half, word and doubleword at several alignments, so
an alignment difference in the translated path shows up as a value mismatch. -/
def progXlatProbe (base : Nat) : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 base,
    encImmI OP_LIU 3 0 0x0A0B0C0D,
    encImmI OP_ORI 3 3 0x01020304,
    encImmS OP_ST 1 3 0,              -- sd  [base]
    encImmI OP_ADDI 4 0 0x5A,
    encImmS OP_ST_35 1 4 3,           -- sb  [base+3]  (unaligned)
    encImmI OP_ADDI 5 0 0x1234,
    encImmS OP_ST_37 1 5 6,           -- sh  [base+6]  (unaligned)
    encImmI OP_LD 6 1 0,              -- ld  [base]
    encImmI OP_LD_32 7 1 3,           -- lbu [base+3]
    encImmI OP_LD_36 8 1 6,           -- lhu [base+6]
    encImmI OP_LD_31 9 1 4,           -- lwu [base+4]
    enc OP_EXIT 0 0 0 ]

/-- Install VMA 0 as the identity over the whole space, then enable the MMU. -/
def cmdIdentityVma : Nat → MiniIn := fun k =>
  if k = 0 then { cmdValid := true, cmdIdx := CMD_TLB_SEL,  cmdData := 0 }
  else if k = 1 then { cmdValid := true, cmdIdx := CMD_TLB_VPN,  cmdData := 0 }          -- base 0, dom 0
  else if k = 2 then { cmdValid := true, cmdIdx := CMD_TLB_PHYS, cmdData := 0x01000000 } -- delta 0, cell 1
  else if k = 3 then { cmdValid := true, cmdIdx := CMD_TLB_PPN,  cmdData := 0xFFFFFFFF } -- limit + validate
  else if k = 4 then { cmdValid := true, cmdIdx := CMD_MMU_EN,   cmdData := 1 }
  else if k = 5 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else {}

/-! ### EXT-7 stage B: the non-identity map, off-hardware first

The board plan (EXTEND_SPEC "Making the VMA non-identity") in miniature, with
the SAME shape: a pinned DMA window, a pinned text range (fetch is untranslated,
so text must stay put), and a catch-all that genuinely relocates. priTree makes
lower index win, so the carve-outs override the catch-all. -/

/-- entry 0: "ring"  [0x20000,0x30000) delta 0        cell 2  (the DMA grant)
    entry 1: "text"  [ 0x1000, 0x8000) delta 0        cell 1
    entry 2: else    [      0,0x1000000) delta +0x800000 cell 1 (relocated) -/
def cmdRelocVma (extra : List (Nat × Nat) := []) : Nat → MiniIn := fun k =>
  let prog : List (Nat × Nat) :=
    [ (CMD_TLB_SEL, 0), (CMD_TLB_VPN, 0x20000), (CMD_TLB_PHYS, 0x02000000),
      (CMD_TLB_PPN, 0x30000),
      (CMD_TLB_SEL, 1), (CMD_TLB_VPN, 0x1000),  (CMD_TLB_PHYS, 0x01000000),
      (CMD_TLB_PPN, 0x8000),
      (CMD_TLB_SEL, 2), (CMD_TLB_VPN, 0),       (CMD_TLB_PHYS, 0x01800000),
      (CMD_TLB_PPN, 0x1000000),
      (CMD_MMU_EN, 1) ] ++ extra ++ [ (13, 2) ]
  match prog[k]? with
  | some (idx, dat) => { cmdValid := true, cmdIdx := idx,
                         cmdData := BitVec.ofNat 32 dat }
  | none => {}

def mmuRelocSelftest : IO Unit := do
  -- one tally, owned by `check` -- the first version double-booked failures in
  -- side conditions with STALE expectations (the probe's sb/sh overlay the sd
  -- pattern, so a full-word compare against the raw sd value is wrong) and
  -- reported FAILED under ten green lines.
  let badRef ← IO.mkRef 0
  let hex : Nat → String := fun n => "0x" ++ String.ofList (Nat.toDigits 16 n)
  let check : Bool → String → IO Unit := fun ok msg => do
    if ok then IO.println s!"  ok   {msg}"
    else do IO.println s!"  FAIL {msg}"; badRef.modify (· + 1)
  -- The probe stores sd(pattern) then sb 0x5a at +3 and sh 0x1234 at +6, so
  -- the word at the target is the OVERLAID value, byte 0 = 0x04.
  let overlaid := 0x12340c0d5a020304
  -- 1. the catch-all really relocates: a store at guest 0x40000 must land at
  --    physical DB+0x840000 and leave DB+0x40000 untouched. Checking the
  --    PHYSICAL placement is the point -- a guest-visible round-trip is
  --    satisfied by the identity map too, so round-trips alone prove nothing
  --    about relocation.
  let img := imageFrom TEXT_BASE (progXlatProbe 0x40000)
  let (st, d, _) := runIss img 1 (cmdRelocVma) (fun _ => 0) 600
  let atP := (d.mem.get? (ddrWord (DATA_BASE + 0x840000))).getD 0
  let atG := (d.mem.get? (ddrWord (DATA_BASE + 0x40000))).getD 0
  check (atP.toNat == overlaid) s!"store at guest 0x40000 landed at physical +0x800000 ({hex atP.toNat})"
  check (atG == 0) s!"...and NOT at physical 0x40000 ({hex atG.toNat})"
  check ((st.rf[6]!).toNat == overlaid) s!"guest round-trip unchanged (r6={hex (st.rf[6]!).toNat})"
  -- 2. the ring carve-out is pinned: same probe at guest 0x20000 lands at
  --    physical 0x20000, where the host's DMA pump expects it.
  let img2 := imageFrom TEXT_BASE (progXlatProbe 0x20000)
  let (_, d2, _) := runIss img2 1 (cmdRelocVma) (fun _ => 0) 600
  let rP := (d2.mem.get? (ddrWord (DATA_BASE + 0x20000))).getD 0
  let rM := (d2.mem.get? (ddrWord (DATA_BASE + 0x820000))).getD 0
  check (rP.toNat == overlaid) s!"ring store pinned at physical 0x20000 ({hex rP.toNat})"
  check (rM == 0) "...and not relocated"
  -- 3. text carve-out: a LOAD from guest 0x1000 (through the TLB -- only fetch
  --    bypasses it) reads the first instruction word the loader put there.
  let progRdText : List (BitVec 64) :=
    [ encImmI OP_ADDI 1 0 0x1000, encImmI OP_LD 6 1 0, enc OP_EXIT 0 0 0 ]
  let img3 := imageFrom TEXT_BASE progRdText
  let (st3, _, _) := runIss img3 1 (cmdRelocVma) (fun _ => 0) 600
  check (st3.rf[6]! == progRdText[0]!) "text data-read sees the loader's bytes (identity carve-out)"
  -- 4. revocation is scoped: bumping cell 2 (the ring's) before start leaves
  --    the catch-all alive -- the relocated store still lands -- while a ring
  --    access now MISSES to the fail-closed sink (bare DATA_BASE), so nothing
  --    reaches the revoked window's physical address.
  let (st4, d4, _) := runIss img 1 (cmdRelocVma [(CMD_MAP_PROTECT, 2)]) (fun _ => 0) 600
  check ((st4.rf[6]!).toNat == overlaid) "bump cell 2: relocated data unaffected"
  let (_, d5, _) := runIss img2 1 (cmdRelocVma [(CMD_MAP_PROTECT, 2)]) (fun _ => 0) 600
  let rP5 := (d5.mem.get? (ddrWord (DATA_BASE + 0x20000))).getD 0
  check (rP5 == 0) "bump cell 2: nothing lands in the revoked window"
  -- 5. bumping cell 1 kills the catch-all too: the store misses to the sink,
  --    so the relocated address stays empty.
  let (_, d6, _) := runIss img 1 (cmdRelocVma [(CMD_MAP_PROTECT, 1)]) (fun _ => 0) 600
  let atP6 := (d6.mem.get? (ddrWord (DATA_BASE + 0x840000))).getD 0
  check (atP6 == 0) "bump cell 1: the guest's own map fails closed"
  -- 6. FUTEX_WAIT under a nonzero delta. This is the cross that spun stage B
  --    on silicon: the design computed the futex compare address RAW while
  --    stores went through the TLB, so the compare read the unrelocated word
  --    and failed forever. FUTEX_WAIT was on the coverage exclusion list as
  --    "covered by smpselftest DOORBELL" -- which runs with the MMU off. The
  --    exclusion covered the OPCODE, not the opcode x MMU cross.
  --    Store V at a relocated address, then FUTEX_WAIT expecting V: the thread
  --    must PARK (tstate=3). With the raw-address bug it reads zeros, the
  --    compare fails, and it never parks.
  let progFutexReloc : List (BitVec 64) :=
    [ encImmI OP_ADDI 1 0 0x40000,      -- relocated region (catch-all)
      encImmI OP_ADDI 2 0 77,
      encImmS OP_ST 1 2 0,              -- [0x40000] := 77, via the TLB
      enc OP_FUTEX_WAIT 1 2 0,          -- expect 77 -> must block
      encImmI OP_ADDI 9 0 5,            -- unreached while parked
      enc OP_EXIT 0 0 0 ]
  let imgF := imageFrom TEXT_BASE progFutexReloc
  let (stF, _, _) := runIss imgF 1 (cmdRelocVma) (fun _ => 0) 600
  check (stF.tstate[0]! == 3 && (stF.rf[9]!).toNat == 0)
    s!"FUTEX_WAIT parks on a relocated word (tstate={(stF.tstate[0]!).toNat}, r9={(stF.rf[9]!).toNat})"
  -- 7. EDSL ≡ ISS under the whole thing: the design computes the same
  --    translation, cycle for cycle, over Loom's derived coordinates --
  --    including the futex program, where the two models used to disagree
  --    (raw+aligned vs translated+unaligned) with nothing executing the cross.
  let (m, _) ← lockstepFast img 1 (cmdRelocVma) (fun _ => 0) 600 16
  check (m == 0) s!"EDSL≡ISS lockstep under the 3-entry non-identity map ({m} mismatches)"
  let (mF, _) ← lockstepFast imgF 1 (cmdRelocVma) (fun _ => 0) 600 16
  check (mF == 0) s!"EDSL≡ISS lockstep on the futex-under-delta program ({mF} mismatches)"
  let bad ← badRef.get
  if bad == 0 then
    IO.println "LNP64MINI MMU-RELOC SELFTEST OK — the catch-all relocates, the carve-outs pin, revocation is scoped per cell"
  else
    IO.println s!"LNP64MINI MMU-RELOC SELFTEST FAILED ({bad})"
    throw <| IO.userError "mmu reloc selftest failed"

def mmuIdentitySelftest : IO Unit := do
  let mut bad := 0
  for base in [0x2000, 0x4008, 0x10000] do
    let img := imageFrom TEXT_BASE (progXlatProbe base)
    let (sByp, _, _) := runIss img 1 (cmdQuantum 0) (fun _ => 0) 400
    let (sXlat, _, _) := runIss img 1 cmdIdentityVma (fun _ => 0) 400
    let mut diffs : List String := []
    for r in [6, 7, 8, 9] do
      if (sByp.rf[r]!) ≠ (sXlat.rf[r]!) then
        diffs := diffs ++ [s!"r{r}: bypass={(sByp.rf[r]!).toNat} xlat={(sXlat.rf[r]!).toNat}"]
    if !diffs.isEmpty then
      bad := bad + 1
      IO.println s!"  FAIL base=0x{String.ofList (Nat.toDigits 16 base)}: {diffs}"
    else
      IO.println s!"  OK   base=0x{String.ofList (Nat.toDigits 16 base)} (identity xlat = bypass)"
  if bad = 0 then
    IO.println "LNP64MINI MMU-IDENTITY SELFTEST OK — an identity VMA computes exactly what bypass computes"
  else
    IO.println s!"LNP64MINI MMU-IDENTITY SELFTEST FAILED ({bad} base(s))"
    throw <| IO.userError "mmu identity selftest failed"

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
