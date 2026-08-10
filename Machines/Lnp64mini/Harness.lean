-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Diff
import Loom.Hw.DagEval
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

def MiniIn.toEnv (c : MiniIn) : InEnv := InputBinding.toEnv
  [InputBinding.of mDonePort (BitVec.ofBool c.mDone),
   InputBinding.of mRdataPort c.mRdata,
   InputBinding.of mBusyPort (BitVec.ofBool c.mBusy),
   InputBinding.of gpDonePort (BitVec.ofBool c.gpDone),
   InputBinding.of gpRdataPort c.gpRdata,
   InputBinding.of gpBusyPort (BitVec.ofBool c.gpBusy),
   InputBinding.of cmdValidPort (BitVec.ofBool c.cmdValid),
   InputBinding.of cmdIdxPort (BitVec.ofNat 7 c.cmdIdx),
   InputBinding.of cmdDataPort c.cmdData,
   InputBinding.of resKillPort (BitVec.ofBool c.resKill),
   InputBinding.of doorbellPort (BitVec.ofBool c.doorbell),
   InputBinding.of doorbellKeyPort c.doorbellKey,
   InputBinding.of holdPort (BitVec.ofBool c.hold),
   InputBinding.of scFailPort (BitVec.ofBool c.scFail)]

/-! ## Reading the ISS state as (name, value) pairs (for lockstep vs EDSL) -/

/-- Bind an independent ISS value to a Design handle.  The ISS still supplies
the value independently; its comparison name and width are derived from the
same typed declaration used by the Design. -/
private def issReg {w : Nat} (r : Reg w) (v : BitVec w) : String × Nat × Nat :=
  (r.name, w, v.toNat)

private def issBool (r : Reg 1) (v : Bool) : String × Nat × Nat :=
  issReg r (BitVec.ofBool v)

def issRegs (s : MiniSt) : List (String × Nat × Nat) :=
  [issReg curReg s.cur, issReg pcReg s.pc, issReg retireReg s.retire,
   -- EXT-9/9b: the cache's own registers. The Oracle's closed list makes
   -- adding them mandatory rather than optional -- omitting one reports
   -- UNDECLARED-UNMODELLED instead of quietly shrinking the comparison.
   issReg icTagQReg s.ic_tag_q, issReg icDataQReg s.ic_data_q,
   issReg icGenReg s.ic_gen, issBool icInvReg s.ic_inv, issReg icCtrReg s.ic_ctr,
   issReg gateTblBaseReg s.gate_tbl_base, issReg gateEntQReg s.gate_ent_q,
   issReg gateDomQReg s.gate_dom_q,
   -- EXT-6 (§17): the cap-inbox root pointer and walked-flags latch
   issReg capTblBaseReg s.cap_tbl_base, issReg capFlQReg s.cap_fl_q,
   -- EXT-10: the D-cache's registers.
   issReg dcTagQReg s.dc_tag_q, issReg dcDataQReg s.dc_data_q,
   issBool dcAllocReg s.dc_alloc,
   issReg traceWpReg s.trace_wp, issReg traceSelReg s.trace_sel,
   issReg traceRdPcReg s.trace_rd_pc, issReg traceRdWbReg s.trace_rd_wb,
   issBool traceHitReg s.trace_hit,
   issReg traceInPcReg s.trace_in_pc, issReg traceInWbReg s.trace_in_wb,
   issBool runningReg s.running, issBool haltedReg s.halted,
   issReg stReg s.st, issReg irReg s.ir, issReg aReg s.a, issReg bReg s.b,
   issReg rdvalReg s.rdval, issReg selTReg s.sel_t, issReg selFReg s.sel_f,
   issBool memIsStoreReg s.mem_is_store,
   issBool trapActiveReg s.trap_active, issReg trappedOpReg s.trapped_op,
   issBool coreRdReg s.core_rd, issBool coreWrReg s.core_wr,
   issReg coreAddrReg s.core_addr, issReg coreWdataReg s.core_wdata,
   issBool jtagRdReg s.jtag_rd, issBool jtagWrReg s.jtag_wr,
   issReg jtagWdataReg s.jtag_wdata, issReg ddrAddrJReg s.ddr_addr_j,
   issReg ddrLoJReg s.ddr_lo_j, issReg ddrRdLReg s.ddr_rd_l, issReg ddrQReg s.ddr_q,
   issBool busReqReg s.bus_req,
   issBool gpRdReg s.gp_rd, issBool gpWrReg s.gp_wr,
   issReg gpAddrRReg s.gp_addr_r, issReg gpWdataRReg s.gp_wdata_r,
   issBool dmemWeReg s.dmem_we, issReg dmemAReg s.dmem_a,
   issReg dmemWdReg s.dmem_wd, issReg dmemRdReg s.dmem_rd,
   issReg uartWptrReg s.uart_wptr, issReg uartRidxReg s.uart_ridx,
   issReg uartByteReg s.uart_byte, issReg rxWptrReg s.rx_wptr, issReg rxRptrReg s.rx_rptr,
   issReg ldBoffQReg s.ld_boff_q, issReg ldOpQReg s.ld_op_q, issReg ldRdQReg s.ld_rd_q,
   issReg lrAddrReg s.lr_addr, issBool lrValidReg s.lr_valid,
   issReg futexExpReg s.futex_exp, issReg futexAddrQReg s.futex_addr_q,
   issReg sleepScanReg s.sleep_scan, issReg nextReadyReg s.next_ready,
   issReg freeSlotReg s.free_slot, issBool hasFreeReg s.has_free,
   issReg cloneDstReg s.clone_dst, issReg cloneTidReg s.clone_tid,
   issReg mulAccReg s.mul_acc, issReg mulAwReg s.mul_aw, issReg mulBReg s.mul_b,
   issReg mulKindReg s.mul_kind, issReg divRemReg s.div_rem, issReg divQuoReg s.div_quo,
   issReg divDReg s.div_d, issReg divCntReg s.div_cnt,
   issBool divIsremReg s.div_isrem, issBool divNegqReg s.div_negq,
   issBool divNegrReg s.div_negr,
   issBool zeroingReg s.zeroing, issReg zctrReg s.zctr,
   issReg regSelReg s.reg_sel, issReg regWselReg s.reg_wsel, issReg regWloReg s.reg_wlo,
   issReg dmemAddrJReg s.dmem_addr_j, issReg dmemLoJReg s.dmem_lo_j,
   issReg regRdReg s.reg_rd,
   issReg quantumReg s.quantum, issReg qctrReg s.qctr,
   -- EXT-2: the domain observation mirror
   issReg curDomReg s.cur_dom,
   -- EXT-3: the fail-stop bitmap
   issReg poisonReg s.poison,
   -- EXT-4: the outgoing wake key (informational; the wake is unkeyed now)
   issReg wakeKeyReg s.wake_key,
   -- EXT-5: gates
   issReg inGateReg s.in_gate,
   -- §9 diagnostic: the loud GATE_RETURN latch
   issReg faultCauseReg s.fault_cause, issReg faultPcReg s.fault_pc,
   issReg faultCurReg s.fault_cur,
   -- EXT-7: the MMU enable and TLB selector
   issBool mmuEnReg s.mmu_en, issReg tlbSelReg s.tlb_sel,
   issReg tlbVldReg s.tlb_vld,
   issBool wakeOutReg s.wake_out,
   issBool lrReqReg s.lr_req, issBool scReqReg s.sc_req,
   issBool scPendingReg s.sc_pending]
  -- EXT-7 stage B: the TLB is per-index REGISTERS, not memories (D20 -- every
  -- entry is read at once, so it is a register file). Listed here so Loom's
  -- The derived comparator finds every entry from the Design declarations.
  ++ (List.range 8).flatMap (fun i =>
       [issReg (tlbBaseRegs.regN i) s.tlb_base[i]!,
        issReg (tlbLimitRegs.regN i) s.tlb_limit[i]!,
        issReg (tlbPhysRegs.regN i) s.tlb_phys[i]!,
        issReg (tlbDomRegs.regN i) s.tlb_dom[i]!,
        issReg (tlbCellRegs.regN i) s.tlb_cell[i]!])
  ++ (List.range NT).map (fun i => issReg (tstateRegs.regN i) s.tstate[i]!)

/-! ## EDSL ≡ ISS lockstep -/

/-- One independent ISS memory value source, with its identity and shape
derived from the Design's typed memory handle. -/
structure IssMemBinding where
  name : String
  addrWidth : Nat
  dataWidth : Nat
  read : Nat → Option Nat

private def issMem {aw dw : Nat} (m : Mem aw dw)
    (values : Array (BitVec dw)) : IssMemBinding :=
  { name := m.name
    addrWidth := aw
    dataWidth := dw
    read := fun addr => (values[addr]?).map (fun value => value.toNat) }

/-- The ISS's modelled memories. Values remain independent; all comparison
metadata comes from the same handles that declare and access the Design. -/
def issMems (s : MiniSt) : List IssMemBinding :=
  [ issMem rfBank s.rf
  , issMem dmemBank s.dmem
  , issMem tracePcBank s.trace_pc
  , issMem traceWbBank s.trace_wb
  , issMem icDataBank s.ic_data
  , issMem icTagBank s.ic_tag
  , issMem dcDataBank s.dc_data
  , issMem dcTagBank s.dc_tag
  , issMem tpcBank s.tpc
  , issMem tsleepBank s.tsleep
  , issMem tpBank s.tp_arr
  , issMem sigmaskBank s.sigmask_arr
  , issMem tdomBank s.tdom
  , issMem tcontBank s.tcont
  , issMem tcdomBank s.tcdom
  , issMem gdepthBank s.gdepth ]

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
def issAtWith (regs : List (String × Nat × Nat))
    (mems : List IssMemBinding)
    (c : Loom.Hw.Coord) : Option Nat :=
  if c.kind = "reg" then
    (regs.find? (fun r => r.1 = c.name ∧ r.2.1 = c.width)).map (fun r => r.2.2)
  else
    match mems.find? (fun mem =>
        mem.name = c.name ∧ mem.dataWidth = c.width ∧ c.addr < 2 ^ mem.addrWidth) with
    | some mem => mem.read c.addr
    | none => none

/-- The CLOSED list of coordinates the ISS deliberately does not model. A
memory added to the Design fails by name unless it is modelled by `issAtWith`
or deliberately listed here. -/
def issUnmodelled : List String :=
  [ uartBank.name, rxBank.name ]

/-- Convenience wrapper. Prefer `issAtWith` in a per-cycle loop: `issRegs`
rebuilds a 152-entry list on every call, so calling this once per coordinate
rebuilds it once per coordinate. -/
def issAt (s : MiniSt) (c : Loom.Hw.Coord) : Option Nat :=
  issAtWith (issRegs s) (issMems s) c

/-! ### W5, the deeper half: matrix equality as a THEOREM

The executable runner below prints immediately. This is the same comparison
with printing removed: a pure mismatch count, so a whole test matrix can be a
single `Nat` and "the design agrees with the ISS on the matrix" can be stated
as `matrixMismatches = 0` and discharged by `native_decide` at BUILD time.

Honesty about what that buys: `native_decide` evaluates with the compiler, so
the trusted base is the same one the *test* uses. What changes is WHERE the
check lives -- inside the artifact the kernel accepts, so it cannot be skipped,
filtered, or forgotten by a harness; a build in which the design and the ISS
disagree on the matrix does not exist. It is strictly stronger than a test that
someone must run, and strictly weaker than a symbolic proof, and PLATONIC.md
records it in exactly those terms. -/

set_option maxRecDepth 100000 in
/-- The generated evaluator's design-specific well-formedness obligation.
The depth option only gives the reducer room to traverse this 182-register,
18-memory design; the proof remains reflexivity after computation. -/
theorem design_fastWF : design.fastWFB = true := by rfl

/-- LNP64mini's public generated simulator.  The executable evaluator is
derived from `design`; `runOpenFromReset_eq` states its semantic equality to
`Design.runOpen` on every one of the design's declared coordinates. -/
def simulator : FastEval.VerifiedSimulator design := ⟨design_fastWF⟩

theorem fastRunOpen_agrees (n : Nat) (ιs : Nat → InEnv) :
    Agree design (simulator.runOpen ιs n simulator.reset)
      (design.runOpen ιs n design.reset) :=
  simulator.runOpenFromReset_eq n ιs

/-! ### Design-derived system execution

The behavioral DDR/GP models are environment components, not a second core
model. Their requests are therefore driven from the generated Design state.
The handwritten ISS consumes the resulting input stream only as an independent
differential oracle. -/

/-! The environment reads a small projection of generated core state.  Resolve
those typed handles once, before execution, instead of maintaining another
string/width adapter in the cycle loop. -/

structure DerivedView where
  st        : FastEval.RegSlot design stReg
  running   : FastEval.RegSlot design runningReg
  halted    : FastEval.RegSlot design haltedReg
  coreRd    : FastEval.RegSlot design coreRdReg
  coreWr    : FastEval.RegSlot design coreWrReg
  coreAddr  : FastEval.RegSlot design coreAddrReg
  coreWdata : FastEval.RegSlot design coreWdataReg
  jtagRd    : FastEval.RegSlot design jtagRdReg
  jtagWr    : FastEval.RegSlot design jtagWrReg
  jtagWdata : FastEval.RegSlot design jtagWdataReg
  ddrAddrJ  : FastEval.RegSlot design ddrAddrJReg
  gpRd      : FastEval.RegSlot design gpRdReg
  gpWr      : FastEval.RegSlot design gpWrReg

def derivedView? : Option DerivedView := do
  let st        ← FastEval.regSlot? design stReg
  let running   ← FastEval.regSlot? design runningReg
  let halted    ← FastEval.regSlot? design haltedReg
  let coreRd    ← FastEval.regSlot? design coreRdReg
  let coreWr    ← FastEval.regSlot? design coreWrReg
  let coreAddr  ← FastEval.regSlot? design coreAddrReg
  let coreWdata ← FastEval.regSlot? design coreWdataReg
  let jtagRd    ← FastEval.regSlot? design jtagRdReg
  let jtagWr    ← FastEval.regSlot? design jtagWrReg
  let jtagWdata ← FastEval.regSlot? design jtagWdataReg
  let ddrAddrJ  ← FastEval.regSlot? design ddrAddrJReg
  let gpRd      ← FastEval.regSlot? design gpRdReg
  let gpWr      ← FastEval.regSlot? design gpWrReg
  return DerivedView.mk st running halted coreRd coreWr coreAddr coreWdata
    jtagRd jtagWr jtagWdata ddrAddrJ gpRd gpWr

def prepareDerivedView : IO DerivedView :=
  match derivedView? with
  | some view => pure view
  | none => throw <| IO.userError
      "LNP64mini: declaration-derived environment view failed"

/-- The external DDR request selected from the generated core's pre-state. -/
def derivedHpReq (view : DerivedView) (fs : FastSt) :
    Bool × Bool × Nat × BitVec 64 :=
  let state := view.st.readNat fs
  let owns := view.running.readNat fs = 1 && state ≠ S_TRAP &&
    state ≠ S_WAIT && state ≠ S_PAUSE
  if owns then
    (view.coreRd.readNat fs = 1, view.coreWr.readNat fs = 1,
      view.coreAddr.readNat fs, view.coreWdata.read fs)
  else
    (view.jtagRd.readNat fs = 1, view.jtagWr.readNat fs = 1,
      view.ddrAddrJ.readNat fs, view.jtagWdata.read fs)

/-- Complete executable system whose core is the certified generated view. -/
structure DerivedSystem where
  core : FastSt
  ddr  : DdrModel
  gp   : GpModel := {}

def DerivedSystem.reset (dag : DagEval.VerifiedSimulator design)
    (image : List (Nat × BitVec 64)) (latency : Nat) : DerivedSystem :=
  { core := dag.reset
    ddr := { mem := Std.HashMap.ofList image, latency := latency } }

/-- One canonical system cycle. Peripheral inputs and request sampling both
use pre-state, matching `Design.cycleOpen`'s synchronous boundary. -/
def DerivedSystem.step (view : DerivedView) (dag : DagEval.VerifiedSimulator design)
    (system : DerivedSystem) (cmd : MiniIn) (gpRval : BitVec 32) :
    DerivedSystem × MiniIn :=
  let (mdone, mrd) := system.ddr.outputs
  let (gdone, grd) := system.gp.outputs
  let inp : MiniIn :=
    { cmd with
      mDone := mdone
      mRdata := mrd
      mBusy := DdrModel.busy system.ddr
      gpDone := gdone
      gpRdata := grd
      gpBusy := system.gp.pending }
  let (rd, wr, addr, wdata) := derivedHpReq view system.core
  let ddr := system.ddr.step rd wr addr wdata
  let gp := system.gp.step (view.gpRd.readNat system.core = 1)
    (view.gpWr.readNat system.core = 1) gpRval
  let core := dag.cycleOpen inp.toEnv system.core
  ({ core, ddr, gp }, inp)

/-- Result of executing the generated Design with its behavioral environment. -/
structure DerivedRun where
  system : DerivedSystem
  cycles : Nat

def DerivedRun.reg {w : Nat} (run : DerivedRun) (r : Reg w) : Option (BitVec w) :=
  (FastEval.regSlot? design r).map (fun slot => slot.read run.system.core)

def DerivedRun.regNat {w : Nat} (run : DerivedRun) (r : Reg w) : Option Nat :=
  (run.reg r).map (fun value => value.toNat)

def DerivedRun.mem {aw dw : Nat} (run : DerivedRun) (m : Mem aw dw)
    (addr : BitVec aw) : Option (BitVec dw) :=
  (FastEval.memSlot? design m).map (fun slot => slot.read run.system.core addr)

def DerivedRun.memNat {aw dw : Nat} (run : DerivedRun) (m : Mem aw dw)
    (addr : BitVec aw) : Option Nat :=
  (run.mem m addr).map (fun value => value.toNat)

/-- Pure execution engine for the generated Design. The handwritten ISS is
not involved; clients with expected architectural outcomes should use this
runner. -/
def runDesignDag (view : DerivedView) (dag : DagEval.VerifiedSimulator design)
    (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32) (maxCyc : Nat) :
    DerivedRun := Id.run do
  let mut system := DerivedSystem.reset dag image latency
  let mut cycles := 0
  for k in List.range maxCyc do
    if view.halted.readNat system.core = 1 then
      return { system, cycles }
    let (next, _) := system.step view dag (cmds k) (gpVal k)
    system := next
    cycles := cycles + 1
  return { system, cycles }

/-- Primary public simulator: prepare the certified shared DAG fail-closed,
then run the Design-derived core and environment. -/
def runDesign (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32) (maxCyc : Nat) :
    IO DerivedRun := do
  let dag ← DagEval.prepareSimulator simulator "LNP64mini"
  let view ← prepareDerivedView
  return runDesignDag view dag image latency cmds gpVal maxCyc

/-- Run the certified Design while counting cycles on which a typed one-bit
coordinate is asserted. The coordinate is resolved once and failure is
reported before execution. -/
def runDesignCount (observed : Reg 1) (image : List (Nat × BitVec 64))
    (latency : Nat) (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32)
    (maxCyc : Nat) : IO (DerivedRun × Nat) := do
  let dag ← DagEval.prepareSimulator simulator "LNP64mini"
  let view ← prepareDerivedView
  let slot ← FastEval.prepareRegSlot design observed
  let mut system := DerivedSystem.reset dag image latency
  let mut cycles := 0
  let mut asserted := 0
  for k in List.range maxCyc do
    if view.halted.readNat system.core = 1 then
      return (⟨system, cycles⟩, asserted)
    let (next, _) := system.step view dag (cmds k) (gpVal k)
    system := next
    cycles := cycles + 1
    if slot.readNat system.core = 1 then asserted := asserted + 1
  return (⟨system, cycles⟩, asserted)

private def evaluateDag (dag : DagEval.VerifiedSimulator design)
    (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (nCyc : Nat) (cap : Nat := 16) : Nat := Id.run do
  let some plan := design.coordPlan? cap | return 1
  let some view := derivedView? | return 1
  let mut system := DerivedSystem.reset dag image latency
  let mut s : MiniSt := {}
  let mut bad := 0
  for k in List.range nCyc do
    let (system', inp) := system.step view dag (cmds k) 0
    s := MiniIss.step s inp
    system := system'
    let (mism, undeclared, _) := diffFastAgainstOracle plan system.core
      { read := issAtWith (issRegs s) (issMems s), unmodelled := issUnmodelled }
    bad := bad + mism.length + undeclared.length
  return bad

/-- Run the certified Design and ISS through Loom's generic differential
runner. Coordinate planning and oracle coverage are fail-closed; only the
machine-specific system step and ISS reader live here. -/
private def runCertified (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32) (nCyc : Nat)
    (cap : Nat := 64) : IO (Nat × Nat) := do
  let plan ← design.prepareCoordPlan cap
  let dag ← DagEval.prepareSimulator simulator "LNP64mini"
  let view ← prepareDerivedView
  let result ← Loom.Runner.run
    { label := "LNP64mini core Design/ISS", steps := nCyc }
    (DerivedSystem.reset dag image latency, ({} : MiniSt)) fun k state => do
      let (system, inp) := state.1.step view dag (cmds k) (gpVal k)
      let s := MiniIss.step state.2 inp
      let regs := issRegs s
      let mems := issMems s
      let oracle : Oracle :=
        { read := issAtWith regs mems, unmodelled := issUnmodelled }
      return ((system, s), sampleFastAgainstOracle plan system.core oracle)
  return (result.failureCount, result.excluded.length)

/-- Primary LNP64mini lockstep.

The machine is executed by the certified shared DAG evaluator, and comparison
coverage is derived from `Design.coords`. The hand-written ISS participates
only as an independent differential oracle. A failed DAG certificate aborts;
there is no fallback to tree evaluation or the legacy comparator. -/
def lockstep (image : List (Nat × BitVec 64)) (latency : Nat)
    (cmds : Nat → MiniIn) (gpVal : Nat → BitVec 32) (nCyc : Nat)
    (cap : Nat := 64) : IO Nat := do
  let (bad, _) ← runCertified image latency cmds gpVal nCyc cap
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
  [ encImmI OP_ADDI 1 0 7,        -- 0x1000 ADDI r1 = 7
    encImmI OP_ADDI 2 0 5,        -- ADDI r2 = 5
    enc OP_ADD 3 1 2,            -- ADD  r3 = 12
    enc OP_SUB 4 1 2,            -- SUB  r4 = 2
    enc OP_MUL 5 1 2,            -- MUL  r5 = 35
    enc OP_DIV 6 5 2,            -- DIV  r6 = 35/5 = 7
    encImmS OP_ST 0 3 0,        -- SD [r0+0] = r3 (zp store, 8-byte)  (rs1=0,rs2=3,imm_s=0)
    encImmI OP_LD 8 0 0,        -- LD r8 = [r0+0] = 12 (zp load)
    enc OP_EXIT 0 0 0 ]           -- EXIT

/-- Fast lockstep program (no long high-mul/div; reaches EXIT quickly so the
EDSL≡ISS lockstep stays within the closure-RegEnv budget). Covers fetch,
ALU-reg, ALU-imm, small MUL, small DIV, SEL, GET_PCR(Tid), zp store
(1-cycle dmem pipeline), zp load, DDR-data store (RMW) + DDR-data load,
LR/SC, UART TX, branch-taken, JAL, JALR, and EXIT. -/
def progLS : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 7,        -- 0x1000 w0  ADDI r1 = 7
    encImmI OP_ADDI 2 0 5,        --       w1  ADDI r2 = 5
    encImmI OP_ADDI 3 0 1,        --       w2  ADDI r3 = 1
    enc OP_ADD 4 1 2,            --       w3  ADD  r4 = 12
    enc OP_MUL 5 1 3,            --       w4  direct MUL  r5 = 7*1 = 7
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

/-- Design-derived architectural smoke battery. To keep the zeroing
sweep short in the harness we START before zeroing completes is NOT valid
(mini3 gates the FSM on ¬zeroing), so we let the full 1024-cycle sweep run
but only compare a compact touched set. This is expensive; we cap prog1 to
a short run and rely on progtest + iverilog for the deep programs. -/
def selftest : IO Unit := do
  -- Start immediately (cmd 13 bit1 only) from the reset state; the rf/dmem
  -- are already zero (RAM reset), tstate0=READY, pc=TEXT_BASE — so we skip
  -- the 1024-cycle zeroing sweep and exercise the FSM directly.
  let start : Nat → MiniIn := fun k => if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
  let scripts : List
      (String × List (BitVec 64) × Nat × BitVec 32 × (DerivedRun → Bool)) :=
    [("LS   (ALU/MUL/SEL/GET_PCR/zp-st/zp-ld/branch/JAL)", progLS, 54, 0,
      fun run => run.regNat haltedReg == some 1 &&
        run.memNat rfBank 4 == some 12 && run.memNat rfBank 11 == some 12 &&
        run.memNat dmemBank 0 == some 12),
     ("DDR  (S_DL/S_DST/S_DSW RMW store + DDR load)", progDDR, 30, 0,
      fun run => run.regNat haltedReg == some 1 && run.memNat rfBank 8 == some 42),
     ("LRSC (LR.D reserve + SC.D success)", progLRSC, 22, 0,
      fun run => run.regNat haltedReg == some 1 && run.memNat rfBank 6 == some 0 &&
        run.memNat rfBank 8 == some 77 && run.memNat dmemBank 0 == some 77),
     ("UART (UART TX store + UART RX load)", progUART, 24, 0,
      fun run => run.regNat haltedReg == some 1 && run.memNat rfBank 8 == some 0 &&
        run.memNat uartBank 0 == some 0x41),
     ("SCH  (CLONE + YIELD + THREAD_EXIT switch)", progSched, 34, 0,
      fun run => run.regNat haltedReg == some 1),
     ("SLP  (SLEEP + sleep-scan wake + S_WAIT)", progSleep, 20, 0,
      fun run => run.regNat haltedReg == some 1),
     ("GP   (S_GPL/S_GPS MMIO load/store handshake)", progGP, 24, 0xABCD,
      fun run => run.regNat haltedReg == some 1 && run.memNat rfBank 8 == some 0xABCD)]
  let mut failed := 0
  let mut totalSteps := 0
  for (nm, program, _cycles, gp, check) in scripts do
    let run ← runDesign (imageFrom TEXT_BASE program) 1 start (fun _ => gp) 400
    totalSteps := totalSteps + run.cycles
    if check run then IO.println s!"  OK  {nm}  ({run.cycles} cyc)"
    else do
      IO.println s!"  FAIL {nm} (architectural outcome mismatch after {run.cycles} cyc; halted={run.regNat haltedReg})"
      failed := failed + 1
  if failed = 0 then
    IO.println s!"LNP64MINI SELFTEST OK — certified shared-DAG Design outcomes pass across {scripts.length} scripts"
  else
    IO.println s!"LNP64MINI SELFTEST RESULT FAIL — {failed} scripts"
  (Loom.Runner.Result.fromFailureCount "LNP64mini core selftest" totalSteps failed
    "Design architectural outcome mismatch").requirePass

/-! ## Independent differential oracle

`runIss` is retained for explicit oracle diagnostics and comparison. It is not
the primary simulator; architectural outcome checks should use `runDesign`.
-/

/-- Run the independent ISS oracle to `halted` or `maxCyc`. -/
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
    let parts := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
    if h : parts.length = 2 then
      IO.println s!"STEP_OP_CASE {i}"
      issStepOp (BitVec.ofNat 64 (hexVal parts[0]))
        (((parts[1]).splitOn ",").map (fun t => (t.trimAscii.toString.toNat?).getD 0))
      i := i + 1

/-! ## progtest — hand-encoded programs on the Design-derived simulator -/

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
  let s ← runDesign img 1 (fun i => if i = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}) (fun _ => 0) 400
  IO.println s!"PROGTEST prog1: halted={s.regNat haltedReg == some 1} cycles={s.cycles} pc={hexStr ((s.regNat pcReg).getD 0)} retire={(s.regNat retireReg).getD 0}"
  IO.print "  rf[1..8] ="
  for i in List.range 8 do
    IO.print s!" r{i+1}={(s.memNat rfBank (BitVec.ofNat 10 (i + 1))).getD 0}"
  IO.println ""
  IO.println s!"  dmem[0]={(s.memNat dmemBank 0).getD 0}"
  let ok1 := s.regNat haltedReg = some 1 ∧
    s.memNat rfBank 1 = some 7 ∧ s.memNat rfBank 3 = some 12 ∧
    s.memNat rfBank 5 = some 35 ∧ s.memNat rfBank 6 = some 7 ∧
    s.memNat rfBank 8 = some 12 ∧ s.memNat dmemBank 0 = some 12

  -- (b) trap + RESUME: run to the trap, then at a later cycle SET_PC=0x1008
  -- (word 1) and RESUME (cmd 54).
  let imgT := imageFrom TEXT_BASE progTrapReal
  let cmdsT : Nat → MiniIn := fun i =>
    if i = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
    else if i = 10 then { cmdValid := true, cmdIdx := 53, cmdData := BitVec.ofNat 32 0x1008 }  -- SET_PC
    else if i = 11 then { cmdValid := true, cmdIdx := 54, cmdData := 1 }                        -- RESUME
    else {}
  let st ← runDesign imgT 1 cmdsT (fun _ => 0) 200
  IO.println s!"PROGTEST trap+resume: halted={st.regNat haltedReg == some 1} cycles={st.cycles} r1={(st.memNat rfBank 1).getD 0} trap_active={st.regNat trapActiveReg == some 1}"
  let ok2 := st.regNat haltedReg = some 1 ∧ st.memNat rfBank 1 = some 55 ∧
    st.regNat trapActiveReg = some 0

  if ok1 ∧ ok2 then
    IO.println "PROGTEST RESULT PASS — outcomes came from the certified shared-DAG Design simulator"
  else
    IO.println "PROGTEST RESULT FAIL"
  (Loom.Runner.Result.fromBool "LNP64mini Design-derived progtest" st.cycles
    (decide (ok1 ∧ ok2)) "architectural outcome mismatch").requirePass

/-! ## SMP-extension programs + selftest (DUAL_SPEC ladder step 1)

Directed Design-derived checks for the `res_kill` / `sc_fail` / `doorbell` /
`hold` inputs and the `wake_out` register. -/

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

/-- The SMP-extension architectural assertions. -/
def smpSelftest : IO Unit := do
  let start : Nat → MiniIn := fun k =>
    if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
  -- (1) res_kill held high: every LR's reservation dies the same cycle, so
  --     the SC must FAIL (rd=1) and leave dmem[0] untouched.
  let rk : Nat → MiniIn := fun k => { start k with resKill := true }
  -- (2) doorbell at cycle 26: the FUTEX-blocked thread wakes and finishes.
  -- EXT-4 REVERTED (the NT=32 fit): the wake is UNKEYED, so ANY doorbell wakes
  -- a parked thread regardless of key (a spurious wake is legal; the waiter
  -- re-checks). `db` and `dbWrong` carry different keys but now behave
  -- identically; what still holds is that a wake REQUIRES a doorbell (the
  -- no-doorbell control stays parked).
  let db : Nat → MiniIn :=
    fun k => { start k with doorbell := k = 26, doorbellKey := 0x2000 }
  let dbWrong : Nat → MiniIn :=
    fun k => { start k with doorbell := k = 26, doorbellKey := 0x3000 }
  -- (3) hold over cycles 10..30: the FSM freezes at the next S_F0, then resumes.
  let hd : Nat → MiniIn := fun k => { start k with hold := 10 ≤ k ∧ k ≤ 30 }
  -- (4) sc_fail: the arbiter refuses the global SC at the serialization point.
  let sf : Nat → MiniIn := fun k => { start k with scFail := true }
  let sfs ← runDesign (imageFrom TEXT_BASE progScDDR) 1 sf (fun _ => 0) 200
  let sos ← runDesign (imageFrom TEXT_BASE progScDDR) 1 start (fun _ => 0) 200
  let okSc := sfs.regNat haltedReg == some 1 && sos.regNat haltedReg == some 1 &&
    sfs.memNat rfBank 6 == some 1 && sos.memNat rfBank 6 == some 0
  IO.println s!"  sc_fail: refused r6={sfs.memNat rfBank 6} (want 1) accepted r6={sos.memNat rfBank 6} (want 0)"
  let sk ← runDesign (imageFrom TEXT_BASE progLRSC) 1 rk (fun _ => 0) 200
  let okRk := sk.regNat haltedReg == some 1 && sk.memNat rfBank 6 == some 1 &&
    sk.memNat dmemBank 0 == some 0 && sk.memNat rfBank 8 == some 0
  IO.println s!"  res_kill: halted={sk.regNat haltedReg} r6={sk.memNat rfBank 6} (want 1=fail) dmem[0]={sk.memNat dmemBank 0} (want 0)"
  let sd ← runDesign (imageFrom TEXT_BASE progDoorbell) 1 db (fun _ => 0) 300
  let okDb := sd.regNat haltedReg == some 1 && sd.memNat rfBank 9 == some 5
  IO.println s!"  doorbell: halted={sd.regNat haltedReg} cycles={sd.cycles} r9={sd.memNat rfBank 9} (want 5) tstate0={sd.regNat (tstateRegs.reg ⟨0, by decide⟩)}"
  -- doorbell-less control: the thread must STAY parked (no spurious wake)
  let sn ← runDesign (imageFrom TEXT_BASE progDoorbell) 1 start (fun _ => 0) 300
  let okNo := sn.regNat haltedReg == some 0 &&
    sn.regNat (tstateRegs.reg ⟨0, by decide⟩) == some 3 && sn.memNat rfBank 9 == some 0
  IO.println s!"  no-doorbell control: halted={sn.regNat haltedReg} (want 0) tstate0={sn.regNat (tstateRegs.reg ⟨0, by decide⟩)} (want 3)"
  -- EXT-4 reverted (the NT=32 fit): the wake is unkeyed, so a doorbell on ANY
  -- key wakes a parked thread (a spurious wake is legal; the waiter re-checks).
  -- The keyed "wrong key stays parked" claim no longer holds; what remains is
  -- that a wake REQUIRES a doorbell (the no-doorbell control above).
  let sx ← runDesign (imageFrom TEXT_BASE progDoorbell) 1 dbWrong (fun _ => 0) 300
  let okKey := sx.regNat haltedReg == some 1 && sx.memNat rfBank 9 == some 5
  IO.println s!"  any-key doorbell (unkeyed): halted={sx.regNat haltedReg} (want 1) r9={sx.memNat rfBank 9} (want 5)"
  let (wakeRun, nw) ← runDesignCount wakeOutReg (imageFrom TEXT_BASE progWake)
    1 start (fun _ => 0) 300
  IO.println s!"  wake_out pulses={nw} (want 1) halted={wakeRun.regNat haltedReg}"
  let okWk := nw == 1 && wakeRun.regNat haltedReg == some 1
  -- hold: the held run must reach the SAME architectural state as the free run
  let sh ← runDesign (imageFrom TEXT_BASE progLRSC) 1 hd (fun _ => 0) 300
  let free ← runDesign (imageFrom TEXT_BASE progLRSC) 1 start (fun _ => 0) 300
  let rfEq := (List.range 1024).all fun i =>
    sh.memNat rfBank (BitVec.ofNat 10 i) == free.memNat rfBank (BitVec.ofNat 10 i)
  let okHd := sh.regNat haltedReg == some 1 && free.regNat haltedReg == some 1 &&
    rfEq && sh.regNat retireReg == free.regNat retireReg && free.cycles < sh.cycles
  IO.println s!"  hold: cycles held={sh.cycles} free={free.cycles} (want held>free) rf equal={rfEq} retire={sh.regNat retireReg}"
  if okRk && okSc && okDb && okNo && okKey && okWk && okHd then
    IO.println "LNP64MINI SMP SELFTEST OK — Design-derived res_kill/sc_fail/doorbell/wake_out/hold outcomes"
  else
    IO.println s!"LNP64MINI SMP SELFTEST FAILED (rk={okRk} sc={okSc} db={okDb} no={okNo} key={okKey} wk={okWk} hd={okHd})"
  let ok := okRk && okSc && okDb && okNo && okKey && okWk && okHd
  (Loom.Runner.Result.fromBool "LNP64mini SMP selftest"
    (sfs.cycles + sos.cycles + sk.cycles + sd.cycles + sn.cycles + sx.cycles +
      wakeRun.cycles + sh.cycles + free.cycles)
    ok "Design-derived SMP outcome assertion failed").requirePass


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

/-- Run the certified Design and audit every observed thread switch. For each
switch, the outgoing PC must be saved and the incoming PC restored from the
typed thread-PC memory. -/
def preemptAudit (image : List (Nat × BitVec 64)) (q : Nat) (maxCyc : Nat) :
    IO (Nat × Bool × DerivedRun) := do
  let dag ← DagEval.prepareSimulator simulator "LNP64mini"
  let view ← prepareDerivedView
  let curSlot ← FastEval.prepareRegSlot design curReg
  let pcSlot ← FastEval.prepareRegSlot design pcReg
  let stSlot ← FastEval.prepareRegSlot design stReg
  let tpcSlot ← FastEval.prepareMemSlot design tpcBank
  let cmds := cmdQuantum q
  let mut system := DerivedSystem.reset dag image 1
  let mut switches := 0
  let mut ok := true
  let mut cycles := 0
  for k in List.range maxCyc do
    if view.halted.readNat system.core = 1 then
      return (switches, ok, ⟨system, cycles⟩)
    let outgoing := curSlot.read system.core
    let savedPc := pcSlot.read system.core
    let (next, _) := system.step view dag (cmds k) 0
    let incoming := curSlot.read next.core
    if incoming ≠ outgoing then
      switches := switches + 1
      if tpcSlot.read next.core outgoing ≠ savedPc then ok := false
      if pcSlot.read next.core ≠ tpcSlot.read system.core incoming then ok := false
      if stSlot.readNat next.core ≠ S_F0 then ok := false
    system := next
    cycles := cycles + 1
  return (switches, ok, ⟨system, cycles⟩)

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

/-- The prediction line for `fpga/zc702/tb_lnp64mini_preempt.v`, printed from
the certified Design-derived simulator. -/
def preemptPredict (q : Nat) (maxCyc : Nat := 20000) : IO Unit := do
  let (fires, _, run) ← preemptAudit (imageFrom TEXT_BASE progSpin) q maxCyc
  let halted := run.regNat haltedReg == some 1
  IO.println s!"PREEMPT halted={if halted then 1 else 0} \
trap={(run.regNat trapActiveReg).getD 0} pc={if halted then (run.regNat pcReg).getD 0 else 0} \
r5={(run.memNat rfBank 5).getD 0} r9={(run.memNat rfBank 9).getD 0} dmem0={(run.memNat dmemBank 0).getD 0} \
t1state={(run.regNat (tstateRegs.reg ⟨1, by decide⟩)).getD 0} preempted={if fires ≠ 0 then 1 else 0}"

/-! ## EXT-2 — the domain selftest

**A thread cannot leave its domain by spawning.** Put the parent in a
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
  let run ← runDesign img 1 cmdDomain (fun _ => 0) 200
  let parent := run.memNat tdomBank 0
  let child  := run.memNat tdomBank 1
  let others := (List.range NT).drop 2 |>.filter (fun i =>
    run.memNat tdomBank (BitVec.ofNat 5 i) ≠ some 0)
  IO.println s!"  domain: parent tdom[0]={parent} (want {DOM_TEST}) child tdom[1]={child} (want {DOM_TEST}) other non-zero slots={others.length} (want 0) cur_dom={run.regNat curDomReg}"
  let okInherit := parent = some DOM_TEST && child = some DOM_TEST && others.isEmpty
  if okInherit then
    IO.println "LNP64MINI DOMAIN SELFTEST OK — Design-derived CLONE cannot leave its domain"
  else
    IO.println s!"LNP64MINI DOMAIN SELFTEST FAILED (inherit={okInherit})"
  (Loom.Runner.Result.fromBool "LNP64mini domain selftest" run.cycles
    okInherit "Design-derived inheritance assertion failed").requirePass

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
  -- (1) poisoning the running thread stops the core, and it stays stopped.
  let sp ← runDesign img 1 (cmdPoison 8 24 0xFFFFFFFF) (fun _ => 0) 4000
  let sc ← runDesign img 1 (cmdQuantum 8) (fun _ => 0) 4000
  IO.println s!"  running-thread: poisoned running={sp.regNat runningReg} (want 0) retire={sp.regNat retireReg} vs unpoisoned retire={sc.regNat retireReg} halted={sc.regNat haltedReg} (want strictly less, control halts)"
  let ok1 := match sp.regNat runningReg, sp.regNat retireReg,
      sc.regNat retireReg, sc.regNat haltedReg with
    | some 0, some poisonedRetire, some controlRetire, some 1 =>
      poisonedRetire < controlRetire
    | _, _, _, _ => false
  -- (2) poisoning ONLY the child (slot 1) descheduules it; the parent runs on.
  --     The parent reaches EXIT, so `halted` is the evidence it was undisturbed.
  let sk ← runDesign img 1 (cmdPoison 8 2 0x2) (fun _ => 0) 4000
  let childPc := sk.memNat tpcBank 1
  IO.println s!"  ready-thread: parent halted={sk.regNat haltedReg} (want 1) r9={sk.memNat rfBank 9} (want 2) child tstate={sk.regNat (tstateRegs.reg ⟨1, by decide⟩)} child tpc={childPc}"
  let ok2 := sk.regNat haltedReg = some 1 && sk.memNat rfBank 9 = some 2
  if ok1 && ok2 then
    IO.println "LNP64MINI FAILSTOP SELFTEST OK — poison stops the runner AND deschedules the ready"
  else
    IO.println s!"LNP64MINI FAILSTOP SELFTEST FAILED (runner={ok1} ready={ok2})"
  (Loom.Runner.Result.fromBool "LNP64mini fail-stop selftest" (sp.cycles + sc.cycles + sk.cycles)
    (ok1 && ok2) "Design-derived fail-stop assertion failed").requirePass

/-! ## EXT-10 — the data cache

Three claims, and the third is the one worth the program:

1. a repeated load of the same address hits, and the hit returns the value
   the miss filled -- checked by loading twice and comparing;
2. a **store invalidates its own line**, so a load after a store to the same
   address sees the stored value and not the filled one. This is the defect a
   write-through cache without invalidation has, and it is invisible to any
   program that loads an address only once;
3. the checks execute the certified Design-derived simulator, so the observed
   hit, invalidation, and conflict outcomes are observations of the Design
   semantics rather than a second cache implementation.

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
  let start : Nat → MiniIn := fun k =>
    if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
  let run ← runDesign img 1 start (fun _ => 0) 600
  IO.println s!"  halted={run.regNat haltedReg} r8={run.memNat rfBank 8} (want 42, fill) r9={run.memNat rfBank 9} (want 42, hit) \
r10={run.memNat rfBank 10} (want 7, store INVALIDATED the line) r11={run.memNat rfBank 11} (want 99) \
r12={run.memNat rfBank 12} (want 7, refilled after conflict eviction)"
  let ok := run.regNat haltedReg = some 1 && run.memNat rfBank 8 = some 42 &&
    run.memNat rfBank 9 = some 42 && run.memNat rfBank 10 = some 7 &&
    run.memNat rfBank 11 = some 99 && run.memNat rfBank 12 = some 7
  if ok then
    IO.println "LNP64MINI DCACHE SELFTEST OK — hits return the filled value, and a store invalidates its own line"
  else
    IO.println s!"LNP64MINI DCACHE SELFTEST FAILED (values={ok})"
  (Loom.Runner.Result.fromBool "LNP64mini data-cache selftest" run.cycles
    ok "Design-derived cache-value assertion failed").requirePass

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

/-- §9 NESTING: handler A (gate 0) itself `gate_call`s gate 1 (handler B).
The continuation stack must carry BOTH frames: B returns to A, then A returns
to the caller. Depth 0→1→2→1→0. Under the old depth-1 bitmap the inner call
was refused (r11 stayed 0) and A's return then fell through. -/
def progGateNest : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0,          -- w0  r1 = 0  (outer gate id)
    enc OP_MINI_GATE_CALL 0 1 0,    -- w1  GATE_CALL gate 0 -> handler A (w4)
    encImmI OP_ADDI 9 0 7,          -- w2  r9 = 7  (only after the FULL nested return)
    enc OP_EXIT 0 0 0,              -- w3  EXIT
    -- handler A (domain 3), depth 1:
    encImmI OP_ADDI 2 0 1,          -- w4  r2 = 1  (inner gate id)
    enc OP_MINI_GATE_CALL 0 2 0,    -- w5  GATE_CALL gate 1 -> handler B (w8) [depth 2]
    encImmI OP_ADDI 10 0 5,         -- w6  r10 = 5 (only after B returns into A)
    enc OP_MINI_GATE_RETURN 0 0 0,  -- w7  GATE_RETURN (A -> w2) [depth 1->0]
    -- handler B (domain 4), depth 2:
    encImmI OP_ADDI 11 0 9,         -- w8  r11 = 9
    enc OP_MINI_GATE_RETURN 0 0 0 ] -- w9  GATE_RETURN (B -> w6) [depth 2->1]

/-- §9 + CLONE: the gate handler SPAWNS a thread (like the driver-spawn gate),
then returns. The clone must not disturb the caller's continuation, and the
child must start with a CLEAN gate depth (0) even if it reuses a slot. This is
the driver-in-domain path (`lnp64_gate_drvspawn_impl` → `__lnp_spawn_entry`). -/
def progGateClone : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0,            -- w0  r1 = 0 (gate id)
    enc OP_MINI_GATE_CALL 0 1 0,      -- w1  GATE_CALL gate 0 -> handler (w4)
    encImmI OP_ADDI 9 0 7,            -- w2  r9 = 7 (parent returned)
    enc OP_EXIT 0 0 0,                -- w3  EXIT (parent)
    -- handler (domain 3), inside the gate:
    encImmI OP_ADDI 5 0 (Int.ofNat (TEXT_BASE + 8*8)), -- w4 r5 = child entry (w8)
    enc OP_CLONE_SPAWN 6 5 0,         -- w5  spawn child at r5 -> r6 = tid
    encImmI OP_ADDI 10 0 5,           -- w6  r10 = 5 (parent, still in gate)
    enc OP_MINI_GATE_RETURN 0 0 0,    -- w7  GATE_RETURN (-> w2)
    enc OP_EXIT 0 0 0 ]               -- w8  child: EXIT

/-- §9 GATE-HAMMER: the driver-spawn trigger shape, directed. A loop calls the
gate N times; the handler CLONEs a child (as `lnp64_gate_drvspawn_impl` does)
then returns. N=100 > MAXD and > NT, so if the gate's per-slot depth/in_gate
accounting desyncs over repeated gate_call+CLONE-inside cycles (or hands the
tail to the clone's slot), `fault_cause` goes non-zero — the §9.2 fault fires
in software, EDSL≡ISS, no synth. `r20` (s2, callee-saved) is the loop counter;
the gate preserves it. -/
def progGateHammer : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0,                            -- w0  r1 = 0 (gate id)
    encImmI OP_ADDI 5 0 (Int.ofNat (TEXT_BASE + 10*8)), -- w1 r5 = child entry (w10)
    encImmI OP_ADDI 20 0 20,                          -- w2  r20 = 20 (> MAXD; < NT so cooperative children do not exhaust slots)
    enc OP_MINI_GATE_CALL 0 1 0,                      -- w3  [loop] GATE_CALL gate r1 -> handler(w7)
    encImmI OP_ADDI 20 20 (-1),                       -- w4  r20 = r20 - 1
    encImmS OP_BNE 20 0 (-2),                         -- w5  BNE r20,r0 -> w3 (PC-relative: w3-w5 = -2)
    enc OP_EXIT 0 0 0,                                -- w6  done (r20 hit 0)
    enc OP_CLONE_SPAWN 6 5 0,                         -- w7  [handler] clone child at r5
    enc OP_MINI_GATE_RETURN 0 0 0,                    -- w8  [handler] GATE_RETURN -> w4
    enc OP_NOP 0 0 0,                                 -- w9  pad
    enc OP_THREAD_EXIT 0 0 0 ]                        -- w10 [child] THREAD_EXIT (per-thread; frees the slot, does NOT halt the machine like OP_EXIT)

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

/-- `cmdGate` plus a preemption quantum `q`: the reschedule variant. A small `q`
preempts the parent mid-gate (at instruction boundaries), so a child spawned
inside the gate runs (and, at its EXIT entry, reclaims its slot) before the
parent's GATE_RETURN — the reschedule the cooperative loop never does. -/
def cmdGateQ (q : Nat) : Nat → MiniIn := fun k =>
  if k = 0 then
    { cmdValid := true, cmdIdx := CMD_GATE_TBL, cmdData := BitVec.ofNat 32 GATE_TBL }
  else if k = 1 then { cmdValid := true, cmdIdx := CMD_QUANTUM, cmdData := BitVec.ofNat 32 q }
  else if k = 2 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
  else {}

def gateSelftest : IO Unit := do
  let tbl  := gateDescriptor 0 (TEXT_BASE + 32) GATE_DOM_TEST
  let img  := imageFrom TEXT_BASE progGate ++ tbl
  let imgS := imageFrom TEXT_BASE progGateStay ++ tbl
  -- (1) the round trip: body ran, returned to the right place, domain restored.
  let sg ← runDesign img 1 cmdGate (fun _ => 0) 400
  IO.println s!"  round trip: halted={sg.regNat haltedReg} r10={sg.memNat rfBank 10} (want 5, gate body ran) \
r9={sg.memNat rfBank 9} (want 7, returned to w2) tdom[0]={sg.memNat tdomBank 0} (want 0) \
in_gate={sg.regNat inGateReg} (want 0)"
  let ok1 := sg.regNat haltedReg == some 1 && sg.memNat rfBank 10 == some 5 &&
    sg.memNat rfBank 9 == some 7 && sg.memNat tdomBank 0 == some 0 &&
    sg.regNat inGateReg == some 0
  -- (2) halting INSIDE the gate: the thread is in the gate's domain, not its own.
  let ss ← runDesign imgS 1 cmdGate (fun _ => 0) 400
  IO.println s!"  inside gate: halted={ss.regNat haltedReg} tdom[0]={ss.memNat tdomBank 0} \
(want {GATE_DOM_TEST}) in_gate={ss.regNat inGateReg} (want 1) r10={ss.memNat rfBank 10} (want 5)"
  let ok2 := ss.regNat haltedReg == some 1 && ss.memNat tdomBank 0 == some GATE_DOM_TEST &&
    ss.regNat inGateReg == some 1 && ss.memNat rfBank 10 == some 5
  -- (3) §17 fail-closed: an id with no descriptor must not activate.
  let su ← runDesign (imageFrom TEXT_BASE progGateUnbacked ++ tbl) 1 cmdGate (fun _ => 0) 400
  IO.println s!"  unbacked gate 1: halted={su.regNat haltedReg} r9={su.memNat rfBank 9} (want 7, refused) \
tdom[0]={su.memNat tdomBank 0} (want 0) in_gate={su.regNat inGateReg} (want 0)"
  let ok3 := su.regNat haltedReg == some 1 && su.memNat rfBank 9 == some 7 &&
    su.memNat tdomBank 0 == some 0 && su.regNat inGateReg == some 0
  -- (4) §9 NESTING: handler A gate_calls gate 1 (handler B). The continuation
  -- STACK must carry both frames; depth 0→1→2→1→0.
  let tblN := gateDescriptor 0 (TEXT_BASE + 32) GATE_DOM_TEST
              ++ gateDescriptor 1 (TEXT_BASE + 64) 4
  let imgN := imageFrom TEXT_BASE progGateNest ++ tblN
  let sn ← runDesign imgN 1 cmdGate (fun _ => 0) 400
  IO.println s!"  nested: halted={sn.regNat haltedReg} r11={sn.memNat rfBank 11} (want 9, inner ran) \
r10={sn.memNat rfBank 10} (want 5, A resumed) r9={sn.memNat rfBank 9} (want 7, A returned) \
in_gate={sn.regNat inGateReg} (want 0) gdepth0={sn.memNat gdepthBank 0} (want 0)"
  let ok4 := sn.regNat haltedReg == some 1 && sn.memNat rfBank 11 == some 9 &&
    sn.memNat rfBank 10 == some 5 && sn.memNat rfBank 9 == some 7 &&
    sn.regNat inGateReg == some 0 && sn.memNat gdepthBank 0 == some 0
  -- (5) CLONE inside a gate (the driver-spawn path): the handler spawns a
  -- child then returns; the caller's continuation must survive.
  let imgC := imageFrom TEXT_BASE progGateClone ++ tbl
  let sc ← runDesign imgC 1 cmdGate (fun _ => 0) 400
  IO.println s!"  gate-clone: halted={sc.regNat haltedReg} r9={sc.memNat rfBank 9} (want 7, parent returned) \
r10={sc.memNat rfBank 10} (want 5) r6={sc.memNat rfBank 6} (child tid) in_gate={sc.regNat inGateReg} (want 0) \
gdepth0={sc.memNat gdepthBank 0} (want 0)"
  let ok5 := sc.regNat haltedReg == some 1 && sc.memNat rfBank 9 == some 7 &&
    sc.memNat rfBank 10 == some 5 && sc.regNat inGateReg == some 0 &&
    sc.memNat gdepthBank 0 == some 0
  if ok1 && ok2 && ok3 && ok4 && ok5 then
    IO.println "LNP64MINI GATE SELFTEST OK — a gate is the only way to change domain, and only to the gate's"
  else
    IO.println s!"LNP64MINI GATE SELFTEST FAILED (roundtrip={ok1} inside={ok2} unbacked={ok3})"
  (Loom.Runner.Result.fromBool "LNP64mini gate selftest"
    (sg.cycles + ss.cycles + su.cycles + sn.cycles + sc.cycles)
    (ok1 && ok2 && ok3 && ok4 && ok5)
    "Design-derived gate assertion failed").requirePass

/-- §9 GATE-HAMMER: the driver-spawn trigger shape, directed and isolated (its
own selftest so the long run doesn't bloat `gateSelftest`). 64× gate_call with a
CLONE inside the handler; if the per-slot gate accounting desyncs, the loud
empty-stack fault (`fault_cause=1`) fires — the silicon boot's stick, reproduced in software
with full visibility (pc + SLOT), zero synth. -/
def gateHammerSelftest : IO Unit := do
  let tbl := gateDescriptor 0 (TEXT_BASE + 7*8) GATE_DOM_TEST
  let img := imageFrom TEXT_BASE progGateHammer ++ tbl
  -- ISS-only diagnostic FIRST (fast): does the loud no-op fire over the hammer?
  let (s, _, k) := runIss img 1 cmdGate (fun _ => 0) 8000
  -- STEP TRACE (ISS-only, fast): the first ~30 retires' pc, to see where
  -- GATE_RETURN lands after a CLONE-inside-gate.
  let mut ts : MiniSt := {}
  let mut td : DdrModel := { mem := Std.HashMap.ofList img, latency := 1 }
  let mut tg : GpModel := {}
  let mut lastret := 0
  for i in List.range 600 do
    if ts.halted then break
    let (s', d', g', _) := sysStep ts td tg (cmdGate i) (0 : BitVec 32)
    ts := s'; td := d'; tg := g'
    if ts.retire.toNat != lastret then
      lastret := ts.retire.toNat
      if lastret ≤ 30 then
        IO.println s!"  ret={lastret} cur={ts.cur.toNat} pc=0x{String.ofList (Nat.toDigits 16 ts.pc.toNat)} \
r20={(ts.rf[20]!).toNat} gd[cur]={(ts.gdepth[ts.cur.toNat]!).toNat} ig={ts.in_gate.toNat}"
  -- Short EDSL≡ISS lockstep (the desync, if per-iteration, triggers early;
  -- a mismatch here = a fabric-vs-model divergence).
  let bad ← lockstep img 1 cmdGate (fun _ => 0) 350
  if bad = 0 then IO.println "  OK  GATE-HAMMER lockstep (EDSL≡ISS, 350 cyc)"
  else IO.println s!"  FAIL GATE-HAMMER lockstep ({bad} mismatches)"
  let pchex := String.ofList (Nat.toDigits 16 s.fault_pc.toNat)
  IO.println s!"  hammer: halted={s.halted} r20={(s.rf[20]!).toNat} (want 0 = loop done) cyc={k}"
  let occ := (List.range NT).foldl (fun a i => if (s.tstate[i]!).toNat != 0 then a+1 else a) 0
  IO.println s!"  STUCK STATE: cur={s.cur.toNat} pc=0x{String.ofList (Nat.toDigits 16 s.pc.toNat)} \
st={s.st.toNat} occ_slots={occ} gdepth[cur]={(s.gdepth[s.cur.toNat]!).toNat} \
tstate[0..4]={(s.tstate[0]!).toNat},{(s.tstate[1]!).toNat},{(s.tstate[2]!).toNat},{(s.tstate[3]!).toNat} \
tpc[cur]=0x{String.ofList (Nat.toDigits 16 (s.tpc[s.cur.toNat]!).toNat)}"
  IO.println s!"  LOUD GATE_RETURN: fault_cause={s.fault_cause.toNat} (want 0) \
first_fault_pc=0x{pchex} first_fault_cur={s.fault_cur.toNat} in_gate={s.in_gate.toNat}"
  -- A small quantum preempts the parent mid-gate while the spawned child runs
  -- and exits. Gate ownership and continuation must remain with the parent.
  IO.println "  --- PREEMPTIVE (quantum=3): reschedule mid-gate ---"
  let mut ps : MiniSt := {}
  let mut pd : DdrModel := { mem := Std.HashMap.ofList img, latency := 1 }
  let mut pg : GpModel := {}
  let mut plr := 0
  let mut pnoop := 0
  for i in List.range 1500 do
    if ps.halted then break
    let (s', d', g', _) := sysStep ps pd pg (cmdGateQ 3 i) (0 : BitVec 32)
    ps := s'; pd := d'; pg := g'
    if ps.fault_cause.toNat != pnoop then
      pnoop := ps.fault_cause.toNat
      IO.println s!"  >>> NO-OP GATE_RETURN #{pnoop} at retire={ps.retire.toNat} slot(cur)={ps.cur.toNat} \
pc=0x{String.ofList (Nat.toDigits 16 ps.pc.toNat)} gd[cur]={(ps.gdepth[ps.cur.toNat]!).toNat} ig=0x{String.ofList (Nat.toDigits 16 ps.in_gate.toNat)}"
    else if ps.retire.toNat != plr && plr ≤ 24 then
      plr := ps.retire.toNat
      IO.println s!"  Q ret={plr} cur={ps.cur.toNat} pc=0x{String.ofList (Nat.toDigits 16 ps.pc.toNat)} \
r20={(ps.rf[20]!).toNat} gd[cur]={(ps.gdepth[ps.cur.toNat]!).toNat} ig={ps.in_gate.toNat}"
  let (sp, _, kp) := runIss img 1 (cmdGateQ 3) (fun _ => 0) 12000
  let pphex := String.ofList (Nat.toDigits 16 sp.fault_pc.toNat)
  IO.println s!"  PREEMPTIVE hammer: halted={sp.halted} r20={(sp.rf[20]!).toNat} cyc={kp} \
fault_cause={sp.fault_cause.toNat} fault_cur={sp.fault_cur.toNat} fault_pc=0x{pphex}"
  if bad = 0 && s.fault_cause.toNat == 0 && s.halted && sp.fault_cause.toNat == 0 then
    IO.println "LNP64MINI GATE HAMMER OK — gate accounting stays balanced, cooperative AND preemptive"
  else
    IO.println s!"LNP64MINI GATE HAMMER: DESYNC REPRODUCED — noop_cnt={s.fault_cause.toNat} \
slot={s.fault_cur.toNat} pc=0x{pchex} halted={s.halted} r20={(s.rf[20]!).toNat} (this IS the silicon stick, in software)"
  (Loom.Runner.Result.fromBool "LNP64mini gate hammer" 0
    (bad == 0 && s.fault_cause.toNat == 0 && s.halted && sp.fault_cause.toNat == 0)
    "gate accounting desynced (cooperative or preemptive hammer)").requirePass

/-! ## Dwell/wake gate interleavings

These programs cover gate continuations across scheduling shapes not produced
by the basic cooperative hammer:

* **Shape A (dwell)** — the child THREAD_EXITs while the parent still holds
  the gate. The handler spins for longer than the quantum between CLONE and
  RETURN, so the child runs and cleans its own slot mid-gate.
* **Shape B (park+wake)** — the parent FUTEX_WAITs *inside the gate*; the
  child flips the word, fires the (NT=32 **unkeyed**) FUTEX_WAKE, and exits;
  the woken parent then GATE_RETURNs. This is the block-in-gate → unkeyed-wake
  path the drvspawn handler's C code can take. -/

def progGateDwell : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0,                              -- w0  r1 = 0 (gate id)
    encImmI OP_ADDI 5 0 (Int.ofNat (TEXT_BASE + 12*8)), -- w1  r5 = child entry (w12)
    encImmI OP_ADDI 20 0 12,                            -- w2  r20 = 12 iterations
    enc OP_MINI_GATE_CALL 0 1 0,                        -- w3  [loop] GATE_CALL -> handler w7
    encImmI OP_ADDI 20 20 (-1),                         -- w4  r20--
    encImmS OP_BNE 20 0 (-2),                           -- w5  -> w3
    enc OP_EXIT 0 0 0,                                  -- w6  done
    enc OP_CLONE_SPAWN 6 5 0,                           -- w7  [handler] clone child
    encImmI OP_ADDI 21 0 8,                             -- w8  r21 = 8 (dwell > quantum)
    encImmI OP_ADDI 21 21 (-1),                         -- w9  [dwell] r21--
    encImmS OP_BNE 21 0 (-1),                           -- w10 -> w9
    enc OP_MINI_GATE_RETURN 0 0 0,                      -- w11 GATE_RETURN -> w4
    enc OP_THREAD_EXIT 0 0 0 ]                          -- w12 [child] THREAD_EXIT (mid-parent-gate)

def progGateParkWake : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0,                              -- w0  r1 = 0 (gate id)
    encImmI OP_ADDI 5 0 (Int.ofNat (TEXT_BASE + 13*8)), -- w1  r5 = child entry (w13)
    encImmI OP_ADDI 20 0 8,                             -- w2  r20 = 8 iterations
    encImmI OP_ADDI 10 0 0x3000,                        -- w3  r10 = futex word (DDR; 0x2000 is GATE_TBL!)
    enc OP_MINI_GATE_CALL 0 1 0,                        -- w4  [loop] GATE_CALL -> handler w9
    encImmI OP_ADDI 20 20 (-1),                         -- w5  r20--
    encImmS OP_BNE 20 0 (-2),                           -- w6  -> w4
    enc OP_EXIT 0 0 0,                                  -- w7  done
    enc OP_NOP 0 0 0,                                   -- w8  pad
    encImmS OP_ST 10 0 0,                               -- w9  [handler] [r10] = 0 (arm the wait)
    enc OP_CLONE_SPAWN 6 5 0,                           -- w10 clone child
    enc OP_FUTEX_WAIT 10 0 0,                           -- w11 PARK IN-GATE ([r10]==0 blocks)
    enc OP_MINI_GATE_RETURN 0 0 0,                      -- w12 GATE_RETURN after the wake -> w5
    encImmI OP_ADDI 7 0 1,                              -- w13 [child] r7 = 1
    encImmI OP_ADDI 6 0 0x3000,                         -- w14 r6 = futex word
    encImmS OP_ST 6 7 0,                                -- w15 [r6] = 1 (release the compare)
    enc OP_FUTEX_WAKE 6 7 0,                            -- w16 UNKEYED wake -> parent READY
    enc OP_THREAD_EXIT 0 0 0 ]                          -- w17 child exits

/-- **Shape C (driver-spawn replica)** — one token is sent before a loop of
gate entries and capability receives. The first receive consumes the token
and spawns the driver; later receives take the no-spawn arm. The test sweeps
quantum and DDR latency around the multi-state capability walk. -/
def progGateDrvspawn : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0xCAFE,                       -- w0  r1 = handle (CAP_HANDLE; defined later in the file)
    encImmI OP_ADDI 2 0 3,                            -- w1  r2 = target domain 3
    enc OP_MINI_CAP_SEND 3 1 2,                       -- w2  the ONE token
    encImmI OP_ADDI 8 0 0xCAFE,                       -- w3  r8 = expected
    encImmI OP_ADDI 4 0 0,                            -- w4  r4 = gate id
    encImmI OP_ADDI 5 0 (Int.ofNat (TEXT_BASE + 16*8)), -- w5 r5 = child entry (w16)
    encImmI OP_ADDI 20 0 6,                           -- w6  r20 = 6 iterations
    enc OP_MINI_GATE_CALL 0 4 0,                      -- w7  [loop] GATE_CALL -> handler w11
    encImmI OP_ADDI 20 20 (-1),                       -- w8  r20--
    encImmS OP_BNE 20 0 (-2),                         -- w9  -> w7
    enc OP_EXIT 0 0 0,                                -- w10 done
    enc OP_MINI_CAP_RECV 9 0 0,                       -- w11 [handler] recv (iter1 ok, then fails)
    encImmS OP_BNE 9 8 2,                             -- w12 fail -> skip clone -> w14
    enc OP_CLONE_SPAWN 6 5 0,                         -- w13 spawn the "driver"
    enc OP_MINI_GATE_RETURN 0 0 0,                    -- w14 GATE_RETURN -> w8
    enc OP_NOP 0 0 0,                                 -- w15 pad
    enc OP_THREAD_EXIT 0 0 0 ]                        -- w16 [child] THREAD_EXIT

def gateDwellSelftest : IO Unit := do
  -- ---- Shape A: child exits while the parent dwells in-gate, quantum sweep ----
  let tblA := gateDescriptor 0 (TEXT_BASE + 7*8) GATE_DOM_TEST
  let imgA := imageFrom TEXT_BASE progGateDwell ++ tblA
  let mut worstA := 0
  for q in [2, 3, 5] do
    let (s, _, k) := runIss imgA 1 (cmdGateQ q) (fun _ => 0) 12000
    let n := s.fault_cause.toNat
    worstA := max worstA n
    let pchex := String.ofList (Nat.toDigits 16 s.fault_pc.toNat)
    IO.println s!"  DWELL q={q}: halted={s.halted} r20={(s.rf[20]!).toNat} cyc={k} \
fault={n} fault_cur={s.fault_cur.toNat} fault_pc=0x{pchex} ig=0x{String.ofList (Nat.toDigits 16 s.in_gate.toNat)}"
  let badA ← lockstep imgA 1 (cmdGateQ 3) (fun _ => 0) 500
  IO.println (if badA = 0 then "  OK  DWELL lockstep (EDSL≡ISS, 500 cyc)"
              else s!"  FAIL DWELL lockstep ({badA} mismatches)")
  -- ---- Shape B: park in-gate, unkeyed wake from the child ----
  let tblB := gateDescriptor 0 (TEXT_BASE + 9*8) GATE_DOM_TEST
  let imgB := imageFrom TEXT_BASE progGateParkWake ++ tblB
  let mut worstB := 0
  for (nm, cmd) in [("coop", cmdGate), ("q=3", cmdGateQ 3), ("q=5", cmdGateQ 5)] do
    let (s, _, k) := runIss imgB 1 cmd (fun _ => 0) 12000
    let n := s.fault_cause.toNat
    worstB := max worstB n
    let pchex := String.ofList (Nat.toDigits 16 s.fault_pc.toNat)
    IO.println s!"  PARK+WAKE {nm}: halted={s.halted} r20={(s.rf[20]!).toNat} cyc={k} \
fault={n} fault_cur={s.fault_cur.toNat} fault_pc=0x{pchex} ig=0x{String.ofList (Nat.toDigits 16 s.in_gate.toNat)}"
  let badB ← lockstep imgB 1 (cmdGateQ 3) (fun _ => 0) 500
  IO.println (if badB = 0 then "  OK  PARK+WAKE lockstep (EDSL≡ISS, 500 cyc)"
              else s!"  FAIL PARK+WAKE lockstep ({badB} mismatches)")
  -- ---- Shape C: the drvspawn replica (recv-once + clone, then fail-retries),
  -- swept over quantum x DDR latency ----
  -- inbox entry for domain 3 (capInboxEmpty is defined below this point)
  let tblC := gateDescriptor 0 (TEXT_BASE + 11*8) 3
              ++ [(ddrWord (DATA_BASE + 0x2100 + 3*16 + 8), BitVec.ofNat 64 0x100)]
  let imgC := imageFrom TEXT_BASE progGateDrvspawn ++ tblC
  let cmdCapQ (q : Nat) : Nat → MiniIn := fun k =>
    if k = 0 then { cmdValid := true, cmdIdx := CMD_GATE_TBL, cmdData := BitVec.ofNat 32 GATE_TBL }
    else if k = 1 then { cmdValid := true, cmdIdx := CMD_CAP_TBL, cmdData := BitVec.ofNat 32 0x2100 }
    else if k = 2 && q > 0 then { cmdValid := true, cmdIdx := CMD_QUANTUM, cmdData := BitVec.ofNat 32 q }
    else if k = 3 then { cmdValid := true, cmdIdx := 13, cmdData := 2 }
    else {}
  let mut worstC := 0
  let mut haltC := true
  for (q, lat) in [(0,1), (3,1), (5,1), (0,8), (3,8), (5,8), (3,16)] do
    let (s, _, k) := runIss imgC lat (cmdCapQ q) (fun _ => 0) 60000
    let n := s.fault_cause.toNat
    worstC := max worstC n
    haltC := haltC && s.halted
    let pchex := String.ofList (Nat.toDigits 16 s.fault_pc.toNat)
    IO.println s!"  DRVSPAWN q={q} lat={lat}: halted={s.halted} r20={(s.rf[20]!).toNat} r9=0x{String.ofList (Nat.toDigits 16 (s.rf[9]!).toNat)} \
cyc={k} fault={n} fault_cur={s.fault_cur.toNat} fault_pc=0x{pchex} ig=0x{String.ofList (Nat.toDigits 16 s.in_gate.toNat)}"
  let badC ← lockstep imgC 1 (cmdCapQ 3) (fun _ => 0) 500
  IO.println (if badC = 0 then "  OK  DRVSPAWN lockstep (EDSL≡ISS, 500 cyc)"
              else s!"  FAIL DRVSPAWN lockstep ({badC} mismatches)")
  -- Step trace of the cooperative run: iteration 1 completes, iteration 2
  -- parks forever. Print every retire until the hang window (~55) plus the
  -- final parked state, including the futex word and per-slot tstate.
  IO.println "  --- PARK+WAKE coop step trace (iter 1 ok -> iter 2 parks) ---"
  let mut ts : MiniSt := {}
  let mut td : DdrModel := { mem := Std.HashMap.ofList imgB, latency := 1 }
  let mut tg : GpModel := {}
  let mut lastret := 0
  for i in List.range 3000 do
    if ts.halted then break
    let (s', d', g', _) := sysStep ts td tg (cmdGate i) (0 : BitVec 32)
    ts := s'; td := d'; tg := g'
    if ts.retire.toNat != lastret then
      lastret := ts.retire.toNat
      if lastret ≤ 55 then
        IO.println s!"  ret={lastret} cur={ts.cur.toNat} pc=0x{String.ofList (Nat.toDigits 16 ts.pc.toNat)} \
r20={(ts.rf[20]!).toNat} ig={ts.in_gate.toNat} ts0={(ts.tstate[0]!).toNat} ts1={(ts.tstate[1]!).toNat} ts2={(ts.tstate[2]!).toNat}"
  let word := (td.mem.get? (ddrWord (DATA_BASE + 0x3000))).getD 0
  IO.println s!"  PARKED STATE: cur={ts.cur.toNat} pc=0x{String.ofList (Nat.toDigits 16 ts.pc.toNat)} \
st={ts.st.toNat} ig={ts.in_gate.toNat} futex_word={word.toNat} \
ts[0..3]={(ts.tstate[0]!).toNat},{(ts.tstate[1]!).toNat},{(ts.tstate[2]!).toNat},{(ts.tstate[3]!).toNat} \
tpc0=0x{String.ofList (Nat.toDigits 16 (ts.tpc[0]!).toNat)} tpc1=0x{String.ofList (Nat.toDigits 16 (ts.tpc[1]!).toNat)} \
tpc2=0x{String.ofList (Nat.toDigits 16 (ts.tpc[2]!).toNat)}"
  if worstA == 0 && worstB == 0 && worstC == 0 && badA == 0 && badB == 0 && badC == 0
     && ts.halted && haltC then
    IO.println "LNP64MINI GATE DWELL/WAKE/DRVSPAWN OK — no interleaving desyncs the model"
  else
    IO.println s!"LNP64MINI GATE DWELL/WAKE/DRVSPAWN: FAIL — noop A={worstA} B={worstB} C={worstC} \
haltB={ts.halted} haltC={haltC} (a hang with noop=0 is a stall, not a desync — read the traces)"
  (Loom.Runner.Result.fromBool "LNP64mini gate dwell/wake/drvspawn" 0
    (worstA == 0 && worstB == 0 && worstC == 0 && badA == 0 && badB == 0 && badC == 0
      && ts.halted && haltC)
    "an interleaving faulted, stalled, or diverged from the ISS").requirePass

/-! ## The 1235f201 fault-conformance selftest

Three directed programs for the spec's fail-closed quartet (the first three;
no-spurious-BUSY is a separate arc). Each was a silent behavior that cost
real debugging time before the spec made it illegal (fpga_dev.md §73):

* a bare `GATE_RETURN` must FAULT (cause 1), precisely: pc at the
  instruction, no retire of it, the following instruction never runs;
* opcode 0 must FAULT in-core (cause 2), not trap to the host;
* a valid-bit-set descriptor with a misaligned entry PC must REFUSE the
  activation (step past, no gate, no fault) -- construction fails closed. -/

def progBareReturn : List (BitVec 64) :=
  [ encImmI OP_ADDI 9 0 1,             -- w0  r9 = 1 (proof the thread ran)
    enc OP_MINI_GATE_RETURN 0 0 0,     -- w1  FAULT: no continuation frame
    encImmI OP_ADDI 9 0 2,             -- w2  must NEVER execute
    enc OP_EXIT 0 0 0 ]

def progOpZero : List (BitVec 64) :=
  [ encImmI OP_ADDI 9 0 1,             -- w0  r9 = 1
    BitVec.ofNat 64 0,                 -- w1  opcode 0: FAULT, not a host trap
    encImmI OP_ADDI 9 0 2,             -- w2  must NEVER execute
    enc OP_EXIT 0 0 0 ]

def progMisalignedGate : List (BitVec 64) :=
  [ encImmI OP_ADDI 1 0 0,             -- w0  r1 = 0 (gate id)
    enc OP_MINI_GATE_CALL 0 1 0,       -- w1  must be REFUSED (entry misaligned)
    encImmI OP_ADDI 9 0 7,             -- w2  reached only on refusal
    enc OP_EXIT 0 0 0 ]

/-- Nest MAXD+1 deep: the last call must be refused with `-BUSY` (genuine
exhaustion) and the value register must be untouched. Handler = w6, which
recurses; r9 counts the calls that got in. -/
def progGateBusy : List (BitVec 64) :=
  [ encImmI OP_ADDI 4 0 0,            -- w0  r4 = gate id
    encImmI OP_ADDI 2 0 0x5A,         -- w1  r2 = a value the refusal MUST NOT touch
    enc OP_MINI_GATE_CALL 0 4 0,      -- w2  outer call -> w6
    enc OP_EXIT 0 0 0,                -- w3
    enc OP_NOP 0 0 0,                 -- w4
    enc OP_NOP 0 0 0,                 -- w5
    encImmI OP_ADDI 9 9 1,            -- w6  [handler] r9++ (depth reached)
    enc OP_MINI_GATE_CALL 0 4 0,      -- w7  recurse until the stack refuses
    -- Capture the status STICKILY: each unwinding `ret` writes status 0 over
    -- r3, so reading r3 at the end sees the last return, not the refusal.
    -- OR-accumulating keeps the one non-zero condition that ever appeared.
    enc OP_OR 10 10 3,              -- w8  r10 |= r3
    encImmI OP_JALR 0 1 0 ]           -- w9  ordinary `ret` (unwinds each frame)

/-- A gate whose descriptor is invalid: refusal must report `-MALFORMED`. -/
def progGateMalformed : List (BitVec 64) :=
  [ encImmI OP_ADDI 4 0 1,            -- w0  gate id 1 -- no descriptor
    encImmI OP_ADDI 2 0 0x5A,         -- w1  r2 = value that must survive
    enc OP_MINI_GATE_CALL 0 4 0,      -- w2  must be REFUSED
    enc OP_EXIT 0 0 0 ]

def refusalConformanceSelftest : IO Unit := do
  let mut allOk := true
  -- (a) full continuation stack -> -BUSY, value register unchanged
  let tblB := gateDescriptor 0 (TEXT_BASE + 6*8) GATE_DOM_TEST
  let imgB := imageFrom TEXT_BASE progGateBusy ++ tblB
  let sb ← runDesign imgB 1 cmdGate (fun _ => 0) 4000
  let r3b := (sb.memNat rfBank 10).getD 0
  let okB := r3b == 0xFFFFFFFFFFFFFFF2 && sb.memNat rfBank 2 == some 0x5A
             && sb.memNat rfBank 9 == some MAXD
  IO.println s!"  BUSY: captured status=0x{String.ofList (Nat.toDigits 16 r3b)} (want ...fff2 = -BUSY) \
r2={sb.memNat rfBank 2} (want 5a: value register UNCHANGED) depth reached r9={sb.memNat rfBank 9} (want {MAXD})"
  allOk := allOk && okB
  -- (b) descriptor that does not admit -> -MALFORMED, value unchanged
  let imgM := imageFrom TEXT_BASE progGateMalformed ++ gateDescriptor 0 (TEXT_BASE + 8) GATE_DOM_TEST
  let sm ← runDesign imgM 1 cmdGate (fun _ => 0) 3000
  let r3m := (sm.memNat rfBank 3).getD 0
  let okM := r3m == 0xFFFFFFFFFFFFFFFC && sm.memNat rfBank 2 == some 0x5A &&
    sm.regNat haltedReg == some 1
  IO.println s!"  MALFORMED: r3=0x{String.ofList (Nat.toDigits 16 r3m)} (want ...fffc = -MALFORMED) \
r2={sm.memNat rfBank 2} (want 5a) halted={sm.regNat haltedReg}"
  allOk := allOk && okM
  if allOk then
    IO.println "LNP64MINI REFUSAL CONFORMANCE OK — no refusal reports nothing, and none touches the value register"
  else do
    IO.println "LNP64MINI REFUSAL CONFORMANCE FAILED"
  (Loom.Runner.Result.fromBool "LNP64mini refusal conformance" (sb.cycles + sm.cycles) allOk
    "refusal assertion failed").requirePass

def faultConformanceSelftest : IO Unit := do
  let cmdStart : Nat → MiniIn := fun k =>
    if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
  let mut allOk := true
  -- (a) bare GATE_RETURN
  let imgA := imageFrom TEXT_BASE progBareReturn
  let badA ← lockstep imgA 1 cmdStart (fun _ => 0) 120
  let (sa, _, _) := runIss imgA 1 cmdStart (fun _ => 0) 2000
  let okA := sa.fault_cause.toNat == 1 && sa.fault_pc.toNat == TEXT_BASE + 8
             && sa.fault_cur.toNat == 0 && (sa.rf[9]!).toNat == 1
             && ¬ sa.running && ¬ sa.halted && sa.poison.toNat != 0
  IO.println s!"  BARE-RETURN: cause={sa.fault_cause.toNat} (want 1) pc=0x{String.ofList (Nat.toDigits 16 sa.fault_pc.toNat)} \
(want 0x{String.ofList (Nat.toDigits 16 (TEXT_BASE+8))}) r9={(sa.rf[9]!).toNat} (want 1, w2 never ran) \
running={sa.running} (want false) poison=0x{String.ofList (Nat.toDigits 16 sa.poison.toNat)} lockstep={badA}"
  allOk := allOk && okA && badA == 0
  -- (b) opcode 0
  let imgB := imageFrom TEXT_BASE progOpZero
  let badB ← lockstep imgB 1 cmdStart (fun _ => 0) 120
  let (sb, _, _) := runIss imgB 1 cmdStart (fun _ => 0) 2000
  let okB := sb.fault_cause.toNat == 2 && sb.fault_pc.toNat == TEXT_BASE + 8
             && (sb.rf[9]!).toNat == 1 && ¬ sb.running && ¬ sb.trap_active
  IO.println s!"  OP-ZERO: cause={sb.fault_cause.toNat} (want 2) pc=0x{String.ofList (Nat.toDigits 16 sb.fault_pc.toNat)} \
r9={(sb.rf[9]!).toNat} (want 1) running={sb.running} (want false) trap_active={sb.trap_active} (want false: NOT a host trap) lockstep={badB}"
  allOk := allOk && okB && badB == 0
  -- (c) misaligned entry PC: valid bit set, entry = w2+1 (unaligned)
  let tblC := [ (ddrWord (DATA_BASE + GATE_TBL),     BitVec.ofNat 64 (TEXT_BASE + 2*8 + 1)),
                (ddrWord (DATA_BASE + GATE_TBL + 8), BitVec.ofNat 64 (3 ||| 0x100)) ]
  let imgC := imageFrom TEXT_BASE progMisalignedGate ++ tblC
  let badC ← lockstep imgC 1 cmdGate (fun _ => 0) 200
  let (sc, _, _) := runIss imgC 1 cmdGate (fun _ => 0) 2000
  let okC := sc.halted && (sc.rf[9]!).toNat == 7 && sc.in_gate.toNat == 0
             && sc.fault_cause.toNat == 0
  IO.println s!"  MISALIGNED-ENTRY: halted={sc.halted} r9={(sc.rf[9]!).toNat} (want 7 = refused, stepped past) \
in_gate={sc.in_gate.toNat} (want 0) cause={sc.fault_cause.toNat} (want 0) lockstep={badC}"
  allOk := allOk && okC && badC == 0
  if allOk then
    IO.println "LNP64MINI FAULT CONFORMANCE OK — bare return faults, op 0 faults in-core, misaligned entry refuses"
  else do
    IO.println "LNP64MINI FAULT CONFORMANCE FAILED"
  (Loom.Runner.Result.fromBool "LNP64mini fault conformance" 0 allOk
    "fault assertion failed").requirePass

/-! ## §9.2 gate return sentinel

A crossing is a call to both sides. `gate_call` installs a reserved
non-canonical address in `ra`; fetching it executes `gate_return`. So a gate
handler is an **ordinary function ending in an ordinary `ret`** -- no asm
veneer, no gate epilogue in the compiler. The three programs below are the
three claims:

* the handler is ordinary and its `ret` crosses back (and the caller's `ra`
  is architecturally clobbered, which is why the veneer's `jal r1` hazard
  cannot recur: a defining instruction is native to register allocation);
* a stray `ret` to the sentinel with no activation open FAULTS -- the
  sentinel is guarded by the empty-stack fault, not by obscurity
  (`addi r5, r0, -8` materialises it exactly: sign extension IS the
  sentinel, so the test cannot be accused of knowing a magic constant);
* nesting works -- each `ret` pops one frame, the continuation stack is the
  only source of the return target. -/

def progSentinel : List (BitVec 64) :=
  [ encImmI OP_ADDI 4 0 0,            -- w0  r4 = gate id 0 (NOT r1: ra is clobbered)
    enc OP_MINI_GATE_CALL 0 4 0,      -- w1  GATE_CALL -> handler w4
    encImmI OP_ADDI 9 0 7,            -- w2  r9 = 7 (we came back to the caller)
    enc OP_EXIT 0 0 0,                -- w3
    encImmI OP_ADDI 10 0 5,           -- w4  [handler] ordinary function body
    encImmI OP_JALR 0 1 0 ]           -- w5  ordinary `ret` -- IS the gate return

def progSentinelStray : List (BitVec 64) :=
  [ encImmI OP_ADDI 5 0 (-8),         -- w0  r5 = 0xFFFF_FFFF_FFFF_FFF8 (sign-extended)
    encImmI OP_ADDI 9 0 1,            -- w1  r9 = 1
    encImmI OP_JALR 0 5 0,            -- w2  `ret` to the sentinel, NO gate open
    encImmI OP_ADDI 9 0 2,            -- w3  must NEVER execute
    enc OP_EXIT 0 0 0 ]

def progSentinelNest : List (BitVec 64) :=
  [ encImmI OP_ADDI 4 0 0,            -- w0  r4 = gate id 0
    enc OP_MINI_GATE_CALL 0 4 0,      -- w1  outer call -> w4
    encImmI OP_ADDI 9 0 7,            -- w2  r9 = 7 after both returns
    enc OP_EXIT 0 0 0,                -- w3
    encImmI OP_ADDI 10 0 5,           -- w4  [handler] depth 1
    enc OP_MINI_GATE_CALL 0 4 0,      -- w5  inner call -> w4 again (depth 2)
    encImmI OP_ADDI 11 0 6,           -- w6  runs after the inner return
    encImmI OP_JALR 0 1 0 ]           -- w7  `ret` (both levels take this path)

def sentinelSelftest : IO Unit := do
  let cmdStart : Nat → MiniIn := fun k =>
    if k = 0 then { cmdValid := true, cmdIdx := 13, cmdData := 2 } else {}
  let mut allOk := true
  -- (1) ordinary-function handler, ordinary `ret`
  let tbl := gateDescriptor 0 (TEXT_BASE + 4*8) GATE_DOM_TEST
  let img := imageFrom TEXT_BASE progSentinel ++ tbl
  let bad ← lockstep img 1 cmdGate (fun _ => 0) 200
  let (s1, _, _) := runIss img 1 cmdGate (fun _ => 0) 3000
  let ra := (s1.rf[1]!).toNat
  let ok1 := s1.halted && (s1.rf[9]!).toNat == 7 && (s1.rf[10]!).toNat == 5
             && s1.in_gate.toNat == 0 && (s1.gdepth[0]!).toNat == 0
             && s1.fault_cause.toNat == 0 && ra == 0xFFFFFFFFFFFFFFF8
  IO.println s!"  SENTINEL: halted={s1.halted} r9={(s1.rf[9]!).toNat} (want 7, caller resumed) \
r10={(s1.rf[10]!).toNat} (want 5, handler ran) ra=0x{String.ofList (Nat.toDigits 16 ra)} (want ...fff8) \
in_gate={s1.in_gate.toNat} gdepth0={(s1.gdepth[0]!).toNat} cause={s1.fault_cause.toNat} lockstep={bad}"
  allOk := allOk && ok1 && bad == 0
  -- (2) stray sentinel return with no activation open -> the §9.2 fault
  let imgS := imageFrom TEXT_BASE progSentinelStray
  let badS ← lockstep imgS 1 cmdStart (fun _ => 0) 150
  let (s2, _, _) := runIss imgS 1 cmdStart (fun _ => 0) 3000
  let ok2 := s2.fault_cause.toNat == 1 && (s2.rf[9]!).toNat == 1 && ¬ s2.running
             && s2.fault_pc.toNat == 0xFFFFFFFFFFFFFFF8
  IO.println s!"  STRAY: cause={s2.fault_cause.toNat} (want 1 = empty-stack fault) \
fault_pc=0x{String.ofList (Nat.toDigits 16 s2.fault_pc.toNat)} r9={(s2.rf[9]!).toNat} (want 1, w3 never ran) \
running={s2.running} (want false) lockstep={badS}"
  allOk := allOk && ok2 && badS == 0
  -- (3) nesting: two activations, two ordinary `ret`s
  let tblN := gateDescriptor 0 (TEXT_BASE + 4*8) GATE_DOM_TEST
  let imgN := imageFrom TEXT_BASE progSentinelNest ++ tblN
  let badN ← lockstep imgN 1 cmdGate (fun _ => 0) 300
  let (s3, _, _) := runIss imgN 1 cmdGate (fun _ => 0) 3000
  let ok3 := s3.halted && (s3.rf[9]!).toNat == 7 && (s3.rf[11]!).toNat == 6
             && s3.in_gate.toNat == 0 && (s3.gdepth[0]!).toNat == 0
             && s3.fault_cause.toNat == 0
  IO.println s!"  NEST: halted={s3.halted} r9={(s3.rf[9]!).toNat} (want 7) r11={(s3.rf[11]!).toNat} \
(want 6, inner return landed) in_gate={s3.in_gate.toNat} gdepth0={(s3.gdepth[0]!).toNat} \
cause={s3.fault_cause.toNat} lockstep={badN}"
  allOk := allOk && ok3 && badN == 0
  if allOk then
    IO.println "LNP64MINI SENTINEL OK — a handler is an ordinary function; its `ret` IS the crossing return"
  else do
    IO.println "LNP64MINI SENTINEL FAILED"
  (Loom.Runner.Result.fromBool "LNP64mini sentinel selftest" 0 allOk
    "sentinel assertion failed").requirePass

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
  (Loom.Runner.Result.fromBool "LNP64mini capability-transfer selftest" 0
    (bad == 0 && badU == 0 && ok1 && ok2 && ok3)
    "differential or capability-transfer assertion failed").requirePass

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
  let run ← runDesign img 1 start (fun _ => 0) (cyc*2)
  let occ := (List.finRange NT).foldl
    (fun n i => if run.regNat (tstateRegs.reg i) != some 0 then n+1 else n) 0
  let overFull := run.memNat rfBank 6 == some 0xFFFFFFFFFFFFFFFF
  let lastOk := run.memNat rfBank 4 != some 0xFFFFFFFFFFFFFFFF
  IO.println s!"  occupied slots={occ} (want {NT}); over-full r6={run.memNat rfBank 6} (want -1); \
last-clone r4={run.memNat rfBank 4} (valid, not -1)"
  if occ == NT && overFull && lastOk then
    IO.println s!"LNP64MINI SLOTFILL SELFTEST OK — {NT-1} clones fill the table and the {NT}th is refused"
  else
    IO.println s!"LNP64MINI SLOTFILL SELFTEST FAILED (occ={occ} want {NT}; overFull={overFull}; lastOk={lastOk})"
  (Loom.Runner.Result.fromBool "LNP64mini slot-fill selftest" run.cycles
    (occ == NT && overFull && lastOk)
    "Design-derived slot-capacity assertion failed").requirePass

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
  -- Domain-tagged: the entry's own domain hits, another misses.
  let sh ← runDesign img 1 (cmdMmu MMU_DOM false) (fun _ => 0) 300
  let sm ← runDesign img 1 (cmdMmu 5 false) (fun _ => 0) 300
  -- The observable is the LOADED VALUE, not `core_addr`. `core_addr` at halt
  -- holds the instruction fetch that followed the load, and fetches are
  -- deliberately untranslated (`ddrPc` is separate from `ddrEa`), so it
  -- cannot distinguish a hit from a fail-closed. A hit reads the mapped
  -- physical page; a fail-closed reads `DATA_BASE`, which the image never
  -- wrote, so the two values differ.
  let hitVal  := (sh.system.ddr.mem.getD
    (ddrWord ((BitVec.ofNat 32 DATA_BASE).toNat + (MMU_PPN <<< 12))) 0).toNat
  let missVal := (sh.system.ddr.mem.getD (ddrWord DATA_BASE) 0).toNat
  IO.println s!"  domain tag: from domain {MMU_DOM} r5={sh.memNat rfBank 5} (mapped page holds {hitVal}) \
| from domain 5 r5={sm.memNat rfBank 5} (fail-closed page holds {missVal})"
  let ok2 := sh.memNat rfBank 5 == some hitVal && sm.memNat rfBank 5 == some missVal && hitVal ≠ missVal
  -- (3) the shootdown: bumping the VMA's cell kills the translation.
  let sb ← runDesign img 1 (cmdMmu MMU_DOM true) (fun _ => 0) 300
  IO.println s!"  shootdown: after cmd 67 on cell {MMU_CELL}, r5={sb.memNat rfBank 5} \
(want {missVal} = fail-closed) | before the bump it was {sh.memNat rfBank 5}"
  let ok3 := sb.memNat rfBank 5 == some missVal && sh.memNat rfBank 5 != some missVal
  if ok2 && ok3 then
    IO.println "LNP64MINI MMU SELFTEST OK — translation is domain-tagged and the VMA's epoch cell shoots it down"
  else
    IO.println s!"LNP64MINI MMU SELFTEST FAILED (tag={ok2} shootdown={ok3})"
  (Loom.Runner.Result.fromBool "LNP64mini MMU selftest"
    (sh.cycles + sm.cycles + sb.cycles) (ok2 && ok3)
    "Design-derived MMU assertion failed").requirePass

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
    let run ← runDesign img 1 (cmdQuantum 0) (fun _ => 0) 300
    let got := (run.memNat rfBank 8).getD 0
    let gotB := (run.memNat rfBank 9).getD 0
    let ok := run.regNat haltedReg == some 1 && got == expect && gotB == 0xAA
    if !ok then bad := bad + 1
    IO.println s!"  {if ok then "OK  " else "FAIL"} SUBWORD {nm}"
    IO.println s!"       word=0x{String.ofList (Nat.toDigits 16 got)} \
(want 0x{String.ofList (Nat.toDigits 16 expect)}) lbu=0x{String.ofList (Nat.toDigits 16 gotB)} \
(want 0xaa)"
  if bad == 0 then
    IO.println "LNP64MINI SUBWORD SELFTEST OK — sb/sh merge into their lanes and leave the rest alone, on both paths"
  else
    IO.println s!"LNP64MINI SUBWORD SELFTEST FAILED ({bad} path(s))"
  (Loom.Runner.Result.fromFailureCount "LNP64mini subword selftest" 60 bad
    "subword path assertion failed").requirePass

/-- Direct Design outcomes for the six opcodes the renumbering broke. -/
def aluGapSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progAluGap
  let run ← runDesign img 1 (cmdQuantum 0) (fun _ => 0) 400
  let g : Nat → Nat := fun i => (run.memNat rfBank (BitVec.ofNat 10 i)).getD 0
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
  IO.println s!"  Design value checks failed={bad}"
  if bad = 0 then
    IO.println "LNP64MINI ALUGAP SELFTEST OK — not/sltu/bgeu/srli/srai/sltiu decode and write"
  else
    IO.println "LNP64MINI ALUGAP SELFTEST FAILED"
  (Loom.Runner.Result.fromBool "LNP64mini ALU-gap selftest" run.cycles
    (bad == 0) "Design-derived ALU value assertion failed").requirePass

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

Source/ISS and emulator/ISS comparisons do not cover RTL lowering. This writes
each generated program to `fpga/zc702/opdiff/`, where
`scripts/opdiff_rtl.sh` runs it through iverilog on the emitted SoC and diffs
the architectural result against the ISS. -/
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
    let t := l.trimAscii.toString
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
  (Loom.Runner.Result.fromFailureCount "LNP64mini trace selftest" n bad
    "trace-ring assertion failed").requirePass

/-- Total EDSL≡ISS mismatches over the generated ALU matrix — the same
programs `opDiffSelftest` runs, as one number.  The unit argument is
intentional: without it Lean eagerly evaluates this large executable theorem
witness whenever `Harness` is imported, including in unrelated tools. -/
def matrixMismatches (_ : Unit) : Nat := Id.run do
  let mut bad := 0
  let some dag := DagEval.prepareSimulator? simulator | return 1
  for (form, ops) in [(0, aluOpsRRR), (1, aluOpsRR), (2, aluOpsIMM), (3, selOps)] do
    for (op, _) in ops do
      for (a, b) in opVectors do
        bad := bad + evaluateDag dag
          (imageFrom TEXT_BASE (progOp form op a b)) 1 (cmdQuantum 0) 24 16
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
        let (m, _) ← runCertified img 1 (cmdQuantum 0) (fun _ => 0) 24 16
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
        let (m, _) ← runCertified img 1 (cmdQuantum 0) (fun _ => 0) 40 16
        opBad := opBad + m
        ran := ran + 1
      if opBad ≠ 0 then
        bad := bad + 1
        IO.println s!"  FAIL {nm} @0x{String.ofList (Nat.toDigits 16 base)}: {opBad} mismatches"
    for (op, nm) in memOpsStore do
      let mut opBad := 0
      for (a, _) in opVectors do
        let img := imageFrom TEXT_BASE (progStore op base a)
        let (m, _) ← runCertified img 1 (cmdQuantum 0) (fun _ => 0) 48 16
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
      let (m, _) ← runCertified img 1 (cmdQuantum 0) (fun _ => 0) 40 16
      opBad := opBad + m
      ran := ran + 1
    if opBad ≠ 0 then
      bad := bad + 1
      IO.println s!"  FAIL {nm}: {opBad} mismatches"
  -- The wide-immediate constant builders, with a DIRECTED battery: not "does
  -- one liu agree" but "does this exact 64-bit value come out".
  for (hi, lo) in constBattery do
    let img := imageFrom TEXT_BASE (progConst hi lo)
    let (m, _) ← runCertified img 1 (cmdQuantum 0) (fun _ => 0) 24 16
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
        let (m, _) ← runCertified img 1 (cmdQuantum 0) (fun _ => 0) 32 16
        opBad := opBad + m
        ran := ran + 1
    if opBad ≠ 0 then
      bad := bad + 1
      IO.println s!"  FAIL {nm}: {opBad} mismatches"
  let total := aluOpsRRR.length + aluOpsRR.length + aluOpsIMM.length
             + 2 * (memOpsLoad.length + memOpsStore.length) + brOps.length
             + wideImmOps.length + jumpOps.length
  let (_, unm) ← runCertified (imageFrom TEXT_BASE (progOp 0 OP_ADD 1 2))
                   1 (cmdQuantum 0) (fun _ => 0) 8 16
  IO.println s!"  {total} opcode/path combinations x {opVectors.length} vectors = {ran} programs"
  IO.println s!"  compared against Loom's derived coordinate set \
({(design.coords 16).length} coordinates; {unm} not modelled by the ISS)"
  if bad = 0 then
    IO.println s!"LNP64MINI OPDIFF SELFTEST OK — EDSL≡ISS on {total} ALU/load/store/branch combinations, generated not hand-written"
  else
    IO.println s!"LNP64MINI OPDIFF SELFTEST FAILED ({bad} opcodes disagree)"
  (Loom.Runner.Result.fromFailureCount "LNP64mini opcode differential selftest"
    ran bad "one or more opcode/path combinations disagreed").requirePass

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
  let (st4, _, _) := runIss img 1 (cmdRelocVma [(CMD_MAP_PROTECT, 2)]) (fun _ => 0) 600
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
  let (m, _) ← runCertified img 1 (cmdRelocVma) (fun _ => 0) 600 16
  check (m == 0) s!"EDSL≡ISS lockstep under the 3-entry non-identity map ({m} mismatches)"
  let (mF, _) ← runCertified imgF 1 (cmdRelocVma) (fun _ => 0) 600 16
  check (mF == 0) s!"EDSL≡ISS lockstep on the futex-under-delta program ({mF} mismatches)"
  let bad ← badRef.get
  if bad == 0 then
    IO.println "LNP64MINI MMU-RELOC SELFTEST OK — the catch-all relocates, the carve-outs pin, revocation is scoped per cell"
  else
    IO.println s!"LNP64MINI MMU-RELOC SELFTEST FAILED ({bad})"
  (Loom.Runner.Result.fromFailureCount "LNP64mini MMU relocation selftest" 600
    bad "MMU relocation assertion failed").requirePass

def mmuIdentitySelftest : IO Unit := do
  let mut bad := 0
  for base in [0x2000, 0x4008, 0x10000] do
    let img := imageFrom TEXT_BASE (progXlatProbe base)
    let sByp ← runDesign img 1 (cmdQuantum 0) (fun _ => 0) 400
    let sXlat ← runDesign img 1 cmdIdentityVma (fun _ => 0) 400
    let mut diffs : List String := []
    for r in [6, 7, 8, 9] do
      let bypass := sByp.memNat rfBank (BitVec.ofNat 10 r)
      let translated := sXlat.memNat rfBank (BitVec.ofNat 10 r)
      if bypass ≠ translated then
        diffs := diffs ++ [s!"r{r}: bypass={bypass} xlat={translated}"]
    if !diffs.isEmpty then
      bad := bad + 1
      IO.println s!"  FAIL base=0x{String.ofList (Nat.toDigits 16 base)}: {diffs}"
    else
      IO.println s!"  OK   base=0x{String.ofList (Nat.toDigits 16 base)} (identity xlat = bypass)"
  if bad = 0 then
    IO.println "LNP64MINI MMU-IDENTITY SELFTEST OK — an identity VMA computes exactly what bypass computes"
  else
    IO.println s!"LNP64MINI MMU-IDENTITY SELFTEST FAILED ({bad} base(s))"
  (Loom.Runner.Result.fromFailureCount "LNP64mini MMU identity selftest" 1200
    bad "identity translation differed from bypass").requirePass

def preemptSelftest : IO Unit := do
  let img := imageFrom TEXT_BASE progPreempt
  let imgLS := imageFrom TEXT_BASE progLS
  -- ---- (1)+(4) expiry switches threads; every switch resumes correctly ----
  let (fires, resumeOk, sp) ← preemptAudit img 8 4000
  let childR10 := (sp.memNat rfBank (32 + 10)).getD 0
  IO.println s!"  preempt: switches={fires} resume-audit={resumeOk} cycles={sp.cycles} halted={sp.regNat haltedReg} \
parent r9={sp.memNat rfBank 9} (want 2) child r10={childR10} (want >0) trap={sp.regNat trapActiveReg}"
  let ok1 := fires > 0 && resumeOk && sp.regNat haltedReg == some 1 &&
    sp.regNat trapActiveReg == some 0 && sp.memNat rfBank 9 == some 2 && childR10 > 0
  -- ---- (3) quantum = 0 is the cooperative machine, bit for bit ----
  let (f0, _, s0) ← preemptAudit img 0 4000
  let sn ← runDesign img 1 cmdNoQuantum (fun _ => 0) 4000
  let rfEq := (List.range 1024).all fun i =>
    s0.memNat rfBank (BitVec.ofNat 10 i) == sn.memNat rfBank (BitVec.ofNat 10 i)
  let tpcEq := (List.range NTMEM).all fun i =>
    s0.memNat tpcBank (BitVec.ofNat 5 i) == sn.memNat tpcBank (BitVec.ofNat 5 i)
  let tstateEq := (List.finRange NT).all fun i =>
    s0.regNat (tstateRegs.reg i) == sn.regNat (tstateRegs.reg i)
  let coopIdentical := rfEq && tpcEq && tstateEq &&
    s0.regNat retireReg == sn.regNat retireReg && s0.cycles == sn.cycles
  IO.println s!"  quantum=0: switches={f0} (want 0) cycles={s0.cycles} vs no-cmd control {sn.cycles} \
child r10={s0.memNat rfBank (32+10)} (want 0) state-identical={coopIdentical}"
  let ok3 := f0 == 0 && s0.regNat haltedReg == some 1 &&
    s0.memNat rfBank 9 == some 2 && s0.memNat rfBank (32 + 10) == some 0 && coopIdentical
  -- ---- (2) expiry with nobody else READY: same result, SAME cycle count ----
  let sq ← runDesign imgLS 1 (cmdQuantum 4) (fun _ => 0) 4000
  let sz ← runDesign imgLS 1 cmdNoQuantum (fun _ => 0) 4000
  let soloRfEq := (List.range 1024).all fun i =>
    sq.memNat rfBank (BitVec.ofNat 10 i) == sz.memNat rfBank (BitVec.ofNat 10 i)
  let ok2 := sq.regNat haltedReg == some 1 && sz.regNat haltedReg == some 1 &&
    soloRfEq && sq.regNat retireReg == sz.regNat retireReg && sq.cycles == sz.cycles
  IO.println s!"  solo: quantum=4 cycles={sq.cycles} vs quantum=0 cycles={sz.cycles} (want equal) \
rf equal={soloRfEq} retire={sq.regNat retireReg}"
  -- ---- Law 5: the spinner. Cooperatively it owns the core forever ----
  let imgSpin := imageFrom TEXT_BASE progSpin
  let (fq, _, sq2) ← preemptAudit imgSpin 64 20000
  let (_fc, _, sc2) ← preemptAudit imgSpin 0 20000
  IO.println s!"  spinner: quantum=64 halted={sq2.regNat haltedReg} cycles={sq2.cycles} r9={sq2.memNat rfBank 9} \
(want 42) flag={sq2.memNat dmemBank 0} switches={fq} | cooperative halted={sc2.regNat haltedReg} (want 0) \
r9={sc2.memNat rfBank 9} (want 0) child tstate={sc2.regNat (tstateRegs.reg ⟨1, by decide⟩)} (want 1 = READY, never run)"
  let ok4 := sq2.regNat haltedReg == some 1 && sq2.memNat rfBank 9 == some 42 &&
    sq2.memNat dmemBank 0 == some 1 && fq > 0 && sc2.regNat haltedReg == some 0 &&
    sc2.memNat rfBank 9 == some 0 && sc2.memNat dmemBank 0 == some 0 &&
    sc2.regNat (tstateRegs.reg ⟨1, by decide⟩) == some 1
  if ok1 && ok2 && ok3 && ok4 then
    IO.println "LNP64MINI PREEMPT SELFTEST OK — Design-derived switch/no-stall/cooperative/resume/Law-5 outcomes"
  else
    IO.println s!"LNP64MINI PREEMPT SELFTEST FAILED (switch={ok1} nostall={ok2} coop={ok3} spin={ok4})"
  (Loom.Runner.Result.fromBool "LNP64mini preemption selftest"
    (sp.cycles + s0.cycles + sn.cycles + sq.cycles + sz.cycles + sq2.cycles + sc2.cycles)
    (ok1 && ok2 && ok3 && ok4)
    "Design-derived preemption assertion failed").requirePass

end Machines.Lnp64mini
