-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Compose
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO
import Loom.Runner
import Loom.Hw.Declarations

/-!
# axi_hp_master — Loom port of the 64-bit single-beat AXI3 HP master

Faithful, bug-for-bug port of
`remote-fpga/fpga/substrate0/rtl/axi_hp_master.v`. The FSM
(IDLE→WA→WD→WB / IDLE→RA→RR) is mirrored as one Loom rule with the D9
non-blocking discipline (every read is pre-cycle). The AXI *response*
signals (`m_awready`, `m_wready`, `m_bvalid`, `m_bresp`, `m_arready`,
`m_rvalid`, `m_rdata`, `m_rresp`) and the handshake control (`start_wr`,
`start_rd`, `addr`, `wdata`) are input ports; the AXI master signals
(`m_awvalid`, `m_wdata`, …) and the status (`rdata`, `busy`, `done`,
`err`) are registers, i.e. `o_*` outputs of the emitted module.

The constant AXI qualifiers (`m_awlen`, `m_awsize`, `m_awburst`, `m_awid`,
`m_wstrb`, `m_wlast`, `m_wid`, `m_arlen`, …) are registers whose reset value
is the Verilog constant and which are never written — they emit as fixed
`o_*` ports (the thin wrapper feeds them straight to the PS7).

The selftest executes the Design directly and checks architectural outcomes
for three handshake scripts (single read, single write, back-to-back), without
maintaining a second transition function.
-/

namespace Machines.Lnp64mini.HpMaster

open Loom.Hw

/-! ## FSM states (localparams) -/

def IDLE : Nat := 0
def WA   : Nat := 1
def WD   : Nat := 2
def WB   : Nat := 3
def RA   : Nat := 4
def RR   : Nat := 5
def TIMEOUT : Nat := 4096

/-! ## Input ports -/

def startWrPort : Reg 1 := ⟨"start_wr"⟩
def startRdPort : Reg 1 := ⟨"start_rd"⟩
def addrPort : Reg 32 := ⟨"addr"⟩
def wdataPort : Reg 64 := ⟨"wdata"⟩
def awreadyPort : Reg 1 := ⟨"m_awready"⟩
def wreadyPort : Reg 1 := ⟨"m_wready"⟩
def bvalidPort : Reg 1 := ⟨"m_bvalid"⟩
def brespPort : Reg 2 := ⟨"m_bresp"⟩
def arreadyPort : Reg 1 := ⟨"m_arready"⟩
def rvalidPort : Reg 1 := ⟨"m_rvalid"⟩
def rdataInPort : Reg 64 := ⟨"m_rdata_in"⟩
def rrespPort : Reg 2 := ⟨"m_rresp"⟩

def startWr : Expr 1 := startWrPort.rd
def startRd : Expr 1 := startRdPort.rd
def addr : Expr 32 := addrPort.rd
def wdata : Expr 64 := wdataPort.rd
def awready : Expr 1 := awreadyPort.rd
def wready : Expr 1 := wreadyPort.rd
def bvalid : Expr 1 := bvalidPort.rd
def bresp : Expr 2 := brespPort.rd
def arready : Expr 1 := arreadyPort.rd
def rvalid : Expr 1 := rvalidPort.rd
def rdataIn : Expr 64 := rdataInPort.rd
def rresp : Expr 2 := rrespPort.rd

/-! ## Registers -/

def stReg : Reg 3 := ⟨"st"⟩
def tmoReg : Reg 16 := ⟨"tmo"⟩
def awaddrReg : Reg 32 := ⟨"m_awaddr"⟩
def awvalidReg : Reg 1 := ⟨"m_awvalid"⟩
def wdataReg : Reg 64 := ⟨"m_wdata"⟩
def wvalidReg : Reg 1 := ⟨"m_wvalid"⟩
def breadyReg : Reg 1 := ⟨"m_bready"⟩
def araddrReg : Reg 32 := ⟨"m_araddr"⟩
def arvalidReg : Reg 1 := ⟨"m_arvalid"⟩
def rreadyReg : Reg 1 := ⟨"m_rready"⟩
def rdataReg : Reg 64 := ⟨"rdata"⟩
def busyReg : Reg 1 := ⟨"busy"⟩
def doneReg : Reg 1 := ⟨"done"⟩
def errReg : Reg 1 := ⟨"err"⟩
def awlenReg : Reg 4 := ⟨"m_awlen"⟩
def awsizeReg : Reg 3 := ⟨"m_awsize"⟩
def awburstReg : Reg 2 := ⟨"m_awburst"⟩
def awidReg : Reg 6 := ⟨"m_awid"⟩
def wstrbReg : Reg 8 := ⟨"m_wstrb"⟩
def wlastReg : Reg 1 := ⟨"m_wlast"⟩
def widReg : Reg 6 := ⟨"m_wid"⟩
def arlenReg : Reg 4 := ⟨"m_arlen"⟩
def arsizeReg : Reg 3 := ⟨"m_arsize"⟩
def arburstReg : Reg 2 := ⟨"m_arburst"⟩
def aridReg : Reg 6 := ⟨"m_arid"⟩
def dbgStateReg : Reg 3 := ⟨"dbg_state"⟩

def st : Expr 3 := stReg.rd
def tmo : Expr 16 := tmoReg.rd

def L1 (n : Nat) : Expr 1  := .lit (BitVec.ofNat 1 n)
def L3 (n : Nat) : Expr 3  := .lit (BitVec.ofNat 3 n)
def L16 (n : Nat) : Expr 16 := .lit (BitVec.ofNat 16 n)

/-! ## The FSM rule

Note the Verilog uses `rstn`; here reset values live in the RegDecls and the
wrapper's POR holds the module in reset before `local_rstn`. We do not model
the async reset inside the rule (the design's `reset` state IS the rstn=0
state); this matches how the mini core is ported.

Verilog `default_state`s: at rstn or timeout the whole master resets to IDLE
with `m_bready<=1`, `m_rready<=1` (ready held HIGH to drain orphan beats).
The reset RegDecl inits already carry that. The timeout branch reproduces the
"abort → err, done, back to IDLE" path. -/

def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

/-- Timeout abort branch (st≠IDLE ∧ tmo≥TIMEOUT). -/
def timeoutBody : Act :=
  actSeq [ stReg.set (L3 IDLE), awvalidReg.set (L1 0),
           wvalidReg.set (L1 0), breadyReg.set (L1 1),
           arvalidReg.set (L1 0), rreadyReg.set (L1 1),
           busyReg.set (L1 0), doneReg.set (L1 1),
           errReg.set (L1 1), tmoReg.set (L16 0) ]

/-- The FSM body when running normally (not reset, not timeout). -/
def runBody : Act :=
  actSeq [
    -- done <= 1'b0; tmo <= (st==IDLE)?0:tmo+1;
    doneReg.set (L1 0),
    tmoReg.set (.mux (.eq st (L3 IDLE)) (L16 0) (.add tmo (L16 1))),
    -- case(st)
    .ite (.eq st (L3 IDLE))
      (.ite startWr
        (actSeq [awaddrReg.set addr, wdataReg.set wdata,
                 awvalidReg.set (L1 1), busyReg.set (L1 1),
                 errReg.set (L1 0), stReg.set (L3 WA)])
        (.ite startRd
          (actSeq [araddrReg.set addr, arvalidReg.set (L1 1),
                   busyReg.set (L1 1), errReg.set (L1 0), stReg.set (L3 RA)])
          .skip)) <|
    .ite (.eq st (L3 WA))
      (.ite awready (actSeq [awvalidReg.set (L1 0), wvalidReg.set (L1 1), stReg.set (L3 WD)]) .skip) <|
    .ite (.eq st (L3 WD))
      (.ite wready (actSeq [wvalidReg.set (L1 0), stReg.set (L3 WB)]) .skip) <|
    .ite (.eq st (L3 WB))
      (.ite bvalid (actSeq [errReg.set (.not (.eq bresp (.lit (BitVec.ofNat 2 0)))),
                            busyReg.set (L1 0), doneReg.set (L1 1), stReg.set (L3 IDLE)]) .skip) <|
    .ite (.eq st (L3 RA))
      (.ite arready (actSeq [arvalidReg.set (L1 0), stReg.set (L3 RR)]) .skip) <|
    .ite (.eq st (L3 RR))
      (.ite rvalid (actSeq [rdataReg.set rdataIn,
                            errReg.set (.not (.eq rresp (.lit (BitVec.ofNat 2 0)))),
                            busyReg.set (L1 0), doneReg.set (L1 1), stReg.set (L3 IDLE)]) .skip)
      .skip ]

def fsmRule : Rule :=
  ⟨"hp_fsm",
    .ite (.and (.not (.eq st (L3 IDLE))) (.not (.ult tmo (L16 TIMEOUT))))
      timeoutBody
      runBody⟩

/-! ## Register / input declarations -/

/-- dbg_state mirror rule: dbg_state <= st (the Verilog `assign dbg_state=st`
becomes a registered mirror here; one-cycle-late observability only). -/
def dbgRule : Rule := ⟨"hp_dbg", dbgStateReg.set st⟩

def declarations : Declarations :=
  Declarations.empty
    |>.addReg stReg (exported := true)
    |>.addReg tmoReg (exported := true)
    |>.addReg awaddrReg (exported := true)
    |>.addReg awvalidReg (exported := true)
    |>.addReg wdataReg (exported := true)
    |>.addReg wvalidReg (exported := true)
    |>.addReg breadyReg 1 (exported := true)
    |>.addReg araddrReg (exported := true)
    |>.addReg arvalidReg (exported := true)
    |>.addReg rreadyReg 1 (exported := true)
    |>.addReg rdataReg (exported := true)
    |>.addReg busyReg (exported := true)
    |>.addReg doneReg (exported := true)
    |>.addReg errReg (exported := true)
    |>.addReg awlenReg (exported := true)
    |>.addReg awsizeReg 3 (exported := true)
    |>.addReg awburstReg 1 (exported := true)
    |>.addReg awidReg (exported := true)
    |>.addReg wstrbReg 0xFF (exported := true)
    |>.addReg wlastReg 1 (exported := true)
    |>.addReg widReg (exported := true)
    |>.addReg arlenReg (exported := true)
    |>.addReg arsizeReg 3 (exported := true)
    |>.addReg arburstReg 1 (exported := true)
    |>.addReg aridReg (exported := true)
    |>.addReg dbgStateReg (exported := true)
    |>.addInput startWrPort
    |>.addInput startRdPort
    |>.addInput addrPort
    |>.addInput wdataPort
    |>.addInput awreadyPort
    |>.addInput wreadyPort
    |>.addInput bvalidPort
    |>.addInput brespPort
    |>.addInput arreadyPort
    |>.addInput rvalidPort
    |>.addInput rdataInPort
    |>.addInput rrespPort

def design : Design := Design.ofDecls "axi_hp_master" declarations [fsmRule, dbgRule]

/-! ## Inputs and Design-derived outcome tests -/

structure HpIn where
  start_wr : Bool := false
  start_rd : Bool := false
  addr     : BitVec 32 := 0
  wdata    : BitVec 64 := 0
  awready  : Bool := false
  wready   : Bool := false
  bvalid   : Bool := false
  bresp    : BitVec 2 := 0
  arready  : Bool := false
  rvalid   : Bool := false
  rdata_in : BitVec 64 := 0
  rresp    : BitVec 2 := 0
  deriving Repr

/-! ## InEnv from HpIn -/

def HpIn.toEnv (c : HpIn) : InEnv := InputBinding.toEnv
  [InputBinding.of startWrPort (BitVec.ofBool c.start_wr),
   InputBinding.of startRdPort (BitVec.ofBool c.start_rd),
   InputBinding.of addrPort c.addr, InputBinding.of wdataPort c.wdata,
   InputBinding.of awreadyPort (BitVec.ofBool c.awready),
   InputBinding.of wreadyPort (BitVec.ofBool c.wready),
   InputBinding.of bvalidPort (BitVec.ofBool c.bvalid),
   InputBinding.of brespPort c.bresp,
   InputBinding.of arreadyPort (BitVec.ofBool c.arready),
   InputBinding.of rvalidPort (BitVec.ofBool c.rvalid),
   InputBinding.of rdataInPort c.rdata_in,
   InputBinding.of rrespPort c.rresp]

/-! ## Design-derived outcome tests -/

private def runStates (script : List HpIn) : List St := Id.run do
  let mut state := design.reset
  let mut states := []
  for input in script do
    state := design.cycleOpen input.toEnv state
    states := states ++ [state]
  return states

private def regAt {w : Nat} (state : St) (reg : Reg w) : Nat :=
  (state.regs reg.name w).toNat

private def pulseCount (states : List St) (reg : Reg 1) : Nat :=
  (states.filter fun state => regAt state reg = 1).length

/-- Single read: start_rd, then arready, then rvalid+rdata. -/
def scriptRead : List HpIn :=
  [ { start_rd := true, addr := 0x1000 },          -- IDLE -> RA
    { arready := true },                            -- RA -> RR (arvalid drops)
    { rvalid := true, rdata_in := 0xDEADBEEF },     -- RR -> IDLE (rdata latched, done)
    {} ]

/-- Single write: start_wr, awready, wready, bvalid. -/
def scriptWrite : List HpIn :=
  [ { start_wr := true, addr := 0x2000, wdata := 0x1122334455667788 }, -- IDLE -> WA
    { awready := true },                                                -- WA -> WD
    { wready := true },                                                 -- WD -> WB
    { bvalid := true },                                                 -- WB -> IDLE (done)
    {} ]

/-- Back-to-back: write completes, then immediately a read starts the next
cycle (start_rd asserted the cycle done pulses). -/
def scriptBack : List HpIn :=
  [ { start_wr := true, addr := 0x30, wdata := 0xAA },
    { awready := true },
    { wready := true },
    { bvalid := true, start_rd := true, addr := 0x40 },  -- WB->IDLE this cyc; start_rd taken next
    { start_rd := true, addr := 0x40 },                  -- IDLE -> RA
    { arready := true },
    { rvalid := true, rdata_in := 0x55 },
    {} ]

def selftest : IO Unit := do
  let readStates := runStates scriptRead
  let writeStates := runStates scriptWrite
  let backStates := runStates scriptBack
  let finalOk (states : List St) := match states.getLast? with
    | some state => regAt state stReg = IDLE && regAt state busyReg = 0 &&
        regAt state doneReg = 0 && regAt state errReg = 0 &&
        regAt state breadyReg = 1 && regAt state rreadyReg = 1
    | none => false
  let readOk := finalOk readStates && pulseCount readStates doneReg = 1 &&
    (readStates.getLast?.map (regAt · rdataReg)) = some 0xDEADBEEF
  let writeOk := finalOk writeStates && pulseCount writeStates doneReg = 1 &&
    (writeStates.getLast?.map (regAt · awaddrReg)) = some 0x2000 &&
    (writeStates.getLast?.map (regAt · wdataReg)) = some 0x1122334455667788
  let backOk := finalOk backStates && pulseCount backStates doneReg = 2 &&
    (backStates.getLast?.map (regAt · rdataReg)) = some 0x55
  let ok := readOk && writeOk && backOk
  if ok then
    IO.println "HP MASTER SELFTEST OK — Design outcomes pass for read/write/back-to-back"
  else
    IO.println "HP MASTER SELFTEST FAILED — Design outcome mismatch"
  (Loom.Runner.Result.fromBool "HP master selftest" 17 ok
    "Design outcome mismatch").requirePass

end Machines.Lnp64mini.HpMaster
