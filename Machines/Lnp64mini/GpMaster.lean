-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Compose
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO
import Loom.Runner
import Loom.Hw.Declarations

/-!
# axi_gp_master — Loom port of the 32-bit single-beat AXI3 GP master

Faithful, bug-for-bug port of
`remote-fpga/fpga/substrate0/rtl/axi_gp_master.v`. Same serialized
AW→W→B / AR→R FSM as the HP master but 32-bit, **no timeout**, and the
`m_bready`/`m_rready` handshakes reset to 0 and pulse during the
transaction (WD raises bready, WB clears; RA raises rready, RR clears).
Inputs = AXI responses + control; outputs = master signals as registers.
-/

namespace Machines.Lnp64mini.GpMaster

open Loom.Hw

def IDLE : Nat := 0
def WA   : Nat := 1
def WD   : Nat := 2
def WB   : Nat := 3
def RA   : Nat := 4
def RR   : Nat := 5

/-! ## Input ports -/

def startWrPort : Reg 1 := ⟨"start_wr"⟩
def startRdPort : Reg 1 := ⟨"start_rd"⟩
def addrPort : Reg 32 := ⟨"addr"⟩
def wdataPort : Reg 32 := ⟨"wdata"⟩
def awreadyPort : Reg 1 := ⟨"m_awready"⟩
def wreadyPort : Reg 1 := ⟨"m_wready"⟩
def bvalidPort : Reg 1 := ⟨"m_bvalid"⟩
def brespPort : Reg 2 := ⟨"m_bresp"⟩
def arreadyPort : Reg 1 := ⟨"m_arready"⟩
def rvalidPort : Reg 1 := ⟨"m_rvalid"⟩
def rdataInPort : Reg 32 := ⟨"m_rdata_in"⟩
def rrespPort : Reg 2 := ⟨"m_rresp"⟩

def startWr : Expr 1 := startWrPort.rd
def startRd : Expr 1 := startRdPort.rd
def addr : Expr 32 := addrPort.rd
def wdata : Expr 32 := wdataPort.rd
def awready : Expr 1 := awreadyPort.rd
def wready : Expr 1 := wreadyPort.rd
def bvalid : Expr 1 := bvalidPort.rd
def bresp : Expr 2 := brespPort.rd
def arready : Expr 1 := arreadyPort.rd
def rvalid : Expr 1 := rvalidPort.rd
def rdataIn : Expr 32 := rdataInPort.rd
def rresp : Expr 2 := rrespPort.rd

/-! ## Registers -/

def stReg : Reg 3 := ⟨"st"⟩
def awaddrReg : Reg 32 := ⟨"m_awaddr"⟩
def awvalidReg : Reg 1 := ⟨"m_awvalid"⟩
def wdataReg : Reg 32 := ⟨"m_wdata"⟩
def wvalidReg : Reg 1 := ⟨"m_wvalid"⟩
def breadyReg : Reg 1 := ⟨"m_bready"⟩
def araddrReg : Reg 32 := ⟨"m_araddr"⟩
def arvalidReg : Reg 1 := ⟨"m_arvalid"⟩
def rreadyReg : Reg 1 := ⟨"m_rready"⟩
def rdataReg : Reg 32 := ⟨"rdata"⟩
def busyReg : Reg 1 := ⟨"busy"⟩
def doneReg : Reg 1 := ⟨"done"⟩
def errReg : Reg 1 := ⟨"err"⟩
def awlenReg : Reg 4 := ⟨"m_awlen"⟩
def awsizeReg : Reg 3 := ⟨"m_awsize"⟩
def awburstReg : Reg 2 := ⟨"m_awburst"⟩
def awidReg : Reg 6 := ⟨"m_awid"⟩
def wstrbReg : Reg 4 := ⟨"m_wstrb"⟩
def wlastReg : Reg 1 := ⟨"m_wlast"⟩
def widReg : Reg 6 := ⟨"m_wid"⟩
def arlenReg : Reg 4 := ⟨"m_arlen"⟩
def arsizeReg : Reg 3 := ⟨"m_arsize"⟩
def arburstReg : Reg 2 := ⟨"m_arburst"⟩
def aridReg : Reg 6 := ⟨"m_arid"⟩
def dbgStateReg : Reg 3 := ⟨"dbg_state"⟩

def st : Expr 3 := stReg.rd

def L1 (n : Nat) : Expr 1 := .lit (BitVec.ofNat 1 n)
def L3 (n : Nat) : Expr 3 := .lit (BitVec.ofNat 3 n)

def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

def runBody : Act :=
  actSeq [
    doneReg.set (L1 0),
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
      (.ite wready (actSeq [wvalidReg.set (L1 0), breadyReg.set (L1 1), stReg.set (L3 WB)]) .skip) <|
    .ite (.eq st (L3 WB))
      (.ite bvalid (actSeq [breadyReg.set (L1 0), errReg.set (.not (.eq bresp (.lit (BitVec.ofNat 2 0)))),
                            busyReg.set (L1 0), doneReg.set (L1 1), stReg.set (L3 IDLE)]) .skip) <|
    .ite (.eq st (L3 RA))
      (.ite arready (actSeq [arvalidReg.set (L1 0), rreadyReg.set (L1 1), stReg.set (L3 RR)]) .skip) <|
    .ite (.eq st (L3 RR))
      (.ite rvalid (actSeq [rdataReg.set rdataIn, rreadyReg.set (L1 0),
                            errReg.set (.not (.eq rresp (.lit (BitVec.ofNat 2 0)))),
                            busyReg.set (L1 0), doneReg.set (L1 1), stReg.set (L3 IDLE)]) .skip)
      .skip ]

def fsmRule : Rule := ⟨"gp_fsm", runBody⟩
def dbgRule : Rule := ⟨"gp_dbg", dbgStateReg.set st⟩

def declarations : Declarations :=
  Declarations.empty
    |>.addReg stReg (exported := true)
    |>.addReg awaddrReg (exported := true)
    |>.addReg awvalidReg (exported := true)
    |>.addReg wdataReg (exported := true)
    |>.addReg wvalidReg (exported := true)
    |>.addReg breadyReg (exported := true)
    |>.addReg araddrReg (exported := true)
    |>.addReg arvalidReg (exported := true)
    |>.addReg rreadyReg (exported := true)
    |>.addReg rdataReg (exported := true)
    |>.addReg busyReg (exported := true)
    |>.addReg doneReg (exported := true)
    |>.addReg errReg (exported := true)
    |>.addReg awlenReg (exported := true)
    |>.addReg awsizeReg 2 (exported := true)
    |>.addReg awburstReg 1 (exported := true)
    |>.addReg awidReg (exported := true)
    |>.addReg wstrbReg 0xF (exported := true)
    |>.addReg wlastReg 1 (exported := true)
    |>.addReg widReg (exported := true)
    |>.addReg arlenReg (exported := true)
    |>.addReg arsizeReg 2 (exported := true)
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

def design : Design := Design.ofDecls "axi_gp_master" declarations [fsmRule, dbgRule]

/-! ## Inputs and Design-derived outcome tests -/

structure GpIn where
  start_wr : Bool := false
  start_rd : Bool := false
  addr     : BitVec 32 := 0
  wdata    : BitVec 32 := 0
  awready  : Bool := false
  wready   : Bool := false
  bvalid   : Bool := false
  bresp    : BitVec 2 := 0
  arready  : Bool := false
  rvalid   : Bool := false
  rdata_in : BitVec 32 := 0
  rresp    : BitVec 2 := 0
  deriving Repr

def GpIn.toEnv (c : GpIn) : InEnv := InputBinding.toEnv
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

private def runStates (script : List GpIn) : List St := Id.run do
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

def scriptRead : List GpIn :=
  [ { start_rd := true, addr := 0xE0000000 },
    { arready := true },
    { rvalid := true, rdata_in := 0xABCD },
    {} ]

def scriptWrite : List GpIn :=
  [ { start_wr := true, addr := 0xE0000004, wdata := 0x99 },
    { awready := true },
    { wready := true },
    { bvalid := true },
    {} ]

def scriptBack : List GpIn :=
  [ { start_wr := true, addr := 0xE0000000, wdata := 0x11 },
    { awready := true },
    { wready := true },
    { bvalid := true },
    { start_rd := true, addr := 0xE0000008 },
    { arready := true },
    { rvalid := true, rdata_in := 0x22 },
    {} ]

def selftest : IO Unit := do
  let readStates := runStates scriptRead
  let writeStates := runStates scriptWrite
  let backStates := runStates scriptBack
  let finalOk (states : List St) := match states.getLast? with
    | some state => regAt state stReg = IDLE && regAt state busyReg = 0 &&
        regAt state doneReg = 0 && regAt state errReg = 0
    | none => false
  let readOk := finalOk readStates && pulseCount readStates doneReg = 1 &&
    (readStates.getLast?.map (regAt · rdataReg)) = some 0xABCD
  let writeOk := finalOk writeStates && pulseCount writeStates doneReg = 1 &&
    (writeStates.getLast?.map (regAt · awaddrReg)) = some 0xE0000004 &&
    (writeStates.getLast?.map (regAt · wdataReg)) = some 0x99
  let backOk := finalOk backStates && pulseCount backStates doneReg = 2 &&
    (backStates.getLast?.map (regAt · rdataReg)) = some 0x22
  let ok := readOk && writeOk && backOk
  if ok then
    IO.println "GP MASTER SELFTEST OK — Design outcomes pass for read/write/back-to-back"
  else
    IO.println "GP MASTER SELFTEST FAILED — Design outcome mismatch"
  (Loom.Runner.Result.fromBool "GP master selftest" 17 ok
    "Design outcome mismatch").requirePass

end Machines.Lnp64mini.GpMaster
