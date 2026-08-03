-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Compose
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

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

def startWr : Expr 1  := .reg 1  "start_wr"
def startRd : Expr 1  := .reg 1  "start_rd"
def addr    : Expr 32 := .reg 32 "addr"
def wdata   : Expr 32 := .reg 32 "wdata"
def awready : Expr 1  := .reg 1  "m_awready"
def wready  : Expr 1  := .reg 1  "m_wready"
def bvalid  : Expr 1  := .reg 1  "m_bvalid"
def bresp   : Expr 2  := .reg 2  "m_bresp"
def arready : Expr 1  := .reg 1  "m_arready"
def rvalid  : Expr 1  := .reg 1  "m_rvalid"
def rdataIn : Expr 32 := .reg 32 "m_rdata_in"
def rresp   : Expr 2  := .reg 2  "m_rresp"

def st : Expr 3 := .reg 3 "st"

def L1 (n : Nat) : Expr 1 := .lit (BitVec.ofNat 1 n)
def L3 (n : Nat) : Expr 3 := .lit (BitVec.ofNat 3 n)

def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

def runBody : Act :=
  actSeq [
    .write 1 "done" (L1 0),
    .ite (.eq st (L3 IDLE))
      (.ite startWr
        (actSeq [.write 32 "m_awaddr" addr, .write 32 "m_wdata" wdata,
                 .write 1 "m_awvalid" (L1 1), .write 1 "busy" (L1 1),
                 .write 1 "err" (L1 0), .write 3 "st" (L3 WA)])
        (.ite startRd
          (actSeq [.write 32 "m_araddr" addr, .write 1 "m_arvalid" (L1 1),
                   .write 1 "busy" (L1 1), .write 1 "err" (L1 0), .write 3 "st" (L3 RA)])
          .skip)) <|
    .ite (.eq st (L3 WA))
      (.ite awready (actSeq [.write 1 "m_awvalid" (L1 0), .write 1 "m_wvalid" (L1 1), .write 3 "st" (L3 WD)]) .skip) <|
    .ite (.eq st (L3 WD))
      (.ite wready (actSeq [.write 1 "m_wvalid" (L1 0), .write 1 "m_bready" (L1 1), .write 3 "st" (L3 WB)]) .skip) <|
    .ite (.eq st (L3 WB))
      (.ite bvalid (actSeq [.write 1 "m_bready" (L1 0), .write 1 "err" (.not (.eq bresp (.lit (BitVec.ofNat 2 0)))),
                            .write 1 "busy" (L1 0), .write 1 "done" (L1 1), .write 3 "st" (L3 IDLE)]) .skip) <|
    .ite (.eq st (L3 RA))
      (.ite arready (actSeq [.write 1 "m_arvalid" (L1 0), .write 1 "m_rready" (L1 1), .write 3 "st" (L3 RR)]) .skip) <|
    .ite (.eq st (L3 RR))
      (.ite rvalid (actSeq [.write 32 "rdata" rdataIn, .write 1 "m_rready" (L1 0),
                            .write 1 "err" (.not (.eq rresp (.lit (BitVec.ofNat 2 0)))),
                            .write 1 "busy" (L1 0), .write 1 "done" (L1 1), .write 3 "st" (L3 IDLE)]) .skip)
      .skip ]

def fsmRule : Rule := ⟨"gp_fsm", runBody⟩
def dbgRule : Rule := ⟨"gp_dbg", .write 3 "dbg_state" st⟩

def regs : List RegDecl :=
  [ ⟨"st",3,0⟩,
    ⟨"m_awaddr",32,0⟩, ⟨"m_awvalid",1,0⟩,
    ⟨"m_wdata",32,0⟩, ⟨"m_wvalid",1,0⟩,
    ⟨"m_bready",1,0⟩,
    ⟨"m_araddr",32,0⟩, ⟨"m_arvalid",1,0⟩,
    ⟨"m_rready",1,0⟩,
    ⟨"rdata",32,0⟩, ⟨"busy",1,0⟩, ⟨"done",1,0⟩, ⟨"err",1,0⟩,
    -- constant AXI qualifiers (never written; AWSIZE=4B=3'b010)
    ⟨"m_awlen",4,0⟩, ⟨"m_awsize",3,2⟩, ⟨"m_awburst",2,1⟩, ⟨"m_awid",6,0⟩,
    ⟨"m_wstrb",4,0xF⟩, ⟨"m_wlast",1,1⟩, ⟨"m_wid",6,0⟩,
    ⟨"m_arlen",4,0⟩, ⟨"m_arsize",3,2⟩, ⟨"m_arburst",2,1⟩, ⟨"m_arid",6,0⟩,
    ⟨"dbg_state",3,0⟩ ]

def inputs : List InputDecl :=
  [ ⟨"start_wr",1⟩, ⟨"start_rd",1⟩, ⟨"addr",32⟩, ⟨"wdata",32⟩,
    ⟨"m_awready",1⟩, ⟨"m_wready",1⟩, ⟨"m_bvalid",1⟩, ⟨"m_bresp",2⟩,
    ⟨"m_arready",1⟩, ⟨"m_rvalid",1⟩, ⟨"m_rdata_in",32⟩, ⟨"m_rresp",2⟩ ]

def design : Design where
  name := "axi_gp_master"
  regs := regs
  -- D39a: outputs are mandatory and explicit, like inputs. This design's
  -- whole register set IS its interface, so it says so rather than
  -- relying on a default that exported everything silently.
  outputs := (regs).map (·.name)
  mems := []
  rules := [fsmRule, dbgRule]
  inputs := inputs

/-! ## ISS mirror -/

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

structure GpSt where
  st       : BitVec 3 := 0
  m_awaddr : BitVec 32 := 0
  m_awvalid: Bool := false
  m_wdata  : BitVec 32 := 0
  m_wvalid : Bool := false
  m_bready : Bool := false
  m_araddr : BitVec 32 := 0
  m_arvalid: Bool := false
  m_rready : Bool := false
  rdata    : BitVec 32 := 0
  busy     : Bool := false
  done     : Bool := false
  err      : Bool := false
  dbg_state: BitVec 3 := 0
  deriving Repr

def GpIss.step (s : GpSt) (inp : GpIn) : GpSt := Id.run do
  let mut s' := s
  let stN := s.st.toNat
  s' := { s' with done := false }
  if stN = IDLE then
    if inp.start_wr then
      s' := { s' with m_awaddr := inp.addr, m_wdata := inp.wdata, m_awvalid := true,
                      busy := true, err := false, st := BitVec.ofNat 3 WA }
    else if inp.start_rd then
      s' := { s' with m_araddr := inp.addr, m_arvalid := true, busy := true,
                      err := false, st := BitVec.ofNat 3 RA }
  else if stN = WA then
    if inp.awready then s' := { s' with m_awvalid := false, m_wvalid := true, st := BitVec.ofNat 3 WD }
  else if stN = WD then
    if inp.wready then s' := { s' with m_wvalid := false, m_bready := true, st := BitVec.ofNat 3 WB }
  else if stN = WB then
    if inp.bvalid then s' := { s' with m_bready := false, err := inp.bresp ≠ 0, busy := false, done := true, st := BitVec.ofNat 3 IDLE }
  else if stN = RA then
    if inp.arready then s' := { s' with m_arvalid := false, m_rready := true, st := BitVec.ofNat 3 RR }
  else if stN = RR then
    if inp.rvalid then s' := { s' with rdata := inp.rdata_in, m_rready := false, err := inp.rresp ≠ 0, busy := false, done := true, st := BitVec.ofNat 3 IDLE }
  else
    s' := { s' with st := BitVec.ofNat 3 IDLE }
  s' := { s' with dbg_state := s.st }
  return s'

def GpIn.toEnv (c : GpIn) : InEnv := fun n w =>
  match n with
  | "start_wr"  => (BitVec.ofBool c.start_wr).setWidth w
  | "start_rd"  => (BitVec.ofBool c.start_rd).setWidth w
  | "addr"      => c.addr.setWidth w
  | "wdata"     => c.wdata.setWidth w
  | "m_awready" => (BitVec.ofBool c.awready).setWidth w
  | "m_wready"  => (BitVec.ofBool c.wready).setWidth w
  | "m_bvalid"  => (BitVec.ofBool c.bvalid).setWidth w
  | "m_bresp"   => c.bresp.setWidth w
  | "m_arready" => (BitVec.ofBool c.arready).setWidth w
  | "m_rvalid"  => (BitVec.ofBool c.rvalid).setWidth w
  | "m_rdata_in"=> c.rdata_in.setWidth w
  | "m_rresp"   => c.rresp.setWidth w
  | _ => 0#w

def issRegs (s : GpSt) : List (String × Nat × Nat) :=
  [("st",3,s.st.toNat),
   ("m_awaddr",32,s.m_awaddr.toNat), ("m_awvalid",1,if s.m_awvalid then 1 else 0),
   ("m_wdata",32,s.m_wdata.toNat), ("m_wvalid",1,if s.m_wvalid then 1 else 0),
   ("m_bready",1,if s.m_bready then 1 else 0),
   ("m_araddr",32,s.m_araddr.toNat), ("m_arvalid",1,if s.m_arvalid then 1 else 0),
   ("m_rready",1,if s.m_rready then 1 else 0),
   ("rdata",32,s.rdata.toNat), ("busy",1,if s.busy then 1 else 0),
   ("done",1,if s.done then 1 else 0), ("err",1,if s.err then 1 else 0),
   ("dbg_state",3,s.dbg_state.toNat)]

def lockstep (script : List GpIn) : IO Nat := do
  let mut s : GpSt := {}
  let mut σ : St := design.reset
  let mut bad := 0
  let mut k := 0
  for inp in script do
    σ := design.cycleOpen inp.toEnv σ
    s := GpIss.step s inp
    for (n, w, v) in issRegs s do
      if (σ.regs n w).toNat ≠ v then
        if bad < 8 then IO.println s!"  MISMATCH step {k} {n}: edsl={(σ.regs n w).toNat} iss={v}"
        bad := bad + 1
    k := k + 1
  return bad

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
  let scripts : List (String × List GpIn) :=
    [("single read ", scriptRead), ("single write", scriptWrite), ("back-to-back", scriptBack)]
  let mut total := 0
  for (nm, sc) in scripts do
    let bad ← lockstep sc
    if bad = 0 then IO.println s!"  OK  gp {nm} ({sc.length} cyc)"
    else IO.println s!"  FAIL gp {nm} ({bad} mismatches)"
    total := total + bad
  if total = 0 then IO.println "GP MASTER SELFTEST OK — EDSL≡ISS on read/write/back-to-back"
  else IO.println s!"GP MASTER SELFTEST FAILED ({total} mismatches)"

end Machines.Lnp64mini.GpMaster
