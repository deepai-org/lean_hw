-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Compose
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

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

An ISS mirror (`HpIss.step`) and a `selftest` lockstep the design's
`cycleOpen` against the ISS on the three handshake scripts (single read,
single write, back-to-back).
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

def startWr : Expr 1  := .reg 1  "start_wr"
def startRd : Expr 1  := .reg 1  "start_rd"
def addr    : Expr 32 := .reg 32 "addr"
def wdata   : Expr 64 := .reg 64 "wdata"
def awready : Expr 1  := .reg 1  "m_awready"
def wready  : Expr 1  := .reg 1  "m_wready"
def bvalid  : Expr 1  := .reg 1  "m_bvalid"
def bresp   : Expr 2  := .reg 2  "m_bresp"
def arready : Expr 1  := .reg 1  "m_arready"
def rvalid  : Expr 1  := .reg 1  "m_rvalid"
def rdataIn : Expr 64 := .reg 64 "m_rdata_in"
def rresp   : Expr 2  := .reg 2  "m_rresp"

/-! ## Registers -/

def st      : Expr 3  := .reg 3  "st"
def tmo     : Expr 16 := .reg 16 "tmo"
def m_awaddr  : Expr 32 := .reg 32 "m_awaddr"
def m_awvalid : Expr 1  := .reg 1  "m_awvalid"
def m_wdata   : Expr 64 := .reg 64 "m_wdata"
def m_wvalid  : Expr 1  := .reg 1  "m_wvalid"
def m_bready  : Expr 1  := .reg 1  "m_bready"
def m_araddr  : Expr 32 := .reg 32 "m_araddr"
def m_arvalid : Expr 1  := .reg 1  "m_arvalid"
def m_rready  : Expr 1  := .reg 1  "m_rready"

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
  actSeq [ .write 3 "st" (L3 IDLE), .write 1 "m_awvalid" (L1 0),
           .write 1 "m_wvalid" (L1 0), .write 1 "m_bready" (L1 1),
           .write 1 "m_arvalid" (L1 0), .write 1 "m_rready" (L1 1),
           .write 1 "busy" (L1 0), .write 1 "done" (L1 1),
           .write 1 "err" (L1 1), .write 16 "tmo" (L16 0) ]

/-- The FSM body when running normally (not reset, not timeout). -/
def runBody : Act :=
  actSeq [
    -- done <= 1'b0; tmo <= (st==IDLE)?0:tmo+1;
    .write 1 "done" (L1 0),
    .write 16 "tmo" (.mux (.eq st (L3 IDLE)) (L16 0) (.add tmo (L16 1))),
    -- case(st)
    .ite (.eq st (L3 IDLE))
      (.ite startWr
        (actSeq [.write 32 "m_awaddr" addr, .write 64 "m_wdata" wdata,
                 .write 1 "m_awvalid" (L1 1), .write 1 "busy" (L1 1),
                 .write 1 "err" (L1 0), .write 3 "st" (L3 WA)])
        (.ite startRd
          (actSeq [.write 32 "m_araddr" addr, .write 1 "m_arvalid" (L1 1),
                   .write 1 "busy" (L1 1), .write 1 "err" (L1 0), .write 3 "st" (L3 RA)])
          .skip)) <|
    .ite (.eq st (L3 WA))
      (.ite awready (actSeq [.write 1 "m_awvalid" (L1 0), .write 1 "m_wvalid" (L1 1), .write 3 "st" (L3 WD)]) .skip) <|
    .ite (.eq st (L3 WD))
      (.ite wready (actSeq [.write 1 "m_wvalid" (L1 0), .write 3 "st" (L3 WB)]) .skip) <|
    .ite (.eq st (L3 WB))
      (.ite bvalid (actSeq [.write 1 "err" (.not (.eq bresp (.lit (BitVec.ofNat 2 0)))),
                            .write 1 "busy" (L1 0), .write 1 "done" (L1 1), .write 3 "st" (L3 IDLE)]) .skip) <|
    .ite (.eq st (L3 RA))
      (.ite arready (actSeq [.write 1 "m_arvalid" (L1 0), .write 3 "st" (L3 RR)]) .skip) <|
    .ite (.eq st (L3 RR))
      (.ite rvalid (actSeq [.write 64 "rdata" rdataIn,
                            .write 1 "err" (.not (.eq rresp (.lit (BitVec.ofNat 2 0)))),
                            .write 1 "busy" (L1 0), .write 1 "done" (L1 1), .write 3 "st" (L3 IDLE)]) .skip)
      .skip ]

def fsmRule : Rule :=
  ⟨"hp_fsm",
    .ite (.and (.not (.eq st (L3 IDLE))) (.not (.ult tmo (L16 TIMEOUT))))
      timeoutBody
      runBody⟩

/-! ## Register / input declarations -/

def regs : List RegDecl :=
  [ ⟨"st",3,0⟩, ⟨"tmo",16,0⟩,
    ⟨"m_awaddr",32,0⟩, ⟨"m_awvalid",1,0⟩,
    ⟨"m_wdata",64,0⟩, ⟨"m_wvalid",1,0⟩,
    ⟨"m_bready",1,1⟩,     -- ready held HIGH at reset
    ⟨"m_araddr",32,0⟩, ⟨"m_arvalid",1,0⟩,
    ⟨"m_rready",1,1⟩,     -- ready held HIGH at reset
    ⟨"rdata",64,0⟩, ⟨"busy",1,0⟩, ⟨"done",1,0⟩, ⟨"err",1,0⟩,
    -- constant AXI qualifiers (never written; fixed reset value)
    ⟨"m_awlen",4,0⟩, ⟨"m_awsize",3,3⟩, ⟨"m_awburst",2,1⟩, ⟨"m_awid",6,0⟩,
    ⟨"m_wstrb",8,0xFF⟩, ⟨"m_wlast",1,1⟩, ⟨"m_wid",6,0⟩,
    ⟨"m_arlen",4,0⟩, ⟨"m_arsize",3,3⟩, ⟨"m_arburst",2,1⟩, ⟨"m_arid",6,0⟩,
    ⟨"dbg_state",3,0⟩ ]

def inputs : List InputDecl :=
  [ ⟨"start_wr",1⟩, ⟨"start_rd",1⟩, ⟨"addr",32⟩, ⟨"wdata",64⟩,
    ⟨"m_awready",1⟩, ⟨"m_wready",1⟩, ⟨"m_bvalid",1⟩, ⟨"m_bresp",2⟩,
    ⟨"m_arready",1⟩, ⟨"m_rvalid",1⟩, ⟨"m_rdata_in",64⟩, ⟨"m_rresp",2⟩ ]

/-- dbg_state mirror rule: dbg_state <= st (the Verilog `assign dbg_state=st`
becomes a registered mirror here; one-cycle-late observability only). -/
def dbgRule : Rule := ⟨"hp_dbg", .write 3 "dbg_state" st⟩

def design : Design where
  name := "axi_hp_master"
  regs := regs
  -- D39a: outputs are mandatory and explicit, like inputs. This design's
  -- whole register set IS its interface, so it says so rather than
  -- relying on a default that exported everything silently.
  outputs := (regs).map (·.name)
  mems := []
  rules := [fsmRule, dbgRule]
  inputs := inputs

/-! ## ISS mirror -/

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

structure HpSt where
  st       : BitVec 3 := 0
  tmo      : BitVec 16 := 0
  m_awaddr : BitVec 32 := 0
  m_awvalid: Bool := false
  m_wdata  : BitVec 64 := 0
  m_wvalid : Bool := false
  m_bready : Bool := true
  m_araddr : BitVec 32 := 0
  m_arvalid: Bool := false
  m_rready : Bool := true
  rdata    : BitVec 64 := 0
  busy     : Bool := false
  done     : Bool := false
  err      : Bool := false
  dbg_state: BitVec 3 := 0
  deriving Repr

/-- One cycle. Mirrors the Verilog always block (rstn handled by reset
state). Reads pre-state `s`, builds `s'` (D9). -/
def HpIss.step (s : HpSt) (inp : HpIn) : HpSt := Id.run do
  let mut s' := s
  let stN := s.st.toNat
  if stN ≠ IDLE ∧ ¬ (s.tmo.toNat < TIMEOUT) then
    s' := { s' with st := BitVec.ofNat 3 IDLE, m_awvalid := false, m_wvalid := false,
                    m_bready := true, m_arvalid := false, m_rready := true,
                    busy := false, done := true, err := true, tmo := 0 }
  else
    s' := { s' with done := false, tmo := if stN = IDLE then 0 else s.tmo + 1 }
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
      if inp.wready then s' := { s' with m_wvalid := false, st := BitVec.ofNat 3 WB }
    else if stN = WB then
      if inp.bvalid then s' := { s' with err := inp.bresp ≠ 0, busy := false, done := true, st := BitVec.ofNat 3 IDLE }
    else if stN = RA then
      if inp.arready then s' := { s' with m_arvalid := false, st := BitVec.ofNat 3 RR }
    else if stN = RR then
      if inp.rvalid then s' := { s' with rdata := inp.rdata_in, err := inp.rresp ≠ 0, busy := false, done := true, st := BitVec.ofNat 3 IDLE }
    else
      s' := { s' with st := BitVec.ofNat 3 IDLE }
  -- registered dbg mirror (uses pre-state st, like the design's dbgRule)
  s' := { s' with dbg_state := s.st }
  return s'

/-! ## InEnv from HpIn -/

def HpIn.toEnv (c : HpIn) : InEnv := fun n w =>
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

def issRegs (s : HpSt) : List (String × Nat × Nat) :=
  [("st",3,s.st.toNat), ("tmo",16,s.tmo.toNat),
   ("m_awaddr",32,s.m_awaddr.toNat), ("m_awvalid",1,if s.m_awvalid then 1 else 0),
   ("m_wdata",64,s.m_wdata.toNat), ("m_wvalid",1,if s.m_wvalid then 1 else 0),
   ("m_bready",1,if s.m_bready then 1 else 0),
   ("m_araddr",32,s.m_araddr.toNat), ("m_arvalid",1,if s.m_arvalid then 1 else 0),
   ("m_rready",1,if s.m_rready then 1 else 0),
   ("rdata",64,s.rdata.toNat), ("busy",1,if s.busy then 1 else 0),
   ("done",1,if s.done then 1 else 0), ("err",1,if s.err then 1 else 0),
   ("dbg_state",3,s.dbg_state.toNat)]

/-! ## Selftest: EDSL ≡ ISS on the three handshake scripts -/

/-- Lockstep the design's `cycleOpen` against the ISS under an input script. -/
def lockstep (script : List HpIn) : IO Nat := do
  let mut s : HpSt := {}
  let mut σ : St := design.reset
  let mut bad := 0
  let mut k := 0
  for inp in script do
    σ := design.cycleOpen inp.toEnv σ
    s := HpIss.step s inp
    for (n, w, v) in issRegs s do
      if (σ.regs n w).toNat ≠ v then
        if bad < 8 then IO.println s!"  MISMATCH step {k} {n}: edsl={(σ.regs n w).toNat} iss={v}"
        bad := bad + 1
    k := k + 1
  return bad

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
  let scripts : List (String × List HpIn) :=
    [("single read ", scriptRead), ("single write", scriptWrite), ("back-to-back", scriptBack)]
  let mut total := 0
  for (nm, sc) in scripts do
    let bad ← lockstep sc
    if bad = 0 then IO.println s!"  OK  hp {nm} ({sc.length} cyc)"
    else IO.println s!"  FAIL hp {nm} ({bad} mismatches)"
    total := total + bad
  if total = 0 then IO.println "HP MASTER SELFTEST OK — EDSL≡ISS on read/write/back-to-back"
  else IO.println s!"HP MASTER SELFTEST FAILED ({total} mismatches)"

end Machines.Lnp64mini.HpMaster
