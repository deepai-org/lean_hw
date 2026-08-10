-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Compose
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO
import Machines.Lnp64mini.Core
import Loom.Runner
import Loom.Hw.Declarations

/-!
# HpArbiter — the two-requester front end of the single HP master

`DUAL_SPEC.md` "New Loom design: HpArbiter". Two requester ports
(`c0_rd`/`c0_wr`/`c0_addr`/`c0_wdata` and `c1_*`) are serialized onto one
downstream simple-handshake master (the existing `HpMaster` instance):

```
core0 ─┐                     ┌─ d_start_rd/d_start_wr/d_addr/d_wdata ─┐
       ├─ HpArbiter (RR) ────┤                                        HpMaster ─ AXI
core1 ─┘                     └─ m_done/m_rdata ←────────────────────┘
```

## Why the requests are *latched*

The core asserts `core_rd`/`core_wr` for exactly **one** cycle and then
parks in `S_FW`/`S_DL`/`S_DSW` waiting for `m_done`. A pure combinational
grant would drop the loser of a collision and hang that core forever, so
each port has a one-entry request buffer (`p{i}_v/_wr/_addr/_wdata`). A
core never has two DDR ops in flight, so the buffer can never overflow.

## Round robin

`last` records the core granted most recently; when both buffers are full
the *other* core wins. Grants happen only at op boundaries (`st = IDLE`),
so a transaction is never interleaved with another core's.

## Global LR/SC — the arbiter is the reservation point (DUAL_SPEC deviation)

`DUAL_SPEC` v1 puts the whole mechanism in `res_kill`: "the arbiter kills a
core's reservation when the OTHER core writes any address". Two designs
were built and measured before settling here:

1. **v1 (kill on remote write).** Not atomic, and the hole is reachable: a
   core checks `lr_valid` in `S_EX` and only pulses `core_wr` the cycle
   after, so both cores can pass their `SC` check before either write is
   ordered — a lost update. A kill delivered at the remote write's issue or
   completion is 2+ cycles too late.
2. **v2 (address-precise kill on any remote *access*, incl. `LR`).** Atomic
   in the common case (the later `LR` steals the reservation), but it
   **livelocks**: two cores whose loops drift into anti-phase steal from
   each other forever. Measured in `tb_lnp64mini_dual.v`: 2,000,000 cycles,
   33,330 kills each way, 2 increments committed.

What actually works — and what a real machine does — is to validate the
reservation **at the serialization point**, i.e. here:

* each request carries two tags from the core: `c{i}_lr` (this read takes a
  reservation) and `c{i}_sc` (this write is conditional);
* granting a tagged read sets `r{i}_v`/`r{i}_a` (reservation for core `i`);
* granting **any write** from core `j` to `r{i}_a` (`i≠j`) clears `r{i}_v`
  and pulses `res_kill{i}` — the spec's extension 1, now an *optimisation*
  (the victim's `SC` fails locally without a bus round trip) rather than the
  correctness mechanism;
* granting a tagged write from core `i` is a **conditional store**: if
  `r{i}_v ∧ r{i}_a = addr` the write is forwarded downstream and `r{i}_v`
  is consumed; otherwise the write is **dropped** and the request completes
  immediately with `c{i}_sc_fail = 1`, which the core turns into `rd = 1` at
  `S_DSW`.

Atomicity is then exact — two `SC`s to the same word are ordered by the
arbiter and the second one always finds its reservation consumed — and
progress is guaranteed: reservations die only when a write *succeeds*, so
every failed `SC` is paid for by another core's committed store.
-/

namespace Machines.Lnp64mini.HpArbiter

open Loom.Hw
open Machines.Lnp64mini (DATA_BASE)

/-! ## FSM states -/

def IDLE : Nat := 0
def BUSY : Nat := 1

/-! ## Literal helpers -/

def L1  (n : Nat) : Expr 1  := .lit (BitVec.ofNat 1 n)
def L32 (n : Nat) : Expr 32 := .lit (BitVec.ofNat 32 n)
def L64 (n : Nat) : Expr 64 := .lit (BitVec.ofNat 64 n)

/-! ## Input ports -/

structure RequestPorts where
  rd : Reg 1
  wr : Reg 1
  addr : Reg 32
  wdata : Reg 64
  lr : Reg 1
  sc : Reg 1

def c0Ports : RequestPorts :=
  ⟨⟨"c0_rd"⟩, ⟨"c0_wr"⟩, ⟨"c0_addr"⟩, ⟨"c0_wdata"⟩, ⟨"c0_lr"⟩, ⟨"c0_sc"⟩⟩

def c1Ports : RequestPorts :=
  ⟨⟨"c1_rd"⟩, ⟨"c1_wr"⟩, ⟨"c1_addr"⟩, ⟨"c1_wdata"⟩, ⟨"c1_lr"⟩, ⟨"c1_sc"⟩⟩

def mDonePort : Reg 1 := ⟨"m_done"⟩
def mRdataPort : Reg 64 := ⟨"m_rdata"⟩

def c0Rd : Expr 1 := c0Ports.rd.rd
def c0Wr : Expr 1 := c0Ports.wr.rd
def c0Addr : Expr 32 := c0Ports.addr.rd
def c0Wdata : Expr 64 := c0Ports.wdata.rd
def c0Lr : Expr 1 := c0Ports.lr.rd
def c0Sc : Expr 1 := c0Ports.sc.rd
def c1Rd : Expr 1 := c1Ports.rd.rd
def c1Wr : Expr 1 := c1Ports.wr.rd
def c1Addr : Expr 32 := c1Ports.addr.rd
def c1Wdata : Expr 64 := c1Ports.wdata.rd
def c1Lr : Expr 1 := c1Ports.lr.rd
def c1Sc : Expr 1 := c1Ports.sc.rd
def mDone : Expr 1 := mDonePort.rd
def mRdata : Expr 64 := mRdataPort.rd

/-! ## Registers -/

structure LaneRegs where
  index : Nat
  pV : Reg 1
  pWr : Reg 1
  pLr : Reg 1
  pSc : Reg 1
  pAddr : Reg 32
  pWdata : Reg 64
  rV : Reg 1
  rA : Reg 32
  scFail : Reg 1
  done : Reg 1
  rdata : Reg 64
  resKill : Reg 1

def lane0 : LaneRegs :=
  ⟨0, ⟨"p0_v"⟩, ⟨"p0_wr"⟩, ⟨"p0_lr"⟩, ⟨"p0_sc"⟩,
    ⟨"p0_addr"⟩, ⟨"p0_wdata"⟩, ⟨"r0_v"⟩, ⟨"r0_a"⟩,
    ⟨"c0_sc_fail"⟩, ⟨"c0_done"⟩, ⟨"c0_rdata"⟩, ⟨"res_kill0"⟩⟩

def lane1 : LaneRegs :=
  ⟨1, ⟨"p1_v"⟩, ⟨"p1_wr"⟩, ⟨"p1_lr"⟩, ⟨"p1_sc"⟩,
    ⟨"p1_addr"⟩, ⟨"p1_wdata"⟩, ⟨"r1_v"⟩, ⟨"r1_a"⟩,
    ⟨"c1_sc_fail"⟩, ⟨"c1_done"⟩, ⟨"c1_rdata"⟩, ⟨"res_kill1"⟩⟩

def stReg : Reg 1 := ⟨"st"⟩
def ownerReg : Reg 1 := ⟨"owner"⟩
def lastReg : Reg 1 := ⟨"last"⟩
def busyReg : Reg 1 := ⟨"busy"⟩
def dStartRdReg : Reg 1 := ⟨"d_start_rd"⟩
def dStartWrReg : Reg 1 := ⟨"d_start_wr"⟩
def dAddrReg : Reg 32 := ⟨"d_addr"⟩
def dWdataReg : Reg 64 := ⟨"d_wdata"⟩

def st : Expr 1 := stReg.rd
def owner : Expr 1 := ownerReg.rd
def last : Expr 1 := lastReg.rd
def p0V : Expr 1 := lane0.pV.rd
def p0Wr : Expr 1 := lane0.pWr.rd
def p0Lr : Expr 1 := lane0.pLr.rd
def p0Sc : Expr 1 := lane0.pSc.rd
def p0Addr : Expr 32 := lane0.pAddr.rd
def p0Wdata : Expr 64 := lane0.pWdata.rd
def p1V : Expr 1 := lane1.pV.rd
def p1Wr : Expr 1 := lane1.pWr.rd
def p1Lr : Expr 1 := lane1.pLr.rd
def p1Sc : Expr 1 := lane1.pSc.rd
def p1Addr : Expr 32 := lane1.pAddr.rd
def p1Wdata : Expr 64 := lane1.pWdata.rd
def r0V : Expr 1 := lane0.rV.rd
def r0A : Expr 32 := lane0.rA.rd
def r1V : Expr 1 := lane1.rV.rd
def r1A : Expr 32 := lane1.rA.rd

def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

/-! ## The one rule -/

/-- Grant body for core `i` (0 or 1), given its buffered request.

`ok` = "core `i` still holds a reservation on this word". A tagged `SC`
whose `ok` is false is dropped: no downstream transaction, immediate
completion with `sc_fail`. Everything else goes downstream, and a write
kills the *other* core's matching reservation on the way. -/
def grantBody (lane other : LaneRegs) : Act :=
  let i := lane.index
  let pWr := lane.pWr.rd
  let pLr := lane.pLr.rd
  let pSc := lane.pSc.rd
  let pAddr := lane.pAddr.rd
  let pWdata := lane.pWdata.rd
  let myV := lane.rV.rd
  let myA := lane.rA.rd
  let remV := other.rV.rd
  let remA := other.rA.rd
  let ok : Expr 1 := .and myV (.eq myA pAddr)
  let scDrop : Expr 1 := .and pSc (.not ok)
  actSeq [
    lane.pV.set (L1 0),
    ownerReg.set (L1 i),
    lastReg.set (L1 i),
    .ite scDrop
      -- refused store-conditional: complete it here, do not touch DDR
      (actSeq [lane.done.set (L1 1), lane.scFail.set (L1 1)])
      (actSeq [
        dAddrReg.set pAddr,
        dWdataReg.set pWdata,
        dStartRdReg.set (.not pWr),
        dStartWrReg.set pWr,
        stReg.set (L1 BUSY),
        busyReg.set (L1 1),
        -- a load-reserved takes the reservation
        .ite pLr (.seq (lane.rV.set (L1 1)) (lane.rA.set pAddr)) .skip,
        -- a successful SC consumes it
        .ite pSc (lane.rV.set (L1 0)) .skip,
        -- ANY write kills the other core's matching reservation
        .ite (.and pWr (.and remV (.eq remA pAddr)))
          (.seq (other.rV.set (L1 0)) (other.resKill.set (L1 1))) .skip ]) ]

def req0 : Expr 1 := p0V
def req1 : Expr 1 := p1V
/-- Round robin: when both buffers are full the core that was *not* last
granted wins. -/
def grant1 : Expr 1 := .and req1 (.or (.not req0) (.eq last (L1 0)))
def grant0 : Expr 1 := .and req0 (.not grant1)

def arbRule : Rule :=
  ⟨"arb", actSeq [
    -- pulse defaults
    dStartRdReg.set (L1 0), dStartWrReg.set (L1 0),
    lane0.done.set (L1 0), lane1.done.set (L1 0),
    lane0.scFail.set (L1 0), lane1.scFail.set (L1 0),
    lane0.resKill.set (L1 0), lane1.resKill.set (L1 0),
    busyReg.set (.not (.eq st (L1 IDLE))),
    -- completion: route done/rdata to the owner, release the master
    .ite (.and (.eq st (L1 BUSY)) mDone)
      (actSeq [stReg.set (L1 IDLE), busyReg.set (L1 0),
                .ite (.eq owner (L1 0))
                  (.seq (lane0.done.set (L1 1)) (lane0.rdata.set mRdata))
                  (.seq (lane1.done.set (L1 1)) (lane1.rdata.set mRdata)) ])
      .skip,
    -- grant at an op boundary
    .ite (.eq st (L1 IDLE))
      (.ite grant0 (grantBody lane0 lane1)
        (.ite grant1 (grantBody lane1 lane0) .skip))
      .skip,
    -- latch incoming requests LAST (a fresh pulse always wins over the
    -- grant's buffer clear; the two can never collide anyway)
    .ite (.or c0Rd c0Wr)
      (actSeq [lane0.pV.set (L1 1), lane0.pWr.set c0Wr,
               lane0.pLr.set c0Lr, lane0.pSc.set c0Sc,
               lane0.pAddr.set c0Addr, lane0.pWdata.set c0Wdata]) .skip,
    .ite (.or c1Rd c1Wr)
      (actSeq [lane1.pV.set (L1 1), lane1.pWr.set c1Wr,
               lane1.pLr.set c1Lr, lane1.pSc.set c1Sc,
               lane1.pAddr.set c1Addr, lane1.pWdata.set c1Wdata]) .skip ]⟩

/-! ## Declarations -/

def declarations : Declarations :=
  Declarations.empty
    |>.addReg stReg (exported := true)
    |>.addReg ownerReg (exported := true)
    |>.addReg lastReg 1 (exported := true)
    |>.addReg busyReg (exported := true)
    |>.addReg lane0.pV (exported := true)
    |>.addReg lane0.pWr (exported := true)
    |>.addReg lane0.pLr (exported := true)
    |>.addReg lane0.pSc (exported := true)
    |>.addReg lane0.pAddr (exported := true)
    |>.addReg lane0.pWdata (exported := true)
    |>.addReg lane1.pV (exported := true)
    |>.addReg lane1.pWr (exported := true)
    |>.addReg lane1.pLr (exported := true)
    |>.addReg lane1.pSc (exported := true)
    |>.addReg lane1.pAddr (exported := true)
    |>.addReg lane1.pWdata (exported := true)
    |>.addReg lane0.rV (exported := true)
    |>.addReg lane0.rA (exported := true)
    |>.addReg lane1.rV (exported := true)
    |>.addReg lane1.rA (exported := true)
    |>.addReg lane0.scFail (exported := true)
    |>.addReg lane1.scFail (exported := true)
    |>.addReg dStartRdReg (exported := true)
    |>.addReg dStartWrReg (exported := true)
    |>.addReg dAddrReg (exported := true)
    |>.addReg dWdataReg (exported := true)
    |>.addReg lane0.done (exported := true)
    |>.addReg lane0.rdata (exported := true)
    |>.addReg lane1.done (exported := true)
    |>.addReg lane1.rdata (exported := true)
    |>.addReg lane0.resKill (exported := true)
    |>.addReg lane1.resKill (exported := true)
    |>.addInput c0Ports.rd
    |>.addInput c0Ports.wr
    |>.addInput c0Ports.addr
    |>.addInput c0Ports.wdata
    |>.addInput c1Ports.rd
    |>.addInput c1Ports.wr
    |>.addInput c1Ports.addr
    |>.addInput c1Ports.wdata
    |>.addInput c0Ports.lr
    |>.addInput c0Ports.sc
    |>.addInput c1Ports.lr
    |>.addInput c1Ports.sc
    |>.addInput mDonePort
    |>.addInput mRdataPort

def design : Design := Design.ofDecls "hp_arbiter" declarations [arbRule]

/-! ## Inputs and Design-derived outcome tests -/

structure ArbIn where
  c0_rd : Bool := false
  c0_wr : Bool := false
  c0_addr : BitVec 32 := 0
  c0_wdata : BitVec 64 := 0
  c1_rd : Bool := false
  c1_wr : Bool := false
  c1_addr : BitVec 32 := 0
  c1_wdata : BitVec 64 := 0
  c0_lr : Bool := false
  c0_sc : Bool := false
  c1_lr : Bool := false
  c1_sc : Bool := false
  m_done : Bool := false
  m_rdata : BitVec 64 := 0
  deriving Repr

/-! ## Design-derived test plumbing -/

def ArbIn.toEnv (c : ArbIn) : InEnv := InputBinding.toEnv
  [InputBinding.of c0Ports.rd (BitVec.ofBool c.c0_rd),
   InputBinding.of c0Ports.wr (BitVec.ofBool c.c0_wr),
   InputBinding.of c0Ports.addr c.c0_addr, InputBinding.of c0Ports.wdata c.c0_wdata,
   InputBinding.of c1Ports.rd (BitVec.ofBool c.c1_rd),
   InputBinding.of c1Ports.wr (BitVec.ofBool c.c1_wr),
   InputBinding.of c1Ports.addr c.c1_addr, InputBinding.of c1Ports.wdata c.c1_wdata,
   InputBinding.of c0Ports.lr (BitVec.ofBool c.c0_lr),
   InputBinding.of c0Ports.sc (BitVec.ofBool c.c0_sc),
   InputBinding.of c1Ports.lr (BitVec.ofBool c.c1_lr),
   InputBinding.of c1Ports.sc (BitVec.ofBool c.c1_sc),
   InputBinding.of mDonePort (BitVec.ofBool c.m_done),
   InputBinding.of mRdataPort c.m_rdata]

private def runStates (script : List ArbIn) : List St := Id.run do
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

/-! ## Selftest scripts -/

/-- Core 0 read only: request, grant, downstream done, routed back. -/
def scriptSolo : List ArbIn :=
  [ { c0_rd := true, c0_addr := 0x10001000 }, {}, {}, { m_done := true, m_rdata := 0xAA }, {}, {} ]

/-- Both cores request on the SAME cycle: round robin must serialize them
(core 1 first — `last` resets to 1... i.e. core 0 wins the first tie), and
both requests must survive (nothing dropped). -/
def scriptCollide : List ArbIn :=
  [ { c0_rd := true, c0_addr := 0x10002000, c1_wr := true, c1_addr := 0x10003000, c1_wdata := 0x77 },
    {}, {},
    { m_done := true, m_rdata := 0x11 },   -- first grantee completes
    {}, {},
    { m_done := true, m_rdata := 0x22 },   -- second grantee completes
    {}, {} ]

/-- The full global-LR/SC protocol, both outcomes.

Phase 1 — core 1 wins an uncontended `SC`:
  c1 `LR` 0x10002000 (reservation), c1 `SC` same word → forwarded (`r1_v`
  consumed), no `sc_fail`.
Phase 2 — the classic race, resolved at the serialization point:
  c0 `LR` 0x10004000, c1 `LR` 0x10004000 (both reserve — reads never steal),
  c0 `SC` → forwarded, kills c1's reservation (`res_kill1`), then c1 `SC`
  → **dropped**, `c1_sc_fail`, and NO downstream write.
Phase 3 — a plain remote write to an unreserved word kills nothing. -/
def scriptResv : List ArbIn :=
  [ -- phase 1
    { c1_rd := true, c1_lr := true, c1_addr := 0x10002000 }, {}, {},
    { m_done := true, m_rdata := 0x55 }, {},
    { c1_wr := true, c1_sc := true, c1_addr := 0x10002000, c1_wdata := 0x1 }, {}, {},
    { m_done := true }, {},
    -- phase 2: both cores reserve the SAME word
    { c0_rd := true, c0_lr := true, c0_addr := 0x10004000 }, {}, {},
    { m_done := true, m_rdata := 0 }, {},
    { c1_rd := true, c1_lr := true, c1_addr := 0x10004000 }, {}, {},
    { m_done := true, m_rdata := 0 }, {},
    -- c0 SC wins (forwarded, kills c1's reservation)
    { c0_wr := true, c0_sc := true, c0_addr := 0x10004000, c0_wdata := 0xAA }, {}, {},
    { m_done := true }, {},
    -- c1 SC loses: dropped in the arbiter, completes with sc_fail, no AXI op
    { c1_wr := true, c1_sc := true, c1_addr := 0x10004000, c1_wdata := 0xBB }, {}, {}, {},
    -- phase 3: a plain remote write elsewhere kills nothing
    { c0_rd := true, c0_lr := true, c0_addr := 0x10006000 }, {}, {},
    { m_done := true, m_rdata := 0 }, {},
    { c1_wr := true, c1_addr := 0x10008000, c1_wdata := 0xCC }, {}, {},
    { m_done := true }, {},
    -- so c0's SC still succeeds
    { c0_wr := true, c0_sc := true, c0_addr := 0x10006000, c0_wdata := 0xDD }, {}, {},
    { m_done := true }, {} ]

/-- Streaming: alternating single-cycle requests from both cores, several
transactions deep — the buffer/latch discipline under sustained traffic. -/
def scriptStream : List ArbIn :=
  ([0,1,2,3].flatMap (fun i =>
    [ { c0_rd := true, c0_addr := BitVec.ofNat 32 (0x10000000 + i*8) : ArbIn },
      { c1_wr := true, c1_addr := BitVec.ofNat 32 (0x10001000 + i*8), c1_wdata := BitVec.ofNat 64 i },
      {}, { m_done := true, m_rdata := BitVec.ofNat 64 (0x100 + i) },
      {}, {}, { m_done := true, m_rdata := 0 }, {} ]))

def selftest : IO Unit := do
  let solo := runStates scriptSolo
  let coll := runStates scriptCollide
  let starts := pulseCount coll dStartRdReg + pulseCount coll dStartWrReg
  let d0 := pulseCount coll lane0.done
  let d1 := pulseCount coll lane1.done
  IO.println s!"  simultaneous: downstream starts={starts} (want 2) c0_done={d0} c1_done={d1} (want 1,1)"
  let rv := runStates scriptResv
  let k1 := pulseCount rv lane1.resKill
  let k0 := pulseCount rv lane0.resKill
  let f1 := pulseCount rv lane1.scFail
  let f0 := pulseCount rv lane0.scFail
  let wrs := pulseCount rv dStartWrReg
  let dn1 := pulseCount rv lane1.done
  IO.println s!"  LR/SC: res_kill1={k1} res_kill0={k0} (want 1,0) sc_fail c1={f1} c0={f0} (want 1,0)"
  IO.println s!"  LR/SC: downstream WRITES={wrs} (want 4 — the refused SC never reaches DDR) c1_done={dn1} (want 5)"
  let strm := runStates scriptStream
  let s0 := pulseCount strm lane0.done
  let s1 := pulseCount strm lane1.done
  IO.println s!"  stream x4: c0_done={s0} c1_done={s1} (want 4,4)"
  let soloOk := pulseCount solo lane0.done = 1 ∧
    (solo.getLast?.map (regAt · lane0.rdata)) = some 0xAA
  let ok := soloOk ∧ starts = 2 ∧ d0 = 1 ∧ d1 = 1 ∧ k1 = 1 ∧ k0 = 0
            ∧ f1 = 1 ∧ f0 = 0 ∧ wrs = 4 ∧ dn1 = 5 ∧ s0 = 4 ∧ s1 = 4
  if ok then IO.println "HP ARBITER SELFTEST OK — Design routing/reservation outcomes pass"
  else IO.println "HP ARBITER SELFTEST FAILED — Design outcome mismatch"
  (Loom.Runner.Result.fromBool "HP arbiter selftest" 91
    (decide ok) "Design routing/reservation outcome mismatch").requirePass

end Machines.Lnp64mini.HpArbiter
