-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Compose
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO
import Machines.Lnp64mini.Core

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

def c0Rd    : Expr 1  := .reg 1  "c0_rd"
def c0Wr    : Expr 1  := .reg 1  "c0_wr"
def c0Addr  : Expr 32 := .reg 32 "c0_addr"
def c0Wdata : Expr 64 := .reg 64 "c0_wdata"
def c1Rd    : Expr 1  := .reg 1  "c1_rd"
def c1Wr    : Expr 1  := .reg 1  "c1_wr"
def c1Addr  : Expr 32 := .reg 32 "c1_addr"
def c1Wdata : Expr 64 := .reg 64 "c1_wdata"
def c0Lr    : Expr 1  := .reg 1  "c0_lr"
def c0Sc    : Expr 1  := .reg 1  "c0_sc"
def c1Lr    : Expr 1  := .reg 1  "c1_lr"
def c1Sc    : Expr 1  := .reg 1  "c1_sc"
def mDone   : Expr 1  := .reg 1  "m_done"
def mRdata  : Expr 64 := .reg 64 "m_rdata"

/-! ## Registers -/

def st      : Expr 1  := .reg 1  "st"
def owner   : Expr 1  := .reg 1  "owner"
def last    : Expr 1  := .reg 1  "last"
def p0V     : Expr 1  := .reg 1  "p0_v"
def p0Wr    : Expr 1  := .reg 1  "p0_wr"
def p0Addr  : Expr 32 := .reg 32 "p0_addr"
def p0Wdata : Expr 64 := .reg 64 "p0_wdata"
def p1V     : Expr 1  := .reg 1  "p1_v"
def p1Wr    : Expr 1  := .reg 1  "p1_wr"
def p1Addr  : Expr 32 := .reg 32 "p1_addr"
def p1Wdata : Expr 64 := .reg 64 "p1_wdata"
def p0Lr    : Expr 1  := .reg 1  "p0_lr"
def p0Sc    : Expr 1  := .reg 1  "p0_sc"
def p1Lr    : Expr 1  := .reg 1  "p1_lr"
def p1Sc    : Expr 1  := .reg 1  "p1_sc"
def r0V     : Expr 1  := .reg 1  "r0_v"
def r0A     : Expr 32 := .reg 32 "r0_a"
def r1V     : Expr 1  := .reg 1  "r1_v"
def r1A     : Expr 32 := .reg 32 "r1_a"

def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

/-! ## The one rule -/

/-- Grant body for core `i` (0 or 1), given its buffered request.

`ok` = "core `i` still holds a reservation on this word". A tagged `SC`
whose `ok` is false is dropped: no downstream transaction, immediate
completion with `sc_fail`. Everything else goes downstream, and a write
kills the *other* core's matching reservation on the way. -/
def grantBody (i : Nat) (pWr pLr pSc : Expr 1) (pAddr : Expr 32) (pWdata : Expr 64)
    (myV : Expr 1) (myA : Expr 32) (remV : Expr 1) (remA : Expr 32) : Act :=
  let j := 1 - i
  let ok : Expr 1 := .and myV (.eq myA pAddr)
  let scDrop : Expr 1 := .and pSc (.not ok)
  actSeq [
    .write 1 s!"p{i}_v" (L1 0),
    .write 1 "owner" (L1 i),
    .write 1 "last" (L1 i),
    .ite scDrop
      -- refused store-conditional: complete it here, do not touch DDR
      (actSeq [ .write 1 s!"c{i}_done" (L1 1), .write 1 s!"c{i}_sc_fail" (L1 1) ])
      (actSeq [
        .write 32 "d_addr" pAddr,
        .write 64 "d_wdata" pWdata,
        .write 1 "d_start_rd" (.not pWr),
        .write 1 "d_start_wr" pWr,
        .write 1 "st" (L1 BUSY),
        .write 1 "busy" (L1 1),
        -- a load-reserved takes the reservation
        .ite pLr (.seq (.write 1 s!"r{i}_v" (L1 1)) (.write 32 s!"r{i}_a" pAddr)) .skip,
        -- a successful SC consumes it
        .ite pSc (.write 1 s!"r{i}_v" (L1 0)) .skip,
        -- ANY write kills the other core's matching reservation
        .ite (.and pWr (.and remV (.eq remA pAddr)))
          (.seq (.write 1 s!"r{j}_v" (L1 0)) (.write 1 s!"res_kill{j}" (L1 1))) .skip ]) ]

def req0 : Expr 1 := p0V
def req1 : Expr 1 := p1V
/-- Round robin: when both buffers are full the core that was *not* last
granted wins. -/
def grant1 : Expr 1 := .and req1 (.or (.not req0) (.eq last (L1 0)))
def grant0 : Expr 1 := .and req0 (.not grant1)

def arbRule : Rule :=
  ⟨"arb", actSeq [
    -- pulse defaults
    .write 1 "d_start_rd" (L1 0), .write 1 "d_start_wr" (L1 0),
    .write 1 "c0_done" (L1 0), .write 1 "c1_done" (L1 0),
    .write 1 "c0_sc_fail" (L1 0), .write 1 "c1_sc_fail" (L1 0),
    .write 1 "res_kill0" (L1 0), .write 1 "res_kill1" (L1 0),
    .write 1 "busy" (.not (.eq st (L1 IDLE))),
    -- completion: route done/rdata to the owner, release the master
    .ite (.and (.eq st (L1 BUSY)) mDone)
      (actSeq [ .write 1 "st" (L1 IDLE), .write 1 "busy" (L1 0),
                .ite (.eq owner (L1 0))
                  (.seq (.write 1 "c0_done" (L1 1)) (.write 64 "c0_rdata" mRdata))
                  (.seq (.write 1 "c1_done" (L1 1)) (.write 64 "c1_rdata" mRdata)) ])
      .skip,
    -- grant at an op boundary
    .ite (.eq st (L1 IDLE))
      (.ite grant0 (grantBody 0 p0Wr p0Lr p0Sc p0Addr p0Wdata r0V r0A r1V r1A)
        (.ite grant1 (grantBody 1 p1Wr p1Lr p1Sc p1Addr p1Wdata r1V r1A r0V r0A) .skip))
      .skip,
    -- latch incoming requests LAST (a fresh pulse always wins over the
    -- grant's buffer clear; the two can never collide anyway)
    .ite (.or c0Rd c0Wr)
      (actSeq [.write 1 "p0_v" (L1 1), .write 1 "p0_wr" c0Wr,
               .write 1 "p0_lr" c0Lr, .write 1 "p0_sc" c0Sc,
               .write 32 "p0_addr" c0Addr, .write 64 "p0_wdata" c0Wdata]) .skip,
    .ite (.or c1Rd c1Wr)
      (actSeq [.write 1 "p1_v" (L1 1), .write 1 "p1_wr" c1Wr,
               .write 1 "p1_lr" c1Lr, .write 1 "p1_sc" c1Sc,
               .write 32 "p1_addr" c1Addr, .write 64 "p1_wdata" c1Wdata]) .skip ]⟩

/-! ## Declarations -/

def regs : List RegDecl :=
  [ ⟨"st",1,0⟩, ⟨"owner",1,0⟩, ⟨"last",1,1⟩, ⟨"busy",1,0⟩,
    ⟨"p0_v",1,0⟩, ⟨"p0_wr",1,0⟩, ⟨"p0_lr",1,0⟩, ⟨"p0_sc",1,0⟩,
    ⟨"p0_addr",32,0⟩, ⟨"p0_wdata",64,0⟩,
    ⟨"p1_v",1,0⟩, ⟨"p1_wr",1,0⟩, ⟨"p1_lr",1,0⟩, ⟨"p1_sc",1,0⟩,
    ⟨"p1_addr",32,0⟩, ⟨"p1_wdata",64,0⟩,
    ⟨"r0_v",1,0⟩, ⟨"r0_a",32,0⟩, ⟨"r1_v",1,0⟩, ⟨"r1_a",32,0⟩,
    ⟨"c0_sc_fail",1,0⟩, ⟨"c1_sc_fail",1,0⟩,
    ⟨"d_start_rd",1,0⟩, ⟨"d_start_wr",1,0⟩, ⟨"d_addr",32,0⟩, ⟨"d_wdata",64,0⟩,
    ⟨"c0_done",1,0⟩, ⟨"c0_rdata",64,0⟩, ⟨"c1_done",1,0⟩, ⟨"c1_rdata",64,0⟩,
    ⟨"res_kill0",1,0⟩, ⟨"res_kill1",1,0⟩ ]

def inputs : List InputDecl :=
  [ ⟨"c0_rd",1⟩, ⟨"c0_wr",1⟩, ⟨"c0_addr",32⟩, ⟨"c0_wdata",64⟩,
    ⟨"c1_rd",1⟩, ⟨"c1_wr",1⟩, ⟨"c1_addr",32⟩, ⟨"c1_wdata",64⟩,
    ⟨"c0_lr",1⟩, ⟨"c0_sc",1⟩, ⟨"c1_lr",1⟩, ⟨"c1_sc",1⟩,
    ⟨"m_done",1⟩, ⟨"m_rdata",64⟩ ]

def design : Design where
  name := "hp_arbiter"
  regs := regs
  mems := []
  rules := [arbRule]
  inputs := inputs

/-! ## ISS mirror -/

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

structure ArbSt where
  st : Bool := false            -- false = IDLE, true = BUSY
  owner : Bool := false
  last : Bool := true
  busy : Bool := false
  p0_v : Bool := false
  p0_wr : Bool := false
  p0_lr : Bool := false
  p0_sc : Bool := false
  p0_addr : BitVec 32 := 0
  p0_wdata : BitVec 64 := 0
  p1_v : Bool := false
  p1_wr : Bool := false
  p1_lr : Bool := false
  p1_sc : Bool := false
  p1_addr : BitVec 32 := 0
  p1_wdata : BitVec 64 := 0
  r0_v : Bool := false
  r0_a : BitVec 32 := 0
  r1_v : Bool := false
  r1_a : BitVec 32 := 0
  c0_sc_fail : Bool := false
  c1_sc_fail : Bool := false
  d_start_rd : Bool := false
  d_start_wr : Bool := false
  d_addr : BitVec 32 := 0
  d_wdata : BitVec 64 := 0
  c0_done : Bool := false
  c0_rdata : BitVec 64 := 0
  c1_done : Bool := false
  c1_rdata : BitVec 64 := 0
  res_kill0 : Bool := false
  res_kill1 : Bool := false
  deriving Repr

def ArbIss.step (s : ArbSt) (inp : ArbIn) : ArbSt := Id.run do
  let mut s' := s
  s' := { s' with d_start_rd := false, d_start_wr := false,
                  c0_done := false, c1_done := false,
                  c0_sc_fail := false, c1_sc_fail := false,
                  res_kill0 := false, res_kill1 := false,
                  busy := s.st }
  if s.st ∧ inp.m_done then
    s' := { s' with st := false, busy := false }
    if ¬ s.owner then s' := { s' with c0_done := true, c0_rdata := inp.m_rdata }
    else s' := { s' with c1_done := true, c1_rdata := inp.m_rdata }
  if ¬ s.st then
    let g1 := s.p1_v ∧ (¬ s.p0_v ∨ ¬ s.last)
    let g0 := s.p0_v ∧ ¬ g1
    if g0 then
      let ok := s.r0_v ∧ s.r0_a = s.p0_addr
      s' := { s' with p0_v := false, owner := false, last := false }
      if s.p0_sc ∧ ¬ ok then
        s' := { s' with c0_done := true, c0_sc_fail := true }
      else
        s' := { s' with d_addr := s.p0_addr, d_wdata := s.p0_wdata,
                        d_start_rd := ¬ s.p0_wr, d_start_wr := s.p0_wr,
                        st := true, busy := true }
        if s.p0_lr then s' := { s' with r0_v := true, r0_a := s.p0_addr }
        if s.p0_sc then s' := { s' with r0_v := false }
        if s.p0_wr ∧ s.r1_v ∧ s.r1_a = s.p0_addr then
          s' := { s' with r1_v := false, res_kill1 := true }
    else if g1 then
      let ok := s.r1_v ∧ s.r1_a = s.p1_addr
      s' := { s' with p1_v := false, owner := true, last := true }
      if s.p1_sc ∧ ¬ ok then
        s' := { s' with c1_done := true, c1_sc_fail := true }
      else
        s' := { s' with d_addr := s.p1_addr, d_wdata := s.p1_wdata,
                        d_start_rd := ¬ s.p1_wr, d_start_wr := s.p1_wr,
                        st := true, busy := true }
        if s.p1_lr then s' := { s' with r1_v := true, r1_a := s.p1_addr }
        if s.p1_sc then s' := { s' with r1_v := false }
        if s.p1_wr ∧ s.r0_v ∧ s.r0_a = s.p1_addr then
          s' := { s' with r0_v := false, res_kill0 := true }
  if inp.c0_rd ∨ inp.c0_wr then
    s' := { s' with p0_v := true, p0_wr := inp.c0_wr,
                    p0_lr := inp.c0_lr, p0_sc := inp.c0_sc,
                    p0_addr := inp.c0_addr, p0_wdata := inp.c0_wdata }
  if inp.c1_rd ∨ inp.c1_wr then
    s' := { s' with p1_v := true, p1_wr := inp.c1_wr,
                    p1_lr := inp.c1_lr, p1_sc := inp.c1_sc,
                    p1_addr := inp.c1_addr, p1_wdata := inp.c1_wdata }
  return s'

/-! ## Lockstep plumbing -/

def ArbIn.toEnv (c : ArbIn) : InEnv := fun n w =>
  match n with
  | "c0_rd" => (BitVec.ofBool c.c0_rd).setWidth w
  | "c0_wr" => (BitVec.ofBool c.c0_wr).setWidth w
  | "c0_addr" => c.c0_addr.setWidth w
  | "c0_wdata" => c.c0_wdata.setWidth w
  | "c1_rd" => (BitVec.ofBool c.c1_rd).setWidth w
  | "c1_wr" => (BitVec.ofBool c.c1_wr).setWidth w
  | "c1_addr" => c.c1_addr.setWidth w
  | "c1_wdata" => c.c1_wdata.setWidth w
  | "c0_lr" => (BitVec.ofBool c.c0_lr).setWidth w
  | "c0_sc" => (BitVec.ofBool c.c0_sc).setWidth w
  | "c1_lr" => (BitVec.ofBool c.c1_lr).setWidth w
  | "c1_sc" => (BitVec.ofBool c.c1_sc).setWidth w
  | "m_done" => (BitVec.ofBool c.m_done).setWidth w
  | "m_rdata" => c.m_rdata.setWidth w
  | _ => 0#w

def issRegs (s : ArbSt) : List (String × Nat × Nat) :=
  let b (x : Bool) : Nat := if x then 1 else 0
  [("st",1,b s.st), ("owner",1,b s.owner), ("last",1,b s.last), ("busy",1,b s.busy),
   ("p0_v",1,b s.p0_v), ("p0_wr",1,b s.p0_wr), ("p0_lr",1,b s.p0_lr), ("p0_sc",1,b s.p0_sc),
   ("p0_addr",32,s.p0_addr.toNat), ("p0_wdata",64,s.p0_wdata.toNat),
   ("p1_v",1,b s.p1_v), ("p1_wr",1,b s.p1_wr), ("p1_lr",1,b s.p1_lr), ("p1_sc",1,b s.p1_sc),
   ("p1_addr",32,s.p1_addr.toNat), ("p1_wdata",64,s.p1_wdata.toNat),
   ("r0_v",1,b s.r0_v), ("r0_a",32,s.r0_a.toNat),
   ("r1_v",1,b s.r1_v), ("r1_a",32,s.r1_a.toNat),
   ("c0_sc_fail",1,b s.c0_sc_fail), ("c1_sc_fail",1,b s.c1_sc_fail),
   ("d_start_rd",1,b s.d_start_rd), ("d_start_wr",1,b s.d_start_wr),
   ("d_addr",32,s.d_addr.toNat), ("d_wdata",64,s.d_wdata.toNat),
   ("c0_done",1,b s.c0_done), ("c0_rdata",64,s.c0_rdata.toNat),
   ("c1_done",1,b s.c1_done), ("c1_rdata",64,s.c1_rdata.toNat),
   ("res_kill0",1,b s.res_kill0), ("res_kill1",1,b s.res_kill1)]

def lockstep (script : List ArbIn) : IO Nat := do
  let mut s : ArbSt := {}
  let mut σ : St := design.reset
  let mut bad := 0
  let mut k := 0
  for inp in script do
    σ := design.cycleOpen inp.toEnv σ
    s := ArbIss.step s inp
    for (n, w, v) in issRegs s do
      if (σ.regs n w).toNat ≠ v then
        if bad < 8 then IO.println s!"  MISMATCH step {k} {n}: edsl={(σ.regs n w).toNat} iss={v}"
        bad := bad + 1
    k := k + 1
  return bad

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
  let scripts : List (String × List ArbIn) :=
    [("solo read    ", scriptSolo), ("simultaneous ", scriptCollide),
     ("reservations ", scriptResv), ("stream x4    ", scriptStream)]
  let mut total := 0
  for (nm, sc) in scripts do
    let bad ← lockstep sc
    if bad = 0 then IO.println s!"  OK  arb {nm} ({sc.length} cyc)"
    else IO.println s!"  FAIL arb {nm} ({bad} mismatches)"
    total := total + bad
  -- semantic assertions on the ISS: nothing dropped, kills are precise
  let runs (sc : List ArbIn) : List ArbSt := Id.run do
    let mut s : ArbSt := {}
    let mut out : List ArbSt := []
    for inp in sc do s := ArbIss.step s inp; out := out ++ [s]
    return out
  let coll := runs scriptCollide
  let starts := (coll.filter (fun s => s.d_start_rd ∨ s.d_start_wr)).length
  let d0 := (coll.filter (·.c0_done)).length
  let d1 := (coll.filter (·.c1_done)).length
  IO.println s!"  simultaneous: downstream starts={starts} (want 2) c0_done={d0} c1_done={d1} (want 1,1)"
  let rv := runs scriptResv
  let k1 := (rv.filter (·.res_kill1)).length
  let k0 := (rv.filter (·.res_kill0)).length
  let f1 := (rv.filter (·.c1_sc_fail)).length
  let f0 := (rv.filter (·.c0_sc_fail)).length
  let wrs := (rv.filter (·.d_start_wr)).length
  let dn1 := (rv.filter (·.c1_done)).length
  IO.println s!"  LR/SC: res_kill1={k1} res_kill0={k0} (want 1,0) sc_fail c1={f1} c0={f0} (want 1,0)"
  IO.println s!"  LR/SC: downstream WRITES={wrs} (want 4 — the refused SC never reaches DDR) c1_done={dn1} (want 5)"
  let strm := runs scriptStream
  let s0 := (strm.filter (·.c0_done)).length
  let s1 := (strm.filter (·.c1_done)).length
  IO.println s!"  stream x4: c0_done={s0} c1_done={s1} (want 4,4)"
  let ok := total = 0 ∧ starts = 2 ∧ d0 = 1 ∧ d1 = 1 ∧ k1 = 1 ∧ k0 = 0
            ∧ f1 = 1 ∧ f0 = 0 ∧ wrs = 4 ∧ dn1 = 5 ∧ s0 = 4 ∧ s1 = 4
  if ok then IO.println "HP ARBITER SELFTEST OK — EDSL≡ISS on 4 scripts + routing/kill assertions"
  else IO.println s!"HP ARBITER SELFTEST FAILED ({total} mismatches)"

end Machines.Lnp64mini.HpArbiter
