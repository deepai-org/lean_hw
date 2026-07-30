-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

/-!
# S0BscanRegs — the substrate-0 M0 register file, ported to Loom (open design)

Port of `remote-fpga fpga/substrate0/rtl/s0_bscan_regs.v`: the JTAG
console/register bridge that all substrate bring-up rests on — an ID
register, a scratch register, a live heartbeat, an LED register, a
19-byte console banner served one character per read, and an 8-word
scratch BRAM.

This is the first **open** Loom design (D15): the original cannot be
expressed as a closed system because JTAG *writes* into it. The BSCAN
DR-shift plumbing and the DRCK→sysclk CDC stay in the untrusted board
wrapper (clock-domain logic µVerilog deliberately excludes); the wrapper
delivers one command per JTAG UPDATE as a one-cycle pulse on the input
ports:

  cmd_valid (1)  — pulse: a transaction arrived
  cmd_wr    (1)  — write enable
  cmd_bram  (1)  — region select (0 = registers, 1 = BRAM)
  cmd_idx   (7)  — register/word index
  cmd_wdata (32) — write data

`o_rd_reg` feeds the next scan's capture — the same pipelined-read
protocol as the original. The register map is the original's, with a
distinct ID (0x5330_1001, "Loom edition") so a probe can tell which
implementation it is talking to.
-/

namespace Machines.Substrate.S0BscanRegs

open Loom.Hw

def ID_MAGIC : Nat := 0x53301001
def BANNER : String := "SUBSTRATE-0 M0 OK\r\n"   -- 19 bytes, the original's
def BANNER_LEN : Nat := 19

/-! ## Inputs (read like any pre-cycle state, per D15) -/

def cmdValid : Expr 1  := .reg 1  "cmd_valid"
def cmdWr    : Expr 1  := .reg 1  "cmd_wr"
def cmdBram  : Expr 1  := .reg 1  "cmd_bram"
def cmdIdx   : Expr 7  := .reg 7  "cmd_idx"
def cmdWdata : Expr 32 := .reg 32 "cmd_wdata"

/-! ## State -/

def scratch : Expr 32 := .reg 32 "scratch"
def led     : Expr 4  := .reg 4  "led"
def conIdx  : Expr 5  := .reg 5  "con_idx"
def rdReg   : Expr 32 := .reg 32 "rd_reg"
def hb      : Expr 32 := .reg 32 "hb"

def bannerInit (a : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((BANNER.toList.getD a ⟨0, by decide⟩).toNat)

def idxIs (n : Nat) : Expr 1 := .eq cmdIdx (.lit (BitVec.ofNat 7 n))
def conValid : Expr 1 := .ult conIdx (.lit (BitVec.ofNat 5 BANNER_LEN))

/-- Current banner character (with valid bit at [8]), or 0 when exhausted. -/
def conData : Expr 32 :=
  .mux conValid
    (.or (.zext (.memRead 8 "banner" conIdx) 32) (.lit 0x100))
    (.lit 0)

/-- The region-0 read mux (indices 0..5, default 0xDEAD0000). -/
def readMux : Expr 32 :=
  .mux (idxIs 0) (.lit (BitVec.ofNat 32 ID_MAGIC)) <|
  .mux (idxIs 1) scratch <|
  .mux (idxIs 2) hb <|
  .mux (idxIs 3) (.zext led 32) <|
  .mux (idxIs 4) (.zext (.sub (.lit (BitVec.ofNat 5 BANNER_LEN)) conIdx) 32) <|
  .mux (idxIs 5) conData (.lit 0xDEAD0000)

/-! ## Rules (the original's UPDATE-block, one command per cycle) -/

def hbRule : Rule := ⟨"hb", .write 32 "hb" (.add hb (.lit 1))⟩

/-- Writes: scratch (1), LED (3), console re-arm (4), BRAM region. -/
def writeRule : Rule :=
  ⟨"write", .ite (.and cmdValid cmdWr)
    (.ite cmdBram
      (.memWrite 3 32 "bram" 0 (.slice cmdIdx 0 3) cmdWdata)
      (.seq (.ite (idxIs 1) (.write 32 "scratch" cmdWdata) .skip)
        (.seq (.ite (idxIs 3) (.write 4 "led" (.slice cmdWdata 0 4)) .skip)
              (.ite (idxIs 4) (.write 5 "con_idx" (.lit 0)) .skip))))
    .skip⟩

/-- Read latch: every transaction updates `rd_reg` for the next capture. -/
def readRule : Rule :=
  ⟨"read", .ite cmdValid
    (.write 32 "rd_reg"
      (.mux cmdBram (.memRead 32 "bram" (.slice cmdIdx 0 3)) readMux))
    .skip⟩

/-- A CON_DATA read consumes the served character. -/
def conAdvRule : Rule :=
  ⟨"conadv", .ite
    (.and cmdValid (.and (.not cmdWr) (.and (.not cmdBram)
      (.and (idxIs 5) conValid))))
    (.write 5 "con_idx" (.add conIdx (.lit 1)))
    .skip⟩

def design : Design where
  name := "s0bscan"
  regs :=
    [⟨"scratch", 32, 0⟩, ⟨"led", 4, 0⟩, ⟨"con_idx", 5, 0⟩,
     ⟨"rd_reg", 32, 0⟩, ⟨"hb", 32, 0⟩]
  mems :=
    [⟨"banner", 5, 8, bannerInit⟩, ⟨"bram", 3, 32, fun _ => 0⟩]
  rules := [hbRule, writeRule, readRule, conAdvRule]
  inputs :=
    [⟨"cmd_valid", 1⟩, ⟨"cmd_wr", 1⟩, ⟨"cmd_bram", 1⟩,
     ⟨"cmd_idx", 7⟩, ⟨"cmd_wdata", 32⟩]

theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

/-! ## The fast executable mirror (ISS) -/

structure Cmd where
  valid : Bool := false
  wr    : Bool := false
  bram  : Bool := false
  idx   : Nat  := 0
  wdata : BitVec 32 := 0
  deriving Repr

structure S0St where
  scratch : BitVec 32 := 0
  led     : BitVec 4  := 0
  conIdx  : BitVec 5  := 0
  rdReg   : BitVec 32 := 0
  hb      : BitVec 32 := 0
  bram    : Vector (BitVec 32) 8 := Vector.replicate 8 0
  deriving Repr, DecidableEq

namespace Iss

def bannerByte (i : Nat) : BitVec 8 := bannerInit i

/-- One cycle under command `c` — all reads pre-cycle, per D9/D15. -/
def step (s : S0St) (c : Cmd) : S0St := Id.run do
  let mut s' := { s with hb := s.hb + 1 }
  if c.valid then
    let conOk := s.conIdx.toNat < BANNER_LEN
    if c.wr then
      if c.bram then
        s' := { s' with bram := s'.bram.set! (c.idx % 8) c.wdata }
      else
        if c.idx = 1 then s' := { s' with scratch := c.wdata }
        if c.idx = 3 then s' := { s' with led := c.wdata.setWidth 4 }
        if c.idx = 4 then s' := { s' with conIdx := 0 }
    -- read latch (pre-cycle state)
    let r : BitVec 32 :=
      if c.bram then s.bram[c.idx % 8]!
      else match c.idx with
        | 0 => BitVec.ofNat 32 ID_MAGIC
        | 1 => s.scratch
        | 2 => s.hb
        | 3 => s.led.setWidth 32
        | 4 => (BitVec.ofNat 5 BANNER_LEN - s.conIdx).setWidth 32
        | 5 => if conOk
               then (bannerByte s.conIdx.toNat).setWidth 32 ||| 0x100
               else 0
        | _ => 0xDEAD0000
    s' := { s' with rdReg := r }
    if ¬ c.wr ∧ ¬ c.bram ∧ c.idx = 5 ∧ conOk then
      s' := { s' with conIdx := s.conIdx + 1 }
  return s'

def run (cs : List Cmd) (s : S0St := {}) : S0St := cs.foldl step s

end Iss

/-! ## Lockstep: EDSL open semantics ≡ ISS on a command trace -/

/-- Drive one `Cmd` as a D15 input valuation. -/
def Cmd.toEnv (c : Cmd) : InEnv := fun n w =>
  match n with
  | "cmd_valid" => (BitVec.ofBool c.valid).setWidth w
  | "cmd_wr"    => (BitVec.ofBool c.wr).setWidth w
  | "cmd_bram"  => (BitVec.ofBool c.bram).setWidth w
  | "cmd_idx"   => (BitVec.ofNat 7 c.idx).setWidth w
  | "cmd_wdata" => c.wdata.setWidth w
  | _ => 0#w

/-- The s0 acceptance trace: ID read, scratch write/readback, heartbeat,
LED write, full banner drain + exhaustion, re-arm, BRAM write/readback. -/
def acceptanceTrace : List Cmd :=
  [⟨true, false, false, 0, 0⟩,                    -- read ID
   ⟨true, true,  false, 1, 0x1EAD5E13⟩,           -- write scratch
   ⟨true, false, false, 1, 0⟩,                    -- read scratch
   ⟨true, false, false, 2, 0⟩,                    -- read heartbeat
   ⟨true, true,  false, 3, 0xA⟩,                  -- write LED = 0b1010
   ⟨true, false, false, 3, 0⟩]                    -- read LED
  ++ (List.replicate 21 (⟨true, false, false, 5, 0⟩ : Cmd))  -- drain banner + 2 past end
  ++ [⟨true, false, false, 4, 0⟩,                 -- remaining (expect 0)
      ⟨true, true,  false, 4, 0⟩,                 -- re-arm console
      ⟨true, false, false, 4, 0⟩,                 -- remaining (expect 19)
      ⟨true, true,  true,  5, 0xB00051E5⟩,        -- BRAM[5] write
      ⟨true, false, true,  5, 0⟩,                 -- BRAM[5] read
      ⟨false, false, false, 0, 0⟩]                -- idle cycle

def issRegs (s : S0St) : List (String × Nat) :=
  [("scratch", s.scratch.toNat), ("led", s.led.toNat),
   ("con_idx", s.conIdx.toNat), ("rd_reg", s.rdReg.toNat), ("hb", s.hb.toNat)]

/-- EDSL-vs-ISS lockstep over the acceptance trace, checking the full
register state after every command. -/
def selftest : IO Unit := do
  let mut σ := design.reset
  let mut iss : S0St := {}
  let mut step := 0
  let mut bad := 0
  for c in acceptanceTrace do
    σ := design.cycleOpen c.toEnv σ
    iss := Iss.step iss c
    for (n, v) in issRegs iss do
      let w := (design.regs.filterMap
        (fun r => if r.name = n then some r.width else none)).headD 32
      if (σ.regs n w).toNat ≠ v then
        IO.println s!"MISMATCH step {step} {n}: design={(σ.regs n w).toNat} iss={v}"
        bad := bad + 1
    for a in List.range 8 do
      if (σ.mems "bram" a 32).toNat ≠ (iss.bram[a]!).toNat then
        IO.println s!"MISMATCH step {step} bram[{a}]"
        bad := bad + 1
    step := step + 1
  if bad = 0 then
    IO.println s!"S0BSCAN SELFTEST OK ({acceptanceTrace.length} cmds, open-design lockstep)"
  else
    IO.println s!"S0BSCAN SELFTEST FAILED ({bad})"

/-- Expected `rd_reg` after each command of the acceptance trace — the
oracle for the iverilog testbench and the on-silicon JTAG run. -/
def predict : IO Unit := do
  let mut iss : S0St := {}
  let mut k := 0
  for c in acceptanceTrace do
    iss := Iss.step iss c
    IO.println s!"{k} rd_reg={iss.rdReg.toNat}"
    k := k + 1

def emit : IO Unit := design.emit "rtl/s0bscan.v"

end Machines.Substrate.S0BscanRegs
