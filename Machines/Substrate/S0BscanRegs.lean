-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Hw.Semantics
import Loom.Hw.FastEval
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

def cmdValidPort : Reg 1  := ⟨"cmd_valid"⟩
def cmdWrPort    : Reg 1  := ⟨"cmd_wr"⟩
def cmdBramPort  : Reg 1  := ⟨"cmd_bram"⟩
def cmdIdxPort   : Reg 7  := ⟨"cmd_idx"⟩
def cmdWdataPort : Reg 32 := ⟨"cmd_wdata"⟩

def cmdValid : Expr 1  := cmdValidPort.rd
def cmdWr    : Expr 1  := cmdWrPort.rd
def cmdBram  : Expr 1  := cmdBramPort.rd
def cmdIdx   : Expr 7  := cmdIdxPort.rd
def cmdWdata : Expr 32 := cmdWdataPort.rd

/-! ## State -/

def scratchReg : Reg 32 := ⟨"scratch"⟩
def ledReg     : Reg 4  := ⟨"led"⟩
def conIdxReg  : Reg 5  := ⟨"con_idx"⟩
def rdRegReg   : Reg 32 := ⟨"rd_reg"⟩
def hbReg      : Reg 32 := ⟨"hb"⟩

def scratch : Expr 32 := scratchReg.rd
def led     : Expr 4  := ledReg.rd
def conIdx  : Expr 5  := conIdxReg.rd
def rdReg   : Expr 32 := rdRegReg.rd
def hb      : Expr 32 := hbReg.rd

def bannerMem : Mem 5 8 := ⟨"banner"⟩
def bramMem   : Mem 3 32 := ⟨"bram"⟩

def bannerInit (a : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((BANNER.toList.getD a ⟨0, by decide⟩).toNat)

def idxIs (n : Nat) : Expr 1 := .eq cmdIdx (.lit (BitVec.ofNat 7 n))
def conValid : Expr 1 := .ult conIdx (.lit (BitVec.ofNat 5 BANNER_LEN))

/-- Current banner character (with valid bit at [8]), or 0 when exhausted. -/
def conData : Expr 32 :=
  .mux conValid
    (.or (.zext (bannerMem.rd conIdx) 32) (.lit 0x100))
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

def hbRule : Rule := ⟨"hb", hbReg.set (.add hb (.lit 1))⟩

/-- Writes: scratch (1), LED (3), console re-arm (4), BRAM region. -/
def writeRule : Rule :=
  ⟨"write", .ite (.and cmdValid cmdWr)
    (.ite cmdBram
      (bramMem.write 0 (.slice cmdIdx 0 3) cmdWdata)
      (.seq (.ite (idxIs 1) (scratchReg.set cmdWdata) .skip)
        (.seq (.ite (idxIs 3) (ledReg.set (.slice cmdWdata 0 4)) .skip)
              (.ite (idxIs 4) (conIdxReg.set (.lit 0)) .skip))))
    .skip⟩

/-- Read latch: every transaction updates `rd_reg` for the next capture. -/
def readRule : Rule :=
  ⟨"read", .ite cmdValid
    (rdRegReg.set
      (.mux cmdBram (bramMem.rd (.slice cmdIdx 0 3)) readMux))
    .skip⟩

/-- A CON_DATA read consumes the served character. -/
def conAdvRule : Rule :=
  ⟨"conadv", .ite
    (.and cmdValid (.and (.not cmdWr) (.and (.not cmdBram)
      (.and (idxIs 5) conValid))))
    (conIdxReg.set (.add conIdx (.lit 1)))
    .skip⟩

def stateDeclarations : Declarations :=
  Declarations.empty
    |>.addReg scratchReg (exported := true)
    |>.addReg ledReg (exported := true)
    |>.addReg conIdxReg (exported := true)
    |>.addReg rdRegReg (exported := true)
    |>.addReg hbReg (exported := true)

/-- The complete state and open interface, derived from typed handles. -/
def declarations : Declarations :=
  stateDeclarations
    |>.addMem bannerMem (init := bannerInit)
    |>.addMem bramMem
    |>.addInput cmdValidPort
    |>.addInput cmdWrPort
    |>.addInput cmdBramPort
    |>.addInput cmdIdxPort
    |>.addInput cmdWdataPort

def s0bRegs : List RegDecl := stateDeclarations.regs

def design : Design :=
  Design.ofDecls "s0bscan" declarations
    [hbRule, writeRule, readRule, conAdvRule]

theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

/-- The FastEval side condition, discharged in the kernel — so the open
(D15) correctness theorem `Loom.Hw.FastEval.fastRunOpen_eq` applies to this
design, and `fastCycleOpen` below is a *proved* stand-in for
`Design.cycleOpen`, not merely a corroborated one. -/
theorem design_fastWF : design.fastWFB = true := by rfl

/-- The instantiated open-design theorem: replaying any input trace through
`fastCycleOpen` agrees with the reference semantics on every declared
coordinate. -/
theorem fastRunOpen_agrees (n : Nat) (ιs : Nat → InEnv) :
    Agree design
      (fastRunOpen design.elaborate ιs n design.fastReset)
      (design.runOpen ιs n design.reset) :=
  FastEval.fastRunOpen_eq design design_fastWF n ιs _ _
    (FastEval.agree_fastReset design)

/-! ## Commands and Design-derived acceptance test -/

structure Cmd where
  valid : Bool := false
  wr    : Bool := false
  bram  : Bool := false
  idx   : Nat  := 0
  wdata : BitVec 32 := 0
  deriving Repr

/-- Drive one `Cmd` as a D15 input valuation. -/
def Cmd.toEnv (c : Cmd) : InEnv := InputBinding.toEnv
  [InputBinding.of cmdValidPort (BitVec.ofBool c.valid),
   InputBinding.of cmdWrPort (BitVec.ofBool c.wr),
   InputBinding.of cmdBramPort (BitVec.ofBool c.bram),
   InputBinding.of cmdIdxPort (BitVec.ofNat 7 c.idx),
   InputBinding.of cmdWdataPort c.wdata]

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

/-! ### The proved generated evaluator (open design) -/

def fast : FastDesign := design.elaborate

/-- Replay the acceptance trace and check its externally meaningful final
outcomes. The transition semantics are not duplicated here: `fastRunOpen_agrees`
connects this generated evaluator to `Design.runOpen` for every input trace and
cycle count. -/
def acceptanceCheck : IO Unit := do
  let mut fs := design.fastReset
  let mut bad := 0
  for c in acceptanceTrace do
    fs := fastCycleOpen fast c.toEnv fs
  let expected : List (String × Nat) :=
    [(scratchReg.name, 0x1EAD5E13), (ledReg.name, 0xA),
     (conIdxReg.name, 0), (rdRegReg.name, 0xB00051E5),
     (hbReg.name, acceptanceTrace.length)]
  let actual := design.fastRegs fs
  for (name, want) in expected do
    match actual.lookup name with
    | some got =>
        if got ≠ want then
          IO.println s!"S0BSCAN OUTCOME MISMATCH {name}: got={got} want={want}"
          bad := bad + 1
    | none =>
        IO.println s!"S0BSCAN OUTCOME MISSING {name}"
        bad := bad + 1
  let bram := design.fastMem fs bramMem.name
  for a in List.range 8 do
    let want := if a = 5 then 0xB00051E5 else 0
    if bram.getD a 0 ≠ want then
      IO.println s!"S0BSCAN OUTCOME MISMATCH {bramMem.name}[{a}]"
      bad := bad + 1
  if bad = 0 then
    IO.println s!"S0BSCAN OUTCOME PASS ({acceptanceTrace.length} cmds, regs + BRAM)"
  else
    throw <| IO.userError s!"S0BSCAN OUTCOME FAIL ({bad} mismatches)"

/-- `fastCycleOpen` ≡ the reference `Design.cycleOpen` over the acceptance
trace, checking the full register state and BRAM after every command. -/
def refCheck : IO Unit := do
  let mut fs := design.fastReset
  let mut σ := design.reset
  let mut bad := 0
  let mut step := 0
  for c in acceptanceTrace do
    fs := fastCycleOpen fast c.toEnv fs
    σ := design.cycleOpen c.toEnv σ
    for (e, i) in design.regList.zipIdx do
      if fs.regs.getD i 0 ≠ (σ.regs e.1 e.2).toNat then
        IO.println s!"REF MISMATCH step {step} {e.1}"
        bad := bad + 1
    for a in List.range 8 do
      if (design.fastMem fs bramMem.name).getD a 0 ≠
          (σ.mems bramMem.name a 32).toNat then
        IO.println s!"REF MISMATCH step {step} bram[{a}]"
        bad := bad + 1
    step := step + 1
  if bad = 0 then
    IO.println "S0BSCAN REF LOCKSTEP OK (fastCycleOpen ≡ Design.cycleOpen)"
  else
    throw <| IO.userError s!"S0BSCAN REF LOCKSTEP FAILED ({bad})"

/-- The full acceptance cross-check. -/
def selftest : IO Unit := do
  refCheck
  acceptanceCheck

/-- Expected `rd_reg` after each command of the acceptance trace — the
oracle for the iverilog testbench and the on-silicon JTAG run, produced by
the verified fast evaluator running the `Design` itself. -/
def predict : IO Unit := do
  let mut fs := design.fastReset
  let mut k := 0
  for c in acceptanceTrace do
    fs := fastCycleOpen fast c.toEnv fs
    IO.println s!"{k} {rdRegReg.name}={((design.fastRegs fs).lookup rdRegReg.name).getD 0}"
    k := k + 1

def emit : IO Unit := design.emit "rtl/s0bscan.v"

end Machines.Substrate.S0BscanRegs
