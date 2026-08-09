-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.DebugTap

/-!
# LNP64mini dual-board debug map

This is the single edit point for ephemeral BSCAN observations. The generated
include performs all hierarchical output selection, two-flop DRCK sampling,
core selection, and address decoding. These observations are intentionally
outside the machine semantics and release theorem.
-/

namespace Machines.Lnp64mini.DebugMap

open Loom.Hw

-- Kept local on purpose: the runtime generator imports no machine design.
-- `DebugMapCheck` independently proves these names exist in the composed dual
-- output surface.
private def traceRdPc : Reg 64 := ⟨"trace_rd_pc"⟩
private def traceRdWb : Reg 64 := ⟨"trace_rd_wb"⟩
private def gretNoopPc : Reg 64 := ⟨"gret_noop_pc"⟩
private def gretNoopCur : Reg 5 := ⟨"gret_noop_cur"⟩
private def gretNoopCnt : Reg 32 := ⟨"gret_noop_cnt"⟩
private def gretNoopTrapped : Reg 1 := ⟨"gret_noop_trapped"⟩
private def igFallPc : Reg 64 := ⟨"ig_fall_pc"⟩
private def igFallInfo : Reg 16 := ⟨"ig_fall_info"⟩
private def running : Reg 1 := ⟨"running"⟩
private def halted : Reg 1 := ⟨"halted"⟩

/-- Current board-bringup surface. Each entry replaces wire declarations,
instance connections, CDC registers, selected views, and read-case arms that
were previously maintained by hand in the board top. -/
def board : Loom.Hw.DebugMap :=
  { name := "lnp64mini_dual_bscan"
    existingPorts := [{ name := "running", width := 1 }, { name := "halted", width := 1 }]
    taps :=
      [ DebugTap.lowWordOfDualReg 47 traceRdPc
      , DebugTap.lowWordOfDualReg 48 traceRdWb
      , DebugTap.ofDualReg 49 gretNoopPc
      , DebugTap.ofDualReg 51 gretNoopCur
      , DebugTap.ofDualReg 52 gretNoopCnt
      , DebugTap.ofDualReg 53 gretNoopTrapped
      -- A typed protocol-violation predicate: one declaration derives the two
      -- child ports, wrapper expression, first-event latch, CDC and read. The
      -- core permits it after cmd 13 start-only; RunHaltInvariant proves it
      -- absent when that host-protocol violation is explicitly excluded.
      , DebugTap.stickyOfDualPredicate 54 "running_and_halted"
          (.and running.rd halted.rd) (haltOnTrigger := true)
      -- The in_gate[0] fall cause-latch (2026-08-09 desync instrument): the
      -- core latches pc + {valid, free_slot, cur, arm flags} at the first
      -- unexpected fall; pc at 55/56, info at 57.
      , DebugTap.ofDualReg 55 igFallPc
      , DebugTap.ofDualReg 57 igFallInfo ] }

def path : System.FilePath := "fpga/zc702/lnp64mini_debug_map.vh"

def emit (outputPath : System.FilePath := path) : IO Unit :=
  -- `DebugMapCheck.board_source_checked` is the build-time certificate in a module
  -- deliberately not imported by this executable path. A `native_decide`
  -- certificate has a generated initializer; importing it here would rebuild
  -- the huge composed dual design whenever a tiny include is regenerated.
  board.emitUnchecked outputPath

def check : IO Unit := do
  if !(← path.pathExists) then
    throw <| IO.userError s!"debug map missing: {path}"
  let actual ← IO.FS.readFile path
  if actual ≠ board.render then
    throw <| IO.userError s!"debug map stale: run `lake exe debugmap` ({path})"
  let rtlPath : System.FilePath := "rtl/lnp64mini_dual.v"
  if !(← rtlPath.pathExists) then
    throw <| IO.userError s!"emitted dual RTL missing: {rtlPath}"
  let rtl ← IO.FS.readFile rtlPath
  for tap in board.taps do
    for output in tap.outputNames do
      if (rtl.splitOn s!"o_{output}").length ≤ 1 then
        throw <| IO.userError s!"debug map port o_{output} absent from {rtlPath}"
  IO.println s!"debugmap: OK — generated include is current and all typed ports exist in {rtlPath}"

end Machines.Lnp64mini.DebugMap
