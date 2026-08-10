-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.DebugTap
import Machines.Lnp64mini.Interface

/-!
# LNP64mini dual-board debug map

This is the single edit point for ephemeral BSCAN observations. The generated
include performs all hierarchical output selection, two-flop DRCK sampling,
core selection, and address decoding. These observations are intentionally
outside the machine semantics and release theorem.
-/

namespace Machines.Lnp64mini.DebugMap

open Loom.Hw

/-- Current board-bringup surface. Each entry replaces wire declarations,
instance connections, CDC registers, selected views, and read-case arms that
were previously maintained by hand in the board top. -/
def board : Loom.Hw.DebugMap :=
  { name := "lnp64mini_dual_bscan"
    existingPorts := [DebugPort.ofReg runningReg, DebugPort.ofReg haltedReg]
    taps :=
      [ DebugTap.lowWordOfDualReg 47 traceRdPcReg
      , DebugTap.lowWordOfDualReg 48 traceRdWbReg
      -- The §9.2/op-0 fault record (1235f201): what faulted, where, who.
      -- These replaced the gret_noop/ig_fall diagnostic latches when the
      -- fault semantics landed in the machine -- the diagnostics' entire
      -- job is now an architectural guarantee.
      , DebugTap.ofDualReg 49 faultPcReg
      , DebugTap.ofDualReg 51 faultCauseReg
      , DebugTap.ofDualReg 52 faultCurReg
      -- A typed protocol-violation predicate: one declaration derives the two
      -- child ports, wrapper expression, first-event latch, CDC and read. The
      -- core permits it after cmd 13 start-only; RunHaltInvariant proves it
      -- absent when that host-protocol violation is explicitly excluded.
      , DebugTap.stickyOfDualPredicate 54 "running_and_halted"
          (.and runningReg.rd haltedReg.rd) (haltOnTrigger := true)
      ] }

def path : System.FilePath := "fpga/zc702/board/lnp64mini_debug_map.vh"

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
  let tclPath := path.withExtension "tcl"
  if !(← tclPath.pathExists) then
    throw <| IO.userError s!"debug reader missing: {tclPath} (run `lake exe debugmap`)"
  if (← IO.FS.readFile tclPath) ≠ board.renderTcl then
    throw <| IO.userError s!"debug reader stale: run `lake exe debugmap` ({tclPath})"
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
