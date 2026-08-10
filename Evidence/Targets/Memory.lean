-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.MemTarget

/-!
# External memory-target profiles

These profiles are engineering evidence supplied to Loom's generic
`MemTarget` API. They do not affect design semantics, compilation, or generic
emission. A concrete flow selects one explicitly.
-/

namespace Loom.Evidence.Targets.Memory

open Loom.Hw

/-- Xilinx 7-series evidence for the repository's ZC702/openXC7 flow. -/
def xc7 : MemTarget where
  name := "xc7"
  macroName := "block RAM"
  softName := "distributed LUT RAM"
  maxMacroWritePorts := 1
  macroMinDataBits := 16384
  macroMinDepth := 0
  macroInitDeliverable := true
  softInitDeliverable := false

/-- Conservative Lattice ECP5 profile derived from DP16KD characteristics.
The repository has not qualified this profile through an ECP5 flow. -/
def ecp5 : MemTarget where
  name := "ecp5"
  macroName := "EBR (DP16KD)"
  softName := "distributed LUT RAM (PFU DPR16X4)"
  maxMacroWritePorts := 1
  macroMinDataBits := 16384
  macroMinDepth := 0
  macroInitDeliverable := true
  softInitDeliverable := false

/-- Conservative compiled-SRAM ASIC profile. SRAM and emitted soft memories
are assumed not to receive Verilog initialization images. Exact macro shape
must be replaced by data for the selected compiler or PDK. -/
def asicSram : MemTarget where
  name := "asicSram"
  macroName := "compiled SRAM macro (1RW)"
  softName := "flip-flop array"
  maxMacroWritePorts := 1
  macroMinDataBits := 0
  macroMinDepth := 64
  macroInitDeliverable := false
  softInitDeliverable := false

/-- Profiles shown by the repository evidence report. -/
def all : List MemTarget := [xc7, ecp5, asicSram]

/-- One summary line per external memory profile. -/
def report (d : Design) : String :=
  String.intercalate "\n" <| all.map fun target =>
    let bad := (d.unrealizableOn target).map (·.name)
    s!"  {d.name} on {target.name}: realizable={d.realizableOnB target}" ++
    (if bad.isEmpty then "" else s!"  offenders={bad}")

end Loom.Evidence.Targets.Memory
