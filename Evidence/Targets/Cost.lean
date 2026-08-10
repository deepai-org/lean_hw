-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CostTarget

/-!
# External cost calibrations

These values are measurements or provisional engineering estimates. They are
not Loom theorems and are kept outside the generic `Loom` library.
-/

namespace Loom.Evidence.Targets.Cost

open Loom.Hw

/-- XC7Z020 calibration fitted to the repository's openXC7 measurements. -/
def xc7z020 : CostTarget where
  name := "xc7z020"
  resourceName := "LUT"
  wStateBits := 0
  wBitOps := 7
  wSoftBits := 400
  macroBitsPerInstance := 36864
  packExpansionMilli := 1260
  capacity := 106400
  macroCapacity := 140
  closurePercent := 50
  weightProvenance := .measured
    "yosys 0.38 (openXC7), SLICE_LUTX"
    "2 designs; underdetermined 3-weight fit; worst residual 1.0%"
  closureProvenance := .measured
    "nextpnr-xilinx (openXC7)"
    "dual routed at 48-52%; epoch failed two seeds at 52-53%"
  fittedOn := "lnp64mini family only; another family is extrapolation"

/-- Provisional generic standard-cell estimate. No ASIC flow in this
repository has calibrated it. -/
def asicGE : CostTarget where
  name := "asicGE"
  resourceName := "gate-equivalent"
  wStateBits := 5000
  wBitOps := 1500
  wSoftBits := 6000
  macroBitsPerInstance := 0
  packExpansionMilli := 1000
  capacity := 0
  macroCapacity := 0
  closurePercent := 70
  weightProvenance := .datasheet
    "standard-cell rules of thumb (FF ≈ 5 GE, 2-input gate ≈ 1 GE)"
  closureProvenance := .datasheet
    "typical placement-density practice, 60-80%"
  fittedOn := "nothing in this repository; no ASIC flow has been run"

end Loom.Evidence.Targets.Cost
