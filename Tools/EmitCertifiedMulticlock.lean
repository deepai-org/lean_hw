-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Substrate.TwoClock

/-! Emit the exact small multiclock artifact carried by `verifiedReleases`. -/

def main : IO Unit :=
  Machines.Substrate.TwoClock.certifiedArtifact.emit
    "rtl/certified_multiclock"
