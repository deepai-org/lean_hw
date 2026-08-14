-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Tutorial.SatCounter

/-! Executable wrapper kept separate so importing the reusable tutorial
Design never injects a root-level `main` into another executable. -/

def main : IO Unit :=
  Machines.Tutorial.SatCounter.design.emit "rtl/satcounter.v"
