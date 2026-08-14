-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.RecoverySmoke

/-! Emit the three-clock recovery acceptance artifact for RTL smoke testing. -/

def main (args : List String) : IO Unit := do
  let directory := args.head?.getD "/tmp/loom-multiclock-recovery-smoke"
  Machines.Multiclock.RecoverySmoke.application.emit directory
