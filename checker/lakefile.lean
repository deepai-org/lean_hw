-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lake
open Lake DSL

/- The second, independent LRAT checker (charter Phase 3; PLAN P6 / §8 4.2).
   This package must NEVER depend on Loom, Machines, or Mathlib — core Lean
   only. Its value is implementation diversity, not shared code. -/
package checker

lean_lib Chk

@[default_target]
lean_exe chk where
  root := `Main
