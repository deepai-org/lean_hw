-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lake
open Lake DSL

package loom where
  -- The trusted path forbids `native_decide` (Rule 1); nothing here changes kernel options.
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-- The machine-generic toolchain. Never imports `Machines` (enforced by
`scripts/check-imports.sh`). -/
@[default_target]
lean_lib Loom

/-- The machine models: LNP64-µ (the driving use case) and Acc8 (the tiny
pathfinder that keeps the toolchain honest about genericity). -/
@[default_target]
lean_lib Machines

lean_lib Tools

lean_lib Tests

lean_exe iss where
  root := `Tools.Iss

lean_exe asm where
  root := `Tools.Asm

lean_exe audit where
  root := `Tools.Audit
  supportInterpreter := true

lean_exe emit where
  supportInterpreter := true
  root := `Tools.Emit

lean_exe bookgen where
  root := `Tools.BookGen

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"
