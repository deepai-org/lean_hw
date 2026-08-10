-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.DeclarationReport

namespace Tests.DeclarationReport

open Loom.Hw

def expected : Declarations :=
  Declarations.empty
    |>.addReg (⟨"count"⟩ : Reg 8) 3 true
    |>.addMem (⟨"ram"⟩ : Mem 4 16) (syncRead := true)
    |>.addInput (⟨"enable"⟩ : Reg 1)

def same : Declarations := expected

def wrong : Declarations :=
  Declarations.empty
    |>.addReg (⟨"count"⟩ : Reg 7) 3 true
    |>.addMem (⟨"ram"⟩ : Mem 4 16)
    |>.addInput (⟨"enabled"⟩ : Reg 1)

example : declarationMigrationOkB expected.entries same.entries = true := by native_decide

example : declarationMigrationOkB expected.entries wrong.entries = false := by native_decide

example : (declarationDiff expected.entries wrong.entries).length = 3 := by native_decide

end Tests.DeclarationReport
