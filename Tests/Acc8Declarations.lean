-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Acc8.Core

/-!
# Acc8 typed-declaration regression

Acc8 is the memory-bearing pathfinder for typed declarations. These
definitional checks pin the derived interface to its pre-migration shape; the
existing A-R/AEV theorems independently pin its rule behavior and compilation.
-/

namespace Tests.Acc8Declarations

open Loom.Hw
open Machines.Acc8

example (prog : BitVec 8 → BitVec 16) : (Core.design prog).regs =
    [⟨"acc", 8, 0⟩, ⟨"pc", 8, 0⟩, ⟨"halted", 1, 0⟩] := rfl

example (prog : BitVec 8 → BitVec 16) : (Core.design prog).mems =
    [ { name := "prog", addrWidth := 8, dataWidth := 16
        init := fun a => prog (BitVec.ofNat 8 a) }
    , { name := "mem", addrWidth := 8, dataWidth := 8, init := fun _ => 0 } ] := rfl

example (prog : BitVec 8 → BitVec 16) :
    (Core.design prog).outputs = ["acc", "pc", "halted"] := rfl

example (prog : BitVec 8 → BitVec 16) :
    (Core.design prog).inputs = [] ∧
    (Core.design prog).ackMemInit = [] ∧
    (Core.design prog).syncReadMems = [] := by
  exact ⟨rfl, rfl, rfl⟩

end Tests.Acc8Declarations
