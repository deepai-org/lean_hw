-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SyncRead
import Loom.Hw.Footprint

/-!
# Technology-neutral memory classification

This module contains only the generic vocabulary and computations shared by
explicit memory-target profiles. It predicts a macro or soft implementation
class from caller-supplied limits; it does not select a target or establish a
synthesis result.
-/

namespace Loom.Hw

/-- The two implementation classes relevant to target memory diagnostics. -/
inductive MemClass where
  | macro
  | soft
deriving BEq, DecidableEq, Repr, Inhabited

/-- Predict an implementation class from an explicitly supplied profile. -/
def predictedClassWith
    (macroMinDataBits macroMinDepth maxMacroWritePorts : Nat)
    (addressWidth dataWidth writePorts : Nat)
    (synchronousRead : Bool) : MemClass :=
  if synchronousRead && writePorts ≤ maxMacroWritePorts
      && macroMinDepth ≤ 2 ^ addressWidth
      && macroMinDataBits ≤ 2 ^ addressWidth * dataWidth then
    .macro
  else
    .soft

/-- Does the declared image contain a set bit in its address space? -/
def MemDecl.imageNonZeroB (decl : MemDecl) : Bool :=
  (List.range (2 ^ decl.addrWidth)).any fun address =>
    decl.init address != 0#decl.dataWidth

/-- Does any rule write the named memory? -/
def Design.memWrittenB (design : Design) (name : String) : Bool :=
  design.rules.any fun rule => rule.body.memWrites.contains name

end Loom.Hw
