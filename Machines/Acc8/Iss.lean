-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Acc8.Spec

/-!
# Acc8 instruction-set simulator

The spec *is* the simulator (P7): `run` iterates `step`. Program images are
built with the assembler view of the generic framework (`encode` over `isa`),
so the ISS, the decoder theorems, and future conformance vectors all flow
from the same declarations. Trace emission joins in task 0.15 when
`Loom.Core.Trace` freezes.
-/

namespace Machines.Acc8

open Loom.Isa

/-- Run `n` cycles. -/
def run : Nat → St → St
  | 0, σ => σ
  | n + 1, σ => run n (step σ)

/-- Assemble one instruction by mnemonic (partial only at the assembler
surface; unknown mnemonics become `hlt`-by-decode-failure words). -/
def asm (mnemonic : String) (imm : BitVec 8) : BitVec 16 :=
  match isa.findFinIdx? (·.mnemonic = mnemonic) with
  | some i => encode isa i (immField.set imm 0)
  | none => 0xff00

/-- Load a program image at address 0; the rest of program memory is
`hlt`-inducing zeros only if `nop` (opcode 0) — so pad with `hlt`. -/
def loadProg (ws : List (BitVec 16)) : BitVec 8 → BitVec 16 :=
  fun a =>
    match ws[a.toNat]? with
    | some w => w
    | none => asm "hlt" 0

/-- A straight-line golden program: computes 7 + 35 - 2 = 40 into cell 3. -/
def golden : List (BitVec 16) :=
  [ asm "ldi" 7
  , asm "add" 35
  , asm "sub" 2
  , asm "sta" 3
  , asm "hlt" 0
  ]

/-- Boot and run the golden program to quiescence. -/
def goldenResult : St := run 10 (boot (loadProg golden))

end Machines.Acc8
