-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Hw.Semantics
import Loom.Hw.ReadsOk
import Loom.Hw.CompileCorrect

/-!
# Typed-handle regressions

The handles and declaration builder are only an authoring layer. These checks
pin their elaboration to the existing EDSL and exercise a complete design
using a typed memory handle.
-/

namespace Tests.Notation

open Loom.Hw
open Loom.Hw.Notation

def addr : Reg 4 := ⟨"addr"⟩
def data : Reg 8 := ⟨"data"⟩
def out : Reg 8 := ⟨"out"⟩
def enable : Reg 1 := ⟨"enable"⟩
def flags : RegArray 1 2 := ⟨"flag"⟩
def ram : Mem 4 8 := ⟨"ram"⟩

example : ram.decl.name = "ram" := rfl
example : ram.decl.addrWidth = 4 := rfl
example : ram.decl.dataWidth = 8 := rfl
example : ram.rd addr.rd = Expr.memRead 8 "ram" addr.rd := rfl
example : ram.write 0 addr.rd data.rd =
    Act.memWrite 4 8 "ram" 0 addr.rd data.rd := rfl

def declarations : Declarations :=
  Declarations.empty
    |>.addReg addr (BitVec.ofNat 4 3)
    |>.addReg data (BitVec.ofNat 8 0xA5)
    |>.addReg out (exported := true)
    |>.addRegArray flags (exported := true)
    |>.addInput enable
    |>.addMem ram (syncRead := true)

def design : Design :=
  Design.ofDecls "typed_memory" declarations
    [⟨"write_and_read", act! {
      ram.write 0 addr.rd data.rd,
      out ⇐ ram.rd addr.rd
    }⟩]

example : declarations.regs.map (·.name) =
    ["addr", "data", "out", "flag0", "flag1"] := by decide
example : declarations.inputs.map (·.name) = ["enable"] := by decide
example : declarations.mems.map (·.name) = ["ram"] := by decide
example : declarations.outputs = ["out", "flag0", "flag1"] := by decide
example : declarations.syncReadMems = ["ram"] := by decide
example : declarations.ackMemInit = [] := by decide

def inputEnv : InEnv :=
  InputBinding.toEnv [InputBinding.of enable (1#1)]

example : inputEnv enable.name 1 = 1#1 := by decide
example : inputEnv enable.name 2 = 0#2 := by decide
example : inputEnv "misspelled" 1 = 0#1 := by decide

example : design.readsOkB = true := by decide

example : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

/-- Reads observe pre-cycle memory and writes commit at the edge. -/
example :
    let s := design.reset
    let s' := design.cycle s
    s'.regs out.name 8 = 0#8 ∧ s'.mems ram.name 3 8 = 0xA5#8 := by
  decide

end Tests.Notation
