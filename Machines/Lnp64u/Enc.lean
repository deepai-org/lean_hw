-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.SpecM
import Loom.Isa.Decode

/-!
# LNP64-µ encoding instance (D1, frozen here)

32-bit instruction word, full partition:
`opcode [5:0]`, `rd [8:6]`, `rs1 [11:9]`, `rs2 [14:12]`, `imm17 [31:15]`.

The semantics payload for the generic framework is `Semantics`: the executable
`exec` plus the *declared* error contract (which errnos and faults this
instruction may produce). The declaration is book- and conformance-visible;
the per-op theorem "exec raises only declared errors" is a T1-adjacent
obligation discharged with T1.
-/

namespace Machines.Lnp64u

open Loom.Isa

/-- Operand fields (D1). -/
def fRd  : Field := { name := "rd",  lo := 6,  width := 3 }
def fRs1 : Field := { name := "rs1", lo := 9,  width := 3 }
def fRs2 : Field := { name := "rs2", lo := 12, width := 3 }
def fImm : Field := { name := "imm", lo := 15, width := 17 }

/-- The LNP64-µ encoding signature. -/
def sig : Sig where
  wordBits := 32
  opcode := { name := "opcode", lo := 0, width := 6 }
  fields := [fRd, fRs1, fRs2, fImm]

/-- The declared error contract of an instruction. -/
structure Semantics where
  exec : Exec
  /-- Errnos this instruction may return (`-errno` in `rd`). -/
  errs : List Errno := []
  /-- Faults this instruction may raise (beyond fetch-time faults, which
  belong to the machine, not the instruction). -/
  faults : List Fault := []

/-- An LNP64-µ instruction declaration. -/
abbrev Instr := InstrDecl sig Semantics WcetClass

/-- The LNP64-µ instruction-set type. -/
abbrev IsaT := Loom.Isa.Isa sig Semantics WcetClass

/-- Extract the operand fields of an instruction word. -/
def operandsOf (w : Loom.Word32) : Operands where
  rd  := ⟨(fRd.get w).toNat, (fRd.get w).isLt⟩
  rs1 := ⟨(fRs1.get w).toNat, (fRs1.get w).isLt⟩
  rs2 := ⟨(fRs2.get w).toNat, (fRs2.get w).isLt⟩
  imm := fImm.get w

/-- Build an operand word (assembler direction). -/
def mkOperands (rd rs1 rs2 : RegId) (imm : BitVec 17) : Loom.Word32 :=
  fImm.set imm (fRs2.set (BitVec.ofNat 3 rs2.val)
    (fRs1.set (BitVec.ofNat 3 rs1.val) (fRd.set (BitVec.ofNat 3 rd.val) 0)))

/-- Sign-extend the 17-bit immediate to a word. -/
def immExt (imm : BitVec 17) : Loom.Word32 := imm.signExtend 32

/-- Effective word address from a register value plus immediate: the low
`Addr` bits of the 32-bit sum (addresses wrap mod `memWords` by
specification). -/
def effAddr (base : Loom.Word32) (imm : BitVec 17) : Addr :=
  (base + immExt imm).setWidth 12

/-- Branch target: this instruction's address plus the sign-extended
immediate, in word addresses. -/
def branchTarget (pc : Addr) (imm : BitVec 17) : Addr :=
  pc + (immExt imm).setWidth 12

end Machines.Lnp64u
