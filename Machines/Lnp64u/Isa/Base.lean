import Machines.Lnp64u.Enc

/-!
# Base instruction set (~14 ops)

Register/ALU work, aligned word memory access, branches, and the jump. The
retire glue (in `Step.lean`) has already advanced `pc` to the next
instruction when `exec` runs; branch/jump semantics overwrite it. Memory
access goes exclusively through `SpecM.load`/`store`, i.e. through region
registers — there is no other path from a domain to memory.

Opcodes 0–13. System ops (`Isa/System.lean`) take 16–26, leaving a gap for
base-set growth without renumbering.
-/

namespace Machines.Lnp64u.Isa

open Machines.Lnp64u Loom.Isa SpecM

private def rrr (mnemonic : String) (opcode : BitVec 6)
    (f : Loom.Word32 → Loom.Word32 → Loom.Word32)
    (summary operation : String) : Instr where
  mnemonic := mnemonic
  opcode := opcode
  operands := ["rd", "rs1", "rs2"]
  sem := { exec := fun c => do
    let a ← reg c.d c.op.rs1
    let b ← reg c.d c.op.rs2
    setReg c.d c.op.rd (f a b) }
  cost := .alu
  prose := { summary := summary, operation := operation }

private def branch (mnemonic : String) (opcode : BitVec 6)
    (test : Loom.Word32 → Loom.Word32 → Bool)
    (summary operation : String) : Instr where
  mnemonic := mnemonic
  opcode := opcode
  operands := ["rs1", "rs2", "imm"]
  sem := { exec := fun c => do
    let a ← reg c.d c.op.rs1
    let b ← reg c.d c.op.rs2
    if test a b then
      updDom c.d (fun ds => { ds with pc := branchTarget c.pc c.op.imm })
    else pure () }
  cost := .alu
  prose := { summary := summary, operation := operation }

def base : List Instr := [
  rrr "add" 0 (· + ·) "Add."
    "`rd := rs1 + rs2`, modulo 2^32.",
  rrr "sub" 1 (· - ·) "Subtract."
    "`rd := rs1 - rs2`, modulo 2^32.",
  rrr "and" 2 (· &&& ·) "Bitwise AND."
    "`rd := rs1 & rs2`.",
  rrr "or" 3 (· ||| ·) "Bitwise OR."
    "`rd := rs1 | rs2`.",
  rrr "xor" 4 (· ^^^ ·) "Bitwise XOR."
    "`rd := rs1 ^ rs2`.",
  rrr "shl" 5 (fun a b => a <<< (b &&& 31)) "Shift left logical."
    "`rd := rs1 << (rs2 & 31)`.",
  rrr "shr" 6 (fun a b => a >>> (b &&& 31)) "Shift right logical."
    "`rd := rs1 >> (rs2 & 31)`, zero-filling.",
  { mnemonic := "addi", opcode := 7, operands := ["rd", "rs1", "imm"]
    sem := { exec := fun c => do
      let a ← reg c.d c.op.rs1
      setReg c.d c.op.rd (a + immExt c.op.imm) }
    cost := .alu
    prose := { summary := "Add immediate."
               operation := "`rd := rs1 + sext(imm17)`, modulo 2^32." } },
  { mnemonic := "lui", opcode := 8, operands := ["rd", "imm"]
    sem := { exec := fun c => do
      setReg c.d c.op.rd ((c.op.imm.setWidth 32) <<< 15) }
    cost := .alu
    prose := { summary := "Load upper immediate."
               operation := "`rd := imm17 << 15`. With `addi`, builds any \
                             32-bit constant in two instructions." } },
  { mnemonic := "lw", opcode := 9, operands := ["rd", "rs1", "imm"]
    sem :=
      { exec := fun c => do
          let a ← reg c.d c.op.rs1
          let v ← load c.d (effAddr a c.op.imm)
          setReg c.d c.op.rd v
        faults := [.memoryAuthority] }
    cost := .mem
    prose := { summary := "Load word."
               operation := "`rd := mem[(rs1 + sext(imm17)) mod 4096]`. \
                             Word-addressed; requires read authority via a \
                             region register, else the domain faults." } },
  { mnemonic := "sw", opcode := 10, operands := ["rs1", "rs2", "imm"]
    sem :=
      { exec := fun c => do
          let a ← reg c.d c.op.rs1
          let v ← reg c.d c.op.rs2
          store c.d (effAddr a c.op.imm) v
        faults := [.memoryAuthority] }
    cost := .mem
    prose := { summary := "Store word."
               operation := "`mem[(rs1 + sext(imm17)) mod 4096] := rs2`. \
                             Word-addressed; requires write authority via a \
                             region register, else the domain faults." } },
  branch "beq" 11 (· == ·) "Branch if equal."
    "If `rs1 = rs2`, `pc := pc + sext(imm17)` (word offset from this \
     instruction); otherwise fall through.",
  branch "blt" 12 (fun a b => a.slt b) "Branch if less than (signed)."
    "If `rs1 <ₛ rs2` (two's complement), `pc := pc + sext(imm17)`; \
     otherwise fall through.",
  { mnemonic := "jalr", opcode := 13, operands := ["rd", "rs1", "imm"]
    sem := { exec := fun c => do
      let a ← reg c.d c.op.rs1
      setReg c.d c.op.rd ((c.pc + 1).setWidth 32)
      updDom c.d (fun ds => { ds with pc := effAddr a c.op.imm }) }
    cost := .alu
    prose := { summary := "Jump and link register."
               operation := "`rd := pc + 1` (the return word address), then \
                             `pc := (rs1 + sext(imm17)) mod 4096`. `jalr` \
                             with `rs1 = r0` is the absolute jump; `rd = r0` \
                             discards the link." } }
]

end Machines.Lnp64u.Isa
