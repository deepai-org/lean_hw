-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Isa.Instr

/-!
# The instruction-declaration surface syntax (P1, task 0.17)

Sugar, nothing more: `instr … end_instr` elaborates to exactly the
`InstrDecl` structure literal you would have written (P1: structure first,
syntax second). The expected type supplies `sig`, `Sem`, and `Cost`, so one
grammar serves every machine. The regression oracle: each machine's
DSL-declared ISA is *definitionally equal* to its structure-level one
(`Machines/Acc8/DslRegression.lean`), so no projection or proof can tell
them apart.

Grammar:
```
instr "mnemonic" opcode <term> operands ["rd", "rs1"]
  cost <term>
  sem  <term>
  summary "…"
  operation "…"
  [notes ["…", …]]
end_instr
```
-/

namespace Loom.Isa.Dsl

macro "instr" mn:str &"opcode" opc:term:max &"operands" "[" ops:str,* "]"
    &"cost" cst:term:max &"sem" sm:term:max &"summary" summ:str
    &"operation" oper:str &"notes" "[" nts:str,* "]" &"end_instr" : term =>
  `({ mnemonic := $mn, opcode := $opc, operands := [$ops,*]
      sem := $sm, cost := $cst
      prose := { summary := $summ, operation := $oper, notes := [$nts,*] } })

macro "instr" mn:str &"opcode" opc:term:max &"operands" "[" ops:str,* "]"
    &"cost" cst:term:max &"sem" sm:term:max &"summary" summ:str
    &"operation" oper:str &"end_instr" : term =>
  `({ mnemonic := $mn, opcode := $opc, operands := [$ops,*]
      sem := $sm, cost := $cst
      prose := { summary := $summ, operation := $oper } })

end Loom.Isa.Dsl
