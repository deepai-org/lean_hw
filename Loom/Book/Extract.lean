-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Book.Model
import Loom.Isa.Instr

/-!
# The generic extractor (L6)

Walks any machine's `Isa` and builds the book model. Machine-specific
payloads (`Sem`, `Cost`) are rendered through hooks the machine supplies —
the extractor never knows what they mean, only how the machine prints them.
-/

namespace Loom.Book

open Loom.Isa

/-- Machine-supplied rendering hooks. -/
structure Hooks (sig : Sig) (Sem Cost : Type) where
  /-- Display a cost label (e.g. an LNP64-µ WCET class). -/
  costLabel : Cost → String
  /-- Extra per-instruction facts (e.g. the declared errno contract), as
  labeled strings. Every string must be produced from checked terms. -/
  extras : InstrDecl sig Sem Cost → List (String × String) := fun _ => []

/-- The opcode table: one row per declaration. -/
def opcodeTable {sig : Sig} {Sem Cost : Type}
    (isa : Isa sig Sem Cost) (hooks : Hooks sig Sem Cost) : Block :=
  .table ["Mnemonic", "Opcode", "Operands", "Cost class", "Summary"]
    (isa.toList.map fun d =>
      [d.mnemonic, toString d.opcode.toNat, String.intercalate ", " d.operands,
       hooks.costLabel d.cost, d.prose.summary])

/-- One instruction's section. -/
def instrSection {sig : Sig} {Sem Cost : Type}
    (hooks : Hooks sig Sem Cost) (d : InstrDecl sig Sem Cost) : List Block :=
  [.heading 2 s!"{d.mnemonic} — {d.prose.summary}",
   .para s!"Opcode {d.opcode.toNat}. Operands: \
     {if d.operands.isEmpty then "none" else String.intercalate ", " d.operands}. \
     Cost class: {hooks.costLabel d.cost}.",
   .para d.prose.operation] ++
  (match hooks.extras d with
   | [] => []
   | ex => [.list (ex.map fun (k, v) => s!"{k}: {v}")]) ++
  (if d.prose.notes.isEmpty then [] else [.list d.prose.notes])

/-- The whole ISA chapter. -/
def isaChapter {sig : Sig} {Sem Cost : Type} (title : String)
    (isa : Isa sig Sem Cost) (hooks : Hooks sig Sem Cost) : Doc where
  title := title
  blocks :=
    [.heading 1 title,
     .para s!"{isa.size} instructions. {sig.wordBits}-bit instruction word; \
       opcode field [{sig.opcode.lo + sig.opcode.width - 1}:{sig.opcode.lo}].",
     opcodeTable isa hooks] ++
    (isa.toList.flatMap (instrSection hooks))

end Loom.Book
