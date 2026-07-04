-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Book.Extract
import Loom.Book.Render.Html
import Machines.Lnp64u.Isa
import Machines.Acc8.Spec

/-!
# `lake exe bookgen` — emit the ISA books (task 0.18, skeletal)

Both machines' books are projections of the same `isa` arrays the theorems
quantify over: opcode tables, per-instruction pages, declared error
contracts, WCET classes — no fact enters by hand. Output: `book-out/`.
-/

open Loom.Book

def lnp64uHooks : Hooks Machines.Lnp64u.sig Machines.Lnp64u.Semantics
    Machines.Lnp64u.WcetClass where
  costLabel c :=
    match c with
    | .alu => "alu" | .mem => "mem" | .capOp => "capOp" | .revoke => "revoke"
    | .gate => "gate" | .mover => "mover" | .sched => "sched"
  extras d :=
    (if d.sem.errs.isEmpty then [] else
      [("May return errno", String.intercalate ", "
        (d.sem.errs.map fun e => s!"-{e.code} ({reprStr e})"))]) ++
    (if d.sem.faults.isEmpty then [] else
      [("May fault", String.intercalate ", "
        (d.sem.faults.map fun f => s!"{f.code} ({reprStr f})"))])

def acc8Hooks : Hooks Machines.Acc8.sig Machines.Acc8.Sem Unit where
  costLabel _ := "1 cycle"

def main : IO Unit := do
  IO.FS.createDirAll "book-out"
  let lnp := isaChapter "LNP64-µ Instruction Set Architecture"
    Machines.Lnp64u.isa lnp64uHooks
  IO.FS.writeFile "book-out/lnp64u.html" (Html.render lnp)
  let acc := isaChapter "Acc8 Instruction Set Architecture"
    Machines.Acc8.isa acc8Hooks
  IO.FS.writeFile "book-out/acc8.html" (Html.render acc)
  IO.println "book-out/lnp64u.html, book-out/acc8.html written"
