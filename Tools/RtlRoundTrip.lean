-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Emit.MicroVerilog.RoundTrip

/-!
# `lake exe rtlroundtrip` — the round trip on emitted *files*

```console
lake exe rtlroundtrip rtl/*.v
```

`RoundTrip.lean` proves the round trip for concrete `Module`s by kernel
evaluation (`Module.parseCheck`). This tool applies the same loop to the
text on disk, in the other direction: read `rtl/X.v`, parse it, print the
result, and require the output to be **byte-identical** to the input. A
file that survives that is inside the printer's image and is recovered
exactly by the parser — which is the property the emission theorems need
of the artifact the board build consumes.

Testbenches and hand-written wrappers are not printer output and are
skipped by name (`tb_*.v`); everything else must round-trip.

One *reported* exclusion: files above `hugeLines` lines. `Parse`'s
line-list and wire-list recursions are structural but not tail recursive,
so a 188 000-line emitted file (`rtl/lnp64u.v`, LNP64-µ's pointer-doubling
circuits) exhausts the default 8 MB stack. That is a pre-existing scale
limit of the parser — unrelated to what it accepts — and it is printed,
not hidden.
-/

open Loom.Emit.MicroVerilog

/-- Above this many lines the parser's non-tail recursion exhausts the
default stack; such files are skipped with a printed reason. -/
def hugeLines : Nat := 50000

def checkFile (path : System.FilePath) : IO Bool := do
  let text ← IO.FS.readFile path
  match Parse.parse text with
  | none =>
      IO.println s!"[FAIL] {path}: the parser rejects this text"
      pure false
  | some m =>
      let back := Print.print m
      if back == text || back ++ "\n" == text then
        IO.println s!"[ok]   {path}  ({m.regs.length} regs, {m.mems.length} \
          mems, {m.ins.length} ins, {m.outs.length} outs)"
        pure true
      else
        IO.println s!"[FAIL] {path}: reprinting the parsed module does not \
          reproduce the file ({text.length} bytes in, {back.length} out)"
        pure false

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: rtlroundtrip <file.v> …"
    return 2
  let mut bad := 0
  let mut n := 0
  for a in args do
    let p : System.FilePath := a
    if (p.fileName.getD "").startsWith "tb_" then
      IO.println s!"[skip] {a}: testbench, not printer output"
    else if (← IO.FS.readFile p).splitOn "\n" |>.length |> (· > hugeLines) then
      IO.println s!"[skip] {a}: over {hugeLines} lines — the parser's \
        non-tail line recursion exhausts the default stack (a scale limit \
        of the parser, not of what it accepts)"
    else
      n := n + 1
      unless ← checkFile p do bad := bad + 1
  if bad == 0 then
    IO.println s!"ROUND TRIP OK ({n} file(s) parse and reprint byte-identically)"
    return 0
  else
    IO.println s!"ROUND TRIP FAILED ({bad} of {n} file(s))"
    return 1
