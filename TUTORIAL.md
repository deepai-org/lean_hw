# Your first proved design

This walks you from an empty file to a two-register hardware design with one
proved invariant, the proof transported to the compiled RTL, and the Verilog
emitted — about 90 lines of Lean, no proof-engineering background assumed
beyond basic Lean tactics.

**What you get at the end (the exact promise).** A theorem that your
property holds in *every reachable state of the compiled RTL* — not of your
model, of the compilation — inherited through the verified compiler's
once-proved correctness theorem, plus the emitted `.v` file. The axioms
under it are exactly `propext`, `Classical.choice`, `Quot.sound`.

**What this document does not cover.** Refinement against an instruction-set
spec (proving your design *implements a program-visible machine*) is a
different, much harder activity; the LNP64-µ development under
`Machines/Lnp64u/Theorems/` is the in-repo evidence that it is possible, not
that it is easy. Start here regardless — this path is the 80% case.

The finished file this tutorial produces is checked into the repo at
`Machines/Tutorial/SatCounter.lean` and is built by CI, so it cannot drift
from the library. If any step below fails for you, that is a bug — see
"Report what went wrong" at the end.

## 0. Setup

From the repo root (the pinned toolchain downloads itself via elan):

```console
lake build Loom.Hw.CompileCorrect Loom.Emit.MicroVerilog.Print
```

The first build of a fresh clone compiles the toolchain's dependencies; give
it a few minutes. Everything after that is incremental.

## 1. The design

Create `Machines/Tutorial/SatCounter.lean` (any module under `Machines/`
is picked up by the build automatically). A design is registers + memories +
rules; rules run each cycle, reads see the pre-cycle state, and the last
write wins — ordinary nonblocking-assignment semantics.

We build a saturating counter: count up; at 255, raise a sticky flag.

```lean
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print

namespace Machines.Tutorial.SatCounter

open Loom.Hw

def count : Expr 8 := .reg 8 "count"
def sat   : Expr 1 := .reg 1 "sat"

def tick : Act :=
  .ite (.eq count (.lit 255))
    (.write 1 "sat" (.lit 1))
    (.write 8 "count" (.add count (.lit 1)))

def design : Design where
  name := "satcounter"
  regs := [⟨"count", 8, 0⟩, ⟨"sat", 1, 0⟩]
  mems := []
  rules := [⟨"tick", tick⟩]
```

`Expr` is width-indexed, so width errors are type errors. `Act.ite`'s
condition is an `Expr 1`; `.eq` produces one.

## 2. The compiler's side conditions

The verified compiler asks for well-formedness (declared names, memory write
ports in order). It has a decision procedure, so for a concrete design this
is one line:

```lean
theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)
```

## 3. The property, on the model

State the property as a predicate on `St` (the design state: named
registers and memories), and prove it invariant by induction: it holds at
reset and every cycle preserves it.

```lean
def SatOk (σ : St) : Prop :=
  σ.regs "sat" 1 = 1#1 → σ.regs "count" 8 = 255#8

theorem satOk_invariant : design.toTSys.Invariant SatOk := by
  apply Loom.TSys.Inductive.invariant
  constructor
  · -- reset: the flag starts at zero
    intro s hinit
    simp only [Design.toTSys_init_iff] at hinit
    subst hinit
    intro hsat
    simp [Design.reset, design, RegEnv.set] at hsat
  · -- step: one cycle preserves the property
    intro s s' hP hstep
    simp only [Design.toTSys_step_iff] at hstep
    subst hstep
    by_cases hc : s.regs "count" 8 = 255#8
    · -- saturated: the rule writes `sat`, leaves `count` unchanged
      intro _
      simp [Design.cycle, design, tick, Act.run, Expr.eval, count,
        RegEnv.set, hc]
    · -- not saturated: the rule writes `count`, leaves `sat` unchanged
      intro hsat
      have hsat' : s.regs "sat" 1 = 1#1 := by
        simpa [Design.cycle, design, tick, Act.run, Expr.eval, count, sat,
          RegEnv.set, hc] using hsat
      exact absurd (hP hsat') hc
```

The opening two lines of each branch are boilerplate:
`Design.toTSys_init_iff` and `Design.toTSys_step_iff` turn the abstract
init/step hypotheses into concrete equalities (`s = design.reset`,
`design.cycle s = s'`) that `subst` can consume.

The one recipe that matters: **put your own definitions in the simp set**
(`design`, your rule, your `Expr` shorthands). `Design.cycle` folds the rule
list, and until `design` is unfolded the goal is a raw `List.foldl` — if you
see one, you forgot a definition, not a lemma. With them, `simp` computes
the cycle and the register reads (`RegEnv.set` resolves name collisions).

## 4. Transport to the RTL

One line. `Compile.simulation` is the verified compiler's once-proved
forward simulation; `invariant_pullback` carries any model invariant down
it. Nothing here is per-design — no proof about the compilation itself is
ever written.

```lean
theorem satOk_rtl :
    (Compile.compile design).toTSys.Invariant
      (fun state => SatOk (Compile.forgetSt state)) :=
  (Compile.simulation design design_wf).invariant_pullback satOk_invariant
```

Read the statement: every reachable state of the *compiled module* satisfies
`SatOk` of its registers. That is the deliverable.

## 5. Emit the Verilog

Add a `main` **at the root level, outside your namespace** (`--run` looks it
up unqualified), then run it:

```lean
end Machines.Tutorial.SatCounter

def main : IO Unit :=
  Machines.Tutorial.SatCounter.design.emit "rtl/satcounter.v"
```

(`Design.emit` — import `Loom.Hw.EmitIO` — compiles with the verified
compiler, prints with the verified printer, and writes the file; it was
added to close defect #1 of the first tutorial run.)

```console
lake env lean --run Machines/Tutorial/SatCounter.lean
```

You get plain synchronous Verilog: your registers, one wire per expression
node, one clocked block. The printed text is the verified compiler's output
(`Print.print (compile design)`) — the same functions the release artifacts
go through.

## 6. Check what you proved

In the file (or any file importing it):

```lean
#print axioms Machines.Tutorial.SatCounter.satOk_rtl
```

should report exactly `propext`, `Classical.choice`, `Quot.sound`.

### Optional: the symbolic-witness denotation

Since 2026-07-29 the printing gap can also be closed per design, without
any generated certificates: `Machines/Tutorial/SatCounterArtifact.lean`
proves `satcounter_denotes` — the emitted SSA witness denotes the
verified compilation at every wire, register, and output — as one
application of the generic theorem `toProgram_denotes` plus four
`by decide` facts (about 18 s of kernel reduction; see the file's
header for the two `set_option` bumps it needs). For a new design of
tutorial scale, copy that file and substitute your design name.

## What is and is not claimed

- **Claimed**: the invariant holds of every reachable state of the compiled
  module's transition semantics (`satOk_rtl`, kernel-checked, three-axiom
  closure), and the `.v` file is produced by printing exactly that compiled
  module. The compiler's correctness is proved once, centrally — your
  design added zero trusted lines and zero per-design compilation proofs.
- **Not claimed**: that the *printing* step is proved correct for your
  design (the printer is corroborated centrally — parser round-trip and
  simulator lockstep on the shipped artifacts — but `satOk_rtl` is a
  theorem about the compiled module, not about the text file); anything
  about what a synthesis tool does with the `.v`
  (`CONCRETE_SSA_BOUNDARY.md` states the tool-boundary assumption); and
  refinement against an ISS-style spec (expert territory; see
  `NEXTSTEPS.md`, "Leg 3 scoped").

## Report what went wrong

This tutorial is under an explicit falsification protocol: if you had to
leave this document — read library source, ask for help, guess a name —
that excursion is a documentation or library bug. Append it to
`Machines/Tutorial/DEFECTS.md` with what you expected and what happened.
The maintainers treat every entry as a defect report, not user error.
