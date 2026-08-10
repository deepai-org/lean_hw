# From Verilog to a proved design, and onto an FPGA

This document assumes you can read basic Verilog and that you know Lean 4 is
a theorem prover — nothing else. It walks one small design from an empty
file to: an emitted `.v` you could hand to any synthesis tool, a build-time
differential check against a reference model, a machine-checked theorem
about every reachable state of the compiled RTL, and the discipline for
taking the result onto an FPGA without losing track of what you actually
know.

**The exact promise.** At the end you hold a theorem that your property
holds in *every reachable state of the compiled RTL* — not of your model, of
the compilation — inherited through the compiler's once-proved correctness
theorem. The axioms under it are exactly Lean's three standard ones
(`propext`, `Classical.choice`, `Quot.sound`). No simulation waveform, no
"we ran it a lot": a proof, checked by the same kernel that checks
mathematics.

The finished files are checked into the repo at
`Machines/Tutorial/SatCounter.lean` and `Machines/Tutorial/SatCounterRun.lean`
and are built by CI, so the code below cannot drift from the library. If any
step fails for you, that is a bug in the library or this document — see the
last section.

## 0. Thirty seconds of Lean

Everything below is readable with five facts:

- `def name : Type := value` defines a value, like a `localparam` that can
  hold anything — including an entire hardware design.
- `⟨"count"⟩` builds a structure from its fields; here, a register handle
  from its name.
- `theorem name : Statement := proof` is a definition whose *type* is the
  claim and whose *value* is the evidence. If it compiles, the claim holds.
- `by ...` enters tactic mode: instead of writing the evidence directly, you
  issue proof commands (`intro`, `simp`, `decide`, ...) that construct it.
  Each tactic used below is explained where it first appears.
- `#eval expr` runs code at compile time and prints the result. We use it to
  execute a differential test *during the build*, so a regression fails the
  build.

## 1. Setup

From the repo root (the pinned toolchain downloads itself via elan):

```console
lake build Loom.Hw.CompileCorrect Loom.Emit.MicroVerilog.Print
```

The first build of a fresh clone compiles the dependencies; give it a few
minutes. Everything after is incremental.

## 2. The design

Create `Machines/Tutorial/SatCounter.lean` (any module under `Machines/` is
picked up by the build automatically). We build a saturating counter: count
up; at 255, raise a sticky flag. In Verilog you would write:

```verilog
always @(posedge clk) begin
  if (count == 8'd255) sat   <= 1'b1;
  else                 count <= count + 8'd1;
end
```

In Loom, the same design is a Lean value:

```lean
import Loom.Hw.Declarations
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print

namespace Machines.Tutorial.SatCounter

open Loom.Hw
open Loom.Hw.Notation

def count : Reg 8 := ⟨"count"⟩
def sat : Reg 1 := ⟨"sat"⟩

def tick : Act :=
  ifA count.rd === 255 then
    sat ⇐ 1
  else
    count ⇐ count.rd + 1

def declarations : Declarations :=
  Declarations.empty
    |>.addReg count (exported := true)
    |>.addReg sat (exported := true)

def design : Design :=
  Design.ofDecls "satcounter" declarations [⟨"tick", tick⟩]
```

Read it against the Verilog. A design is registers + memories + a list of
named rules. Rules run every cycle; **reads observe the pre-cycle state and
writes commit at the cycle edge, last write wins** — ordinary nonblocking
semantics, stated once as the language's meaning rather than re-learned per
always-block. `⇐` is `<=`, `ifA ... then ... else` is the procedural `if`,
`===` is comparison (spelled distinctly because `=` is Lean's own equality).

Two things have no Verilog counterpart:

- `Reg 8` carries the width in the *type*. A width mismatch is a compile
  error in the type checker, and each register's name is written exactly
  once — the declaration, the reads, the writes, the reset entry, and the
  output port below are all derived from the same handle.
- `exported := true` declares an output port. Policy is explicit: state you
  do not export is not observable, and you will want `count` and `sat`
  observable on the board later. Decide observability at design time, not
  after the bitstream exists.

## 3. Watch it run — against a reference model, during the build

Before proving anything, check the design does what you meant. The habit
that scales: never eyeball waveforms; write an independent **reference
model** (what a testbench golden model is in Verilog, except here it is
five lines of ordinary code) and compare *every declared coordinate, every
cycle*. Create `Machines/Tutorial/SatCounterRun.lean`:

```lean
import Machines.Tutorial.SatCounter
import Loom.Hw.Diff

namespace Machines.Tutorial.SatCounterRun

open Loom.Hw Machines.Tutorial.SatCounter

structure Ref where
  count : Nat := 0
  sat   : Bool := false

def Ref.step (r : Ref) : Ref :=
  if r.count = 255 then { r with sat := true }
  else { r with count := r.count + 1 }

def oracle (r : Ref) : Oracle where
  read := fun c =>
    if c.kind = "reg" && c.name = "count" then some r.count
    else if c.kind = "reg" && c.name = "sat" then some (if r.sat then 1 else 0)
    else none

#eval do
  let result ← Loom.Runner.run { label := "satcounter vs reference", steps := 300 }
    (design.reset, ({} : Ref)) fun _ s => do
      let hw := design.cycle s.1
      let ref := s.2.step
      return ((hw, ref), design.sampleAgainstOracle 8 hw (oracle ref))
  result.requirePass

end Machines.Tutorial.SatCounterRun
```

`design.cycle` is the design's own semantics — the same function the
theorems below are about, executed. The runner steps both worlds and
compares; because the `#eval` runs at build time, a divergence **fails the
build** with the cycle number and the offending coordinate:

```text
satcounter vs reference: RESULT PASS steps=300 mismatches=0 coverage_gaps=0 excluded=0
```

The part that is deliberately strict: comparison coverage is derived from
the design's declarations, **fail-closed**. Delete the `sat` line from the
oracle and rerun — you do not get a quieter test, you get:

```text
  coverage-gap step 6 sat
satcounter vs reference: RESULT FAIL ... coverage_gaps=1
```

A coordinate your oracle silently fails to model is a *failure*, not a
blind spot. If a coordinate is genuinely out of scope, say so —
`unmodelled := ["sat"]` in the oracle — and it is accounted as an honest,
named exclusion (`excluded=1`) instead. The distinction sounds pedantic
until the coordinate nobody modelled is the one carrying the bug; in this
repository's own history it was a bus qualifier that no hand-written
checklist had ever included.

## 4. The property, proved on the model

The flag must only rise at saturation. First state it — a predicate on the
design state `St`, whose register file is read by name and width:

```lean
def SatOk (σ : St) : Prop :=
  σ.regs sat.name 1 = 1#1 → σ.regs count.name 8 = 255#8
```

(`1#1` is the 1-bit literal 1; `→` is implication: *if* the flag is up,
the counter reads 255.)

Now the proof, by induction over cycles: the property holds at reset, and
one cycle preserves it. This is the one section requiring real tactic work,
so the tactics are glossed as they appear.

```lean
theorem satOk_invariant : design.toTSys.Invariant SatOk := by
  apply Loom.TSys.Inductive.invariant
  constructor
  · -- reset: the flag starts at zero
    intro s hinit
    simp only [Design.toTSys_init_iff] at hinit
    subst hinit
    intro hsat
    simp [Design.reset, design, declarations, sat, RegEnv.set] at hsat
  · -- step: one cycle preserves the property
    intro s s' hP hstep
    simp only [Design.toTSys_step_iff] at hstep
    subst hstep
    by_cases hc : s.regs count.name 8 = 255#8
    · -- saturated: the rule writes `sat`, leaves `count` unchanged
      simp only [count] at hc
      intro _
      simp [Design.cycle, design, declarations, tick, Reg.rd, Reg.set,
        Act.run, Expr.eval, count, sat, RegEnv.set, hc]
    · -- not saturated: the rule writes `count`, leaves `sat` unchanged
      simp only [count] at hc
      intro hsat
      have hsat' : s.regs sat.name 1 = 1#1 := by
        simpa [Design.cycle, design, declarations, tick, Reg.rd, Reg.set,
          Act.run, Expr.eval, count, sat, RegEnv.set, hc] using hsat
      exact absurd (hP hsat') hc
```

Tactic gloss: `apply` uses a library lemma (here: "inductive implies
invariant"); `constructor` splits the two obligations; `intro` names
hypotheses; `subst` rewrites with an equality hypothesis; `by_cases` splits
on a condition — note it mirrors the `ifA` in the rule, which is the shape
most hardware proofs take; `simp [...]` simplifies with the listed
definitions; `have` states an intermediate fact; `exact absurd ...` closes
a contradictory branch.

The opening two lines of each branch are boilerplate: `toTSys_init_iff` /
`toTSys_step_iff` turn the abstract init/step hypotheses into concrete
equalities (`s = design.reset`, `design.cycle s = s'`) that `subst` can
consume.

The one recipe that matters: **put your own definitions in the simp set**
(`design`, `declarations`, your rule, and the typed handles). `Design.cycle`
folds the rule list, and until your definitions are unfolded the goal is a
raw `List.foldl` — if you see one, you forgot a definition, not a lemma.
With them, `simp` computes the cycle like the simulator just did in
step 3 — the proof and the run are the same semantics, which is why passing
the differential first makes this proof unsurprising.

For designs with many rules, the library also derives *footprints*: which
rules can touch which state. An invariant about two registers of a
21-rule machine can be proved against a reduced cycle containing only their
writers, with a proved-equal observation. At this tutorial's scale the full
cycle is already small; know the facility exists before your design grows.

## 5. Transport to the RTL

The compiler is verified once, centrally; its side conditions are decidable,
so discharging them for a concrete design is `by decide` (a tactic that runs
a decision procedure and checks the result in the kernel):

```lean
theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

theorem satOk_rtl :
    (Compile.compile design).toTSys.Invariant
      (fun state => SatOk (Compile.forgetSt state)) :=
  (Compile.simulation design design_wf).invariant_pullback satOk_invariant
```

Read `satOk_rtl`'s statement: every reachable state of the **compiled
module** satisfies `SatOk` of its registers. `Compile.simulation` is the
once-proved forward simulation; `invariant_pullback` carries any model
invariant across it. Nothing here is per-design — you will never write a
proof about the compilation itself.

## 6. Emit the Verilog

Add a `main` at the root level, **outside the namespace**, then run the
file:

```lean
end Machines.Tutorial.SatCounter

def main : IO Unit :=
  Machines.Tutorial.SatCounter.design.emit "rtl/satcounter.v"
```

```console
lake env lean --run Machines/Tutorial/SatCounter.lean
```

The output is plain synchronous Verilog — your registers, one explicitly
sized wire per expression node, one clocked block with reset:

```verilog
module satcounter(
  input wire clk,
  input wire rst,
  output wire [7:0] o_count,
  output wire [0:0] o_sat
);
```

Every `exported` register became an `o_*` port; nothing else did.
`Design.emit` is also a gate, not just a printer: duplicate names,
reads of undeclared state, undeclared synchronous-read memories, and
malformed write ports are *rejected at emission* — an obligation the caller
cannot skip. Emission is deterministic: re-emitting an unchanged design
reports `unchanged` and rewrites nothing, which matters below.

Check what you proved, from any file:

```lean
#print axioms Machines.Tutorial.SatCounter.satOk_rtl
```

should report exactly `propext`, `Classical.choice`, `Quot.sound`.

## 7. Onto an FPGA — the discipline

Nothing in this section is vendor-specific; it is the shape of the
boundary, and the practices that keep evidence trustworthy across it.

**Know where the theorem stops.** Proved: the invariant, of every reachable
state of the compiled module. Corroborated but not proved per-design: that
the printed text means that module (the printer is checked centrally by
parser round-trip and simulator lockstep on shipped artifacts). Assumed:
that your synthesis tool implements the standard meaning of the emitted
subset — sized wires, one positive-edge block, synchronous reset. Entirely
outside: place-and-route, timing closure, configuration, electrons. From
here on you are collecting *evidence*, not extending the theorem — the goal
is that the evidence be attributable and hard to fool.

**Wrap, don't touch.** The emitted module is a leaf. Board-specific
material — clock generation, reset conditioning, pin constraints, clock
domain crossings, debug transports — lives in a small hand-written top that
instantiates it:

```verilog
module board_top(input wire board_clk, input wire board_rst_n, ...);
  wire [7:0] count_view;
  satcounter u_dut(
    .clk(clk_buffered), .rst(rst_sync),
    .o_count(count_view), .o_sat(sat_led)
  );
  // clocking, reset synchronizer, pin mapping: yours, and untrusted
endmodule
```

Never hand-edit `rtl/satcounter.v`. If the wrapper needs something the
module doesn't expose, that is a design change: add the export in Lean,
re-prove (usually: nothing to redo — exports don't change semantics), and
re-emit. The generated file is a build product with exactly one producer.

**Give every artifact an identity, and every observation a provenance.**
The failure mode that wastes weeks is not a wrong design; it is a *stale*
one — yesterday's bitstream, an old image in memory, a debug readback from
the previous run — silently read as today's. Practices this repository
treats as mandatory, all of them cheap:

- Record, next to every bitstream, the hash of the exact `.v` (and design
  revision) it was built from. Deterministic emission makes this
  meaningful; the repo's script layer maintains such manifests and fails
  loudly when an artifact is stale or a producer dies silently.
- Make the design *self-identifying* on the board: reserve an output or a
  first console action that reports a build stamp. An observation that
  cannot name the artifact that produced it is not evidence.
- Health-check the debug channel before believing it. Readback paths
  degrade; the classic symptom is one stale value returned for every
  address. Read a few locations that must differ, and refuse the data if
  they don't. Loud beats plausible.
- Clear observation buffers between runs, so a fresh boot cannot replay the
  previous run's success text. (This repository learned that one the hard
  way.)

**Generate the observability, both halves.** You exported `count` and `sat`
in step 2; on a board they typically surface through a debug read port in
the wrapper. Loom generates that plumbing from a declared tap list — the
wrapper-side decode *and* the host-side reader script from the same
declaration, plus sticky first-event captures ("latch the first time this
predicate fires, optionally halt") for should-never-happen conditions.
Hand-wired debug decode is where read maps drift; a generated map cannot
disagree with its reader, and its checker refuses to emit taps for signals
the design no longer exports. Debug instrumentation is explicitly outside
the theorem — the tooling labels it as such — but outside-the-theorem does
not mean sloppy.

**Keep the differential loop alive on silicon.** Step 3's reference model
does not retire when the bitstream exists: the same oracle that checked the
simulated design checks board readbacks. When board and model disagree,
you now have three worlds — model, RTL simulation, silicon — and the
discipline above tells you which pair diverged and which artifact was
involved. Most "hardware bugs" die at that triage step, identified as a
stale artifact, an untrusted readback, or a wrapper mistake — each of which
the practices above catch by construction rather than by heroics.

## 8. What you have, and the loop you now own

- A design stated once, in a form a type checker guards.
- A build-time differential against an independent model, with fail-closed
  coverage — every declared coordinate compared or honestly excluded.
- A kernel-checked invariant of the compiled RTL, three-axiom closure,
  zero per-design trusted lines.
- Emitted Verilog with exactly one producer, an identity, and a wrapper
  discipline that keeps the proved leaf intact on a board.

The working loop, from here: edit the design → the emit gate and type
checker catch structural mistakes → the build-time differential catches
semantic ones → proofs re-check → re-emit (bytes change only if meaning
did) → re-synthesize → observe on the board with provenance. Each stage
catches what the previous one cannot, and nothing in the loop asks you to
trust a tool this repository could have checked instead.

Refinement against a full instruction-set specification — proving a
processor *implements a program-visible machine* — is the same workflow
with much larger proofs; the LNP64-µ development under `Machines/Lnp64u/`
is the in-repo evidence that the path continues. Start smaller than you
think; this counter is the honest template.

## Report what went wrong

This tutorial is under an explicit falsification protocol: if you had to
leave this document — read library source, ask for help, guess a name —
that excursion is a documentation or library bug, not user error. Add an
entry to the defects ledger kept beside the tutorial files in
`Machines/Tutorial/`, stating what you expected and what happened. Every
entry is treated as a defect report.
