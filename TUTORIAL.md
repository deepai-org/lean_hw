# From a hardware design to proved, emitted RTL

This document assumes you can read basic Verilog and that you know Lean 4 is
a theorem prover — nothing else. It walks one small design from an empty
file to an emitted `.v`, a certified Design-derived execution, an optional
independent differential check, and a machine-checked theorem about every
reachable state of the compiled µVerilog transition system. The final section
explains how to take that neutral RTL into an FPGA or ASIC flow without
confusing external evidence with the theorem.

**The exact promise.** At the end you hold a theorem that your property holds
in every reachable state of `Compile.compile design`, inherited through the
compiler's once-proved correctness theorem. The axioms under it are exactly
Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`). The
separate text boundary between that formal module and the emitted Verilog is
stated explicitly rather than silently folded into the claim.

The finished design is checked into the repo at
`Machines/Tutorial/SatCounter.lean`. Its optional independent reference run is
in `Machines/Tutorial/SatCounterRun.lean`. Both are built by CI, so the code
below cannot drift from the library. If any step fails for you, that is a bug
in the library or this document — see the last section.

## 0. Thirty seconds of Lean

Everything below is readable with five facts:

- `def name : Type := value` defines a value, like a `localparam` that can
  hold anything — including an entire hardware design.
- `theorem name : Statement := proof` is a definition whose *type* is the
  claim and whose *value* is the evidence. If it compiles, the claim holds.
- `by ...` enters tactic mode: instead of writing the evidence directly, you
  issue proof commands (`intro`, `simp`, `decide`, ...) that construct it.
  Each tactic used below is explained where it first appears.
- Commands beginning with `#`, such as `#run_hardware`, inspect or execute a
  value while Lean checks the file. `#eval` executes an ordinary Lean program;
  a thrown error fails the build.

## 1. Setup

From the repo root (the pinned toolchain downloads itself via elan):

```console
lake build Loom.Hw.Dsl Loom.Hw.CompileCorrect Loom.Emit.MicroVerilog.Print
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
import Loom.Hw.Dsl
import Loom.Hw.Semantics
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print

namespace Machines.Tutorial.SatCounter

open Loom.Hw
open Loom.Hw.Dsl

hardware satcounter where
  output reg count : 8
  output reg sat : 1

  rule tick :=
    if count == 255 then
      sat <- 1
    else
      count <- count + 1
```

Read it against the Verilog. A design contains declarations and a visibly
ordered list of named rules. Every rule runs every cycle; a rule is not an
implicitly scheduled or atomic Bluespec rule. **All reads observe the
start-of-cycle state, writes commit at the edge, and the last executed write
to one target wins.** `<-` is therefore the only state-assignment spelling.
`:=` defines declarations and rules; `==` compares hardware values.

Two things have no Verilog counterpart:

- The width after `:` becomes the width in the generated `Reg` type. A width
  mismatch is a Lean type error. Numeric literals acquire that expected width
  and are rejected if they do not fit; they never silently truncate.
- `output reg` makes the state an output port. Plain `reg` is internal state.
  The command generates the typed handles, declarations, rule values, and the
  final `design`; there is no parallel hidden representation.

## 3. Watch the Design-derived simulator run

The normal execution path is generated from the `Design` itself and is proved
to agree with `Design.run` on every declared coordinate. Add this after the
hardware block, or use it from a small importing file:

```lean
#run_hardware design for 256 cycles
```

It prints:

```text
after 256 cycles:
  count = 255
  sat = 1
```

This uses Loom's certified shared-DAG simulator. Its run theorem connects the
optimized execution to the same `Design` semantics used below; you do not
write a second cycle implementation merely to run the hardware. For a
single-cycle explanation, including which writes fired and their old and new
values, use:

```lean
#trace_cycle design with {} from { count := 254 }
```

which reports the `count` write from 254 to 255. This is especially useful for
seeing start-of-cycle reads and last-write-wins ordering.

An independent reference model remains valuable when it expresses a genuinely
separate specification. The checked-in optional differential example is
`Machines/Tutorial/SatCounterRun.lean`:

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

The runner steps both worlds and compares every declared coordinate. Because
the `#eval` runs at build time, a divergence **fails the build** with the cycle
number and offending coordinate:

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
on a condition — note it mirrors the `if` in the rule, which is the shape
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

Put the executable wrapper in a separate file so importing the reusable
Design does not inject a root-level `main` into another program:

```lean
import Machines.Tutorial.SatCounter

def main : IO Unit :=
  Machines.Tutorial.SatCounter.design.emit "rtl/satcounter.v"
```

```console
lake env lean --run Machines/Tutorial/SatCounterEmit.lean
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

Every `output reg` became an `o_*` port; nothing else did.
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

## 7. Into an FPGA or ASIC flow

The emitted module is technology-neutral. Generic `Design.emit` does not
choose an FPGA family, ASIC library, memory profile, or synthesis producer.
Use `emitFor` only when you deliberately want Loom to validate against an
explicit target evidence profile.

Keep four claim layers separate:

1. `satOk_invariant` is a theorem about the source `Design` semantics.
2. `satOk_rtl` transports it to the compiled µVerilog transition system.
3. Rendering gives deterministic Verilog text. The exact text-semantics
   assumption is documented in `CONCRETE_SSA_BOUNDARY.md`; selected release
   artifacts additionally carry byte-exact theorem bindings.
4. Synthesis, technology mapping, timing closure, reset delivery, placement,
   configuration, and physics are target-specific external evidence.

That fourth layer is equally external for FPGA and ASIC use. Loom currently
has no post-synthesis equivalence theorem and does not prove that a particular
tool, cell library, RAM macro, bitstream, or manufactured device preserves the
RTL.

Treat generated RTL as a build product with one producer. Do not hand-edit
`rtl/satcounter.v`; change the `Design`, recheck the proof, and re-emit. A
board or chip wrapper may add clocks, reset conditioning, pins, scan, power
intent, memories, or debug, but those additions are outside this counter's
theorem unless separately modeled.

Make external observations attributable:

- record the exact source RTL and design revision used by each downstream
  artifact;
- fail when generated artifacts are stale or a producing command exits without
  a useful diagnostic;
- make deployed images self-identifying where practical; and
- health-check debug or readback transports before treating their values as
  evidence.

The same independent oracle from step 3 can compare RTL simulation or hardware
observations, provided the adapter accounts for every declared coordinate.
That comparison is useful evidence; it does not replace the universal theorem.

## 8. Add states and structured values

The counter used only scalar registers. Real designs can keep intent in the
type instead of encoding everything as anonymous vectors.

A declared state family chooses the minimum width and generates named values
and case lemmas:

```lean
hardware controller where
  const COMMAND : 7 := 72
  output states mode : { Idle, Run, Done } := Idle

  rule advance :=
    case mode of
    | Idle => mode <- Run
    | Run  => mode <- Done
    | Done => mode <- Idle
```

Packed values may contain earlier packed values:

```lean
packed struct Header where
  tag : 3
  address : 5

packed struct Packet where
  header : Header
  payload : 16

hardware packet_register where
  input wire incoming : Packet
  output reg pending : Packet

  rule capture := {
    pending.header <- incoming.header,
    pending.payload <- incoming.payload
  }
```

This lowers to one padding-free flat vector; nesting and field assignment add
no cycle. Every right-hand side still reads pre-cycle state. The packed type
survives through registers, inputs, outputs, memories, and channels, so an
unrelated equal-width type cannot be assigned accidentally.

Use destination construction when meanings are being mapped. Use
`reinterpret value to Destination` only when the protocol says the complete
bit representation is identical. `reinterpret` requires equal widths and
adds no hardware; it is never an implicit cast, truncation, or extension.

The complete authoring contract—including operator precedence, register-family
indexing, lints, and intentional omissions—is in `PRETTY.md`.

## 9. Compose clock domains without changing island proofs

Keep latency-sensitive logic inside ordinary synchronous islands. Cross an
island boundary through a typed channel and select its physical realization
separately:

```lean
system twoClock where
  clock clkA
  clock clkB
  clocks Clock.asynchronous
  reset Reset.together
  channel q : 8 depth 2

  island producer on clkA where
    output reg sent : 1
    rule transmit :=
      if ~sent then
        send 42 to q then sent <- 1

  island consumer on clkB where
    output reg got : 8
    rule accept :=
      receive value from q then got <- value

  connect q from producer to consumer
  realize q with Cdc.grayFifo
```

Loom generates and checks the endpoint adapters, compiled FIFO controls,
synchronizer stages, portable storage, crossing inventory, timing description,
and neutral physical requirements. Island invariants are still proved on the
ordinary `Design`; `system_lift` transports them across every admitted clock
schedule.

Channel latency is not hidden. Inspect it with `#show_system twoClock timing`.
The current conservative sink can consume at most once per two destination
ticks under continuous traffic, and an asynchronous schedule supplies no
finite delivery bound without an explicit progress premise. A downstream
physical backend must separately discharge every generated timing, reset, and
CDC obligation.

Start with `MULTICLOCK.md` before using independent reset recovery or a custom
FPGA/ASIC binding. `MULTICLOCK_BOUNDARY.md` states exactly where the digital
proof ends.

## 10. What you now have

- A design stated once, with widths, capabilities, and structured values
  checked at the authoring boundary.
- A certified executable view derived from that design.
- An optional independent differential with fail-closed coordinate coverage.
- A kernel-checked invariant transported to the compiled transition system.
- Deterministic neutral Verilog plus an explicit text and physical boundary.
- A path to multiclock composition that preserves ordinary island proofs.

The working loop is: edit the design → run inspection and focused tests →
recheck proofs → emit deterministic RTL → run target-specific implementation
and evidence checks. Each stage states what it established and what remains an
assumption.

Refinement against a full instruction-set specification uses the same shape
with larger proofs; the LNP64-µ development under `Machines/Lnp64u/` is the
in-repository example. Start smaller than you think—the counter is the honest
template.

## Report a tutorial defect

If following this document requires guessing an API name or reading library
internals, record the unresolved excursion in
`Machines/Tutorial/DEFECTS.md`: the command that failed, what you expected, and
the smallest documentation or API change that would have prevented it.
