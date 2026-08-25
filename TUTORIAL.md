# Loom tutorial

This tutorial takes one synchronous design from source to simulation, proof,
and neutral Verilog. The checked version is
[`Machines/Tutorial/SatCounter.lean`](Machines/Tutorial/SatCounter.lean).

## Build Loom

Install [Elan](https://lean-lang.org/lean4/doc/quickstart.html), then run:

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
lake build
```

No HDL tool is needed for Loom's semantics or proofs.

## Define hardware

Create `Counter.lean`:

```lean
import Loom.Hw.Dsl
open Loom.Hw Loom.Hw.Dsl

hardware counter where
  output reg count : 8
  output reg saturated : 1

  rule tick :=
    if count == 255 then
      saturated <- 1
    else
      count <- count + 1

#trace_cycle design with {} from { count := 254 }
#run_hardware design for 256 cycles
```

Run it with `lake env lean Counter.lean`.

A `hardware` block generates typed handles and one ordinary `Design`. Every
rule executes in source order each cycle. Reads see the state at the start of
the cycle; writes commit at the edge; the last write to one target wins. Width
errors and overflowing literals are rejected rather than truncated.

Use `input wire`, `reg`, `output reg`, and combinational `output wire` for the
usual capabilities. State machines and constants are concise:

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

The complete syntax reference is [`PRETTY.md`](PRETTY.md).

## Prove a property

Properties are predicates on `Design` state. Prove reset and preservation,
then use Loom's induction theorem. The checked example defines:

```lean
def SatOk (s : St) : Prop :=
  s.regs saturated.name 1 = 1#1 → s.regs count.name 8 = 255#8
```

[`satOk_invariant`](Machines/Tutorial/SatCounter.lean) uses
`Loom.TSys.Inductive.invariant`: one obligation proves `SatOk design.reset` and
the other proves that `design.cycle` preserves it. For larger designs, rule
footprints can reduce a cycle to only the rules that affect its coordinates.

Transport the invariant through the once-proved compiler simulation:

```lean
theorem design_wf : Compile.DesignWF design :=
  Compile.designWFCheck_sound design (by decide)

theorem satOk_rtl :
    (Compile.compile design).toTSys.Invariant
      (fun state => SatOk (Compile.forgetSt state)) :=
  (Compile.simulation design design_wf).invariant_pullback satOk_invariant
```

`satOk_rtl` concerns every reachable state of the compiled µVerilog module,
not a sample test.

## Test against an independent model

`#run_hardware` uses the certified Design-derived DAG evaluator. When a truly
independent reference model is useful, `Loom.Runner.run` can compare it against
every declared design coordinate. Missing oracle coordinates fail closed
unless explicitly excluded. See
[`Machines/Tutorial/SatCounterRun.lean`](Machines/Tutorial/SatCounterRun.lean)
for the small complete example.

## Emit Verilog

Keep the executable emitter in a separate file:

```lean
import Machines.Tutorial.SatCounter

def main : IO Unit :=
  Machines.Tutorial.SatCounter.design.emit "rtl/satcounter.v"
```

Run:

```console
lake env lean --run Machines/Tutorial/SatCounterEmit.lean
```

Emission is deterministic and fail-closed on malformed declarations, reads,
writes, memories, and names. Generic emission is technology-neutral; use a
target profile only when intentionally validating target-specific assumptions.

## Packed values

Packed structs are nominal, padding-free, MSB-first values and may nest:

```lean
packed struct Header where
  tag : 3
  address : 5

packed struct Packet where
  header : Header
  payload : 16
```

They work in inputs, registers, outputs, memories, and channels. Field reads
and writes introduce no cycle. Equal-width packed types remain distinct;
construct the destination type for a semantic conversion, or use explicit
`reinterpret value to Type` only when the protocol specifies identical bits.

## Multiple clock domains

Keep cycle-sensitive logic inside ordinary single-clock islands. Communicate
between islands with typed channels and choose a realization separately:

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

Loom checks topology and realization, generates the endpoints and portable CDC
logic, and lets existing island invariants lift over admitted schedules. It
also emits crossing, timing, reset, and physical-obligation inventories.
Physical timing closure and metastability remain downstream responsibilities.
See [`MULTICLOCK.md`](MULTICLOCK.md).

## Know the boundary

Loom proves source semantics, compiler preservation, and selected exact RTL
bytes. It does not prove synthesis, place-and-route, external IP, timing,
electrical reset, or silicon. Start with [`TCB.md`](TCB.md) and check the
current gates in [`STATUS.md`](STATUS.md) before making a release claim.
