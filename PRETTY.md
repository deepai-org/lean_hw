# Loom hardware syntax

Loom's readable syntax is a thin authoring layer over the public `Expr`, `Act`,
`Reg`, `Mem`, `Design`, and `System` values. It adds no second semantics: the
generated values are consumed by the same evaluator, proofs, compiler, and
emitter as hand-built designs.

Import it with:

```lean
import Loom.Hw.Dsl
open Loom.Hw Loom.Hw.Dsl
```

## Hardware blocks

```lean
hardware example where
  input wire enable : 1
  output reg count : 8 := 0
  output wire done : 1 := count == 255
  reg scratch : 8
  const STEP : 8 := 1
  states phase : { Idle, Run, Done } := Idle

  rule count_up :=
    if enable & (phase == Run) then {
      count <- count + STEP
      scratch <- count
    }
```

Declarations precede rules. Every rule executes each cycle in source order.
All right-hand sides read pre-cycle state; writes commit at the edge; later
writes to an overlapping target win. Consequently `scratch <- count` above
reads the old `count`.

The common declarations are:

```text
input wire name : width
reg name : width [:= reset]
output reg name : width [:= reset]
output wire name : width := expression
const name : width := value
states name : { A, B, C } [:= A]
memory name : dataWidth [depth] [using Memory.synchronousRead]
```

Widths, depths, and generated collections may be reducible Lean `Nat` values.
Widths must be positive. Literals accept decimal, `0x` hex, `0b` binary, and
underscores; they are range-checked and never silently truncated. Design-local
`const` and `states` names are preferred for ordinary constants. Shared
cross-design constants may opt into `@[hw_const]`.

## Expressions

The principal forms are literals, signal names, parentheses, `$(leanTerm)`,
field projection, static bit/slice selection, memory reads, muxes, extensions,
and these operators:

| Tight to loose | Forms | Notes |
| --- | --- | --- |
| postfix | `.field`, `[bit]`, `[hi:lo]`, indices | static selects |
| prefix | `~x`, `zext x to w`, `sext x to w`, `reinterpret x to T` | postfix binds first |
| multiply | `*`, `/`, `%` | equal-width operands/result |
| add | `+`, `-` | equal-width operands/result |
| shift | `<<`, `>>` | logical; result has left width |
| concatenate | `++` | high bits on the left |
| bitwise | `&`, then `^`, then `|` | equal-width operands |
| compare | `==`, `<u`, `<s` | non-associative; 1-bit result |
| mux | `if c then a else b` | 1-bit condition |

Arithmetic binds before comparison, so `a + b == c` is valid. Loom requires
parentheses when mixing comparison with bitwise operations, shifts with
arithmetic, or concatenation with another infix family. Comparison chains such
as `a <u b <u c` are rejected. There is no unary minus or arithmetic right
shift syntax. A shift amount at least the value width produces zero.

Static shift amounts may be ordinary reducible constants (`x << 3`). Dynamic
amounts are hardware expressions and receive a cost warning because they may
infer a barrel shifter.

## Statements

```text
reg <- expression
packedReg.field <- expression
mem[port n, address] <- expression
if condition then statement [else statement]
case expression of | value => statement | default => statement
{ statement ... }
let name [: width] := expression
for i in $(values) generate statement
skip
$stmt(leanAct)
```

`let` is notation for an expression, not a register, wire, net, or sharing
promise. Use an `output wire` when a named observable combinational signal is
intended.

Static register families accept literal indices and reducible `Fin n` values.
A hardware `Expr` index selects dynamically. Memory port numbers are static
and checked for legal ordering.

## Channels

Application code uses behavioral endpoints rather than raw valid/ready wires:

| Form | Meaning on the island's current tick |
| --- | --- |
| `q.canSend` | source endpoint can accept a payload |
| `send x to q then body` | if accepted, send once and run `body` |
| `send x to q` | best-effort send; warns unless visibly guarded |
| `q.hasData` | a valid sink payload is visible |
| `q.data` | visible payload; meaningful only with `hasData` |
| `receive x from q then body` | bind, run `body`, and consume once |
| `consume q` | consume the visible payload if present |

At most one possible send and one possible consume per endpoint is allowed in
an event. Alternative branches are fine; sequential duplicates or duplicates
across rules are rejected. Parameterized expert actions use the proof-carrying
`EndpointAct` builders rather than hiding endpoint effects in opaque `Act`s.

## Packed structs

```lean
packed struct Header where
  tag : 3
  address : 5

packed struct Packet where
  header : Header
  payload : 16
```

Layouts are checked, padding-free, and first-field-MSB. Fields may themselves
be packed structs; projections and register-field writes compose through any
nesting depth while lowering to one flat vector. Packed types work in inputs,
registers, outputs, memories, and channels.

```lean
Packet {
  header := Header { tag := 1, address := addr }
  payload := data
}

packet.header.tag
packet.bits
Packet.fromBits raw
reinterpret packet to WireCompatiblePacket
```

Equal-width packed types are nominally distinct. Construct the destination
record when fields have semantic meaning. `reinterpret` is an explicit,
equal-width, zero-logic bit-identity conversion; it does not truncate, extend,
or create general assignment compatibility. Whole-memory elements are
writable; packed memory field read-modify-write is intentionally not implicit.

## Systems

```lean
system twoClock where
  clock clkA
  clock clkB
  clocks Clock.asynchronous
  reset Reset.together
  channel q : 8 depth 2

  island producer on clkA where
    output reg sent : 1
    rule tx := send 42 to q then sent <- 1

  island consumer on clkB where
    output reg got : 8
    rule rx := receive value from q then got <- value

  connect q from producer to consumer
  realize q with Cdc.grayFifo
```

The stock clock relations are `Clock.asynchronous` (coincident edges allowed),
`Clock.interleaved` (at most one clock per event), `Clock.aligned`, and
`Clock.alignGroups`. Alignment constrains proof schedules; it does not certify
a physical clock relationship or permit a same-clock FIFO between differently
named clocks.

The stock reset policies are `Reset.together` and the advanced
`Reset.independentFlush`. The stock realization names are
`Cdc.synchronousFifo`, `Cdc.grayFifo`, and `Cdc.recoverableGrayFifo`.
Every connected channel must be realized exactly once before emission. See
[`MULTICLOCK.md`](MULTICLOCK.md) for timing, recovery, proofs, and physical
obligations.

## Diagnostics and inspection

The authoring layer rejects duplicate or undeclared names, width and literal
errors, invalid reads/writes, malformed memory ports, incomplete realizations,
and endpoint transaction conflicts. Informational lints cover:

- reading state after writing it in the same cycle;
- overlapping writes and last-write-wins behavior;
- unguarded channel data or best-effort sends; and
- potentially expensive dynamic hardware.

Intentional cases use one visible suppression form with a nonempty reason:

```lean
suppress multiple_write because "pulse default overridden by later rule" in
  pulse <- 0
```

Useful checked commands include:

```lean
#trace_cycle design with {} from { count := 41 }
#run_hardware design for 10 cycles
#show_hardware design
#show_system twoClock
```

Inspection is a derived view. If Loom cannot faithfully reconstruct pretty
syntax, it falls back visibly to core notation instead of inventing source.

## Deliberate boundaries

The syntax does not infer interface widths, silently cast packed values,
create implicit CDCs, choose target technology, or hide timing. Arbitrary Lean
remains available through typed `$(term)` and `$stmt(term)` escapes; structural
and certification checks still apply after lowering.

Executable examples and negative diagnostics live in
[`Tests/PrettyDsl.lean`](Tests/PrettyDsl.lean); the end-to-end beginner example
is [`Machines/Acc8/Core.lean`](Machines/Acc8/Core.lean).
