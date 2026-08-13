# Pretty Loom hardware DSL

This document is the implementation plan for a readable, beginner-friendly
authoring layer over Loom's existing hardware EDSL. The destination is concise
hardware code that remains an ordinary shallow embedding: syntax elaborates to
the current `Expr`, `Act`, `Reg`, `Mem`, `Declarations`, and `Design` values,
and the kernel, semantics, compiler, verified simulators, and emission boundary
do not acquire a second representation.

This is only a syntax and presentation plan. Its permitted work is grammar,
elaboration into existing public Loom values, generated declarations and
metadata, source-local diagnostics, faithful delaboration/inspection, and
migration tests that prove the lowering changed no hardware. It does not plan
new channel semantics, CDC circuits, runners, proof foundations, compiler
passes, emitters, or evidence models. When a proposed pretty construct needs a
core capability Loom does not already provide, the surface rejects or defers
that construct and records the dependency in the owning core plan.

Small authoring facades named below—such as the read-only `Input` handle,
`addWireInput`, ordered `actFor` fold, and discoverable reset/realization library
aliases—are in scope only as definitional wrappers over existing public values,
`Design` fields, and `Act.seq`; they may not introduce a new transition or
emission behavior.

The purpose is not to accept or imitate Verilog. It is to make cycle semantics
hard to misread, including for a junior hardware engineer. Hardware nouns and
concepts remain familiar—inputs, outputs, registers, memories, rules, widths,
ports, cycles, bit selects, and slices—but Verilog punctuation survives only
when its familiar reading is exactly Loom's meaning. Loom uses rules instead
of event controls, one explicit next-cycle assignment, explicit signedness,
typed widths, and ordinary Lean as the parameterization language.

The scope includes named multiclock `System`s, but not as an opaque connectivity
language above hidden RTL. Multiclock authoring has three progressively
disclosed levels:

1. the architecture names clocks, ordinary `Design` islands, typed logical
   channels, endpoint direction, and admissible clock relations;
2. an explicit realization selects the actual synthesizable crossing circuit;
3. optional physical evidence consumes the generated neutral intent and may
   bind technology-specific synchronizers or memories while stating every
   external assumption.

The architecture block need not repeat Gray equations, synchronizer registers,
flags, storage ports, or controllers. Those behavioral components are still
ordinary, public, pretty-printable `Design`s—not secret backend machinery—and
an expert can inspect or replace them. Only proof plumbing, generated structural
coordinates, wrappers, and tool constraints remain implementation details.
Names from the mechanical API such as `portableAsync`,
`CertifiedPortableBinding`, `PhysicalLeaf`, `ResetIntent`, and
`PhysicalCheckReport` do not become beginner syntax merely because they are
public Lean definitions. The surface uses hardware vocabulary; inspection
commands reveal the exact underlying values and generated hardware on demand.

## Outcome

The tutorial's saturating counter should eventually read:

```lean
import Loom.Hw.Dsl

namespace Machines.Tutorial.SatCounter

open Loom.Hw

hardware satcounter where
  output reg count : 8
  output reg sat : 1

  rule tick :=
    if count == 255 then
      sat <- 1
    else
      count <- count + 1

end Machines.Tutorial.SatCounter
```

The command generates definitions in the current Lean namespace:

```lean
count        : Reg 8
sat          : Reg 1
tick         : Act
declarations : Declarations
design       : Design
```

The identifier after `hardware` is only the emitted module name passed to
`Design.ofDecls`; it does not open a Lean namespace. Consequently the existing
proofs and emit call continue to refer to
`Machines.Tutorial.SatCounter.count`, `.tick`, and `.design` exactly as before.

The single-source pipeline remains:

```text
pretty hardware source
        |
        v
unchanged Loom Design
   |         |                  |
   v         v                  v
semantics  proved FastEval/   checked micro-Verilog
and proofs DagEval simulator  and Verilog emission
                                   |
                                   v
                          external FPGA toolchain
                                   |
                                   v
                               bitstream
```

There is no second handwritten cycle implementation. `FastEval` and `DagEval`
remain the generated, proved executable forms of the same `Design`. A separate
architectural model or reference model remains useful when it is genuinely an
independent specification, but it is not required merely to execute a design
or produce RTL expectations.

For multiclock work the same single-source rule composes rather than changes:

```text
ordinary pretty Design islands + typed logical channels + named clocks
                              |
                              v
                     checked System semantics
                         |             |
                         v             v
              CertifiedSystem replay  explicit compiled CDC realization
                                             |
                                             v
                              certified structural system.v
```

The channel declaration is the stable protocol meaning. The realization clause
names which circuit implements it, and that circuit's controller, synchronizer,
flag, and storage `Design`s remain inspectable hardware. An optional physical
binding refines those Designs to target cells or macros; it does not silently
change the channel semantics.

## Semantic boundary

The authoring layer obeys one rule:

> Every token's obvious reading must be its true cycle-level meaning. Each
> hardware operation corresponds to one unambiguous core constructor; a token
> that would require choosing among plausible semantics is omitted until the
> core represents that choice explicitly.

Keywords are reserved for fundamental language structure and operations, not
for an open-ended catalog of library strategies. `reset` and `realize` are
structural system items; coordinated reset, Gray FIFO, recovery, target storage,
and future certified adapters are ordinary namespaced Lean values supplied by
libraries. Adding a realization profile must not require extending the parser.

In particular:

1. Every construct lowers to the existing core. No new expression, action, or
   transition semantics lives only in the parser or elaborator.
2. `<-` is the only state assignment and lowers to next-cycle `Act.write`.
   There is no blocking `=` statement and no borrowed `<=` token suggesting a
   missing alternative assignment form. `:=` remains definition/reset syntax.
3. Rules replace `always @(posedge clk)`. There are no sensitivity lists.
4. Numeric literals are unsized and acquire their width from the expected
   `Expr w` type. Loom does not add a second width declaration with `8'd255`.
5. Ordering comparisons expose signedness: `<u`/`<s` in an ASCII surface, or
   `<ᵤ`/`<ₛ` in a Unicode surface. There is no unmarked `<` and no expression
   `<=` in v1. Less-or-equal arrives only after `Expr` has distinct unsigned
   and signed constructors and semantics.
6. There are no multi-bit `&&`, `||`, or `!` operators because the core has no
   Verilog truthiness rule. Bitwise operators mirror `Expr.and`, `Expr.or`,
   `Expr.xor`, and `Expr.not`; they may be used on `Expr 1` conditions.
7. Part selects are static because `Expr.slice` takes constant `lo` and
   `width`. A dynamic part select is rejected at its source span with a direct
   diagnostic.
8. Memory write-port indices remain explicit. They participate in Loom's
   compilation obligations and must not be hidden for visual simplicity.
9. Command-time checks improve locations and messages but never replace core
   validation or the fail-closed emission gate. Programmatically constructed
   designs retain the same authoritative checks.
10. A multiclock surface lowers to the existing `Chan`, `SystemBuilder`,
    `System`, `CertifiedSystem`, and certified realization values. It does not
    create a second crossing semantics or expose one particular CDC circuit as
    the meaning of a channel.
11. `Design.cycle` remains a single-clock transition. A combinational output is
    a pure same-cycle `CombOutput` observation and never an implicit state
    update, clock crossing, or sensitivity-list construct.
12. A logical channel is not itself synthesizable hardware. Every emitted
    cross-clock channel therefore has an explicit realization, and every
    behavioral component of that realization is available as an ordinary
    `Design` for inspection, proof, simulation, replacement, and emission.

## Surface syntax

### Expressions and statements

Two dedicated syntax categories own their grammar. Lean's term parser is
entered only through an explicit escape.

```lean
declare_syntax_cat hwexpr
declare_syntax_cat hwstmt

syntax "[hwexpr| " hwexpr "]" : term
syntax "[hwstmt| " hwstmt* "]" : term
```

The initial `hwexpr` audit mirrors the current `Expr` constructors:

- literals and readable signal identifiers;
- `+`, `-`, `*`, `/`, and `%`;
- bitwise AND, OR, XOR, and complement;
- left and right shifts;
- equality, unsigned less-than, and signed less-than;
- ternary mux;
- static slice and bit select;
- concatenation as `high ++ low`;
- `zext value to width` and `sext value to width`;
- memory reads;
- logical-channel observations `channel.canSend`, `channel.hasData`, and
  `channel.data`;
- parentheses;
- `$(term)` for an ordinary Lean term expected to elaborate as `Expr w`.

A bare identifier is elaborated using the expected `Expr w` type. It may be a
`Reg w` or `Input w` handle (read through its coercion), an existing `Expr w`
helper, or a `Nat` constant such as `S_F0`, which is lifted to `Expr.lit` at the
expected width. This is what lets state-machine code say `st == S_F0` without
an annotation or escape while retaining width checking. Arbitrary Lean
computation still uses `$(term)`.

Resolution has a fixed shadowing rule. Inside a `hardware` command, a
design-local signal wins over every non-signal candidate with the same short
name. Otherwise the elaborator collects the reachable `Expr w` and `Nat`
candidates; exactly one viable candidate is accepted, while two or more are an
ambiguity error at the identifier. Fully qualified names and `$(term)` remain
available to select an ordinary Lean declaration explicitly. The command may
emit an informational note when a design-local signal shadows a viable
imported constant, but it must never silently choose between two non-signal
candidates. Outside a command wrapper there is no design-local table, so the
same unique-candidate rule applies without the signal-priority step.

The initial `hwstmt` forms are:

```lean
r <- expr
packedReg.field <- expr
mem[port n, addr] <- expr
if cond then branch else branch
if cond then branch else if cond then branch else branch
if cond then branch
{ statement* }
case expr of
| constant => branch
| default => branch
for ident in $(term) generate branch
send expr to channel
consume channel
receive ident from channel then branch
skip
$stmt(term)
```

`$stmt(term)` expects `Act`. It is deliberately distinct from `$(term)`,
which expects `Expr w`; expression and statement escapes never blur.

Logical channel vocabulary is intentionally behavioral rather than
signal-level. Its v1 syntax-to-core and behavioral contract is:

| Surface | Core | Cycle-level meaning |
| --- | --- | --- |
| `q.canSend` | `q.canEnq` | The generated source endpoint can accept a new payload on this island cycle. |
| `send value to q` | `q.enq value` | If `canSend`, write the endpoint payload and mark it valid; otherwise do nothing. |
| `q.hasData` | `q.canDeq` | A head is visible and no earlier consume request is still outstanding. |
| `q.data` | `q.deq` | Read the endpoint payload; its value is meaningful only when `hasData` is true. |
| `consume q` | `q.pop` | If `hasData`, record a one-cycle consume request; otherwise do nothing. |
| `receive value from q then body` | guarded `q.deq`; `body`; `q.pop` | If a head is available, bind it for the body and consume it exactly once; otherwise do nothing. |

The guarded actions are deliberately idempotent when unavailable, but their
guards do not cover neighboring statements. For example:

```lean
send 42 to q
sent <- 1
```

sets `sent` even if the send does nothing. State that should update only on an
accepted local transaction belongs under the same explicit `q.canSend` guard.
Likewise, reading `q.data` without a dominating `q.hasData` guard receives a
teaching warning. The logical runner currently supplies zero for an empty
queue, while a physical storage realization may retain an old sample; neither
value is a payload guarantee, and portable code must not observe it.

`Chan.exchange` and `Chan.refusePush` describe a full queue when producer and
consumer are accepted on the same named-clock event. `exchange` accepts the
push after removing the old head; `refusePush` rejects it. `Clock.asynchronous`
admits coincident unrelated edges, so a channel between distinct domains can
encounter that co-tick case. Only the deliberately narrower
`Clock.interleaved` proof relation excludes it. The default policy and this
distinction must both appear in generated documentation and cold-read tests.

Users never author valid/ready bits, acknowledgements, pointer state, or
endpoint maintenance rules. The canonical beginner form for a guarded
read-and-consume transaction is:

```lean
receive value from q then {
  got <- value
  observed_count <- observed_count + 1
}
```

It has one fixed lowering contract: hygienically bind `value` to `q.deq`, guard
the body with `q.canDeq`, and append exactly one `q.pop`. The bound value is a
typed `Expr`/`PackedExpr`, not a mutable local or an extra register. An empty
channel executes neither the body nor the consume. The lower-level
`hasData`/`data`/`consume` forms remain available when hardware needs to inspect
or conditionally defer the visible head, but tutorials and cold-read examples
prefer `receive` because it makes the validity region and exactly-once consume
structural.

Channel transactions have stricter composition rules than ordinary register
writes. For each endpoint and island event, the lowered action must contain at
most one possible `send` and at most one possible `consume`. The checker is
branch-sensitive: counts add through `Act.seq`, take their maximum across the
arms of `Act.ite`, and add across rules because every rule executes in its
defined source order. Alternative branch sends are therefore valid; sequential
sends or sends from two rules are errors pointing at both transaction sites.
The same rule applies to consumes. A statement escape that touches generated
endpoint coordinates must expose an analyzable channel footprint or be
rejected at the escape, rather than silently reintroducing last-write-wins
data loss.

Braces delimit multi-statement blocks. Newlines and indentation are encouraged
for readability but are not semantic, so v1 does not require a custom
whitespace-sensitive parser. `if` owns an entire `else if` chain. A branch is
an assignment, block, `case`, `skip`, or statement escape—not an unbraced
nested `if`. A genuinely nested conditional therefore uses braces, and an
`else` cannot silently attach to the wrong `if`. An `if` without `else` lowers
its absent branch to `Act.skip`.

`case` matches equality against width-checked compile-time constants and lowers
to a right-nested `Act.ite`; it has no `casez`/`casex`, wildcard, parallel, or
priority modes. Labels are normalized to their `BitVec w` values before
checking, so two different Lean terms that denote the same value are still a
duplicate. A duplicate label is a command-time error pointing at both arms:
the later arm would otherwise be silently dead.

`default` is required unless the distinct labels cover all `2 ^ w` values of
the scrutinee. It may be omitted for provably total coverage. If a total case
also supplies `default`, the command accepts it but warns that the branch is
unreachable; a non-final default remains an error. Exhaustiveness is computed
from the normalized finite label set, never guessed from source spelling.

This construct is v1-adjacent: it should land before the FSM-heavy LNP64mini
migration even if the scalar tutorial ships without it. Its release is also
gated on proof ergonomics: right-nested `ite` is semantically simple but may
produce poor invariant goals for a large state machine. Phase 4 must test the
ordinary `simp`/case-splitting workflow on an FSM-sized example. If it produces
an impractical split tower, the case elaborator metadata should support a
generated per-rule split lemma or tactic; the public surface must not ship on
the assumption that parsing ergonomics imply proof ergonomics.

Purely structural forms lower with macros:

```text
expression operator  -> the corresponding Expr constructor
if                    -> Act.ite
brace sequence        -> right-associated Act.seq ending in Act.skip
case                   -> a source-ordered, right-nested Act.ite chain
for/generate           -> an ordered Lean List fold using Act.seq
send/consume           -> Chan.enq / Chan.pop
receive                -> one guarded Chan.deq/body/Chan.pop action
```

Assignments and escapes use term elaborators rather than translation macros.
The `<-` elaborator first classifies the target. A scalar `Reg w` supplies
expected RHS type `Expr w` and lowers to `Act.write`; an indexed memory target
supplies its existing address/data/port obligations; and a field of
`PackedReg α` supplies the registered static offset, total width, and expected
field `Expr` width before lowering to bounded `Act.writeSlice`. This works for
command-generated, handwritten, and indexed scalar handles, while packed
field lvalues require registered layout metadata. It also permits diagnostics
at the user's tokens:

```text
cannot assign to input `clk_en`
8-bit target, but this expression has width 1
expected an Expr 8 splice, but the Lean term has type Expr 16
field `address` belongs to packed input `request` and is not writable
packed memory fields require an explicit whole-element write
```

### Readable and writable handles

Inputs receive a distinct handle:

```lean
structure Input (w : Nat) where
  name : String

def Input.rd (input : Input w) : Expr w := .reg w input.name
instance : Coe (Input w) (Expr w) := ⟨Input.rd⟩
```

`Reg w` retains `Reg.rd` and its existing coercion to `Expr w`. Read position
therefore treats both handle kinds uniformly, including a splice such as
`$(regs[i])`. Only `Reg w` has a write operation, so writing an input is a type
error even without the early diagnostic.

The declaration builder gains an additive operation:

```lean
Declarations.addWireInput (ds : Declarations) (input : Input w)
```

The existing `addInput` API remains untouched. No declaration-lowering
typeclass is introduced in v1: the command knows which declaration production
it parsed, and two concrete lowering functions keep diagnostics direct. A
shared abstraction should be reconsidered only if a third handle kind creates
real repeated client code.

### Packed structs

The pretty layer exposes the packed-value contract from `PLATONIC.md`; it does
not add a field-wise state model. A basic declaration is:

```lean
packed struct Request where
  address : 64
  write   : 1
  size    : 3
  data    : 64
```

This command generates the semantic Lean record, its `HwPacked` instance,
field-layout metadata, typed packed expression/register/input/channel views,
and the projection/construction helpers needed by the syntax. Its total width
is 132, with `address` in the most-significant 64 bits and `data` in the
least-significant 64 bits. It does not generate 132 separately named signals,
insert padding, or select a SystemVerilog ABI.

Hardware declaration type positions accept either a scalar width or a packed
type:

```lean
hardware requester where
  input wire request : Request
  output reg pending : Request
  output wire request_address : 64 := request.address

  rule capture :=
    pending <- request
```

The same packed type may be used as a memory element and channel payload once
those existing scalar forms are available:

```lean
memory requests : Request [16]
channel outbound : Request depth 2
```

All uses erase through the generated packed wrapper to the existing total
width: one `Reg 132`, `InputDecl` of width 132, `Mem aw 132`, `CombOutput` of
width 132, or `Chan 132`. The generated typed handle must prevent accidental
assignment of a different 132-bit packed type merely because its raw width is
equal.

Inside `hwexpr`, field projection, construction, whole-value update, and
explicit representation conversion are supported:

```lean
request.address

Request {
  address := pc
  write   := 0
  size    := WORD
  data    := 0
}

{ pending with address := next_pc }

request.bits
Request.fromBits raw_request
```

Projection lowers to the generated static `Expr.slice`; construction lowers to
a declaration-ordered concatenation tree; update lowers to a construction that
reuses every unchanged field; `.bits` unwraps to the underlying `Expr`; and
`fromBits` performs the inverse typed wrap. Equality between values of the same
packed type lowers to existing packed `Expr.eq`. Arithmetic, ordering, bitwise
operations, concatenation, and slicing on a whole struct are rejected unless
the author explicitly writes `.bits`, because those operations have no
field-level meaning.

Record literals elaborate field expressions with their declared expected
widths. Missing, duplicate, and unknown fields are errors at the literal;
declaration-field duplicates are errors at both tokens. V1 requires every
field exactly once and accepts named scalar fields only. Nested packed structs,
arrays, tagged unions, defaults, and spread syntax are deferred until the
packed-layout core contract supports them explicitly.

Partial lvalue assignment is part of v1:

```lean
pending.address <- next_pc
pending.write <- 1
```

Each field lvalue resolves the packed register, looks up the field's static
offset and width, elaborates the RHS with that expected width, and lowers
directly to the core `Act.writeSlice`. It does not become an independent
whole-register `Act.write` and does not require the command to merge different
named rules. Whole-value update remains available as the expression form:

```lean
pending <- { pending with address := next_pc }
```

Because `writeSlice` merges against the existing `Act.run` write accumulator,
ordinary sequencing, branches, and rule order compose as expected:

```lean
if update_address then
  pending.address <- next_pc
pending.write <- next_write
```

The true path updates both fields and the false path updates only `write`.
Conditions and every RHS still read start-of-cycle state—not the accumulated
next value—so:

```lean
pending.address <- next_pc
observed <- pending.address
```

assigns the old address to `observed`, with the ordinary read-after-write
teaching diagnostic. This is not blocking assignment; it is the core
static-slice write semantics specified in `PLATONIC.md`.

Disjoint field writers compose even when they occur in different rules. A
later write to the same field wins and receives the existing multiple-write
teaching note; a later whole-value write supersedes earlier field updates and
points back to them. A whole write followed by field writes intentionally
modifies the newly accumulated whole value. The generated metadata retains the
source field and span for footprints, diagnostics, proof presentation, and
delaboration, while each named rule remains an independently meaningful `Act`.

Only packed-register fields are lvalues in v1:

```lean
request.address <- next_pc                 -- rejected: input
requests[port 0, index].address <- next_pc -- rejected: memory field update
```

Packed memories support whole-element writes such as
`requests[port 0, index] <- request`. A field update would imply memory
read-modify-write and port behavior that `writeSlice` does not provide. Raw
`.bits` is expression-only and is not accepted as an lvalue.

Reset initializers use a semantic packed Lean value or an equivalent complete
record literal accepted by the declaration elaborator, then call the same
`HwPacked.pack` used by execution and observation. A struct channel similarly
packs once at `send` and projects a typed packed expression at `data`:

```lean
send Request {
  address := pc
  write   := 0
  size    := WORD
  data    := instruction
} to outbound

if outbound.hasData then {
  pending <- outbound.data
  consume outbound
}
```

The delaborator preserves the type boundary. It prints named fields and record
literals only when their slices/concatenations match the registered layout and
the printed form reparses to the same packed core expression. Otherwise it
falls back visibly to `.bits`, slices, concatenation, or ordinary core
notation. `#show_hardware` follows the same structural round-trip rule.

Packed structs are values, not interfaces. A later `interface` facility may
group directional ports such as valid/ready/payload and define connection
policy, but it must not be smuggled into this feature. V1 emits a packed struct
port as one vector; native SystemVerilog struct emission and opt-in field
flattening belong to the emitter plan, not prettification.

### The `hardware` command

Declarations precede rules structurally:

```lean
syntax "hardware " ident " where" hwDecl* hwRule* : command
```

A rule before a declaration receives the custom error `declarations must
precede rules`, rather than a raw parser expectation. Declaration-first order
makes the interface visible at the top and avoids two-pass name availability
in v1.

The scalar productions are:

```text
input wire name : width
output reg name : width
output reg name : width := reset-value
output wire name : width := expression
reg name : width
reg name : width := reset-value
```

The width position is a Lean `term`, elaborated as `Nat`, rather than a
Verilog-style `[hi:0]` range. Consequently `reg pc : 64`, `reg idx : addrW`,
and a computed width all use the same production; parametric widths do not
need a later grammar extension. Widths must reduce far enough to construct the
indexed handle and declaration, and a zero width receives a direct warning or
error according to the core policy established in Phase 0.

`input reg` is not accepted because it lies about writability. `output wire`
is a distinct combinational-output production: its RHS elaborates as
`Expr width`, lowers to `Declarations.addCombOutput`, and generates a readable
`Expr width` definition for reuse. It has no `Reg` handle and cannot appear on
the left of `<-`; `Design.cycle` is unchanged. A register initializer is
declaration syntax, not `hwexpr`: it elaborates with expected type
`BitVec width` and becomes the `RegDecl.init` value. Numeric literals use that
expected width, and a bare `Nat` constant is lifted with `BitVec.ofNat`, so
`reg pc : 64 := TEXT_BASE` needs no annotation. An arbitrary computed reset
image uses an explicit Lean escape. This keeps reset values separate from
expressions over pre-cycle state and same-cycle observations.

The command creates handles, rule bodies, `declarations`, and `design` in the
current namespace. It uses `withRef` and declaration ranges based on the user
tokens so go-to-definition and generated-code failures return to the DSL
source.

One `NameSet` covers every Lean name the command will generate:

- signal and memory handles;
- rule definitions;
- `declarations` and `design`;
- public helper lemmas;
- all reserved generated suffixes.

It checks collisions between user tokens, reserved names, and declarations
already in the current environment. When two user tokens collide, the error
identifies both locations. Two `hardware` commands in one namespace continue
to collide on `design`, just as two handwritten designs do today, but the
second command reports that fact directly.

### Teaching cycle semantics

The syntax makes state updates look distinct from Lean definitions, but it
cannot by itself prevent the most common software-shaped misconception:

```lean
rule step := {
  a <- b
  c <- a
}
```

Here `c` receives the start-of-cycle value of `a`, not the value assigned on
the preceding line. The command already has the statement tree and can derive
read/write sets, so the DSL should provide an enabled-by-default informational
lint at the second `a`:

```text
reads observe the start-of-cycle value; the write to `a` above takes effect
next cycle
```

The same analysis should explain multiple writes rather than reject them.
Within a rule, and across Loom's ordered rule list, the last executed write
wins. A diagnostic can list the earlier and later source locations and the
rule order. This is particularly important for intentional patterns such as
LNP64mini's `pulse_defaults`, whose early default writes are overridden later.

These findings are informational lints, not proof obligations or semantic
checks. Intentional sites need a narrow suppression mechanism, and generated
or highly parametric `$stmt(...)` actions may fall back to the core footprint
analysis instead of pretending the surface command can see through arbitrary
Lean. The authoritative semantics and compiler checks remain unchanged.

### Generated proof support

Every handle receives visible simplification lemmas, initially:

```lean
@[simp] theorem count_name : count.name = "count" := rfl
```

A width lemma should be generated when the concrete handle API provides a
stable useful statement for it. Generated suffixes such as `_name` and
`_width` are public and reserved by the command. The reservation and generator
share one constant list so they cannot drift.

Per-design unfolding uses one fixed tactic:

```lean
hw_unfold design
hw_unfold Machines.Tutorial.SatCounter.design
```

A `SimpleScopedEnvExtension` maps the fully qualified name of each generated
`design` constant to the array of definitions generated for it. The tactic
elaborates its argument, extracts its head constant, performs the lookup, and
constructs a per-design `simp only` invocation. It does not register a new
parser keyword per module and does not collect definitions from unrelated
imported designs.

Name lemmas should ship before `hw_unfold`: they are smaller, independently
useful, and handle much of the state-map reasoning without unfolding handle
structures.

### Delaboration

`Loom.Hw.Dsl` imports the authoring syntax and its delaborators together. A
user who opts into the syntax should see proof states in the same notation.

Delaboration is conservative:

- action and expression unexpanders produce `[hwstmt| ...]` and
  `[hwexpr| ...]` wrappers;
- a helper collapses `Reg.rd` and `Input.rd` to bare identifiers only while
  reconstructing syntax inside those wrappers;
- no global `Reg.rd` unexpander is registered;
- ordinary Lean terms continue to print `count.rd` when the read operation is
  itself relevant;
- any partially simplified term without a faithful DSL representation falls
  back to core notation.

The faithfulness condition is that wrapped output reparses through the same
syntax category to the original core term. Pretty output must not depend on an
ambient coercion that the printed syntax does not reveal.

## Functional Lean and pretty hardware

Lean is the parameterization and construction language; the pretty DSL is the
notation for the hardware fragments Lean constructs. The boundary should be
compositional in both directions rather than forcing a choice between an
entirely pretty rule and an opaque `$stmt(...)` action.

Pretty quotations are ordinary Lean terms and may appear inside functions,
maps, folds, recursion, and proofs:

```lean
def wakeOne (i : Fin NT) : Act :=
  [hwstmt|
    if wakeEn & (tstate[i] == FUTEX) then
      tstate[i] <- READY
  ]

def readyAt (i : Fin NT) : Expr 1 :=
  [hwexpr| tstate[i] == READY ]
```

Conversely, a pretty rule may ask Lean to replicate a visible hardware body:

```lean
rule wake_threads :=
  for i in $(List.finRange NT) generate {
    if wakeEn & (tstate[i] == FUTEX) then
      tstate[i] <- READY
  }
```

`generate` means structural construction, not a runtime hardware loop. Its v1
collection elaborates as `List α`, preserving an explicit order, and lowers to
one small ordinary Lean combinator:

```lean
def actFor (xs : List α) (body : α → Act) : Act :=
  xs.foldr (fun x rest => Act.seq (body x) rest) Act.skip
```

Thus the example is equivalent to:

```lean
actFor (List.finRange NT) fun i =>
  [hwstmt|
    if wakeEn & (tstate[i] == FUTEX) then
      tstate[i] <- READY
  ]
```

No evaluator, compiler case, or loop semantics is added. The ordinary Lean
term constructs the same finite `Act.seq` tree the handwritten fold constructs
today. Collection order is semantically visible because later writes win; v1
therefore accepts `List`, not unordered containers or an arbitrary traversal
whose ordering may surprise the author.

Inside a generated body, the binder is an ordinary hygienic Lean local. Index
elaboration distinguishes two useful cases by type:

- `tstate[i]` with `i : Fin NT` selects one static `RegArray` member;
- `tstate[idx]` with `idx : Expr w` constructs the existing dynamic read or
  write network.

Both are valid hardware operations, but they can have very different circuit
cost. The dynamic form should receive a source-local informational cost note
when a static index may have been intended. This distinction is derived from
the types, not from different punctuation.

A generate binder may hygienically shadow an imported non-signal Lean name.
It may not reuse a design-local signal name: that is a command-time collision
error, preserving the signal-first identifier rule and preventing the body
from visually changing the meaning of a declared net.

Ordinary Lean remains available around quotations for richer reductions:

```lean
def readyAny : Expr 1 :=
  orTree <| (List.finRange NT).map fun i =>
    [hwexpr| tstate[i] == READY ]
```

The first release should not grow `any`, `all`, `sum`, or priority-selection
syntax merely to hide this small amount of functional Lean. Such reductions
have ordering, empty-case, cost, and proof-shape decisions of their own. Add a
pretty reduction only after repeated real use shows that it improves reading
without concealing those decisions.

`$()` and `$stmt()` remain the universal escape hatches. They are appropriate
for an isolated pre-existing expression/action or machinery the pretty grammar
does not model. They are not the preferred way to hide a whole parameterized
hardware rule. Similarly, a later conditional-generation form should use an
explicit `generate` keyword so it cannot be confused with runtime hardware
`if`; it is outside the v1 surface until its declaration and rule behavior is
specified.

## First-class multiclock systems

Multiclock authoring gets a separate `system` command rather than adding clock
annotations to `hardware`. A `hardware` block is always one ordinary
single-clock `Design`; a `system` gives named clocks to islands and connects
them with logical `Chan`s. This preserves the existing theorem boundary and
makes a raw cross-clock wire unrepresentable in the pretty surface.

An ordinary author needs six ideas: island hardware, named clocks, typed
channels, send/receive, one explicit reset policy, and one realization per
route. Gray equations, synchronizer stages, endpoint registers, storage ports,
physical object paths, coverage witnesses, and backend statuses are inspection
material—not authoring vocabulary. If the common tutorial or SoC-gauntlet
source requires a seventh CDC concept, the surface has failed its progressive-
disclosure goal and must justify or remove it before v1 freezes.

The small two-clock example should eventually read:

```lean
system twoClock where
  clock clkA
  clock clkB
  clocks Clock.asynchronous
  reset Reset.together

  channel q : 8 depth 2

  island producer on clkA where
    output reg sent : 1

    rule send :=
      if ~sent & q.canSend then {
        send 42 to q
        sent <- 1
      }

  island consumer on clkB where
    output reg got : 8

    rule receive :=
      receive value from q then
        got <- value

  connect q from producer to consumer
  realize q with Cdc.grayFifo
```

The architecture is concise, but the hardware choice is not implicit.
`Cdc.grayFifo` is a discoverable library value naming the actual stock
crossing family: compiled source and sink
controllers, Gray-coded pointers, two-register synchronization paths,
full/empty logic, and coherent FWFT register-bank storage. It supports the
existing certified power-of-two depths of at least two. A storage keyword is
not repeated in the default spelling: compiler-produced neutral register
storage is what the stock profile means, and `#show_system` reports it.
Target storage replacement is an explicit library binding described below.
Tokens that appear configurable must correspond to real typed choices; another
pointer encoding or synchronizer depth receives a distinct certified profile
rather than decorative syntax over fixed internals.

The system author does not have to restate that stock circuit on every
connection. Nevertheless, the generated controller and storage `Design`s are
public hardware definitions with stable names, and the pretty printer can show
them in the same `hardware` syntax used for an island. The system command is
therefore composition plus certified generation, not an architectural model
that skips the implementation.

A `system` containing an unrealized cross-clock channel is useful for logical
semantics and proofs, but it is not an emit-ready hardware description. The
emission gate must reject it. Adding a realization is the step that supplies
the missing circuit and makes the structural artifact synthesizable.

### System declarations

The v1 system items are:

```text
clock clockName
clocks clockRelation
clocks $(clockRelationTerm)

reset resetPolicy

channel name : width depth depthTerm
channel name : width depth depthTerm policy channelPolicy
channel name := $(Chan term)

island name on clockName where hardware-items
island name on clockName module moduleName where hardware-items
island name on clockName := $(Design term)
island name on clockName module moduleName := $(Design term)
island name on clockName extends $(Design term) where hardware-items
island name on clockName module moduleName extends $(Design term) where hardware-items

connect channel from sourceIsland to sinkIsland
realize channel with realization
realize channel, channel, ... with realization
```

The block has one canonical visual order: clock declarations, one clock
relation, one reset policy, channel declarations, island declarations,
connections, then realizations. The grammar enforces those sections and reports
an out-of-order item directly. This keeps a large system skimmable and ensures
all names exist before topology and realization are checked; it does not impose
an order on the generated semantic connection list beyond the visible
connection section.

Widths and depths are Lean `Nat` terms. The stock library exposes
`Chan.exchange` and `Chan.refusePush`; `Chan.exchange` is the documented default,
while `policy Chan.refusePush` makes the alternative explicit. `policy` is
structural grammar, but its value is not a keyword.

The stock clock-relation library exposes:

```lean
Clock.asynchronous            -- arbitrary phase; coincident edges allowed
Clock.interleaved             -- at most one named clock per event
Clock.aligned clkA clkB       -- the named clocks always tick together
```

The `clocks` item elaborates its argument with expected type `ClockRel` under
generated clock-handle locals. A simple qualified name/application needs no
escape; arbitrary Lean computation uses `$(term)`. The mechanical
`.unconstrained` name is not exposed as a second stock alias because it is
currently definitionally the same relation as `.asynchronous`; two names would
imply a distinction that does not exist. A project may define another
`ClockRel` library value without extending grammar or creating a second
schedule language.

Every `system` explicitly supplies one library reset-policy value. The stock
library initially exposes:

```lean
Reset.together          -- SystemResetPolicy.coordinated
Reset.independentFlush  -- SystemResetPolicy.independentFlush
```

The dotted names make completion and go-to-definition useful, while the source
does not turn either policy into reserved grammar. `reset` is the only keyword;
its argument elaborates with expected type `SystemResetPolicy`, so a project may
define a shorter alias or a future core/library policy without changing the
parser. The item describes traffic/reset semantics, not electrical reset
delivery. The current active-high synchronous `rst`, clock-required assertion,
and independently sampled per-domain release are derived from emitted RTL and
shown by inspection; they are not configurable-looking syntax.

`Reset.together` is the beginner/default library choice.
`Reset.independentFlush` is advanced and inherits the exact current
recovery theorem boundary. If the aggregate emitted-wrapper refinement is not
release-closed, `#show_system` says so and the pretty command must not label the
artifact fully certified merely because the policy term elaborated. Syntax
never upgrades an experimental core capability into a stronger claim.

The channel escape reuses an existing typed `Chan w`; the other forms generate
one from the visible width, depth, and full-queue policy.

A grouped realization clause is only shorthand for applying the same typed
library selection to every listed route. Duplicate membership points at both
clauses, and final validation still requires every connected channel exactly
once. V1 deliberately has no wildcard/default realization: adding a channel to
a safety-critical system must produce a missing-realization error rather than
silently inheriting a circuit choice.

V1 is not restricted to two clocks. `clocks Clock.asynchronous` admits arbitrary
phase and coincident edges; it is the ordinary physical-unrelated-clock
schedule model. `clocks Clock.interleaved` is the stronger proof/testing
relation in which at most one named clock fires in an event. `clocks
Clock.aligned leftClock rightClock` constrains that named pair to tick together,
while other clocks remain unconstrained. Duplicate relation declarations, undeclared names
in an aligned pair, and a relation that names the same clock twice are
source-local errors. An escaped relation changes the admitted schedule set; it
does not change whether two endpoints have distinct physical clock names or
remove the need to realize such a crossing.

Every named clock must be declared and used by at least one island. Island,
clock, and channel names are checked for duplicates and empty names at their
tokens. A connection must name one declared channel plus declared source and
sink islands, and every channel is connected exactly once. The command reports
both locations for duplicates and reports an unused declaration rather than
silently dropping it from the emitted interface.

An inline island body uses the same declarations, rules, expressions,
statements, source locations, generated name lemmas, and teaching diagnostics
as `hardware`. `extends` appends pretty declarations/rules to an existing
ordinary `Design` before endpoint generation; it is the migration path for a
large design such as LNP64mini. The plain `:=` form uses an existing `Design`
unchanged except for the channel endpoints derived below. By default an inline
island's emitted Design/module name is `systemName_islandName`, while `module`
supplies an explicit user-owned name. An existing Design retains its name
unless the optional module override is present. This gives unrelated systems
collision-resistant defaults while preserving literal RTL identity during
migration through an explicit module name.

Every handle referenced by an inline extension must resolve to the base
Design, a declaration added by that body, or an endpoint generated for that
island. Metadata from a prior `hardware` command permits an immediate check.
For a closed reducible `$(Design term)`, the command evaluates its declarations
and retains a source map for the generated check. V1 rejects `extends` when the
base declarations cannot be inspected; authors may compose that parametric
Design in ordinary Lean and pass the finished result through the unchanged
plain-island form instead. The pretty plan does not add a new declaration
manifest or certificate solely to make every opaque term extensible. In no
case may it accept a foreign handle merely because `Reg w` type-checks. The
ordinary design and emission checks remain the final backstop.

Inline islands may use the scalar `output wire` form because it lowers to the
existing island `CombOutput`. The current physical top renderer does not lift
such observations to top-level ports. Until its owning API defines that
mapping, the pretty command must not imply otherwise: logical/component use is
accepted, but a realization clause on a system containing an exported island
`CombOutput` receives a direct unsupported-top-projection diagnostic. This plan
does not alter `Design.cycle` or add the missing renderer feature.

V1 does not add top-module naming syntax because the existing physical renderer
currently owns the fixed name `loom_system`. Changing or parameterizing that
name belongs to the realization/emitter API, not this plan. The pretty surface
documents the existing top exactly: declared clock names are ports, one common
`rst` port is fanned out, and external island ports are named
`islandName__signalName`; generated endpoint nets use the same island prefix
plus their reserved channel stem. Clock names, `rst`, flattened external ports,
generated wires, instance names, island module names, and realization module
names are checked in their actual Verilog namespaces. A same-spelled register
inside an island module is not falsely rejected merely because a top port has
that name. Systems emitted into separate artifact directories retain the
existing `system.v`/`loom_system` convention; combining several tops under new
names is explicitly outside the prettification scope until the owning API
supports it.

### Connections generate endpoints

`connect q from producer to consumer` is the single source of endpoint
direction. After parsing all items, the command applies `q.withSource` to the
producer island and `q.withSink` to the consumer island, then constructs the
existing ordered `SystemBuilder.island` and `.connect` declarations. Users do
not repeat `source q`/`sink q` inside island bodies and cannot drift endpoint
direction away from the connection list.

When several channels touch an island, endpoint transforms are folded in
connection declaration order. Their generated coordinates are disjoint, but
the order remains deterministic and is recorded in command metadata. The
ordinary `SystemBuilder.check` remains authoritative: the earlier command
diagnostics do not replace its fail-closed endpoint, name, and depth checks.

A logical-only `System` may omit realization clauses, but an emit-ready system
gives every connection exactly one realization. A same-clock route normally
selects `Cdc.synchronousFifo`; a route between distinct clock names must select
`Cdc.grayFifo` or `Cdc.recoverableGrayFifo` according to reset policy. The core
Gray realization remains legal for equal clock names when recovery policy
requires it, but the command warns when ordinary coordinated-reset source uses
it needlessly. This remains explicit even
when `ClockRel` happens to admit aligned schedules: schedule admissibility does
not choose a circuit. Mixed systems are first-class and may contain synchronous
and Gray FIFO routes in one total plan. Clock/realization mismatches point at
the realization phrase and both endpoint clock declarations.

A larger mixed system remains an architectural list rather than a Lean plan
program. The SoC Fabric Gauntlet should be able to end with a visibly complete
selection like:

```lean
  connect cpuRequest  from cpu       to fabric
  connect cpuResponse from fabric    to cpu
  connect dmaRequest  from dma       to fabric
  connect dmaResponse from fabric    to dma
  connect memRequest  from fabric    to registers
  connect memResponse from registers to fabric
  connect audit       from registers to monitor

  realize cpuRequest, cpuResponse with Cdc.synchronousFifo
  realize dmaRequest, dmaResponse,
          memRequest, memResponse,
          audit with Cdc.grayFifo
```

Every channel appears once, route direction stays beside `connect`, and circuit
family stays in the realization block. Formatting may wrap a comma-separated
list but does not change its meaning. A missing or repeated name is a local
error; no hidden default plan absorbs it.

The identifier after `system` is the Lean name of the generated checked
`System`, not a CDC module name. For `system twoClock`, the public results are
conceptually:

```lean
twoClock                     : System
twoClock.q                   : Chan 8
twoClock.producer            : Design
twoClock.consumer            : Design
twoClock.certified           : CertifiedSystem twoClock
twoClock.application         : System.Application twoClock
twoClock.q.sourceControl     : Design
twoClock.q.sinkControl       : Design
twoClock.q.storageWriter     : Design
twoClock.q.storageReader     : Design
```

The system identifier is both the public `System` definition and the namespace
for its generated authoring handles. Lean permits declarations beneath an
existing name, so dot-qualified names avoid underscore soup while preserving a
single obvious system value. Inside the command, the short architectural names
remain `q`, `producer`, and `consumer`. Default emitted module names remain
system-qualified independently of these Lean aliases.

The realization and its behavioral components are generated only when a
realization is requested. Stable camel-case public aliases point to the exact
existing Designs; they do not duplicate their values or invent a second
hierarchy. Base-island intermediates, endpoint transforms, lookup equalities,
proof terms, ordered-coverage witnesses, and structural coordinates use private
generated names. Users should never need names such as
`twoClock_q_storage_reader` or a generated `__loom_...` coordinate in source,
proofs, or ordinary diagnostics. All public and private generated names still
participate in collision and reserved-suffix checks.

User spelling is preserved exactly. The command does not convert `core_clk` to
`coreClk`, change a channel's case, or derive an emitted signal by applying a
style transformation. Generated dot selectors use one frozen lower-camel list
(`sourceControl`, `sinkControl`, `storageWriter`, `storageReader`,
`application`, and `certified`); emitted module/signal names continue to follow
the existing renderer and explicit `module` overrides. This keeps Lean lookup,
printed hardware, RTL inventories, and diagnostics from disagreeing about a
name merely for aesthetics.

### Explicit and inspectable CDC realization

Realizations are library values, not grammar alternatives. The opt-in aggregate
provides these thin discoverable aliases over the existing mechanical API:

| Library value | Existing selection | Meaning |
| --- | --- | --- |
| `Cdc.synchronousFifo` | `RealizationKind.synchronous` | Ordinary proved FIFO; endpoint clock names must match; every positive depth is supported. |
| `Cdc.grayFifo` | `RealizationKind.portableAsync` | Compiler-produced Gray-pointer FIFO with neutral FWFT register storage; required for distinct endpoint clocks; depth is a power of two and at least two. |
| `Cdc.recoverableGrayFifo` | `RealizationKind.recoveryPortableAsync` | The same Gray FIFO plus the compiled independent-flush recovery protocol and guards. |

The aliases are definitions, not new constructors or semantics. Projects may
provide their own names, and adding a fourth stock profile does not extend the
parser. The public source need not say `portableAsync`: “portable” is a property
and “async” is a clock relationship, while `Cdc.grayFifo` tells a hardware
designer which crossing circuit is actually instantiated.

`realize q with Cdc.grayFifo` obtains a `CertifiedDesign` for each final island,
derives the `Chan.Refinement`, constructs the existing compiled controllers and
coherent combinational/FWFT register-bank storage, proves ordered coverage, and
produces the exact `system.v` artifact. The channel width and depth configure
the real certified implementation; no second realization parameter can drift
from them.

The stock realization is inspectable from source and proof states:

```lean
#show_hardware twoClock.q.sourceControl
#show_hardware twoClock.q.sinkControl
#show_hardware twoClock.q.storageWriter
```

The first view should show ordinary hardware along these lines, derived from
the actual `AsyncFifoDesign` rather than maintained as a second rendering:

```lean
hardware q_source_control where
  input wire raw_read_gray : 2
  output reg write_binary : 2
  output reg write_gray : 2
  reg read_gray_sync0 : 2
  reg read_gray_sync1 : 2

  rule synchronize_read_pointer := {
    read_gray_sync0 <- raw_read_gray
    read_gray_sync1 <- read_gray_sync0
  }

  -- The remaining flag and pointer rules are printed here too.
```

This display matters semantically: it makes the start-of-cycle behavior of the
two synchronizer registers, the Gray transformation, and the full/empty logic
available to review with the same tools as any handwritten `Design`. It must be
possible to prove properties of these public components and emit them
individually for debugging.

`#show_hardware` has the same faithfulness rule as expression and action
delaboration: output is labeled as pretty hardware only when reparsing it
produces a structurally equal `Design`. The command may flatten a Design built
by Lean folds into a canonical declaration/rule listing, but it must not invent
the original parametric source. If a value contains a component the surface
cannot reify faithfully, such as an opaque initializer function, the command
prints an explicit “pretty rendering unavailable” notice and visibly falls
back to ordinary core notation. Every stock controller and storage component
gets a pretty-print/reparse structural-equality test and an emitted-RTL
identity test; plausible but unfaithful review output is never accepted.

This clause is convenience around existing certificates, not a new trusted
generator. All behavioral CDC logic remains ordinary compiled `Design`s; the
system renderer remains structural; the mechanical gate continues to reject
handwritten behavioral CDC RTL; and exact artifact/axiom audits remain the
release authority. Ordinary architecture-level goals should stay at the logical
channel/system level. Explicit inspection, unfolding, or a goal about a
realization component must instead reveal its pretty hardware, not conceal it
behind an opaque backend constant.

An expert-provided realization uses
`realize q with $(binding)`. The term must carry the same channel refinement,
component certification, coverage, and artifact obligations as the stock
binding. Its controllers and storage can themselves be authored with
`hardware` blocks and quotations, so replacing the stock implementation does
not require dropping to raw constructors. This is the escape hatch for a real
CDC architecture choice, not a way to bypass the emission gate.

Target storage does not get a second realization grammar. An evidence/library
module constructs an ordinary certified binding and the fundamental binding
escape consumes it:

```lean
realize q with $(targetBinding)
```

The library constructor used to define `targetBinding` is checked against the
exact generated `PhysicalLeaf` interface/configuration for `q`; width, depth,
address width, FWFT combinational read, write mode, reset, and port names flow
through its Lean type. The leaf genuinely replaces the portable storage modules
in the emitted wrapper. Its named assumption remains visible in `#show_system`;
the channel semantics and controller proof do not change. Generic
`Loom.Hw.Dsl` imports no target evidence and never selects a macro implicitly.
FPGA/ASIC brand names, primitive names, PDK cells, backend PASS results, and
constraint-language tokens stay in the supplied library/evidence term rather
than hardening into Loom syntax. A future ergonomic library combinator may
shorten construction of `targetBinding`; it still does not add keywords.

### LNP64mini multiclock destination

The production-scale telemetry system should reduce to the architecture it
actually expresses:

```lean
system lnpMulticlock where
  clock core_clk
  clock observer_clk
  clocks Clock.asynchronous
  reset Reset.together

  channel telemetry : 64 depth 2

  island core on core_clk module lnp64mini_multiclock_core
      extends $(Machines.Lnp64mini.design) where
    rule publish_retire_pc :=
      if telemetry.canSend then
        send trace_rd_pc to telemetry

  island observer on observer_clk module lnp64mini_retire_observer where
    output reg observed_pc : 64
    output reg observed_count : 64

    rule consume :=
      receive retire_pc from telemetry then {
        observed_pc <- retire_pc
        observed_count <- observed_count + 1
      }

  connect telemetry from core to observer
  realize telemetry with Cdc.grayFifo
```

The command may need a source-local certificate escape for an exceptionally
large existing island when automatic kernel reduction exceeds normal limits,
but that escape supplies a `CertifiedDesign` term for the final island. The
ordinary system author does not assemble connection records, lookup proofs,
coverage equations, or clock-rule proofs. The FIFO controls and storage remain
named public component Designs, however; they are implementation hardware, not
proof bureaucracy.

### One system inspection surface

Authoring stays small because inspection is first-class. One command presents
the existing typed System/application data at increasing detail:

```lean
#show_system twoClock
#show_system twoClock channel q
#show_system twoClock physical
#show_system twoClock physical with $(report)
```

The default view shows declared clocks and their relation, logical reset policy,
one plain-language reset-delivery summary, islands, channel
directions/types/depths, and selected realizations. The channel view adds
full-queue policy, source/sink issue intervals, structural latency, delivery
premises, storage kind, and links to its public controller/storage Designs. The
physical view expands the exact per-domain reset contract, synchronizer chains,
Gray launch/capture buses, relative skew/datapath requirements, target-leaf
assumptions, and any supplied backend result as `PASS`, `SKIP`, or
`UNCONSTRAINED`.

This is a pretty renderer over `CrossingInfo`, `ChannelTiming`, `ResetIntent`,
`PhysicalArtifacts`, and an optional `PhysicalCheckReport`; it creates no new
evidence model and generic emission never displays an invented PASS. Without a
report splice the physical view labels every item `REQUIRED`, not PASS; the
splice is expected to cover the selected artifact's exact dependent report
type. Internal object paths appear only in the physical view. The default
output should read approximately:

```text
system twoClock
  clocks: clkA, clkB (asynchronous; coincident edges allowed)
  reset: all islands together
  physical reset: rst, active high, synchronous in each domain

  q : 8, depth 2
    producer @ clkA -> consumer @ clkB
    realization: Gray FIFO, compiler register storage (FWFT)
    source issue: at most one value per ready source tick
    sink issue: at most one value per two sink ticks
    delivery: schedule dependent
```

The renderer uses prose for reports rather than leaking mechanical constructor
names such as `.portableAsync`, `.sampledIndependently`, or
`.scheduleDependent`. Those exact Lean values remain available in the expanded
view and ordinary terms when an expert needs them.

### Executable schedule surface

Prettification exposes the existing `System.runPrefixChecked` and
`CertifiedSystem.runPrefixChecked`; it does not create another multiclock
runner or schedule representation. A small command may translate readable
named events into the existing `SchedulePrefix`:

```lean
#run_system twoClock where
  tick clkA
  tick clkB
  tick clkA
  tick clkB
```

An event with aligned edges names all clocks that fire together:

```lean
tick clkA clkB
```

Clock identifiers are resolved against the selected system metadata. The
command rejects undeclared and repeated clock names at their tokens, calls the
existing checked runner, and reports the first event prefix rejected by the
system's `ClockRel`. Its default view shows user island outputs and accepted
channel transactions, not generated endpoint coordinates. An expert Lean-term
escape supplies the existing external-input trace when required. Certified
execution uses the already proved certified runner on the identical event
array; no pretty command maintains a second execution function or translates
through `List Bool`.

### Multiclock proof and diagnostic surface

The command records full-name metadata for islands and connections just as
`hardware` records generated definitions. A fixed proof helper should support:

```lean
system_lift lnpMulticlock core using core_invariant
```

and lower to the existing named-island lookup plus `System.liftIsland` theorem.
Generated lookup lemmas keep ordinary proofs out of `findIsland?` simplification
boilerplate. Certified register views should likewise be derivable from an
island name and typed register handle without manually reconstructing
`RegSlot`, while retaining the existing fail-closed width/name resolution.

Diagnostics teach both the architectural and realization boundaries:

- a direct cross-island signal reference says to declare and connect a typed
  channel;
- a missing or mismatched `Cdc.synchronousFifo`/`Cdc.grayFifo` selection points
  at both endpoint clocks and suggests the legal library value;
- `Cdc.grayFifo` with depth below two or not a power of two points at the
  channel depth and states the exact certified restriction;
  `Cdc.synchronousFifo` accepts every positive depth;
- a missing realization on an emitted cross-clock channel says that a logical
  channel is semantics, not a circuit, and offers the certified profile;
- an island certificate failure points at the island body or supplied design;
- a realization-component failure names and opens the source controller, sink
  controller, or storage Design that failed, rather than calling it a backend
  error;
- an unguarded `q.data` explains that payload is meaningful only under
  `q.hasData`;
- two possible sends or consumes in one island event point at both sites and
  explain the one-transaction endpoint rule;
- a handle used in an `extends` body but absent from its base Design points at
  the identifier rather than surfacing later as undeclared emitted state;
- `Reset.independentFlush` paired with a non-recovery realization points at both
  terms and offers `Cdc.recoverableGrayFifo`;
- a target storage leaf mismatch points at the splice and reports the expected
  FWFT interface/configuration; and
- a target storage selection displays its one named external assumption rather
  than presenting it as a theorem.

The two-clock example joins the cold-read suite before its vocabulary freezes.
Readers are asked to predict an unavailable send, an empty `q.data` read, the
cycle in which `consume` takes effect, a full-queue co-tick under both policies,
and whether a statement following `send` is acceptance-guarded. Recurring
misreadings change syntax or diagnostics; familiarity with valid/ready naming
is not assumed to establish that this vocabulary teaches the right semantics.

## LNP64mini destination

The following is a representative final-form excerpt based on the actual
LNP64mini trace ring, registered memory reads, pulse defaults, quantum counter,
and domain observation. It shows the intended reading experience; the exact
memory and register-family declaration spellings are a v2 design task below.

```lean
import Loom.Hw.Dsl
import Machines.Lnp64mini.Interface

namespace Machines.Lnp64mini

open Loom.Hw

def TEXT_BASE : Nat := 0x1000
def CMD_QUANTUM : Nat := 72
def READY : Nat := 1
def FUTEX : Nat := 3

hardware lnp64mini where
  input wire m_done : 1
  input wire m_rdata : 64
  input wire m_busy : 1
  input wire cmd_valid : 1
  input wire cmd_idx : 7
  input wire cmd_data : 32
  input wire hold : 1

  output reg cur : 5
  output reg pc : 64 := TEXT_BASE
  output reg retire : 32
  output reg st : 5

  output reg dmem_we : 1
  output reg dmem_a : 9
  output reg dmem_wd : 64
  output reg dmem_rd : 64

  output reg core_rd : 1
  output reg core_wr : 1
  output reg core_addr : 32
  output reg core_wdata : 64

  output reg gp_rd : 1
  output reg gp_wr : 1
  output reg lr_req : 1
  output reg sc_req : 1

  output reg trace_wp : 4
  output reg trace_sel : 4
  output reg trace_hit : 1
  output reg trace_in_pc : 64
  output reg trace_in_wb : 64
  output reg trace_rd_pc : 64
  output reg trace_rd_wb : 64

  output reg quantum : 32
  output reg qctr : 32
  output reg cur_dom : 8

  memory dmem : 64 [512] using Memory.synchronousRead
  memory rf : 64 [1024] using Memory.synchronousRead
  memory uart_mem : 8 [256] using Memory.synchronousRead
  memory trace_pc : 64 [16]
  memory trace_wb : 64 [16]
  memory tdom : 8 [32]

  rule latches :=
    {
      if dmem_we then
        dmem[port 0, dmem_a] <- dmem_wd

      dmem_rd     <- dmem[dmem_a]
      trace_rd_pc <- trace_pc[trace_sel]
      trace_rd_wb <- trace_wb[trace_sel]
    }

  rule trace_ring :=
    if trace_hit then {
      trace_pc[port 0, trace_wp] <- trace_in_pc
      trace_wb[port 0, trace_wp] <- trace_in_wb
      trace_wp <- trace_wp + 1
    }

  rule pulse_defaults :=
    {
      dmem_we   <- 0
      core_rd   <- 0
      core_wr   <- 0
      gp_rd     <- 0
      gp_wr     <- 0
      lr_req    <- 0
      sc_req    <- 0
      trace_hit <- 0
    }

  rule quantum_tick :=
    if cmd_valid & (cmd_idx == CMD_QUANTUM) then
      qctr <- cmd_data
    else if cmd_valid & (cmd_idx == 13) & (cmd_data[0] == 1) then
      qctr <- quantum
    else if preemptAtF0 then
      qctr <- quantum
    else if qTick then
      qctr <- qctr - 1

  rule observe_domain :=
    cur_dom <- tdom[cur]

end Machines.Lnp64mini
```

An FSM arm should become recognizable hardware instead of a constructor tree:

```lean
rule fetch_boundary :=
  if st == S_F0 then {
    if bus_req then
      st <- S_PAUSE
    else if curPoisoned then
      running <- 0
    else if preemptFire then {
      cur <- next_ready
      pc  <- tpc[next_ready]
    }
    else if sentinelPc then
      st <- S_GRET
    else {
      ic_tag_q  <- ic_tag[ic_idx]
      ic_data_q <- ic_data[ic_idx]
      st        <- S_IC
    }
}
```

State dispatch can use the deliberately small `case` form once it lands:

```lean
rule fsm :=
  case st of
  | S_F0 => $stmt(s_f0_body)
  | S_IC => $stmt(s_ic_body)
  | S_EX => $stmt(s_ex_body)
  | default => skip
```

This is equality dispatch, not a promise of Verilog wildcards or parallel-case
behavior. For this partial state list the default is mandatory; a case listing
every value of its finite scrutinee may omit it.

LNP64mini's generated per-thread wake action should keep the hardware visible
while Lean supplies the finite thread set:

```lean
rule wake_threads :=
  for i in $(List.finRange NT) generate {
    if wakeEn & (tstate[i] == FUTEX) then
      tstate[i] <- READY
  }
```

If the body is shared, it can instead be a quoted Lean function and remain
pretty at its definition site:

```lean
def wakeOne (i : Fin NT) : Act :=
  [hwstmt|
    if wakeEn & (tstate[i] == FUTEX) then
      tstate[i] <- READY
  ]

rule wake_threads :=
  for i in $(List.finRange NT) generate
    $stmt(wakeOne i)
```

Balanced trees, `Fin`-generated banks, priority encoders, recursion, and
reusable builders therefore stay ordinary Lean, with their hardware leaves
written as `[hwexpr| ...]` or `[hwstmt| ...]`. Scalar state machines,
conditions, memory traffic, assignments, and generated bodies use hardware
notation. Every mixture produces the same existing `Expr` and `Act` values.

The current LNP64mini exports every scalar and `tstate` register. The excerpt
reflects that existing interface rather than prescribing that every future
internal register be an output.

The current source also has paired authoring names such as `pcReg`/`pc` and
`mDonePort`/`mDone`. A fully converted command intentionally collapses each
pair to one handle token such as `pc` or `m_done`. The staged migration must
update downstream Lean references or provide temporary, explicitly deprecated
aliases; it must not add an alias field to the hardware syntax and recreate the
name-drift problem. This is a Lean source-API change, not a `Design` or emitted
signal-name change.

## Memory and register-family extension

The scalar command is sufficient for the tutorial but not for a complete
LNP64mini conversion. LNP64mini depends on `Mem`, `RegArray`, initialization,
and memory implementation policy. Their grammar must be designed before the
large migration, not improvised during it.

A candidate readable surface is:

```lean
memory rf : 64 [1024] using Memory.synchronousRead
memory trace_pc : 64 [16]
output reg tlb_base : 32 [8]
```

The final productions must determine without ambiguity:

- memory address width and data width;
- logical depth, the power-of-two restriction, and its diagnostic;
- reset image expressions;
- `syncRead` policy;
- `ackInit` policy;
- `RegArray` versus `Mem` lowering;
- exported versus internal register families;
- the generated Lean handle names and physical signal base names;
- explicit write-port indices at every memory write.

The current `Mem aw dw` represents exactly `2 ^ aw` addresses and carries no
independent depth. Therefore the first memory declaration syntax accepts only
power-of-two depths and derives `aw`; it rejects any other depth with an error
that explains the core limitation. Arbitrary logical depths require a core
representation decision first, not rounding hidden in the grammar.

The declaration syntax must not turn each memory policy into a keyword or
pretend an implementation policy is a behavioral difference.
`Memory.synchronousRead` is a discoverable library value for Loom's declared
synchronous-read/macro-candidate policy and must be documented in those terms,
not presented as a new memory transition semantics. Other initialization or
implementation policies likewise belong after `using` as typed library values;
adding one must not extend grammar.

## Implementation sequence

Each phase leaves the existing raw EDSL usable and keeps core modules free of
the new aggregate import.

### Phase 0: lock the contract with examples

1. Audit every `Expr` and `Act` constructor and write the syntax-to-core table.
2. Record omitted constructs and their reason: ambiguous signedness, missing
   truthiness, dynamic slices, blocking assignment, or absent core semantics.
3. Freeze examples for the tutorial, flat `else if` chains, nested brace
   blocks, expression precedence, `case`, `for ... generate`, explicit memory
   ports, packed struct declarations/literals/updates, quotations inside Lean
   functions, and both escape categories.
4. Decide ASCII spellings for signed/unsigned comparison and bitwise operators
   before any public parser surface ships.
5. Put the frozen examples in front of several junior hardware engineers with
   no explanation and ask them to narrate the cycle behavior. Treat every
   plausible misreading as syntax or diagnostic evidence, not user failure.
6. Settle zero-width policy and the exact distinction between declaration
   reset values and runtime expressions. Freeze the `case` rules above:
   normalized duplicate rejection, finite exhaustiveness, optional default
   only for total coverage, and a dead-default warning.
7. Freeze identifier resolution examples covering a design-local signal that
   shadows an imported constant, two viable non-signal candidates, and an
   explicit fully qualified disambiguation.

### Phase 1: wrappers and scalar expression/statement syntax

1. Add a syntax module that imports only the existing authoring core.
2. Declare `hwexpr` and `hwstmt` plus `[hwexpr| ...]` and `[hwstmt| ...]`.
3. Implement pure constructor lowering with macros.
4. Implement `<-`, bare-identifier/literal lifting, and escape elaborators with
   expected-type propagation.
5. Add `Input`, `Input.rd`, its coercion, and `addWireInput` additively.
6. Test that an input cannot reach `Reg.set` even when the friendly diagnostic
   is bypassed.
7. Implement brace blocks and the structural flat `else if` grammar; do not
   depend on parser longest-match for branch ownership.
8. Prototype `case` lowering and diagnostics, but allow its public shipment to
   follow the scalar tutorial surface.
9. Add `actFor` and `for i in $(list) generate body`, accepting ordered
   `List α` only and elaborating the body under a hygienic Lean binder.
10. Support `[hwexpr| ...]` and `[hwstmt| ...]` under ordinary Lean lambdas,
    maps, folds, and definitions without requiring command-generated metadata.

### Phase 2: scalar `hardware` command

1. Parse declaration-first scalar inputs and registers followed by rules.
2. Generate handles and rule definitions in the current namespace.
3. Accumulate `Declarations` and emit `Design.ofDecls` using the command token
   only as the design's string name.
4. Elaborate optional register initializers against expected `BitVec w` and
   preserve their values in `RegDecl.init`.
5. Elaborate `output wire` values at expected `Expr w`, generate their readable
   expression definitions, and lower them only through `addCombOutput`.
6. Preserve source locations with `withRef` and declaration ranges.
7. Implement collision checks across user names, generated names, reserved
   suffixes, and the current environment.
8. Generate public `_name` lemmas and reserve their names.
9. Add `Loom.Hw.Dsl` as the opt-in aggregate. Existing imports see no syntax or
   delaborator changes.

### Phase 3: proof presentation

1. Add the scoped environment extension keyed by the full generated `design`
   constant name.
2. Implement `hw_unfold design` as a fixed tactic using per-design metadata.
3. Add conservative expression and action unexpanders that produce wrappers.
4. Keep read-collapsing local to wrapper reconstruction.
5. Confirm that partially simplified expressions fall back cleanly to core
   notation rather than printing invalid DSL.

### Phase 4: tests before migration

Add positive elaboration and structural equality tests for every production,
then golden diagnostic tests for:

- flat `else if` ownership and rejection of an unbraced nested `if` branch;
- sequencing and empty/nested brace blocks;
- every precedence boundary;
- writes to inputs;
- writes to combinational outputs, and same-cycle evaluation of valid
  `output wire` observations without changing `Design.cycle`;
- target/RHS and splice width mismatches;
- register reset-value width mismatches;
- invalid widths and dynamic slice attempts;
- non-exhaustive `case` without a default;
- exhaustive `case` without a default (accepted) and with a dead default
  (warning);
- duplicate `case` labels both textually and after normalization;
- non-final default and a pattern of the wrong width;
- design-local signal precedence over an imported constant;
- ambiguity between viable non-signal candidates, plus fully qualified
  disambiguation;
- empty, singleton, and nested `for ... generate` bodies;
- generated write ordering, including two iterations writing the same target;
- a hygienic generate binder that shadows an imported non-signal name without
  capture, and rejection when it collides with a design-local signal;
- static `Fin` family indexing versus dynamic `Expr` indexing, including the
  informational cost diagnostic;
- quotations embedded in Lean functions, maps, folds, and reusable actions;
- duplicate registers, inputs, rules, and cross-category names;
- collisions with `design`, `declarations`, generated suffixes, and an existing
  Lean declaration;
- declarations after the first rule;
- unsupported or ambiguous operator spellings.

Packed-struct golden tests cover:

- exact field offsets, total width, first-field-MSB layout, and no padding;
- expression projection, complete construction, whole-value update, equality,
  `.bits`, and `fromBits` lowering;
- packed registers, inputs, combinational outputs, memories, and channels;
- rejection of missing, duplicate, unknown, and wrong-width fields;
- single and multiple partial field writes, conditional merges, disjoint
  cross-rule writers, same-field last-writer diagnostics, whole-then-field and
  field-then-whole ordering, and composition with a raw whole-register action;
- start-of-cycle RHS reads after a field write and implicit whole-record
  arithmetic rejection;
- rejection of out-of-bounds core slices plus evaluator/compiler/certified-
  simulator agreement for valid `Act.writeSlice` actions;
- rejection of assignment between distinct packed types with the same width;
- reset packing through the same layout used by expression evaluation;
- delaboration of recognized layouts and visible fallback for an arbitrary
  slice/concatenation tree; and
- structural equality and byte-identical vector RTL against a handwritten
  scalar packed implementation.

Semantic teaching diagnostics receive their own golden tests:

- a register written and then read later in the same rule;
- one register written more than once in a rule;
- one register written by several ordered rules;
- suppression at an intentional site without suppressing other findings.

Proof-shape tests lower an FSM-sized `case` and exercise the standard invariant
workflow with the tactics used elsewhere in Loom. They record goal count,
nesting, and whether branch hypotheses retain recognizable case labels. `case`
does not graduate from v1-adjacent status until this is usable. If ordinary
splitting is not sane, add and test per-rule case-split metadata/lemmas before
the LNP64mini FSM migration; do not leave that repair to individual proofs.

Round-trip tests parse each supported expression and action, delaborate it,
reparse the wrapper, and compare the lowered core term. Separate negative tests
ensure ordinary `Reg.rd` terms outside wrappers are not collapsed.

### Phase 5: tutorial conversion

1. Convert only the saturating-counter declarations and rule.
2. Keep the namespace, generated names, theorem statements, compiled-RTL proof,
   runner, and emit call unchanged.
3. Replace broad handwritten unfolding lists with generated name lemmas and
   `hw_unfold design` only where the resulting goals are smaller and clearer.
4. Update the tutorial's execution story: the Design-derived verified simulator
   is the default path; a mirrored `Ref.step` is optional independent
   differential validation, not a required second implementation.
5. Run the complete existing tutorial, simulation, compiler, emission, parser,
   and axiom-audit gates.

### Phase 6: packed hardware structs

1. Gate this syntax phase on the `HwPacked`-style wrappers, inverse/layout laws,
   and bounded `Act.writeSlice` constructor specified in `PLATONIC.md`, including
   its evaluator, compiler, footprint, simulator, artifact, and correctness
   cases. Those are core prerequisites, not implementations owned here.
2. Add `packed struct` for named scalar fields and generate the semantic Lean
   record, layout metadata, typed views, pack/unpack instance, projection
   helpers, and collision-checked public names.
3. Generalize declaration type positions to distinguish scalar widths from
   registered packed types with source-local ambiguity and unknown-type errors.
4. Add complete record literals, field projection, whole-value update,
   equality, `.bits`, and `fromBits`; reject implicit whole-record operations.
5. Lower a packed-register field lvalue directly to bounded `Act.writeSlice`,
   preserving the field's source metadata and expected RHS width. Reject input,
   combinational-expression, `.bits`, and memory-element field lvalues.
6. Carry the packed type identity—not only its total width—through register,
   input, output, memory-element, and channel elaboration.
7. Add faithful packed delaboration and `#show_hardware` reconstruction guarded
   by layout lookup and structural round-trip equality.
8. Run the packed golden matrix above and convert one real LNP64mini request or
   pipeline bundle without changing its packed bits, simulator behavior,
   proofs, or emitted RTL.

### Phase 7: memories and register families

1. Design and review the `Mem`/`RegArray` declaration grammar against actual
   LNP64mini cases.
2. Add memory-read expressions and explicit-port memory-write statements.
3. Lower initialization and implementation-policy modifiers into the existing
   `Declarations.addMem` fields without weakening emission checks.
4. Add family indexing, generated families, and family initialization.
5. Make static `Fin` and dynamic `Expr` family indices lower through the
   existing `RegArray` operations with no duplicated semantics.
6. Test multiple write sites, port ordering, sync-read obligations, reset
   images, non-power-of-two depths, and policy diagnostics.

### Phase 8: channel syntax and system composition

1. Freeze the five-entry channel syntax-to-core table, unavailable-operation
   behavior, invalid-empty-data rule, and full co-tick policy examples before
   adding productions.
2. Add channel observations/statements to `hwexpr`/`hwstmt`, lowering only to
   the existing `Chan.canEnq`, `canDeq`, `deq`, `enq`, and `pop` definitions.
   Include canonical `receive value from q then body` as hygienic syntax for one
   `canDeq` guard, one bound `deq`, the body, and one appended `pop`.
3. Implement branch-sensitive send/consume footprint checking over lowered
   actions. Point at both sites for a sequential or cross-rule conflict, and
   require analyzable metadata from statement escapes that touch endpoints.
4. Implement the `system` grammar for any number of named clocks plus typed term
   positions for one `ClockRel`, one `SystemResetPolicy`, optional channel
   policy, and per-channel realization selection. Supply discoverable
   `Clock.*`, `Reset.*`, `Chan.*`, and `Cdc.*` library aliases; do not encode
   individual strategies as grammar or expose `.unconstrained` as a duplicate
   stock alias for `Clock.asynchronous`.
5. Reuse the `hardware` item elaborators for inline islands and add the
   `:= Design` and `extends Design where` forms without a second island AST.
   Check referenced-handle membership immediately from metadata/reducible
   declarations; reject `extends` when it cannot be established and direct the
   author to compose the opaque/parametric Design in Lean before using `:=`.
6. Derive source/sink endpoint transforms solely from connections, with stable
   connection-order folding and source-local direction diagnostics.
7. Generate the checked `SystemBuilder`/`System` through the existing APIs and
   preserve `SystemBuilder.check` as the authoritative structural gate.
8. Freeze system-qualified default island module names, top port/reset naming,
   reserved endpoint stems, and collision checks in their actual emitted
   namespaces. Document the existing fixed `loom_system` top and defer
   configurable top naming to the owning emitter plan.
9. Elaborate the term after `realize ... with` at the existing realization
   selection type. Supply `Cdc.synchronousFifo`, `.grayFifo`, and
   `.recoverableGrayFifo` as library aliases for the existing
   `RealizationKind`s, then construct the existing total per-route
   `RealizationPlan`, supporting mixed same-clock and cross-clock routes.
   Diagnose clock-family and reset-policy mismatches at the terms.
10. Add fixed `system_lift` and certified-view syntax backed by full-name
    metadata and the existing lookup/slot theorems.
11. Add `#show_system` default/channel/physical views over existing typed
    inventory, timing, reset-intent, physical-requirement, and optional backend
    report values; no second report model or manufactured PASS result.
12. Add `#run_system` as syntax over the existing named `SchedulePrefix` and
    checked System/CertifiedSystem runners, including multi-clock tick events,
    source-local clock resolution, and readable result projection.

Channel/system golden diagnostics cover unguarded `data`; double send/consume;
`receive` binding scope, empty-channel no-op behavior, and exactly one appended
consume; unanalyzable endpoint escapes; handles outside an extended Design;
duplicate or unused clocks, channels, and islands; malformed global/pairwise
clock relations; missing or repeated connections; wrong endpoint direction;
undeclared clock use; missing reset policy; malformed width/depth/policy;
grouped realization coverage and duplicate membership; clock-family or
reset/recovery mismatch; unsupported top projection of an island `CombOutput`;
emitted-name collisions; and direct cross-island signal references.

### Phase 9: realization syntax and faithful inspection

1. Define `Cdc.synchronousFifo`, `Cdc.grayFifo`, and
   `Cdc.recoverableGrayFifo` as discoverable aliases for the existing three
   `RealizationKind`s, then elaborate `realize ... with profile` against that
   type. Adding a profile must not extend grammar. The pretty layer adds no FIFO
   controller, synchronizer, recovery protocol, storage implementation,
   refinement theorem, or artifact path.
2. Enforce each existing profile's real depth/clock/reset constraints at the
   clause: synchronous depth positive and clocks equal; Gray depth at least two
   and power-of-two, and mandatory for distinct clocks; recoverable Gray paired
   with independent-flush policy. Warn on needless coordinated-reset Gray use
   for equal clock names. Do not expose fake tuning tokens.
3. Give the selected existing realization and all of its behavioral
   controller/storage Designs stable public aliases. Keep only generated proof
   plumbing, structural coordinates, and intermediate endpoint transforms
   private.
4. Lower `realize q with $(binding)` to the existing certified-binding escape,
   with expected-type propagation and errors at the splice.
5. Keep target storage entirely in the library/evidence layer: its constructor
   uses the existing exact `PhysicalLeaf` substitution seam and yields a
   certified binding consumed through `$(binding)`. The named assumption must
   remain visible in inspection; no target-storage keyword is added.
6. Implement `#show_hardware` as a faithful canonical Design renderer. Require
   pretty-print/reparse structural equality before labeling output as pretty
   hardware and visibly fall back to core notation when reification fails.
7. Keep ordinary architecture-level delaboration at the logical system/channel
   level; explicit inspection and component-level goals show the existing
   controller, synchronizer, Gray, flag, and storage Designs readably.
8. Test every stock component's pretty round trip, its structural identity with
   the existing `AsyncFifoDesign`/storage value, and identity between its
   individual emitted RTL and the module already present in `system.v`.
9. Run the existing emission, mechanical CDC-boundary, exact-artifact, neutral
   synthesis-sanity, and axiom-audit gates unchanged. Target brand/primitive
   syntax remains out of scope even though a typed leaf escape is supported.

Realization golden diagnostics cover a missing realization; synchronous/Gray
clock mismatch; invalid Gray depth; coordinated/recovery mismatch; duplicate
realization clauses; binding and storage-leaf splice type mismatch; island or
realization-component certification failure; incomplete existing binding or
physical-requirement coverage; and an unrenderable `#show_hardware` value with
an explicit core fallback.

### Phase 10: two-clock syntax validation

1. Convert the small existing two-clock example to `system` syntax and require
   equality with its handwritten `System`, identical crossing inventory,
   certified replay agreement, exact current `system.v`, and unchanged axiom
   closure.
2. Exercise `#run_system` with source-only, sink-only, aligned, rejected, and
   canonical adversarial prefixes through the existing runner APIs. Include a
   coincident event accepted by `asynchronous` and rejected by `interleaved`.
3. Run cold-read sessions focused on unavailable sends, empty data, consume
   timing, an aligned variant's full co-ticks under both policies, and
   neighboring statements that are not acceptance-guarded.
4. Freeze channel vocabulary only after recurring misreadings have been fixed
   in syntax or source-local diagnostics.

### Phase 11: SoC Fabric Gauntlet usability validation

Use [`SOC_FABRIC_GAUNTLET.md`](SOC_FABRIC_GAUNTLET.md) as the first
multi-route acceptance test rather than inventing synthetic parser fixtures:

1. Express its packed request, response, and audit values with `packed struct`
   and preserve the exact registered layouts.
2. Author its client, arbiter, register-service, and monitor islands with
   ordinary Lean parameterization and pretty hardware bodies.
3. Require explicit `reset Reset.together`, all seven connections, and grouped
   `Cdc.synchronousFifo`/`Cdc.grayFifo` selections with no wildcard default.
4. Prefer `receive` for ordinary dequeue-and-consume rules and retain primitive
   `hasData`/`data`/`consume` only where arbitration genuinely inspects a head
   before deciding to consume it.
5. Use `#show_system` to review the mixed realization plan, FWFT storage,
   half-rate sink contract, reset delivery, synchronizer/Gray paths, and neutral
   physical requirements without generated-coordinate noise.
6. Require equality with the handwritten `System`/`RealizationPlan`, the same
   schedule theorems and replay results, exact artifact identity, and unchanged
   proof/evidence boundary before converting the canonical source.
7. Cold-read the final file with SoC designers and junior hardware engineers.
   Ask them to identify each arbitration point, CDC route, backpressure path,
   reset loss behavior, and target-specific assumption. A fact they can learn
   only by opening generated Lean is a presentation failure.

This phase validates syntax and naming only. It does not make the pretty plan
responsible for the gauntlet's hardware, proofs, FPGA campaigns, or evidence
model.

### Phase 12: staged LNP64mini conversion

Convert by coherent blocks rather than rewriting `Core.lean` at once:

1. ports, scalar handles, and direct read aliases;
2. pulse defaults and observation-only rules;
3. trace ring and registered memory-read rules;
4. cache latch/fill rules and explicit memory ports;
5. small FSM arms;
6. command handling and larger dispatch trees;
7. register families, generated thread-table actions, and TLB structures;
8. remaining rules and declaration assembly;
9. the telemetry `system` surface, explicit realization, component inspection,
   and readable schedule replay.

After every block, require equality of the lowered `Design` or an equivalent
structural characterization, the existing `DesignWF` and sync-read checks,
FastEval/DagEval agreement, deterministic emitted RTL, and the current
LNP64mini behavioral and board-facing regression suite. Generated Verilog
should remain byte-identical whenever only authoring syntax changed; any
difference stops the migration for review.

Do not mechanically force balanced reductions, priority trees, recursion, or
host-side algorithms into new statement syntax. Use ordinary Lean composition
with pretty quotations at the hardware leaves. Conversely, use
`for ... generate` when a `List.finRange` fold merely replicates a visible
action body; hiding that body in a raw constructor fold defeats the readability
goal. The success criterion is a clear boundary, not eliminating Lean from a
Lean EDSL or hiding hardware behind it.

## Completion criteria

The pretty layer is complete when:

1. The tutorial design is written once in the new syntax and all existing
   semantic, simulation, compilation, and emission consumers use the generated
   definitions.
2. Every supported token has a documented one-to-one core meaning.
3. Width, mutability, collision, and static-slice errors point at user syntax.
4. Wrapped delaborator output reparses to the same core term.
5. Importing lower-level hardware modules does not activate the new syntax or
   pretty-printers.
6. `hw_unfold` is isolated per fully qualified design.
7. A representative LNP64mini block reads in the form shown above while its
   generated simulator, proof obligations, and checked RTL path remain
   unchanged.
8. Full LNP64mini migration preserves the existing design and emitted RTL, or
   explicitly identifies and reviews any intentional semantic change rather
   than hiding it inside syntax conversion.
9. Cold-reading trials with junior hardware engineers find no recurring
   incorrect interpretation of assignment timing, branch ownership, widths,
   signedness, or memory-port behavior; any recurring misreading is addressed
   in syntax or a source-local teaching diagnostic before declaring v1 stable.
10. `case` rejects normalized duplicate labels, handles exhaustive/default
    behavior as specified, and has a tested proof workflow on an FSM-sized
    rule rather than merely acceptable parser output.
11. Bare identifiers follow the documented signal-first, unique-candidate
    resolution rule, and every ambiguous non-signal use fails before it can
    select the wrong netlist expression.
12. Parameterized hardware keeps its generated body visible through
    quotations and `for ... generate`; Lean maps, folds, functions, and
    recursion compose with those quotations while lowering to the unchanged
    finite `Expr`/`Act` core.
13. The small two-clock example and LNP64mini telemetry system use first-class
    clocks, islands, logical channels, and connections while lowering to their
    existing checked `System`/`CertifiedSystem` values and exact artifacts.
14. The library values `Cdc.synchronousFifo`, `Cdc.grayFifo`, and
    `Cdc.recoverableGrayFifo` select the existing total per-route realization
    kinds, including mixed physical plans; adding another profile requires no
    grammar change. The Gray profile supports every currently certified
    power-of-two depth at least two and preserves the exact artifact/axiom
    boundary and gate rejecting uncertified handwritten behavioral CDC RTL.
15. Architecture syntax does not force every system author to restate Gray
    logic, synchronizer stages, FIFO controllers, flag equations, and storage
    ports. The realization choice is nevertheless explicit, and every emitted
    behavioral component is a stable public, inspectable, provable, replaceable
    `Design`; only proof plumbing, structural coordinates, and wrappers may
    remain private. Physical requirements are not authoring syntax, but they
    remain complete and inspectable through `#show_system ... physical`.
16. Combinational outputs remain typed pure observations. Optional target
    storage is constructed as a typed library/evidence binding consumed through
    the universal `$(binding)` escape, genuinely replaces the portable leaf,
    and displays its named assumption rather than becoming a default or hidden
    theorem. Target brands, primitive names, and storage strategies do not enter
    the grammar. The system syntax does not silently promise top-level
    projection that the existing renderer lacks.
17. Every channel token has the frozen availability, empty-data, request, and
    full co-tick behavior above; canonical `receive` structurally guards data
    and appends exactly one consume, and the command rejects more than one
    possible send or consume per endpoint event with branch-sensitive
    locations.
18. An `extends` body cannot reference a handle outside the inspectable base
    Design, its new declarations, or its generated endpoints; an opaque base
    is rejected rather than weakening this source-local guarantee.
19. Default inline-island module names are system-qualified, explicit island
    module overrides preserve established artifacts, generated public Lean
    names use `system.channel.component` dot qualification rather than
    underscore concatenation, the existing fixed top naming is documented
    rather than reimplemented, and collision checking follows actual Lean and
    Verilog namespaces rather than one overbroad set.
20. `#show_hardware` labels output as pretty hardware only after a successful
    structural round trip and visibly falls back to core notation otherwise.
21. `#show_system` is only progressive presentation of existing logical,
    realization, timing, reset, physical-intent, and backend-result values; it
    hides mechanical names by default but never hides an assumption or invents
    PASS. `#run_system` remains readable syntax over the existing named schedule
    and checked runners, and cold-read trials confirm the channel vocabulary
    does not teach false acceptance, payload-validity, or consume-timing
    intuitions.
22. Work performed under this plan is limited to syntax, lowering, generated
    metadata/names, diagnostics, faithful presentation, and equivalence-based
    migration. Missing core semantics or implementation capability is deferred
    to its owning plan rather than added here.
23. A basic packed struct has one no-padding, first-field-MSB layout and works
    uniformly in registers, inputs, combinational outputs, memory elements, and
    channels while lowering to the existing total-width core values.
24. Packed literals, projections, updates, reset values, and delaboration all
    use the same generated layout; distinct packed types of equal width remain
    type-incompatible unless explicitly converted through bits.
25. V1 partial packed-register writes lower directly to bounded
    `Act.writeSlice`, compose through existing action/rule accumulation, retain
    independently meaningful rule `Act`s, and keep every RHS read pre-cycle.
26. V1 rejects implicit whole-record arithmetic, incomplete literals, and
    unsupported aggregate kinds rather than inventing semantics, and its vector
    RTL remains structurally/byte equivalent to the corresponding handwritten
    packed core design.
27. Every pretty `system` explicitly names its logical reset policy, while
    derived electrical reset behavior appears in `#show_system` rather than as
    fake configurable syntax; independent flush requires recoverable
    realizations and coordinated reset never silently selects them.
