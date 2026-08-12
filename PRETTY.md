# Pretty Loom hardware DSL

This document is the implementation plan for a readable, beginner-friendly
authoring layer over Loom's existing hardware EDSL. The destination is concise
hardware code that remains an ordinary shallow embedding: syntax elaborates to
the current `Expr`, `Act`, `Reg`, `Mem`, `Declarations`, and `Design` values,
and the kernel, semantics, compiler, verified simulators, and emission boundary
do not acquire a second representation.

The purpose is not to accept or imitate Verilog. It is to make cycle semantics
hard to misread, including for a junior hardware engineer. Hardware nouns and
concepts remain familiar—inputs, outputs, registers, memories, rules, widths,
ports, cycles, bit selects, and slices—but Verilog punctuation survives only
when its familiar reading is exactly Loom's meaning. Loom uses rules instead
of event controls, one explicit next-cycle assignment, explicit signedness,
typed widths, and ordinary Lean as the parameterization language.

The scope includes named multiclock `System`s, but not as an opaque connectivity
language above hidden RTL. Multiclock authoring has three visible levels:

1. the architecture names clocks, ordinary `Design` islands, typed logical
   channels, endpoint direction, and admissible clock relations;
2. an explicit realization selects the actual synthesizable crossing circuit;
3. optional physical evidence binds technology-specific synchronizers or
   memories and states any external assumptions.

The architecture block need not repeat Gray equations, synchronizer registers,
flags, storage ports, or controllers. Those behavioral components are still
ordinary, public, pretty-printable `Design`s—not secret backend machinery—and
an expert can inspect or replace them. Only proof plumbing, generated structural
coordinates, wrappers, and tool constraints remain implementation details.

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
skip
$stmt(term)
```

`$stmt(term)` expects `Act`. It is deliberately distinct from `$(term)`,
which expects `Expr w`; expression and statement escapes never blur.

Logical channel vocabulary is intentionally behavioral rather than
signal-level. `q.canSend`, `q.hasData`, and `q.data` lower to `Chan.canEnq`,
`Chan.canDeq`, and `Chan.deq`; `send value to q` and `consume q` lower to the
already guarded `Chan.enq` and `Chan.pop` actions. Users never author
valid/ready bits, payload wires, acknowledgements, pointer state, or endpoint
maintenance rules. When another register update must occur only with a send or
receive, the user guards the whole block with `canSend` or `hasData`, making
the atomic intent visible.

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
```

Assignments and escapes use term elaborators rather than translation macros.
The `<-` elaborator first elaborates the target, obtains `w` from its
actual `Reg w` type, then elaborates the RHS with expected type `Expr w`. This
works for command-generated handles, handwritten handles, and indexed handles.
It also permits diagnostics at the user's tokens:

```text
cannot assign to input `clk_en`
8-bit target, but this expression has width 1
expected an Expr 8 splice, but the Lean term has type Expr 16
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

The small two-clock example should eventually read:

```lean
system twoClock where
  clock clkA
  clock clkB
  clocks asynchronous

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
      if q.hasData then {
        got <- q.data
        consume q
      }

  connect q from producer to consumer
  realize q as async_fifo using registers
```

The architecture is concise, but the hardware choice is not implicit.
`async_fifo using registers` names a concrete circuit family and its storage
implementation. In v1 it denotes the existing certified depth-two profile:
compiled source and sink controllers, Gray-coded pointers, the existing fixed
two-register synchronization paths, full/empty logic, and compiled
register-bank storage. Those are not configurable-looking tokens over fixed
internals; if Loom later supports another encoding or synchronizer depth, it
gets a distinct certified profile or a real typed parameter.

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
clocks asynchronous
clocks unconstrained
clocks left and right aligned
clocks := $(ClockRel term)

channel name : width depth depthTerm
channel name : width depth depthTerm when full exchange
channel name : width depth depthTerm when full refuse
channel name := $(Chan term)

island name on clockName where hardware-items
island name on clockName module moduleName where hardware-items
island name on clockName := $(Design term)
island name on clockName extends $(Design term) where hardware-items
island name on clockName module moduleName extends $(Design term) where hardware-items

connect channel from sourceIsland to sinkIsland
realize channel as async_fifo using registers
realize channel with $(CertifiedDepthTwoBinding term)
```

Widths and depths are Lean `Nat` terms. `exchange` is the default and maps to
`FullCoTickPolicy.exchange`; `refuse` maps to `refusePush`. The clock relation
forms map directly to `ClockRel.asynchronous`, `.unconstrained`, and `.aligned`.
The escape form admits a custom `ClockRel` without creating a second schedule
language. Reset-release skew is already quantified by the channel refinement
and is not a user declaration. The channel escape reuses an existing typed
`Chan w`; the other forms generate one from the visible width, depth, and
full-queue policy.

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
island's emitted Design/module name is its island name, while `module` supplies
an explicit user-owned name. An existing Design retains its name unless the
optional module override is present. This distinction preserves literal RTL
identity during migration without exposing structural CDC module names.

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

The identifier after `system` is the Lean name of the generated checked
`System`, not a CDC module name. For `system twoClock`, the public results are
conceptually:

```lean
twoClock_q          : Chan 8
twoClock_producer   : Design
twoClock_consumer   : Design
twoClock_builder    : SystemBuilder
twoClock            : System
twoClock_q_source_control : Design
twoClock_q_sink_control   : Design
twoClock_q_storage_writer : Design
twoClock_q_storage_reader : Design
twoClock_q_realization    : CertifiedDepthTwoBinding
twoClock_certified        : CertifiedSystem twoClock
twoClock_artifact         : CertifiedRealizedSystem ...
```

System-local public handles and final island designs use the system-name prefix
to avoid collisions between several systems in one Lean namespace; inside the
command their short architectural names remain `q`, `producer`, and `consumer`.
The realization and its behavioral components are generated only when a
realization is requested. Their exact public API should follow the existing
binding structure rather than duplicating it, but it must provide stable access
to every emitted behavioral `Design`. Base-island intermediates, endpoint
transforms, lookup equalities, proof terms, ordered-coverage witnesses, and
structural coordinates may use private generated names. All public and private
generated names participate in collision and reserved-suffix checks.

### Explicit and inspectable CDC realization

`realize q as async_fifo using registers` selects the unconditional
compiler-only depth-two route already closed by `CertifiedRealizedSystem`. It
requires `q` to have depth two, obtains a `CertifiedDesign` for each final
island, derives the `Chan.Refinement`, constructs the existing compiled
controllers and register-bank storage, proves ordered coverage, and produces
the exact `system.v` artifact. The wording names what is built: `portable` is a
useful property of this realization, but it is not a circuit topology.

The stock realization is inspectable from source and proof states. The exact
command spelling is a Phase 7 decision, but the required experience is:

```lean
#show_hardware twoClock_q_source_control
#show_hardware twoClock_q_sink_control
#show_hardware twoClock_q_storage_writer
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

Optional FPGA RAM and ASIC SRAM storage remain evidence-layer choices with one
named assumption each. Generic `Loom.Hw.Dsl` must not import target evidence or
silently prefer a macro. A later, separate realization command may accept an
explicit `AsyncQueueStorage.Binding` Lean term after the adapter from that
binding to the artifact path is finalized; the pretty `system` syntax itself
continues to describe the same technology-neutral channel. V1 ships the
explicit register-backed asynchronous FIFO profile rather than freezing
premature vendor syntax.

### LNP64mini multiclock destination

The production-scale telemetry system should reduce to the architecture it
actually expresses:

```lean
system lnpMulticlock where
  clock core_clk
  clock observer_clk
  clocks asynchronous

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
      if telemetry.hasData then {
        observed_pc <- telemetry.data
        observed_count <- observed_count + 1
        consume telemetry
      }

  connect telemetry from core to observer
  realize telemetry as async_fifo using registers
```

The command may need a source-local certificate escape for an exceptionally
large existing island when automatic kernel reduction exceeds normal limits,
but that escape supplies a `CertifiedDesign` term for the final island. The
ordinary system author does not assemble connection records, lookup proofs,
coverage equations, or clock-rule proofs. The FIFO controls and storage remain
named public component Designs, however; they are implementation hardware, not
proof bureaucracy.

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
- a same-clock connection explains that it can lower synchronously, while a
  cross-clock connection requires certified realization before emission;
- an `async_fifo using registers` channel with depth other than two points at
  the depth and states the currently certified implementation limit;
- a missing realization on an emitted cross-clock channel says that a logical
  channel is semantics, not a circuit, and offers the certified profile;
- an island certificate failure points at the island body or supplied design;
- a realization-component failure names and opens the source controller, sink
  controller, or storage Design that failed, rather than calling it a backend
  error;
- a macro storage selection, once supported, displays its one named external
  assumption rather than presenting it as a theorem.

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

  sync memory dmem : 64 [512]
  sync memory rf : 64 [1024]
  sync memory uart_mem : 8 [256]
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
sync memory rf : 64 [1024]
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

The declaration syntax must not pretend an implementation policy is a
behavioral difference. For example, `sync` above means Loom's declared
synchronous-read/macro-candidate policy and must be documented in those terms,
not presented as a new memory transition semantics.

## Implementation sequence

Each phase leaves the existing raw EDSL usable and keeps core modules free of
the new aggregate import.

### Phase 0: lock the contract with examples

1. Audit every `Expr` and `Act` constructor and write the syntax-to-core table.
2. Record omitted constructs and their reason: ambiguous signedness, missing
   truthiness, dynamic slices, blocking assignment, or absent core semantics.
3. Freeze examples for the tutorial, flat `else if` chains, nested brace
   blocks, expression precedence, `case`, `for ... generate`, explicit memory
   ports, quotations inside Lean functions, and both escape categories.
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

### Phase 6: memories and register families

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

### Phase 7: first-class systems and certified multiclock realization

1. Add channel observations/statements to `hwexpr`/`hwstmt`, lowering only to
   `Chan.canEnq`, `canDeq`, `deq`, `enq`, and `pop`.
2. Implement the `system` grammar for clocks, clock relations, channels,
   islands, connections, and an explicit per-channel realization clause.
3. Reuse the `hardware` item elaborators for inline islands and add the
   `:= Design` and `extends Design where` forms without a second island AST.
4. Derive source/sink endpoint transforms solely from connections, with stable
   connection-order folding and source-local direction diagnostics.
5. Generate the checked `SystemBuilder`/`System` and preserve the existing
   `SystemBuilder.check` as the authoritative structural gate.
6. Implement `async_fifo using registers` as the named profile for the existing
   compiled depth-two controllers, fixed synchronization paths, Gray logic, and
   register-bank storage. Do not advertise fixed details as configurable
   parameters.
7. Give the realization and every behavioral controller/storage `Design`
   stable public names. Keep only proof plumbing, structural coordinates, and
   intermediate endpoint transforms private.
8. Add an inspection command that renders those component Designs through the
   pretty delaborator, plus `realize channel with $(binding)` for an expert
   certified replacement.
9. Generate island certificates, channel refinements, ordered coverage, and
   `CertifiedRealizedSystem` through the existing certificate types and gate.
10. Add fixed `system_lift` and certified-view helpers backed by full-name
   metadata and the existing lookup/slot theorems.
11. Keep ordinary architecture-level delaboration at the logical
   system/channel level, while explicit inspection and component-level goals
   show controller, synchronizer, Gray, flag, and storage hardware readably.
12. Test the small `TwoClock` and production LNP64mini telemetry systems for
   structural equality with their handwritten `System`s, identical crossing
   inventories, certified replay agreement, exact `system.v` bytes, and the
   exact axiom closure `[propext, Classical.choice, Quot.sound]`.
13. Test each public realization component against the existing
    `AsyncFifoDesign`/storage Design and assert that its individually emitted
    RTL is the hardware included in the final structural artifact.
14. Run the mechanical boundary gate and assert that no uncertified handwritten
    behavioral CDC RTL can enter through the new command. Leave FPGA/ASIC
    storage syntax deferred until the explicit evidence binding has an artifact
    adapter.

System golden diagnostics cover duplicate/unused clocks, channels, and
islands; missing or repeated connections; wrong endpoint direction; undeclared
clock use; malformed channel width/depth/policy; a missing realization;
non-depth-two `async_fifo using registers`; island or realization-component
certification failure; incomplete ordered binding coverage; and direct
cross-island signal references. Same-clock systems also remain tested against
ordinary synchronous `System.elaborate`.

### Phase 8: staged LNP64mini conversion

Convert by coherent blocks rather than rewriting `Core.lean` at once:

1. ports, scalar handles, and direct read aliases;
2. pulse defaults and observation-only rules;
3. trace ring and registered memory-read rules;
4. cache latch/fill rules and explicit memory ports;
5. small FSM arms;
6. command handling and larger dispatch trees;
7. register families, generated thread-table actions, and TLB structures;
8. remaining rules and declaration assembly.

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
14. The named register-backed asynchronous FIFO realization generates the
    complete compiled depth-two binding, preserves the exact `system.v` bytes
    and axiom closure, and still passes the gate rejecting uncertified
    handwritten behavioral CDC RTL.
15. Architecture syntax does not force every system author to restate Gray
    logic, synchronizer stages, FIFO controllers, flag equations, and storage
    ports. The realization choice is nevertheless explicit, and every emitted
    behavioral component is a stable public, inspectable, provable, replaceable
    `Design`; only proof plumbing, structural coordinates, wrappers, and
    constraints may remain private.
16. Combinational outputs remain typed pure observations, and optional
    FPGA/ASIC storage remains an explicit evidence-layer choice with its named
    assumption rather than a default or hidden theorem.
